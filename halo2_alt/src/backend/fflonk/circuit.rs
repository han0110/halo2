use crate::{
    backend::{fflonk::keygen::query_infos, Circuit},
    protocol::{Expression, PolynomialRef, Protocol},
    util::{
        chain, div_ceil, felt_from_bool,
        halo2::{
            batch_invert_assigned, convert_expressions, ColumnType, Permutation,
            PreprocessCollector, WitnessCollector,
        },
        horner, izip, log2_ceil, powers,
    },
};
use halo2_proofs::{
    halo2curves::ff::{BatchInvert, Field, PrimeField, WithSmallOrderMulGroup},
    plonk::{self, ConstraintSystem, Error, FloorPlanner, Gate},
    poly::EvaluationDomain,
};
use rand_core::RngCore;
use rayon::{current_num_threads, prelude::*};
use std::{
    collections::HashMap,
    fmt::Debug,
    hash::Hash,
    iter::{self, Cycle, Product, Sum},
    mem,
    ops::Range,
};

#[derive(Clone, Debug)]
pub struct FflonkCircuit<F, C>
where
    F: Field,
    C: Debug + plonk::Circuit<F>,
    C::Config: Debug,
{
    circuit: C,
    circuit_config: C::Config,
    cs: ConstraintSystem<F>,
    protocol: Protocol<F>,
    // NOTE: In the future we can traitify these 2 to let users plug their own protocols,
    //       the methods might contain one that takes `protocol` and return a diff to protocol to
    //       be merged later, and the other takes `(phase, values)` and returns some witnesses.
    lookups: Vec<LogUp<F>>,
    permutation: Option<ZigZagPermutation<F>>,
}

impl<F, C> FflonkCircuit<F, C>
where
    F: WithSmallOrderMulGroup<3>,
    C: Debug + plonk::Circuit<F>,
    C::Config: Debug,
{
    pub fn new(k: usize, circuit: C) -> Self {
        let mut cs = ConstraintSystem::default();
        let circuit_config = C::configure(&mut cs);
        let cs = cs;

        // NOTE: To support multi-phase circuit we might need to mess up with the query index,
        //       and lookup and permutation needs to choose which phase to insert their extra
        //       polynomials.
        assert!(
            !cs.advice_column_phase().into_iter().any(|phase| phase != 0),
            "Multi-phase circuit is not yet supported",
        );
        assert!(
            cs.challenge_phase().is_empty(),
            "Multi-phase circuit is not yet supported",
        );

        let column_idx = column_idx(&cs);
        let permutation_columns = cs.permutation().get_columns();
        let num_preprocessed_polys =
            cs.num_selectors() + cs.num_fixed_columns() + permutation_columns.len();
        let num_instance_polys = cs.num_instance_columns();

        let m_offset = num_preprocessed_polys + num_instance_polys + cs.num_advice_columns();
        let phi_offset = m_offset + cs.lookups().len();
        let z_offset = phi_offset + cs.lookups().len();
        let gamma = 0;
        let beta = 1;

        let lookups = izip!(cs.lookups(), m_offset.., phi_offset..)
            .map(|(lookup, m, phi)| {
                let [input, table] = [lookup.input_expressions(), lookup.table_expressions()]
                    .map(|expressions| convert_expressions(expressions, &column_idx));
                LogUp {
                    input,
                    table,
                    m,
                    phi,
                    gamma,
                    beta,
                }
            })
            .collect::<Vec<_>>();
        let permutation = (!permutation_columns.is_empty()).then(|| {
            let chunk_size = cs.degree() - 2;
            let inputs = permutation_columns
                .iter()
                .map(|column| {
                    column_idx[&(ColumnType::from(*column.column_type()), column.index())]
                })
                .collect::<Vec<_>>();
            let permutations = (cs.num_selectors() + cs.num_fixed_columns()..)
                .take(inputs.len())
                .collect::<Vec<_>>();
            let zs = (z_offset..)
                .take(div_ceil(inputs.len(), chunk_size))
                .collect();
            ZigZagPermutation {
                inputs,
                permutations,
                chunk_size,
                zs,
                gamma,
                beta,
                omega: EvaluationDomain::new(1, k as u32).get_omega(),
            }
        });

        let constraints = {
            let last_row = -(cs.blinding_factors() as i32 + 1);
            let l_0 = &PolynomialRef::<F>::Lagrange(0);
            let l_last = &PolynomialRef::<F>::Lagrange(last_row);
            let l_active = &(PolynomialRef::Constant(F::ONE)
                - Expression::sum((last_row..0).map(PolynomialRef::Lagrange)));
            chain![
                convert_expressions(cs.gates().iter().flat_map(Gate::polynomials), &column_idx),
                lookups
                    .iter()
                    .flat_map(|lookup| lookup.constraints(l_0, l_last, l_active)),
                permutation
                    .as_ref()
                    .map(|permutation| permutation.constraints(l_0, l_last, l_active))
                    .into_iter()
                    .flatten()
            ]
            .collect::<Vec<_>>()
        };

        let phases = {
            let num_lookups = lookups.len();
            let num_zs = permutation
                .as_ref()
                .map(|permutation| permutation.zs.len())
                .unwrap_or_default();
            let has_beta = lookups.iter().any(|lookup| lookup.input.len() > 1) || num_zs > 0;
            match (num_lookups, num_zs) {
                (0, 0) => vec![(cs.num_advice_columns(), 0)],
                (num_lookups, num_zs) => vec![
                    (cs.num_advice_columns() + num_lookups, 1 + has_beta as usize),
                    (num_lookups + num_zs, 0),
                ],
            }
        };

        let protocol = Protocol {
            k,
            num_preprocessed_polys,
            num_instance_polys,
            phases,
            constraints,
        };

        Self {
            circuit,
            circuit_config,
            cs,
            protocol,
            lookups,
            permutation,
        }
    }

    pub fn min_params_k(&self) -> usize {
        let (preprocessed_query_info, phase_infos) = query_infos(&self.protocol);
        let max_combined_degree = chain![
            [preprocessed_query_info.t],
            phase_infos.iter().map(|phase_info| {
                let max_degree = phase_info
                    .constraints
                    .iter()
                    .map(|idx| self.protocol.constraints[*idx].degree().saturating_sub(1))
                    .max()
                    .unwrap_or(1);
                phase_info.t * max_degree
            })
        ]
        .max()
        .unwrap();
        self.protocol.k + log2_ceil(max_combined_degree)
    }
}

fn column_idx<F: Field>(cs: &ConstraintSystem<F>) -> HashMap<(ColumnType, usize), usize> {
    izip!(
        chain![
            (0..cs.num_selectors()).map(|idx| Some((ColumnType::Selector, idx))),
            (0..cs.num_fixed_columns()).map(|idx| Some((ColumnType::Fixed, idx))),
            (0..cs.permutation().get_columns().len()).map(|_| None),
            (0..cs.num_instance_columns()).map(|idx| Some((ColumnType::Instance, idx))),
            (0..cs.num_advice_columns()).map(|idx| Some((ColumnType::Advice, idx)))
        ],
        0..
    )
    .flat_map(|(k, v)| k.map(|k| (k, v)))
    .collect()
}

impl<F, C> Circuit<F> for FflonkCircuit<F, C>
where
    F: PrimeField + Hash,
    C: Debug + plonk::Circuit<F>,
    C::Config: Debug,
{
    type WitnessBuf = Vec<[Vec<Vec<F>>; 2]>;

    fn protocol(&self) -> Protocol<F> {
        self.protocol.clone()
    }

    fn preprocess(&self) -> Result<Vec<Vec<F>>, Error> {
        let n = self.protocol.n();
        let mut collector = PreprocessCollector {
            k: self.protocol.k as u32,
            fixeds: vec![vec![F::ZERO.into(); n]; self.cs.num_fixed_columns()],
            permutation: Permutation::new(self.cs.permutation().get_columns()),
            selectors: vec![vec![false; n]; self.cs.num_selectors()],
            usable_rows: 0..n - (self.cs.blinding_factors() + 1),
        };

        C::FloorPlanner::synthesize(
            &mut collector,
            &self.circuit,
            self.circuit_config.clone(),
            self.cs.constants().clone(),
        )
        .map_err(|_| Error::Synthesis)?;

        let fixeds = batch_invert_assigned(collector.fixeds);
        let selectors = collector
            .selectors
            .into_iter()
            .map(|selectors| selectors.into_iter().map(felt_from_bool).collect());
        let permutations = self
            .permutation
            .as_ref()
            .map(|permutation| permutation.preprocess(n, collector.permutation.into_cycles()));

        Ok(chain![fixeds, selectors, permutations.into_iter().flatten()].collect())
    }

    fn witness(
        &self,
        phase: usize,
        values: &[&[F]],
        challenges: &[F],
        buf: &mut Self::WitnessBuf,
        mut rng: impl RngCore,
    ) -> Result<Vec<Vec<F>>, Error> {
        let n = self.protocol.n();
        let usable_rows = 0..n - (self.cs.blinding_factors() + 1);

        let mut values = match phase {
            0 => {
                let mut collector = WitnessCollector {
                    k: self.protocol.k as u32,
                    phase: phase as u8,
                    instance_values: &values[self.protocol.poly_range().instance],
                    advices: vec![vec![F::ZERO.into(); n]; self.cs.num_advice_columns()],
                    usable_rows: usable_rows.clone(),
                };

                C::FloorPlanner::synthesize(
                    &mut collector,
                    &self.circuit,
                    self.circuit_config.clone(),
                    self.cs.constants().clone(),
                )
                .map_err(|_| Error::Synthesis)?;

                let advices = batch_invert_assigned(collector.advices);

                let values = chain![values.iter().cloned(), advices.iter().map(Vec::as_slice)]
                    .collect::<Vec<_>>();

                *buf = vec![Default::default(); self.lookups.len()];
                let ms = izip!(&self.lookups, buf)
                    .map(|(lookup, buf)| lookup.witness_m(n, &usable_rows, &values, buf))
                    .collect::<Result<Vec<_>, _>>()?;

                chain![advices, ms].collect::<Vec<_>>()
            }
            1 => {
                let phis = izip!(&self.lookups, buf)
                    .map(|(lookup, buf)| {
                        lookup.witness_phi(n, &usable_rows, values, challenges, buf)
                    })
                    .collect::<Vec<_>>();

                let zs = self
                    .permutation
                    .as_ref()
                    .map(|permutation| permutation.witness_zs(n, &usable_rows, values, challenges));

                chain![phis, zs.into_iter().flatten()].collect()
            }
            _ => unimplemented!(),
        };

        values.iter_mut().for_each(|values| {
            values[..]
                .iter_mut()
                .rev()
                .take(self.cs.blinding_factors())
                .for_each(|value| *value = F::random(&mut rng))
        });

        Ok(values)
    }
}

#[derive(Clone, Debug)]
struct LogUp<F> {
    // NOTE: In the future we can extend this to multi-inputs lookup to multi-tables, and sharing
    //       the same `m` and `phi` poly.
    input: Vec<Expression<F>>,
    table: Vec<Expression<F>>,
    m: usize,
    phi: usize,
    gamma: usize,
    beta: usize,
}

impl<F: PrimeField> LogUp<F> {
    fn constraints(
        &self,
        l_0: &PolynomialRef<F>,
        l_last: &PolynomialRef<F>,
        l_active: &Expression<F>,
    ) -> Vec<Expression<F>> {
        let gamma = &PolynomialRef::Challenge(self.gamma);
        let beta = &PolynomialRef::Challenge(self.beta);
        let f = &(horner(&self.input, beta) + gamma);
        let t = &(horner(&self.table, beta) + gamma);
        let m = &PolynomialRef::opaque((self.m, 0));
        let phi = &PolynomialRef::opaque((self.phi, 0));
        let phi_next = &PolynomialRef::opaque((self.phi, 1));
        vec![
            l_0 * phi,
            l_last * phi,
            l_active * (((phi_next - phi) * t + m) * f - t),
        ]
    }

    fn witness_m(
        &self,
        n: usize,
        usable_rows: &Range<usize>,
        values: &[&[F]],
        buf: &mut [Vec<Vec<F>>; 2],
    ) -> Result<Vec<F>, Error>
    where
        F: Hash,
    {
        let evaluate_row = |expressions: &Vec<Expression<F>>, row: usize| {
            expressions
                .iter()
                .map(|expression| {
                    expression.evaluate_felt(&|poly| match poly {
                        PolynomialRef::Constant(constant) => constant,
                        PolynomialRef::Opaque(query) => {
                            let rotated = (row as i32 + query.rotation.0).rem_euclid(n as i32);
                            values[query.index][rotated as usize]
                        }
                        PolynomialRef::Challenge(_)
                        | PolynomialRef::Identity
                        | PolynomialRef::Lagrange(_) => unimplemented!(),
                    })
                })
                .collect::<Vec<_>>()
        };

        *buf = [&self.input, &self.table].map(|expressions| {
            usable_rows
                .clone()
                .into_par_iter()
                .map(|row| evaluate_row(expressions, row))
                .collect::<Vec<_>>()
        });

        let table = buf[1]
            .par_iter()
            .zip(usable_rows.clone())
            .collect::<HashMap<_, _>>();
        let counts = buf[0][usable_rows.clone()]
            .par_iter()
            .map(|input| table.get(&input))
            .try_fold(HashMap::new, |mut counts, row| {
                counts
                    .entry(row?)
                    .and_modify(|count| *count += 1)
                    .or_insert(1);
                Some(counts)
            })
            .try_reduce(HashMap::new, |mut acc, counts| {
                counts.into_iter().for_each(|(row, count)| {
                    acc.entry(row)
                        .and_modify(|acc| *acc += count)
                        .or_insert(count);
                });
                Some(acc)
            })
            .ok_or(Error::Synthesis)?;
        Ok(counts
            .into_iter()
            .fold(vec![F::ZERO; n], |mut m, (row, count)| {
                m[*row] = F::from(count);
                m
            }))
    }

    fn witness_phi(
        &self,
        n: usize,
        usable_rows: &Range<usize>,
        values: &[&[F]],
        challenges: &[F],
        buf: &mut [Vec<Vec<F>>; 2],
    ) -> Vec<F> {
        let gamma = challenges[self.gamma];
        let beta = challenges.get(self.beta).copied().unwrap_or_default();

        let [mut input, mut table] = mem::take(buf).map(|value| {
            value
                .par_iter()
                .map(|row| horner(row, &beta) + gamma)
                .collect::<Vec<_>>()
        });

        let par_chunk_size = div_ceil(2 * n, current_num_threads());
        input
            .par_chunks_mut(par_chunk_size)
            .chain(table.par_chunks_mut(par_chunk_size))
            .for_each(|values| {
                values.batch_invert();
            });

        let sum = input
            .par_iter()
            .zip(&table)
            .zip(values[self.m])
            .map(|((input, table), m)| *input - *table * m)
            .collect::<Vec<_>>();

        let phi = chain![
            chain![sum, [F::ZERO]].scan(F::ZERO, |acc, item| mem::replace(acc, *acc + item).into()),
            iter::repeat(F::ZERO)
        ]
        .take(n)
        .collect::<Vec<_>>();

        if cfg!(feature = "sanity-checks") {
            assert_eq!(phi[usable_rows.end], F::ZERO);
        }

        phi
    }
}

#[derive(Clone, Debug)]
struct ZigZagPermutation<F> {
    inputs: Vec<usize>,
    permutations: Vec<usize>,
    chunk_size: usize,
    zs: Vec<usize>,
    beta: usize,
    gamma: usize,
    omega: F,
}

impl<F: PrimeField> ZigZagPermutation<F> {
    fn constraints(
        &self,
        l_0: &PolynomialRef<F>,
        l_last: &PolynomialRef<F>,
        l_active: &Expression<F>,
    ) -> Vec<Expression<F>> {
        let gamma = &PolynomialRef::Challenge(self.gamma);
        let beta = &PolynomialRef::Challenge(self.beta);
        let [inputs, permutations] = [&self.inputs, &self.permutations].map(|indices| {
            indices
                .iter()
                .map(|idx| PolynomialRef::opaque((*idx, 0)).into())
                .collect::<Vec<_>>()
        });
        let delta_omegas = powers(F::DELTA)
            .take(inputs.len())
            .map(|delta| PolynomialRef::Identity * PolynomialRef::Constant(delta))
            .collect::<Vec<_>>();
        let zs = self
            .zs
            .iter()
            .map(|idx| PolynomialRef::opaque((*idx, 0)))
            .collect::<Vec<_>>();
        let z_0_next = self.zs.first().map(|z_0| PolynomialRef::opaque((*z_0, 1)));
        let one = PolynomialRef::Constant(F::ONE);
        chain![
            zs.first().map(|z_0| l_0 * (z_0 - one)),
            zs.first().map(|z_0| l_last * (z_0 * z_0 - z_0)),
            izip!(
                inputs.chunks(self.chunk_size),
                delta_omegas.chunks(self.chunk_size),
                permutations.chunks(self.chunk_size),
                &zs,
                chain![zs.iter().skip(1), &z_0_next]
            )
            .map(|(inputs, delta_omegas, permutations, z_lhs, z_rhs)| {
                let [lhs, rhs] = [delta_omegas, permutations].map(|ids| {
                    Expression::product(
                        izip!(inputs, ids).map(|(input, id)| input + beta * id + gamma),
                    )
                });
                l_active * (z_lhs * lhs - z_rhs * rhs)
            }),
        ]
        .collect::<Vec<_>>()
    }

    fn preprocess(&self, n: usize, cycles: Vec<Vec<(usize, usize)>>) -> Vec<Vec<F>> {
        let mut permutations = powers(F::DELTA)
            .map(|delta| {
                let mut permutation = vec![F::ZERO; n];
                let chunk_size = div_ceil(n, current_num_threads());
                permutation
                    .par_chunks_mut(chunk_size)
                    .enumerate()
                    .for_each(|(idx, chunk)| {
                        let mut delta_omega = delta * self.omega.pow([(idx * chunk_size) as u64]);
                        chunk.iter_mut().for_each(|value| {
                            *value = delta_omega;
                            delta_omega *= self.omega
                        });
                    });
                permutation
            })
            .take(self.permutations.len())
            .collect::<Vec<_>>();
        for cycle in cycles.iter() {
            let (i0, j0) = cycle[0];
            let mut last = permutations[i0][j0];
            for &(i, j) in cycle.iter().cycle().skip(1).take(cycle.len()) {
                mem::swap(&mut permutations[i][j], &mut last);
            }
        }
        permutations
    }

    fn witness_zs(
        &self,
        n: usize,
        usable_rows: &Range<usize>,
        values: &[&[F]],
        challenges: &[F],
    ) -> Vec<Vec<F>> {
        let gamma = challenges[self.gamma];
        let beta = challenges[self.beta];

        let products = izip!(
            0..,
            self.inputs.chunks(self.chunk_size),
            self.permutations.chunks(self.chunk_size)
        )
        .map(|(chunk_idx, inputs, permutations)| {
            let mut product = vec![F::ONE; usable_rows.len()];

            izip!(inputs, permutations).for_each(|(input, permutation)| {
                let input = values[*input];
                let permutation = values[*permutation];
                product
                    .par_iter_mut()
                    .zip(usable_rows.clone())
                    .for_each(|(product, row)| {
                        *product *= input[row] + beta * permutation[row] + gamma
                    });
            });

            let par_chunk_size = div_ceil(product.len(), current_num_threads());

            product[usable_rows.clone()]
                .par_chunks_mut(par_chunk_size)
                .for_each(|product| {
                    product.batch_invert();
                });

            let deltas = powers(F::DELTA).skip(chunk_idx * self.chunk_size);
            izip!(inputs, deltas).for_each(|(input, delta)| {
                let input = values[*input];
                product.par_chunks_mut(par_chunk_size).enumerate().for_each(
                    |(chunk_idx, product)| {
                        let start = usable_rows.start + chunk_idx * par_chunk_size;
                        let mut beta_delta_omega = beta * delta * self.omega.pow([start as u64]);
                        izip!(start.., product).for_each(|(row, product)| {
                            *product *= input[row] + beta_delta_omega + gamma;
                            beta_delta_omega *= self.omega;
                        });
                    },
                );
            });

            product
        })
        .collect::<Vec<_>>();

        let products = Multizip::new(products.into_iter().map(Vec::into_iter).collect())
            .chain([F::ZERO])
            .scan(F::ONE, |acc, item| mem::replace(acc, *acc * item).into())
            .collect::<Vec<_>>();

        if cfg!(feature = "sanity-checks") {
            assert_eq!(*products.last().unwrap(), F::ONE);
        }

        let mut zs = vec![vec![F::ZERO; n]; self.zs.len()];
        zs[0][usable_rows.end] = F::ONE;
        zs.par_iter_mut().enumerate().for_each(|(col, z)| {
            z[usable_rows.clone()]
                .par_iter_mut()
                .enumerate()
                .for_each(|(row, value)| *value = products[col + self.zs.len() * row])
        });
        zs
    }
}

struct Multizip<T>(Vec<T>, Cycle<Range<usize>>);

impl<T: Iterator> Multizip<T> {
    fn new(values: Vec<T>) -> Self {
        assert_ne!(values.len(), 0);
        let ptr = (0..values.len()).cycle();
        Self(values, ptr)
    }
}

impl<T: Iterator> Iterator for Multizip<T> {
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0[self.1.next().unwrap()].next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.0[0].size_hint().0 * self.0.len();
        (exact, Some(exact))
    }
}
