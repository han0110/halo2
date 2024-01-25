use crate::{
    protocol::Protocol,
    util::{chain, div_ceil, evaluator::Evaluator, izip, lcm, root_of_unity},
};
use blake2b_simd::Params as Blake2bParams;
use halo2_proofs::{
    halo2curves::{
        ff::{Field, FromUniformBytes, PrimeField},
        CurveAffine,
    },
    poly::{Coeff, EvaluationDomain, ExtendedLagrangeCoeff, PinnedEvaluationDomain, Polynomial},
    transcript::{EncodedChallenge, Transcript},
};
use rayon::{current_num_threads, prelude::*};
use std::{collections::BTreeSet, io, iter, ops::Deref};

mod circuit;
mod keygen;
mod prover;
mod verifier;

pub use circuit::FflonkCircuit;
pub use keygen::{keygen_pk, keygen_vk};
pub use prover::create_proof;
pub use verifier::verify_proof;

#[derive(Clone, Debug)]
struct QueryInfo<F> {
    num_polys: usize,
    t: usize,
    omega_t: F,
    omega_kt: F,
    omega_kt_inv: F,
    rotations: BTreeSet<i32>,
}

impl<F: PrimeField> QueryInfo<F> {
    fn new(k: usize, num_polys: usize, rotations: BTreeSet<i32>) -> Self {
        assert!(rotations.contains(&0));
        // NOTE: Currently it only supports `t` as some power of 2, but we can find other domain
        //       with smaller size (e.g. 3) that `num_polys` fits to reduce prover opening cost.
        let t = num_polys.next_power_of_two();
        let omega_t = root_of_unity(t);
        let omega_kt = root_of_unity::<F>(t << k);
        let omega_kt_inv = omega_kt.invert().unwrap();
        Self {
            num_polys,
            t,
            omega_t,
            omega_kt,
            omega_kt_inv,
            rotations,
        }
    }

    fn roots(&self, lcm_t: usize, x_lcm_t: F, rotation: i32) -> impl Iterator<Item = F> + '_ {
        assert_eq!(lcm_t % self.t, 0);
        let x_t = x_lcm_t.pow([(lcm_t / self.t) as u64]);
        let omega = if rotation >= 0 {
            self.omega_kt.pow([rotation as u64])
        } else {
            self.omega_kt_inv.pow([(rotation as i64).unsigned_abs()])
        };
        iter::successors(Some(omega * x_t), |root| Some(self.omega_t * root)).take(self.t)
    }
}

#[derive(Clone, Debug)]
struct PhaseInfo<F> {
    query_info: QueryInfo<F>,
    constraints: Vec<usize>,
}

impl<F> Deref for PhaseInfo<F> {
    type Target = QueryInfo<F>;

    fn deref(&self) -> &Self::Target {
        &self.query_info
    }
}

impl<F: PrimeField> PhaseInfo<F> {
    fn new(query_info: QueryInfo<F>, constraints: Vec<usize>) -> Self {
        Self {
            query_info,
            constraints,
        }
    }
}

#[derive(Debug)]
pub struct VerifyingKey<C: CurveAffine> {
    domain: EvaluationDomain<C::Scalar>,
    protocol: Protocol<C::Scalar>,
    preprocessed_commitment: C,
    preprocessed_query_info: QueryInfo<C::Scalar>,
    phase_infos: Vec<PhaseInfo<C::Scalar>>,
    transcript_repr: C::Scalar,
}

impl<C: CurveAffine> VerifyingKey<C> {
    fn new(
        protocol: Protocol<C::Scalar>,
        preprocessed_commitment: C,
        preprocessed_query_info: QueryInfo<C::Scalar>,
        phase_infos: Vec<PhaseInfo<C::Scalar>>,
    ) -> Self
    where
        C::Scalar: FromUniformBytes<64>,
    {
        let mut vk = Self {
            domain: EvaluationDomain::new(protocol.degree() as u32, protocol.k as u32),
            protocol,
            preprocessed_query_info,
            preprocessed_commitment,
            phase_infos,
            transcript_repr: C::Scalar::ZERO,
        };

        vk.transcript_repr = {
            let mut hasher = Blake2bParams::new()
                .hash_length(64)
                .personal(b"Fflonk-Vk")
                .to_state();

            let s = format!("{:?}", vk.pinned());

            hasher.update(&(s.len() as u64).to_le_bytes());
            hasher.update(s.as_bytes());

            C::Scalar::from_uniform_bytes(hasher.finalize().as_array())
        };

        vk
    }

    pub fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)
    }

    fn query_infos(&self) -> impl Iterator<Item = &QueryInfo<C::Scalar>> + '_ {
        chain![
            [&self.preprocessed_query_info],
            self.phase_infos.iter().map(Deref::deref),
        ]
    }

    fn lcm_t(&self) -> usize {
        self.query_infos()
            .map(|query_info| query_info.t)
            .reduce(lcm)
            .unwrap()
    }

    fn pinned(&self) -> PinnedVerificationKey<C> {
        PinnedVerificationKey {
            base_modulus: C::Base::MODULUS,
            scalar_modulus: C::Scalar::MODULUS,
            domain: self.domain.pinned(),
            protocol: &self.protocol,
            preprocessed_commitment: &self.preprocessed_commitment,
            preprocessed_query_info: &self.preprocessed_query_info,
            phase_infos: &self.phase_infos,
        }
    }
}

#[derive(Debug)]
pub struct ProvingKey<C: CurveAffine> {
    vk: VerifyingKey<C>,
    preprocessed_values: Vec<Vec<C::Scalar>>,
    preprocessed_polys: Vec<Polynomial<C::Scalar, Coeff>>,
    preprocessed_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    transparent_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    evaluators: Vec<Vec<Evaluator<C::Scalar>>>,
}

#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, C: CurveAffine> {
    base_modulus: &'static str,
    scalar_modulus: &'static str,
    domain: PinnedEvaluationDomain<'a, C::Scalar>,
    protocol: &'a Protocol<C::Scalar>,
    preprocessed_commitment: &'a C,
    preprocessed_query_info: &'a QueryInfo<C::Scalar>,
    phase_infos: &'a [PhaseInfo<C::Scalar>],
}

fn combine_polys<'a, F: Field>(
    t: usize,
    polys: impl IntoIterator<Item = &'a Polynomial<F, Coeff>>,
) -> Polynomial<F, Coeff> {
    let polys = polys.into_iter().collect::<Vec<_>>();
    assert!(t >= polys.len());
    let size = polys
        .iter()
        .map(|poly| poly.len())
        .max()
        .unwrap_or_default()
        * t;
    let mut combined = Polynomial::new(vec![F::ZERO; size]);
    izip!(0.., polys).for_each(|(idx, poly)| {
        izip!(combined[idx..].iter_mut().step_by(t), &poly[..]).for_each(|(lhs, rhs)| *lhs = *rhs)
    });
    combined
}

fn eval_combined_polynomial<F: Field>(t: usize, num_evals: usize, poly: &[F], point: F) -> Vec<F> {
    let num_threads = current_num_threads();
    let chunk_size = div_ceil(poly.len() / t, num_threads).max(2 * num_threads);
    let point_to_chunk_size = point.pow([chunk_size as u64]);
    poly.par_chunks(chunk_size * t)
        .rev()
        .map(|poly| {
            poly.chunks(t)
                .rfold(vec![F::ZERO; num_evals], |mut acc, coeffs| {
                    izip!(&mut acc, coeffs).for_each(|(acc, coeff)| {
                        *acc *= point;
                        *acc += coeff
                    });
                    acc
                })
        })
        .reduce_with(|mut acc, chunk| {
            izip!(&mut acc, chunk).for_each(|(acc, chunk)| {
                *acc *= point_to_chunk_size;
                *acc += chunk
            });
            acc
        })
        .unwrap_or_default()
}

#[cfg(test)]
mod test {
    use crate::backend::fflonk::{
        circuit::FflonkCircuit,
        keygen::{keygen_pk, keygen_vk},
        prover::create_proof,
        verifier::verify_proof,
    };
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        halo2curves::{
            bn256::{Bn256, Fr},
            ff::Field,
        },
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed},
        poly::{
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
            Rotation,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    #[test]
    fn vanilla_plonk_with_lookup() {
        #[derive(Clone, Debug)]
        pub struct SampleConfig {
            selectors: [Column<Fixed>; 7],
            wires: [Column<Advice>; 4],
        }

        impl SampleConfig {
            fn configure<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
                let pi = meta.instance_column();
                let [q_l, q_r, q_m, q_o, q_c, q_lookup, t] = [(); 7].map(|_| meta.fixed_column());
                let [w_l, w_r, w_o, w_lookup] = [(); 4].map(|_| meta.advice_column());
                [w_l, w_r, w_o, w_lookup].map(|column| meta.enable_equality(column));
                meta.create_gate(
                    "q_l·w_l + q_r·w_r + q_m·w_l·w_r + q_o·w_o + q_c + pi = 0",
                    |meta| {
                        let [q_l, q_r, q_o, q_m, q_c] = [q_l, q_r, q_o, q_m, q_c]
                            .map(|column| meta.query_fixed(column, Rotation::cur()));
                        let [w_l, w_r, w_o] = [w_l, w_r, w_o]
                            .map(|column| meta.query_advice(column, Rotation::cur()));
                        let pi = meta.query_instance(pi, Rotation::cur());
                        Some(
                            q_l * w_l.clone()
                                + q_r * w_r.clone()
                                + q_m * w_l * w_r
                                + q_o * w_o
                                + q_c
                                + pi,
                        )
                    },
                );
                meta.lookup_any("(q_lookup * w_lookup) in (t)", |meta| {
                    let [q_lookup, t] =
                        [q_lookup, t].map(|column| meta.query_fixed(column, Rotation::cur()));
                    let w_lookup = meta.query_advice(w_lookup, Rotation::cur());
                    vec![(q_lookup * w_lookup, t)]
                });
                SampleConfig {
                    selectors: [q_l, q_r, q_m, q_o, q_c, q_lookup, t],
                    wires: [w_l, w_r, w_o, w_lookup],
                }
            }
        }

        #[derive(Clone, Debug, Default)]
        pub struct Sample<F>(Vec<F>);

        impl<F: Field> Circuit<F> for Sample<F> {
            type Config = SampleConfig;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                unimplemented!()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                meta.set_minimum_degree(6);
                SampleConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "",
                    |mut region| {
                        let one = Value::known(F::ONE);
                        for (row, value) in self.0.iter().enumerate() {
                            let minus_value = Value::known(-*value);
                            region.assign_fixed(|| "", config.selectors[0], row, || one)?;
                            region.assign_advice(|| "", config.wires[0], row, || minus_value)?;
                        }
                        let offset = self.0.len();
                        let minus_four = Value::known(-F::ONE.double().double());
                        for selector in &config.selectors {
                            region.assign_fixed(|| "", *selector, offset, || one)?;
                        }
                        let a = region.assign_advice(|| "", config.wires[0], offset, || one)?;
                        let b = region.assign_advice(|| "", config.wires[1], offset, || one)?;
                        let c = region.assign_advice(|| "", config.wires[2], offset + 1, || one)?;
                        let d = region.assign_advice(|| "", config.wires[3], offset, || one)?;
                        region.constrain_equal(a.cell(), b.cell())?;
                        region.constrain_equal(b.cell(), c.cell())?;
                        region.constrain_equal(c.cell(), d.cell())?;
                        region.assign_advice(|| "", config.wires[2], offset, || minus_four)?;
                        Ok(())
                    },
                )
            }
        }

        let mut rng = ChaCha20Rng::seed_from_u64(0);
        let instances = vec![Fr::random(&mut rng), Fr::random(&mut rng)];
        let circuit = FflonkCircuit::new(4, Sample(instances.clone()));

        let params = ParamsKZG::<Bn256>::setup(circuit.min_params_k() as u32, &mut rng);
        let pk = keygen_pk::<KZGCommitmentScheme<_>, _>(&params, &circuit).unwrap();
        let vk = keygen_vk::<KZGCommitmentScheme<_>, _>(&params, &circuit).unwrap();
        assert_eq!(pk.vk.transcript_repr, vk.transcript_repr);

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _>(
            &params,
            &pk,
            &circuit,
            &[&instances],
            &mut rng,
            &mut transcript,
        )
        .unwrap();
        let proof = transcript.finalize();

        let mut transcript = Blake2bRead::init(proof.as_slice());
        verify_proof::<KZGCommitmentScheme<_>, VerifierSHPLONK<_>, _, _>(
            &params,
            &vk,
            &[&instances],
            SingleStrategy::new(&params),
            &mut transcript,
        )
        .unwrap();

        assert_eq!(proof.len(), {
            let num_commitments = vk.phase_infos.len() + 2;
            let num_evals = vk.preprocessed_query_info.rotations.len()
                * vk.preprocessed_query_info.num_polys
                + vk.phase_infos
                    .iter()
                    .map(|phase_info| {
                        phase_info.rotations.len() * phase_info.num_polys
                            - phase_info.constraints.len()
                    })
                    .sum::<usize>();
            num_commitments * 32 + num_evals * 32
        });
    }
}
