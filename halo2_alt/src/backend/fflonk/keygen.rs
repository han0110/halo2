use crate::{
    backend::{
        fflonk::{combine_polys, PhaseInfo, ProvingKey, QueryInfo, VerifyingKey},
        Circuit,
    },
    protocol::{Expression, PolynomialRef::*, Protocol},
    util::{chain, evaluator::Evaluator, felt_from_bool, izip},
};
use halo2_proofs::{
    halo2curves::{
        ff::{Field, FromUniformBytes, PrimeField, WithSmallOrderMulGroup},
        group::Curve,
    },
    plonk::Error,
    poly::{
        commitment::{Blind, CommitmentScheme, ParamsProver},
        EvaluationDomain, ExtendedLagrangeCoeff, Polynomial,
    },
};
use rayon::prelude::*;
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
    hash::Hash,
    iter,
};

pub fn keygen_vk<S: CommitmentScheme, C>(
    params: &S::ParamsProver,
    circuit: &C,
) -> Result<VerifyingKey<S::Curve>, Error>
where
    S::Scalar: FromUniformBytes<64> + WithSmallOrderMulGroup<3>,
    C: Circuit<S::Scalar>,
{
    let protocol = circuit.protocol();
    protocol.assert_valid();

    let (preprocessed_query_info, phase_infos) = query_infos(&protocol);

    let preprocessed_commitment = {
        let domain = EvaluationDomain::new(protocol.degree() as u32, protocol.k as u32);
        let preprocessed_values = circuit.preprocess()?;
        if preprocessed_values.len() != protocol.num_preprocessed_polys {
            return Err(Error::Synthesis);
        }

        let preprocessed_polys = preprocessed_values
            .into_iter()
            .map(|values| domain.lagrange_to_coeff(Polynomial::new(values)))
            .collect::<Vec<_>>();
        let combined = combine_polys(preprocessed_query_info.t, &preprocessed_polys);
        params.commit(&combined, Blind::default()).to_affine()
    };

    Ok(VerifyingKey::new(
        protocol,
        preprocessed_commitment,
        preprocessed_query_info,
        phase_infos,
    ))
}

pub fn keygen_pk<S: CommitmentScheme, C>(
    params: &S::ParamsProver,
    circuit: &C,
) -> Result<ProvingKey<S::Curve>, Error>
where
    S::Scalar: FromUniformBytes<64> + WithSmallOrderMulGroup<3> + Hash,
    C: Circuit<S::Scalar>,
{
    let protocol = circuit.protocol();
    protocol.assert_valid();

    let (preprocessed_query_info, phase_infos) = query_infos(&protocol);

    let domain = EvaluationDomain::new(protocol.degree() as u32, protocol.k as u32);

    let preprocessed_values = circuit.preprocess()?;
    assert_eq!(preprocessed_values.len(), protocol.num_preprocessed_polys);

    let preprocessed_polys = preprocessed_values
        .iter()
        .map(|values| domain.lagrange_to_coeff(Polynomial::new(values.clone())))
        .collect::<Vec<_>>();
    let preprocessed_cosets = preprocessed_polys
        .iter()
        .map(|poly| domain.coeff_to_extended(poly.clone()))
        .collect::<Vec<_>>();
    let preprocessed_commitment = {
        let combined = combine_polys(preprocessed_query_info.t, &preprocessed_polys);
        params.commit(&combined, Blind::default()).to_affine()
    };

    let (evaluators, transparent_cosets) = evaluators(&protocol, &phase_infos);

    Ok(ProvingKey {
        vk: VerifyingKey::new(
            protocol,
            preprocessed_commitment,
            preprocessed_query_info,
            phase_infos,
        ),
        preprocessed_values,
        preprocessed_polys,
        preprocessed_cosets,
        transparent_cosets,
        evaluators,
    })
}

pub(super) fn query_infos<F: PrimeField>(
    protocol: &Protocol<F>,
) -> (QueryInfo<F>, Vec<PhaseInfo<F>>) {
    let constraints_by_earliest_phase = constraints_by_earliest_phase(protocol);
    let poly_ranges = protocol.poly_range();
    let poly_combination_idx = chain![
        [(poly_ranges.preprocessed, Some(0))],
        [(poly_ranges.instance, None)],
        izip!(poly_ranges.advices, (1..).map(Some))
    ]
    .flat_map(|(range, phase)| izip!(range, iter::repeat(phase)))
    .collect::<HashMap<_, Option<usize>>>();
    let rotations = protocol
        .constraints
        .iter()
        .flat_map(Expression::used_query)
        .fold(
            chain![
                [BTreeSet::new()],
                iter::repeat(BTreeSet::from([0])).take(protocol.num_phases())
            ]
            .collect::<Vec<_>>(),
            |mut rotations, query| {
                if let Some(idx) = poly_combination_idx[&query.index] {
                    rotations[idx].insert(query.rotation.0);
                }
                rotations
            },
        );
    let num_polys = chain![
        [protocol.num_preprocessed_polys],
        izip!(&protocol.phases, &constraints_by_earliest_phase)
            .map(|((num_advice_polys, _), constraints)| *num_advice_polys + constraints.len()),
    ];
    let mut query_infos = izip!(num_polys, rotations)
        .map(|(num_polys, rotations)| QueryInfo::new(protocol.k, num_polys, rotations))
        .collect::<Vec<_>>()
        .into_iter();
    let preprocessed_query_info = query_infos.next().unwrap();
    let phase_infos = izip!(query_infos, constraints_by_earliest_phase)
        .map(|(query_info, constraints)| PhaseInfo::new(query_info, constraints))
        .collect();
    (preprocessed_query_info, phase_infos)
}

fn constraints_by_earliest_phase<F: Field>(protocol: &Protocol<F>) -> Vec<Vec<usize>> {
    let poly_ranges = protocol.poly_range();
    let poly_usable_phase = chain![
        [(poly_ranges.preprocessed, 0)],
        [(poly_ranges.instance, 0)],
        izip!(poly_ranges.advices.clone(), 0..)
    ]
    .flat_map(|(range, phase)| izip!(range, iter::repeat(phase)))
    .collect::<HashMap<_, usize>>();
    let challenge_usable_phase = izip!(poly_ranges.challenges, 1..)
        .flat_map(|(range, phase)| izip!(range, iter::repeat(phase)))
        .collect::<HashMap<_, usize>>();
    protocol.constraints.iter().enumerate().fold(
        vec![vec![]; protocol.num_phases()],
        |mut constraints_by_earliest_phase, (idx, constraint)| {
            let phase = constraint.evaluate(
                &|poly| match poly {
                    Constant(_) | Identity | Lagrange(_) => 0,
                    Challenge(idx) => challenge_usable_phase[&idx],
                    Opaque(query) => poly_usable_phase[&query.index],
                },
                &|a| a,
                &|a, b| a.max(b),
                &|a, b| a.max(b),
            );
            constraints_by_earliest_phase[phase].push(idx);
            constraints_by_earliest_phase
        },
    )
}

#[allow(clippy::type_complexity)]
fn evaluators<F: WithSmallOrderMulGroup<3> + Hash>(
    protocol: &Protocol<F>,
    phase_infos: &[PhaseInfo<F>],
) -> (
    Vec<Vec<Evaluator<F>>>,
    Vec<Polynomial<F, ExtendedLagrangeCoeff>>,
) {
    let num_opaque_polys = protocol.num_opaque_polys();
    let transparents = RefCell::new(HashMap::<_, usize>::new());
    let replace = |constraint: &Expression<F>| {
        let inner = |(is_transparent, constraint): (bool, Expression<F>)| {
            if !is_transparent || constraint.degree() == 0 {
                return constraint;
            };

            let mut transparents = transparents.borrow_mut();
            let idx = if let Some(idx) = transparents.get(&constraint).copied() {
                idx
            } else {
                let idx = num_opaque_polys + transparents.len();
                transparents.insert(constraint.clone(), idx);
                idx
            };
            Opaque((idx, 0).into()).into()
        };

        inner(constraint.evaluate::<(bool, Expression<F>)>(
            &|poly| match poly {
                Constant(_) | Lagrange(_) => (true, poly.into()),
                Challenge(_) | Identity | Opaque(_) => (false, poly.into()),
            },
            &|value| (value.0, -value.1),
            &|a, b| match a.0 && b.0 {
                true => (true, a.1 + b.1),
                false => (false, inner(a) + inner(b)),
            },
            &|a, b| (false, inner(a) * inner(b)),
        ))
    };

    let evaluators = phase_infos
        .iter()
        .map(|phase_info| {
            phase_info
                .constraints
                .iter()
                .map(|idx| Evaluator::new(protocol.k, &replace(&protocol.constraints[*idx])))
                .collect()
        })
        .collect();

    let transparent_cosets = {
        let domain = EvaluationDomain::new(protocol.degree() as u32, protocol.k as u32);
        let n = 1 << protocol.k;

        let mut transparents = transparents.take().into_iter().collect::<Vec<_>>();
        transparents.sort_by(|(_, a), (_, b)| a.cmp(b));
        transparents
            .into_iter()
            .map(|(expr, _)| {
                let mut poly = domain.empty_lagrange();
                poly.par_iter_mut().enumerate().for_each(|(idx, eval)| {
                    *eval = expr.evaluate_felt(&|poly| match poly {
                        Constant(constant) => constant,
                        Lagrange(i) => felt_from_bool(i.rem_euclid(n) == idx as i32),
                        _ => unreachable!(),
                    });
                });
                domain.coeff_to_extended(domain.lagrange_to_coeff(poly))
            })
            .collect()
    };

    (evaluators, transparent_cosets)
}
