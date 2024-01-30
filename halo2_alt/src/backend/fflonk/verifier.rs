use crate::{
    backend::fflonk::VerifyingKey,
    protocol::{Expression, PolynomialRef::*, Query},
    util::{chain, halo2::TranscriptReadVec, izip, powers, squares},
};
use halo2_proofs::{
    arithmetic::eval_polynomial,
    halo2curves::{
        ff::{BatchInvert, Field, FromUniformBytes, WithSmallOrderMulGroup},
        CurveAffine,
    },
    plonk::Error,
    poly::{
        commitment::{CommitmentScheme, Verifier},
        EvaluationDomain, Rotation, VerificationStrategy, VerifierQuery,
    },
    transcript::{EncodedChallenge, TranscriptRead},
};
use std::collections::{BTreeSet, HashMap};

/// Verify a fflonk proof.
pub fn verify_proof<'params, S, V, E, ST>(
    params: &'params S::ParamsVerifier,
    vk: &VerifyingKey<S::Curve>,
    instances: &[&[S::Scalar]],
    strategy: ST,
    transcript: &mut impl TranscriptRead<S::Curve, E>,
) -> Result<ST::Output, Error>
where
    S: CommitmentScheme,
    S::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    V: Verifier<'params, S>,
    E: EncodedChallenge<S::Curve>,
    ST: VerificationStrategy<'params, S, V>,
{
    if instances.len() != vk.protocol.num_instance_polys() {
        return Err(Error::InvalidInstances);
    }

    vk.hash_into(transcript)?;

    for instance in instances.iter() {
        for instance in instance.iter() {
            transcript.common_scalar(*instance)?;
        }
    }

    let mut combined_commitments = vec![vk.preprocessed_commitment];
    let mut challenges = vec![];
    for (_, num_challenges) in vk.protocol.phases() {
        combined_commitments.push(transcript.read_point()?);

        for _ in 0..*num_challenges {
            challenges.push(*transcript.squeeze_challenge_scalar::<()>());
        }
    }

    let lcm_t = vk.lcm_t();
    let x_lcm_t = *transcript.squeeze_challenge_scalar::<()>();
    let x = x_lcm_t.pow([lcm_t as u64]);

    let evals = {
        let mut evals = vec![Vec::new(); combined_commitments.len()];
        for _ in &vk.preprocessed_query_info.rotations {
            let num_evals = vk.preprocessed_query_info.num_polys;
            evals[0].push(transcript.read_scalars(num_evals)?);
        }
        for (phase_info, evals) in izip!(&vk.phase_infos, &mut evals[1..]) {
            for rotation in &phase_info.rotations {
                let num_evals = if *rotation == 0 {
                    phase_info.num_polys - phase_info.constraints.len()
                } else {
                    phase_info.num_polys
                };
                evals.push(transcript.read_scalars(num_evals)?);
            }
        }

        let quotient_evals = quotient_evals(vk, instances, &challenges, x, &evals);
        for (phase_info, evals, quotient_evals) in
            izip!(&vk.phase_infos, &mut evals[1..], quotient_evals)
        {
            let idx = phase_info.rotations.iter().position(|r| *r == 0).unwrap();
            evals[idx].extend(quotient_evals);
        }

        evals
    };

    let queries = izip!(vk.query_infos(), &combined_commitments, evals)
        .flat_map(|(query_info, commitment, evals)| {
            izip!(&query_info.rotations, evals).flat_map(move |(rotation, evals)| {
                query_info
                    .roots(lcm_t, x_lcm_t, *rotation)
                    .map(move |point| {
                        let eval = eval_polynomial(&evals, point);
                        VerifierQuery::new_commitment(commitment, point, eval)
                    })
            })
        })
        .collect::<Vec<_>>();

    let verifier = V::new(params);
    strategy.process(|msm| {
        verifier
            .verify_proof(transcript, queries, msm)
            .map_err(|_| Error::Opening)
    })
}

fn quotient_evals<C: CurveAffine>(
    vk: &VerifyingKey<C>,
    instances: &[&[C::Scalar]],
    challenges: &[C::Scalar],
    x: C::Scalar,
    evals: &[Vec<Vec<C::Scalar>>],
) -> Vec<Vec<C::Scalar>> {
    let domain = &vk.domain;
    let poly_range = vk.protocol.poly_range();

    let x_to_n = squares(x).nth(vk.protocol.k()).unwrap();
    let (lagrange_evals, instance_evals) = {
        let instances = izip!(poly_range.instance.clone(), instances).collect::<HashMap<_, _>>();
        let instance_queries = vk
            .protocol
            .constraints()
            .iter()
            .flat_map(Expression::used_query)
            .filter(|query| poly_range.instance.contains(&query.index))
            .collect::<Vec<_>>();
        let (min_rotation, max_rotation) =
            instance_queries.iter().fold((0, 0), |(min, max), query| {
                if query.rotation.0 < min {
                    (query.rotation.0, max)
                } else if query.rotation.0 > max {
                    (min, query.rotation.0)
                } else {
                    (min, max)
                }
            });
        let max_instance_len = instances
            .values()
            .map(|instance| instance.len())
            .max_by(Ord::cmp)
            .unwrap_or_default();
        let i_s = chain![
            max_rotation..max_instance_len as i32 + min_rotation.abs(),
            vk.protocol
                .constraints()
                .iter()
                .flat_map(Expression::used_langrange),
        ]
        .collect::<BTreeSet<_>>();
        let lagrange_evals = lagrange_evals(domain, i_s, x, x_to_n);
        let instance_evals = instance_queries
            .into_iter()
            .map(|query| {
                let instance = instances[&query.index];
                let eval = izip!(*instance, max_rotation - query.rotation.0..)
                    .map(|(instance, i)| *instance * lagrange_evals[&i])
                    .sum();
                (query, eval)
            })
            .collect::<Vec<_>>();
        (lagrange_evals, instance_evals)
    };

    let evals = chain![
        instance_evals,
        izip!(
            vk.query_infos(),
            chain![[poly_range.preprocessed], poly_range.advices],
            evals
        )
        .flat_map(|(query_info, polys, evals)| {
            izip!(&query_info.rotations, evals).flat_map(move |(rotation, evals)| {
                izip!(polys.clone(), evals).map(|(idx, eval)| ((idx, *rotation).into(), *eval))
            })
        }),
    ]
    .collect::<HashMap<Query, C::Scalar>>();
    let vanishing_eval = (x_to_n - C::Scalar::ONE).invert().unwrap();
    vk.phase_infos
        .iter()
        .map(|phase_info| {
            phase_info
                .constraints
                .iter()
                .map(|idx| {
                    vk.protocol.constraints()[*idx].evaluate_felt(&|poly| match poly {
                        Constant(constant) => constant,
                        Challenge(idx) => challenges[idx],
                        Identity => x,
                        Lagrange(i) => lagrange_evals[&i],
                        Opaque(query) => evals[&query],
                    }) * vanishing_eval
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn lagrange_evals<F: WithSmallOrderMulGroup<3>>(
    domain: &EvaluationDomain<F>,
    i_s: impl IntoIterator<Item = i32>,
    x: F,
    x_to_n: F,
) -> HashMap<i32, F> {
    let i_s = i_s.into_iter().collect::<Vec<_>>();
    let n_inv = powers(F::TWO_INV).nth(domain.k() as usize).unwrap();
    let common = (x_to_n - F::ONE) * n_inv;

    let mut evals = i_s
        .iter()
        .map(|i| x - domain.rotate_omega(F::ONE, Rotation(*i)))
        .collect::<Vec<_>>();
    evals.batch_invert();
    izip!(i_s, evals)
        .map(|(i, eval)| (i, domain.rotate_omega(common * eval, Rotation(i))))
        .collect()
}
