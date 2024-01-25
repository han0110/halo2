use crate::{
    backend::{
        fflonk::{combine_polys, eval_combined_polynomial, ProvingKey},
        Circuit,
    },
    util::{chain, izip},
};
use halo2_proofs::{
    arithmetic::eval_polynomial,
    halo2curves::{
        ff::{Field, FromUniformBytes, WithSmallOrderMulGroup},
        group::Curve,
    },
    plonk::Error,
    poly::{
        commitment::{Blind, CommitmentScheme, ParamsProver, Prover},
        Polynomial, ProverQuery, Rotation,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use rand_core::RngCore;
use std::iter;

pub fn create_proof<'params, S, P, E, C>(
    params: &'params S::ParamsProver,
    pk: &ProvingKey<S::Curve>,
    circuit: &C,
    instances: &[&[S::Scalar]],
    mut rng: impl RngCore,
    transcript: &mut impl TranscriptWrite<S::Curve, E>,
) -> Result<(), Error>
where
    S: CommitmentScheme,
    S::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
    P: Prover<'params, S>,
    E: EncodedChallenge<S::Curve>,
    C: Circuit<S::Scalar>,
{
    let vk = &pk.vk;
    let domain = &vk.domain;
    if instances.len() != vk.protocol.num_instance_polys {
        return Err(Error::InvalidInstances);
    }

    vk.hash_into(transcript)?;

    for instance in instances.iter() {
        for instance in instance.iter() {
            transcript.common_scalar(*instance)?;
        }
    }

    let instance_values = instances
        .iter()
        .map(|instance| {
            chain![instance.iter().cloned(), iter::repeat(S::Scalar::ZERO)]
                .take(vk.protocol.n())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let instance_cosets = instance_values
        .iter()
        .cloned()
        .map(|value| domain.coeff_to_extended(domain.lagrange_to_coeff(Polynomial::new(value))))
        .collect::<Vec<_>>();

    let mut combineds = vec![(Polynomial::new(Vec::new()), Default::default())];
    let mut advice_values = vec![];
    let mut advice_cosets = vec![];
    let mut challenges = vec![];
    let mut buf = C::WitnessBuf::default();
    for (phase, (num_advice_polys, num_challegnes), phase_info, evaluators) in
        izip!(0.., &vk.protocol.phases, &vk.phase_infos, &pk.evaluators)
    {
        let values = {
            let values = chain![&pk.preprocessed_values, &instance_values, &advice_values]
                .map(Vec::as_slice)
                .collect::<Vec<_>>();
            circuit.witness(phase, &values, &challenges, &mut buf, &mut rng)?
        };
        assert_eq!(values.len(), *num_advice_polys);
        let polys = values
            .iter()
            .map(|value| domain.lagrange_to_coeff(Polynomial::new(value.clone())))
            .collect::<Vec<_>>();
        let cosets = polys
            .iter()
            .map(|poly| domain.coeff_to_extended(poly.clone()))
            .collect::<Vec<_>>();
        advice_values.extend(values);
        advice_cosets.extend(cosets);

        let quotient_polys = {
            let dummy_coset = Polynomial::new(Vec::new());
            let polys = chain![
                &pk.preprocessed_cosets,
                &instance_cosets,
                chain![&advice_cosets, iter::repeat(&dummy_coset)]
                    .take(vk.protocol.num_advice_polys()),
                &pk.transparent_cosets
            ]
            .collect::<Vec<_>>();
            evaluators
                .iter()
                .map(|evaluator| evaluator.evaluate_quotient(&polys, &challenges))
                .collect::<Vec<_>>()
        };

        let polys = chain![polys, quotient_polys].collect::<Vec<_>>();
        let combined_poly = combine_polys(phase_info.t, &polys);
        let combined_blind = Blind::new(&mut rng);
        let combined_commitment = params.commit(&combined_poly, combined_blind).to_affine();
        transcript.write_point(combined_commitment)?;
        combineds.push((combined_poly, combined_blind));

        for _ in 0..*num_challegnes {
            challenges.push(*transcript.squeeze_challenge_scalar::<()>());
        }
    }

    drop(advice_values);
    drop(advice_cosets);
    drop(challenges);
    drop(buf);

    let lcm_t = vk.lcm_t();
    let x_lcm_t = *transcript.squeeze_challenge_scalar::<()>();
    let x = x_lcm_t.pow([lcm_t as u64]);

    for rotation in &vk.preprocessed_query_info.rotations {
        let point = domain.rotate_omega(x, Rotation(*rotation));
        for poly in &pk.preprocessed_polys {
            transcript.write_scalar(eval_polynomial(poly, point))?;
        }
    }
    for (phase_info, (poly, _)) in izip!(&vk.phase_infos, &combineds[1..]) {
        for rotation in &phase_info.rotations {
            let point = domain.rotate_omega(x, Rotation(*rotation));
            let num_evals = if *rotation == 0 {
                phase_info.num_polys - phase_info.constraints.len()
            } else {
                phase_info.num_polys
            };
            for eval in eval_combined_polynomial(phase_info.t, num_evals, poly, point) {
                transcript.write_scalar(eval)?;
            }
        }
    }

    combineds[0].0 = combine_polys(vk.preprocessed_query_info.t, &pk.preprocessed_polys);

    // NOTE: Because `Polynomial` assumes all values have same length, we need to pad here.
    let combineds = {
        let max_size = combineds.iter().map(|(poly, _)| poly.len()).max().unwrap();
        combineds
            .into_iter()
            .map(|(poly, blind)| {
                let mut poly = poly.into_vec();
                poly.resize(max_size, S::Scalar::ZERO);
                (Polynomial::new(poly), blind)
            })
            .collect::<Vec<_>>()
    };

    let queries = izip!(vk.query_infos(), &combineds)
        .flat_map(|(query_info, (poly, blind))| {
            query_info.rotations.iter().flat_map(move |rotation| {
                query_info
                    .roots(lcm_t, x_lcm_t, *rotation)
                    .map(move |point| ProverQuery::new(point, poly, *blind))
            })
        })
        .collect::<Vec<_>>();

    let prover = P::new(params);
    prover
        .create_proof(rng, transcript, queries)
        .map_err(|_| Error::ConstraintSystemFailure)
}
