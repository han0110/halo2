use ff::Field;
use group::Curve;
use halo2curves::CurveExt;
use rand_core::RngCore;
use std::env::var;
use std::ops::RangeTo;
use std::sync::atomic::AtomicUsize;
use std::time::Instant;
use std::{iter, sync::atomic::Ordering};

use super::{
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    lookup, permutation, vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX,
    ChallengeY, Error, Expression, ProvingKey,
};
use crate::poly::{
    self,
    commitment::{Blind, CommitmentScheme, Params, Prover as _Prover},
    Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial, ProverQuery,
};
use crate::{
    arithmetic::{eval_polynomial, CurveAffine, FieldExt},
    circuit::Value,
    plonk::Assigned,
};
use crate::{
    poly::batch_invert_assigned,
    transcript::{EncodedChallenge, TranscriptWrite},
};
use group::prime::PrimeCurveAffine;

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_proof<
    'params,
    Scheme: CommitmentScheme,
    Prover: _Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
    const ZK: bool,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
    mut rng: R,
    transcript: &mut T,
) -> Result<(), Error> {
    for instance in instances.iter() {
        if instance.len() != pk.vk.cs.num_instance_columns {
            return Err(Error::InvalidInstances);
        }
    }

    // Hash verification key into transcript
    pk.vk.hash_into(transcript)?;

    let domain = &pk.vk.domain;
    let mut meta = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut meta);

    // Selector optimizations cannot be applied here; use the ConstraintSystem
    // from the verification key.
    let meta = &pk.vk.cs;

    struct InstanceSingle<C: CurveAffine> {
        pub instance_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub instance_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub instance_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    }

    let instance: Vec<InstanceSingle<Scheme::Curve>> = instances
        .iter()
        .map(|instance| -> Result<InstanceSingle<Scheme::Curve>, Error> {
            let instance_values = instance
                .iter()
                .map(|values| {
                    let mut poly = domain.empty_lagrange();
                    assert_eq!(poly.len(), params.n() as usize);
                    if ZK && values.len() > meta.usable_rows::<ZK>(params.n() as usize).end {
                        return Err(Error::InstanceTooLarge);
                    }
                    for (poly, value) in poly.iter_mut().zip(values.iter()) {
                        *poly = *value;
                    }
                    Ok(poly)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let instance_commitments_projective: Vec<_> = instance_values
                .iter()
                .map(|poly| params.commit_lagrange(poly, Blind::default()))
                .collect();
            let mut instance_commitments =
                vec![Scheme::Curve::identity(); instance_commitments_projective.len()];
            <<Scheme as CommitmentScheme>::Curve as CurveAffine>::CurveExt::batch_normalize(
                &instance_commitments_projective,
                &mut instance_commitments,
            );
            let instance_commitments = instance_commitments;
            drop(instance_commitments_projective);

            for commitment in &instance_commitments {
                transcript.common_point(*commitment)?;
            }

            let instance_polys: Vec<_> = instance_values
                .iter()
                .map(|poly| {
                    let lagrange_vec = domain.lagrange_from_vec(poly.to_vec());
                    domain.lagrange_to_coeff(lagrange_vec)
                })
                .collect();

            let instance_cosets: Vec<_> = instance_polys
                .iter()
                .map(|poly| domain.coeff_to_extended(poly.clone()))
                .collect();

            Ok(InstanceSingle {
                instance_values,
                instance_polys,
                instance_cosets,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    struct AdviceSingle<C: CurveAffine> {
        pub advice_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
        pub advice_polys: Vec<Polynomial<C::Scalar, Coeff>>,
        pub advice_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
        pub advice_blinds: Vec<Blind<C::Scalar>>,
    }

    let advice: Vec<AdviceSingle<Scheme::Curve>> = circuits
        .iter()
        .zip(instances.iter())
        .map(
            |(circuit, instances)| -> Result<AdviceSingle<Scheme::Curve>, Error> {
                struct WitnessCollection<'a, F: Field> {
                    k: u32,
                    pub advice: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
                    instances: &'a [&'a [F]],
                    usable_rows: RangeTo<usize>,
                    _marker: std::marker::PhantomData<F>,
                }

                impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
                    fn enter_region<NR, N>(&mut self, _: N)
                    where
                        NR: Into<String>,
                        N: FnOnce() -> NR,
                    {
                        // Do nothing; we don't care about regions in this context.
                    }

                    fn exit_region(&mut self) {
                        // Do nothing; we don't care about regions in this context.
                    }

                    fn enable_selector<A, AR>(
                        &mut self,
                        _: A,
                        _: &Selector,
                        _: usize,
                    ) -> Result<(), Error>
                    where
                        A: FnOnce() -> AR,
                        AR: Into<String>,
                    {
                        // We only care about advice columns here

                        Ok(())
                    }

                    fn query_instance(
                        &self,
                        column: Column<Instance>,
                        row: usize,
                    ) -> Result<Value<F>, Error> {
                        if !self.usable_rows.contains(&row) {
                            return Err(Error::not_enough_rows_available(self.k));
                        }

                        self.instances
                            .get(column.index())
                            .and_then(|column| column.get(row))
                            .map(|v| Value::known(*v))
                            .ok_or(Error::BoundsFailure)
                    }

                    fn assign_advice<V, VR, A, AR>(
                        &mut self,
                        _: A,
                        column: Column<Advice>,
                        row: usize,
                        to: V,
                    ) -> Result<(), Error>
                    where
                        V: FnOnce() -> Value<VR>,
                        VR: Into<Assigned<F>>,
                        A: FnOnce() -> AR,
                        AR: Into<String>,
                    {
                        if !self.usable_rows.contains(&row) {
                            return Err(Error::not_enough_rows_available(self.k));
                        }

                        *self
                            .advice
                            .get_mut(column.index())
                            .and_then(|v| v.get_mut(row))
                            .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

                        Ok(())
                    }

                    fn assign_fixed<V, VR, A, AR>(
                        &mut self,
                        _: A,
                        _: Column<Fixed>,
                        _: usize,
                        _: V,
                    ) -> Result<(), Error>
                    where
                        V: FnOnce() -> Value<VR>,
                        VR: Into<Assigned<F>>,
                        A: FnOnce() -> AR,
                        AR: Into<String>,
                    {
                        // We only care about advice columns here

                        Ok(())
                    }

                    fn copy(
                        &mut self,
                        _: Column<Any>,
                        _: usize,
                        _: Column<Any>,
                        _: usize,
                    ) -> Result<(), Error> {
                        // We only care about advice columns here

                        Ok(())
                    }

                    fn fill_from_row(
                        &mut self,
                        _: Column<Fixed>,
                        _: usize,
                        _: Value<Assigned<F>>,
                    ) -> Result<(), Error> {
                        Ok(())
                    }

                    fn push_namespace<NR, N>(&mut self, _: N)
                    where
                        NR: Into<String>,
                        N: FnOnce() -> NR,
                    {
                        // Do nothing; we don't care about namespaces in this context.
                    }

                    fn pop_namespace(&mut self, _: Option<String>) {
                        // Do nothing; we don't care about namespaces in this context.
                    }
                }

                let unusable_rows_start = meta.usable_rows::<ZK>(params.n() as usize).end;

                let mut witness = WitnessCollection {
                    k: params.k(),
                    advice: vec![domain.empty_lagrange_assigned(); meta.num_advice_columns],
                    instances,
                    // The prover will not be allowed to assign values to advice
                    // cells that exist within inactive rows, which include some
                    // number of blinding factors and an extra row for use in the
                    // permutation argument.
                    usable_rows: ..unusable_rows_start,
                    _marker: std::marker::PhantomData,
                };

                // Synthesize the circuit to obtain the witness and other information.
                ConcreteCircuit::FloorPlanner::synthesize(
                    &mut witness,
                    circuit,
                    config.clone(),
                    meta.constants.clone(),
                )?;

                let mut advice = batch_invert_assigned(witness.advice);

                // Add blinding factors to advice columns if ZK is enabled
                if ZK {
                    for advice in &mut advice {
                        for cell in &mut advice[unusable_rows_start..] {
                            *cell = Scheme::Scalar::random(&mut rng);
                        }
                    }
                }

                // Compute commitments to advice column polynomials
                let advice_blinds: Vec<_> = advice
                    .iter()
                    .map(|_| Blind(Scheme::Scalar::random(&mut rng)))
                    .collect();
                let advice_commitments_projective: Vec<_> = advice
                    .iter()
                    .zip(advice_blinds.iter())
                    .map(|(poly, blind)| params.commit_lagrange(poly, *blind))
                    .collect();
                use group::Group;
                let mut advice_commitments = vec![
                    <Scheme as CommitmentScheme>::Curve::identity();
                    advice_commitments_projective.len()
                ];
                <<Scheme as CommitmentScheme>::Curve as CurveAffine>::CurveExt::batch_normalize(
                    &advice_commitments_projective,
                    &mut advice_commitments,
                );
                let advice_commitments = advice_commitments;
                drop(advice_commitments_projective);

                for commitment in &advice_commitments {
                    transcript.write_point(*commitment)?;
                }

                let advice_polys: Vec<_> = advice
                    .clone()
                    .into_iter()
                    .map(|poly| domain.lagrange_to_coeff(poly))
                    .collect();

                let advice_cosets: Vec<_> = advice_polys
                    .iter()
                    .map(|poly| domain.coeff_to_extended(poly.clone()))
                    .collect();

                Ok(AdviceSingle {
                    advice_values: advice,
                    advice_polys,
                    advice_cosets,
                    advice_blinds,
                })
            },
        )
        .collect::<Result<Vec<_>, _>>()?;

    // Sample theta challenge for keeping lookup columns linearly independent
    let theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    let lookups: Vec<Vec<lookup::prover::Permuted<Scheme::Curve>>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| -> Result<Vec<_>, Error> {
            // Construct and commit to permuted values for each lookup
            pk.vk
                .cs
                .lookups
                .iter()
                .map(|lookup| {
                    lookup.commit_permuted::<Scheme, _, _, _, ZK>(
                        pk,
                        params,
                        domain,
                        theta,
                        &advice.advice_values,
                        &pk.fixed_values,
                        &instance.instance_values,
                        &mut rng,
                        transcript,
                    )
                })
                .collect()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    // Commit to permutations.
    let permutations: Vec<permutation::prover::Committed<Scheme::Curve>> = instance
        .iter()
        .zip(advice.iter())
        .map(|(instance, advice)| {
            pk.vk.cs.permutation.commit::<Scheme, _, _, _, ZK>(
                params,
                pk,
                &pk.permutation,
                &advice.advice_values,
                &pk.fixed_values,
                &instance.instance_values,
                beta,
                gamma,
                &mut rng,
                transcript,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let lookups: Vec<Vec<lookup::prover::Committed<Scheme::Curve>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            // Construct and commit to products for each lookup
            lookups
                .into_iter()
                .map(|lookup| {
                    lookup.commit_product::<Scheme, _, _, _, ZK>(
                        pk, params, beta, gamma, &mut rng, transcript,
                    )
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Commit to the vanishing argument's random polynomial for blinding h(x_3)
    let vanishing =
        vanishing::Argument::commit::<Scheme, _, _, _, ZK>(params, domain, &mut rng, transcript)?;

    // Obtain challenge for keeping all separate gates linearly independent
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    // Evaluate the h(X) polynomial
    let h_poly = pk.ev.evaluate_h::<ZK>(
        pk,
        advice.iter().map(|a| &a.advice_cosets).collect(),
        instance.iter().map(|i| &i.instance_cosets).collect(),
        *y,
        *beta,
        *gamma,
        *theta,
        &lookups,
        &permutations,
    );

    // Construct the vanishing argument's h(X) commitments
    let vanishing =
        vanishing.construct::<Scheme, _, _, _>(params, domain, h_poly, &mut rng, transcript)?;

    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
    let xn = x.pow(&[params.n() as u64, 0, 0, 0]);

    // Compute and hash instance evals for each circuit instance
    for instance in instance.iter() {
        // Evaluate polynomials at omega^i x
        let instance_evals: Vec<_> = meta
            .instance_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(
                    &instance.instance_polys[column.index()],
                    domain.rotate_omega(*x, at),
                )
            })
            .collect();

        // Hash each instance column evaluation
        for eval in instance_evals.iter() {
            transcript.write_scalar(*eval)?;
        }
    }

    // Compute and hash advice evals for each circuit instance
    for advice in advice.iter() {
        // Evaluate polynomials at omega^i x
        let advice_evals: Vec<_> = meta
            .advice_queries
            .iter()
            .map(|&(column, at)| {
                eval_polynomial(
                    &advice.advice_polys[column.index()],
                    domain.rotate_omega(*x, at),
                )
            })
            .collect();

        // Hash each advice column evaluation
        for eval in advice_evals.iter() {
            transcript.write_scalar(*eval)?;
        }
    }

    // Compute and hash fixed evals (shared across all circuit instances)
    let fixed_evals: Vec<_> = meta
        .fixed_queries
        .iter()
        .map(|&(column, at)| {
            eval_polynomial(&pk.fixed_polys[column.index()], domain.rotate_omega(*x, at))
        })
        .collect();

    // Hash each fixed column evaluation
    for eval in fixed_evals.iter() {
        transcript.write_scalar(*eval)?;
    }

    let vanishing = vanishing.evaluate::<_, _, ZK>(x, xn, domain, transcript)?;

    // Evaluate common permutation data
    pk.permutation.evaluate(x, transcript)?;

    // Evaluate the permutations, if any, at omega^i x.
    let permutations: Vec<permutation::prover::Evaluated<Scheme::Curve>> = permutations
        .into_iter()
        .map(|permutation| -> Result<_, _> {
            permutation
                .construct()
                .evaluate::<_, _, ZK>(pk, x, transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Evaluate the lookups, if any, at omega^i x.
    let lookups: Vec<Vec<lookup::prover::Evaluated<Scheme::Curve>>> = lookups
        .into_iter()
        .map(|lookups| -> Result<Vec<_>, _> {
            lookups
                .into_iter()
                .map(|p| p.evaluate(pk, x, transcript))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;

    let instances = instance
        .iter()
        .zip(advice.iter())
        .zip(permutations.iter())
        .zip(lookups.iter())
        .flat_map(|(((instance, advice), permutation), lookups)| {
            iter::empty()
                .chain(
                    pk.vk
                        .cs
                        .instance_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &instance.instance_polys[column.index()],
                            blind: Blind::default(),
                        }),
                )
                .chain(
                    pk.vk
                        .cs
                        .advice_queries
                        .iter()
                        .map(move |&(column, at)| ProverQuery {
                            point: domain.rotate_omega(*x, at),
                            poly: &advice.advice_polys[column.index()],
                            blind: advice.advice_blinds[column.index()],
                        }),
                )
                .chain(permutation.open::<ZK>(pk, x))
                .chain(lookups.iter().flat_map(move |p| p.open(pk, x)).into_iter())
        })
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                .map(|&(column, at)| ProverQuery {
                    point: domain.rotate_omega(*x, at),
                    poly: &pk.fixed_polys[column.index()],
                    blind: Blind::default(),
                }),
        )
        .chain(pk.permutation.open(x))
        // We query the h(X) polynomial at x
        .chain(vanishing.open::<ZK>(x));

    let prover = Prover::new(params);
    prover
        .create_proof(rng, transcript, instances)
        .map_err(|_| Error::ConstraintSystemFailure)
}
