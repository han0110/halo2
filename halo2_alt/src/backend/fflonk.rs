//! Implementation of [fflonk] proof system.
//!
//! [fflonk]: https://eprint.iacr.org/2021/1167

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

#[cfg(test)]
mod test;

pub use circuit::FflonkCircuit;
pub use keygen::{keygen_pk, keygen_vk};
pub use prover::create_proof;
pub use verifier::verify_proof;

/// Query information of a phase.
#[derive(Clone, Debug)]
pub struct QueryInfo<F> {
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

/// Query information and constraint indices of a phase.
#[derive(Clone, Debug)]
pub struct PhaseInfo<F> {
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

/// Verifying key of fflonk.
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
            domain: protocol.domain(),
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

    /// Returns `EvaluationDomain`.
    pub fn domain(&self) -> &EvaluationDomain<C::Scalar> {
        &self.domain
    }

    /// Returns `Protocol`.
    pub fn protocol(&self) -> &Protocol<C::Scalar> {
        &self.protocol
    }

    /// Returns preprocessed commitment.
    pub fn preprocessed_commitment(&self) -> &C {
        &self.preprocessed_commitment
    }

    /// Returns preprocessed `QueryInfo`.
    pub fn preprocessed_query_info(&self) -> &QueryInfo<C::Scalar> {
        &self.preprocessed_query_info
    }

    /// Returns `PhaseInfo` of phases.
    pub fn phase_infos(&self) -> &[PhaseInfo<C::Scalar>] {
        &self.phase_infos
    }

    /// Returns transcript representation of this `VerifyingKey`.
    pub fn transcript_repr(&self) -> &C::Scalar {
        &self.transcript_repr
    }

    fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
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

    fn max_combined_poly_size(&self) -> usize {
        max_combined_poly_size(
            &self.protocol,
            &self.preprocessed_query_info,
            &self.phase_infos,
        )
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

/// Proving key of fflonk.
#[derive(Debug)]
pub struct ProvingKey<C: CurveAffine> {
    vk: VerifyingKey<C>,
    preprocessed_values: Vec<Vec<C::Scalar>>,
    preprocessed_polys: Vec<Polynomial<C::Scalar, Coeff>>,
    preprocessed_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    transparent_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    evaluators: Vec<Vec<Evaluator<C::Scalar>>>,
}

impl<C: CurveAffine> ProvingKey<C> {
    /// Returns verifying key.
    pub fn vk(&self) -> &VerifyingKey<C> {
        &self.vk
    }
}

#[allow(dead_code)]
#[derive(Debug)]
struct PinnedVerificationKey<'a, C: CurveAffine> {
    base_modulus: &'static str,
    scalar_modulus: &'static str,
    domain: PinnedEvaluationDomain<'a, C::Scalar>,
    protocol: &'a Protocol<C::Scalar>,
    preprocessed_commitment: &'a C,
    preprocessed_query_info: &'a QueryInfo<C::Scalar>,
    phase_infos: &'a [PhaseInfo<C::Scalar>],
}

fn max_combined_poly_size<F>(
    protocol: &Protocol<F>,
    preprocessed_query_info: &QueryInfo<F>,
    phase_infos: &[PhaseInfo<F>],
) -> usize {
    let max_combined_degree = chain![
        [preprocessed_query_info.t],
        phase_infos.iter().map(|phase_info| {
            let max_degree = phase_info
                .constraints
                .iter()
                .map(|idx| protocol.constraints()[*idx].degree().saturating_sub(1))
                .max()
                .unwrap_or(1);
            phase_info.t * max_degree
        })
    ]
    .max()
    .unwrap();
    max_combined_degree << protocol.k()
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
    let combined = (0..size)
        .into_par_iter()
        .map(|idx| {
            polys
                .get(idx % t)
                .and_then(|poly| poly.get(idx / t))
                .copied()
                .unwrap_or(F::ZERO)
        })
        .collect();
    Polynomial::new(combined)
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
