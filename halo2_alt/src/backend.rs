//! Plonkish proof systems implementations.

use crate::protocol::Protocol;
use halo2_proofs::plonk::Error;
use rand_core::RngCore;
use std::fmt::Debug;

pub mod fflonk;

/// `Circuit` is an abstraction to make proof systems easier to handle.
pub trait Circuit<F>: Debug {
    /// A arbitrary buffer for multi-phase circuit to be stateful when witnessing.
    type WitnessBuf: Debug + Default;

    /// Returns `Protocol` of the circuit.
    fn protocol(&self) -> Protocol<F>;

    /// Returns values of preprocessed polynomials.
    fn preprocess(&self) -> Result<Vec<Vec<F>>, Error>;

    /// Returns values of advice polynomials of given `phase`.
    fn witness(
        &self,
        phase: usize,
        values: &[&[F]],
        challenges: &[F],
        buf: &mut Self::WitnessBuf,
        rng: impl RngCore,
    ) -> Result<Vec<Vec<F>>, Error>;
}
