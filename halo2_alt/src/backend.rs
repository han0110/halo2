use crate::protocol::Protocol;
use halo2_proofs::plonk::Error;
use rand_core::RngCore;
use std::fmt::Debug;

pub mod fflonk;

pub trait Circuit<F>: Debug {
    type WitnessBuf: Debug + Default;

    fn protocol(&self) -> Protocol<F>;

    fn preprocess(&self) -> Result<Vec<Vec<F>>, Error>;

    fn witness(
        &self,
        phase: usize,
        values: &[&[F]],
        challenges: &[F],
        buf: &mut Self::WitnessBuf,
        rng: impl RngCore,
    ) -> Result<Vec<Vec<F>>, Error>;
}
