//! Alternative Plonkish proof systems for `halo2_proofs` circuits.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]

pub mod backend;
pub mod protocol;
mod util;

pub use halo2_proofs;
