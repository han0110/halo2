#[macro_use]
extern crate criterion;

use crate::arithmetic::small_multiexp;
use crate::halo2curves::pasta::Fp;
use criterion::{black_box, Criterion};
use group::ff::Field;
use halo2_proofs::poly::commitment::ParamsProver;
use halo2_proofs::poly::ipa::commitment::ParamsIPA;
use halo2_proofs::*;
use halo2curves::pasta::EqAffine;
use rand_core::OsRng;

fn criterion_benchmark(c: &mut Criterion) {
    let rng = OsRng;

    // small multiexp
    {
        let params: ParamsIPA<EqAffine> = ParamsIPA::new(5, rng);
        let g = &mut params.get_g();
        let len = g.len() / 2;
        let (g_lo, g_hi) = g.split_at_mut(len);

        let coeff_1 = Fp::random(rng);
        let coeff_2 = Fp::random(rng);

        c.bench_function("double-and-add", |b| {
            b.iter(|| {
                for (g_lo, g_hi) in g_lo.iter().zip(g_hi.iter()) {
                    small_multiexp(&[black_box(coeff_1), black_box(coeff_2)], &[*g_lo, *g_hi]);
                }
            })
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
