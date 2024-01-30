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
                    let [w_l, w_r, w_o] =
                        [w_l, w_r, w_o].map(|column| meta.query_advice(column, Rotation::cur()));
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
        #[cfg(feature = "circuit-params")]
        type Params = ();

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
                    phase_info.rotations.len() * phase_info.num_polys - phase_info.constraints.len()
                })
                .sum::<usize>();
        num_commitments * 32 + num_evals * 32
    });
}
