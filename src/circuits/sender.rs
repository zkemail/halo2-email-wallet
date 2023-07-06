use crate::circuits::poseidon_chip::{
    poseidon_hash, poseidon_hash_bytes, HasherChip, HasherChipDigest, PoseidonChipBn254_8_58,
};
use crate::circuits::utils::*;
use halo2_base::halo2_proofs::circuit::{AssignedCell, Cell, Region, SimpleFloorPlanner, Value};
use halo2_base::halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Instance};
use halo2_base::halo2_proofs::{circuit::Layouter, plonk::Error};
use halo2_base::utils::{decompose, decompose_fe_to_u64_limbs, value_to_option};
use halo2_base::{gates::range::RangeStrategy::Vertical, ContextParams, SKIP_FIRST_PASS};
use halo2_base::{
    gates::{flex_gate::FlexGateConfig, range::RangeConfig, GateInstructions, RangeInstructions},
    utils::PrimeField,
    Context,
};
use halo2_base::{AssignedValue, QuantumCell};
use halo2_zk_email::halo2_dynamic_sha256::*;
use halo2_zk_email::halo2_regex::defs::{AllstrRegexDef, RegexDefs, SubstrRegexDef};
use halo2_zk_email::halo2_regex::*;
use halo2_zk_email::halo2_rsa::*;
use halo2_zk_email::regex_sha2::RegexSha2Config;
use halo2_zk_email::sign_verify::SignVerifyConfig;
use halo2_zk_email::utils::{get_email_substrs, get_substr, read_default_circuit_config_params};
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::FromPrimitive;
use rand::{thread_rng, CryptoRng, Rng, RngCore};
use rsa::{PublicKeyParts, RsaPrivateKey};
use serde_json;
use sha2::{Digest, Sha256};
use snark_verifier::loader::LoadedScalar;
use snark_verifier_sdk::CircuitExt;
use std::fs::File;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct SenderSignVerifyConfig<F: PrimeField> {
    sign_verify_config: SignVerifyConfig<F>,
    public_input: Column<Instance>,
}

#[derive(Debug, Clone)]
pub struct SenderSignVerifyCircuit<F: PrimeField> {
    pub header_hash_bytes: Vec<u8>,
    pub public_key_n: BigUint,
    pub signature: BigUint,
    _f: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for SenderSignVerifyCircuit<F> {
    type Config = SenderSignVerifyConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            header_hash_bytes: vec![0; self.header_hash_bytes.len()],
            public_key_n: self.public_key_n.clone(),
            signature: self.signature.clone(),
            _f: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let params = read_default_circuit_config_params();
        let range_config = RangeConfig::configure(
            meta,
            Vertical,
            &[params.num_flex_advice],
            &[params.num_range_lookup_advice],
            params.num_flex_advice,
            params.range_lookup_bits,
            0,
            params.degree as usize,
        );
        // let header_params = params.header_config.expect("header_config is required");
        let sign_verify_params = params
            .sign_verify_config
            .expect("sign_verify_config is required");
        // let sha256_config = params.sha256_config.expect("sha256_config is required");
        // assert_eq!(
        //     header_config.allstr_filepathes.len(),
        //     header_config.substr_filepathes.len()
        // );
        // let sha256_config = Sha256DynamicConfig::configure(
        //     meta,
        //     vec![
        //         header_config.max_byte_size,
        //         sign_verify_config.public_key_bits / 8 + 64, // RSA public key
        //     ],
        //     range_config.clone(),
        //     sha256_config.num_bits_lookup,
        //     sha256_config.num_advice_columns,
        //     false,
        // );
        let sign_verify_config =
            SignVerifyConfig::configure(range_config, sign_verify_params.public_key_bits);

        let public_input = meta.instance_column();
        meta.enable_equality(public_input);
        Self::Config {
            sign_verify_config,
            public_input,
        }
    }

    fn synthesize(
        &self,
        mut config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config
            .sign_verify_config
            .rsa_config
            .range()
            .load_lookup_table(&mut layouter)?;
        let mut first_pass = SKIP_FIRST_PASS;
        let mut public_input_cell = vec![];
        // let params = read_default_circuit_config_params();
        // let sign_verify_params = params
        //     .sign_verify_config
        //     .expect("sign_verify_config is required");
        layouter.assign_region(
            || "zkemail",
            |region| {
                if first_pass {
                    first_pass = false;
                    return Ok(());
                }
                let ctx = &mut config.sign_verify_config.rsa_config.new_context(region);
                // let sha256_result = config.sha256_config.digest(ctx, &self.header_bytes)?;

                let range = config.sign_verify_config.rsa_config.range();
                let gate = config.sign_verify_config.rsa_config.gate();
                let assigned_hash_bytes = self
                    .header_hash_bytes
                    .iter()
                    .map(|byte| gate.load_witness(ctx, Value::known(F::from(*byte as u64))))
                    .collect_vec();
                let public_key = RSAPublicKey::<F>::new(
                    Value::known(self.public_key_n.clone()),
                    RSAPubE::Fix(BigUint::from(Self::DEFAULT_E)),
                );
                let signature = RSASignature::<F>::new(Value::known(self.signature.clone()));
                let (assigned_public_key, assigned_signature) = config
                    .sign_verify_config
                    .verify_signature(ctx, &assigned_hash_bytes, public_key, signature)?;
                // let mut hash_bytes = self.header_hash_bytes.to_vec();
                // hash_bytes.reverse();
                // // let bytes_bits = hash_bytes.len() * 8;
                // let limb_bits = Self::LIMB_BITS;
                // let limb_bytes = limb_bits / 8;
                // let mut hashed_u64s = vec![];
                // // let bases = (0..limb_bytes)
                // //     .map(|i| F::from((1u64 << (8 * i)) as u64))
                // //     .map(QuantumCell::Constant)
                // //     .collect::<Vec<QuantumCell<F>>>();
                // for i in 0..(hash_bytes.len() / limb_bytes) {
                //     let mut hashed_u64 = 0;
                //     for j in 0..limb_bytes {
                //         hashed_u64 += (hash_bytes[limb_bytes * i + j] as u64) << (8 * j);
                //     }
                //     let assigned = gate.load_witness(ctx, Value::known(F::from(hashed_u64)));
                //     hashed_u64s.push(assigned);
                // }
                // let public_key = RSAPublicKey::<F>::new(
                //     Value::known(self.public_key_n.clone()),
                //     RSAPubE::Fix(BigUint::from(Self::DEFAULT_E)),
                // );
                // let signature = RSASignature::<F>::new(Value::known(self.signature.clone()));
                // let assigned_public_key = config.rsa_config.assign_public_key(ctx, public_key)?;
                // let assigned_signature = config.rsa_config.assign_signature(ctx, signature)?;
                // let is_sign_valid = config.rsa_config.verify_pkcs1v15_signature(
                //     ctx,
                //     &assigned_public_key,
                //     &hashed_u64s,
                //     &assigned_signature,
                // )?;
                // gate.assert_is_const(ctx, &is_sign_valid, F::one());
                let poseidon = PoseidonChipBn254_8_58::new(ctx, &gate);
                {
                    let public_key_hash_input = assigned_public_key.n.limbs();
                    let public_key_hash =
                        poseidon.hash_elements(ctx, gate, public_key_hash_input)?;
                    public_input_cell.push(public_key_hash.to_assigned()[0].cell());
                }
                {
                    let signature_limbs = assigned_signature.c.limbs();
                    let sign_limbs = vec![
                        signature_limbs[0].clone(),
                        signature_limbs[1].clone(),
                        signature_limbs[2].clone(),
                        slice_first_7bytes_from_u64(ctx, range, &signature_limbs[3]),
                    ];
                    let signature_int = assigned_u64s_to_31bytes_field(ctx, range, &sign_limbs);
                    let hash_int =
                        assigned_bytes_to_31bytes_field(ctx, range, &assigned_hash_bytes[0..31]);
                    let header_hash_commit =
                        poseidon.hash_elements(ctx, gate, &[signature_int, hash_int])?;
                    public_input_cell.push(header_hash_commit.to_assigned()[0].cell());
                }

                // let assigned_public_key_bytes = assigned_public_key
                //     .n
                //     .limbs()
                //     .into_iter()
                //     .flat_map(|limb| {
                //         let limb_val = value_to_option(limb.value()).unwrap();
                //         let bytes = decompose_fe_to_u64_limbs(limb_val, 64 / 8, 8);
                //         let mut sum = gate.load_zero(ctx);
                //         let assigned = bytes
                //             .into_iter()
                //             .enumerate()
                //             .map(|(idx, byte)| {
                //                 let assigned = gate.load_witness(ctx, Value::known(F::from(byte)));
                //                 range.range_check(ctx, &assigned, 8);
                //                 sum = gate.mul_add(
                //                     ctx,
                //                     QuantumCell::Existing(&assigned),
                //                     QuantumCell::Constant(F::from(1u64 << (8 * idx))),
                //                     QuantumCell::Existing(&sum),
                //                 );
                //                 assigned
                //             })
                //             .collect_vec();
                //         gate.assert_equal(
                //             ctx,
                //             QuantumCell::Existing(&sum),
                //             QuantumCell::Existing(limb),
                //         );
                //         assigned
                //     })
                //     .collect_vec();
                // let public_key_hash_result = config.sha256_config.digest(
                //     ctx,
                //     &value_to_option(self.public_key.n.clone())
                //         .unwrap()
                //         .to_bytes_le(),
                // )?;
                // for (a, b) in public_key_hash_result.input_bytes[0..assigned_public_key_bytes.len()]
                //     .into_iter()
                //     .map(|v| v.cell())
                //     .collect_vec()
                //     .into_iter()
                //     .zip(assigned_public_key_bytes.into_iter())
                // {
                //     ctx.region.constrain_equal(a, b.cell())?;
                // }

                // debug_assert_eq!(public_key_hash_result.output_bytes.len(), 32);
                // let mut packed_public_hash = gate.load_zero(ctx);
                // let mut coeff = F::from(1u64);
                // for byte in public_key_hash_result.output_bytes[0..31].iter() {
                //     packed_public_hash = gate.mul_add(
                //         ctx,
                //         QuantumCell::Existing(byte),
                //         QuantumCell::Constant(coeff),
                //         QuantumCell::Existing(&packed_public_hash),
                //     );
                //     coeff *= F::from(256u64);
                // }
                // config.sha256_config.range().finalize(ctx);
                // public_input_cell.push(header_bytes_poseidon.to_assigned()[0].cell());
                // public_input_cell.push(header_hash_poseidon.to_assigned()[0].cell());
                // public_input_cell.push(packed_public_hash.cell());
                Ok(())
            },
        )?;
        layouter.constrain_instance(public_input_cell[0], config.public_input, 0)?;
        layouter.constrain_instance(public_input_cell[1], config.public_input, 1)?;
        Ok(())
    }
}

impl<F: PrimeField> CircuitExt<F> for SenderSignVerifyCircuit<F> {
    fn num_instance(&self) -> Vec<usize> {
        vec![2]
    }

    fn instances(&self) -> Vec<Vec<F>> {
        let mut hash_bytes = self.header_hash_bytes.to_vec();
        hash_bytes.reverse();
        let params = read_default_circuit_config_params();
        let sign_verify_params = params
            .sign_verify_config
            .expect("sign_verify_config is required");
        // let bytes_bits = hash_bytes.len() * 8;
        // let limb_bits = Self::LIMB_BITS;
        // let limb_bytes = limb_bits / 8;
        // let mut hashed_u64s = vec![];
        // for i in 0..(hash_bytes.len() / limb_bytes) {
        //     let mut hashed_u64 = 0;
        //     for j in 0..limb_bytes {
        //         hashed_u64 += (hash_bytes[limb_bytes * i + j] as u64) << (8 * j);
        //     }
        //     hashed_u64s.push(F::from(hashed_u64));
        // }
        let public_key_hash_input: Vec<F> = decompose_biguint(
            &self.public_key_n,
            sign_verify_params.public_key_bits / Self::LIMB_BITS,
            Self::LIMB_BITS,
        );
        let public_key_hash = poseidon_hash(&public_key_hash_input);
        let signature_int = {
            let mut sum = F::zero();
            let mut base = F::one();
            for byte in self.signature.to_bytes_le().iter() {
                sum += F::from(*byte as u64) * base;
                base *= F::from_u128(1u128 << 64);
            }
            sum
        };
        let hash_int = {
            let mut sum = F::zero();
            let mut base = F::one();
            for byte in self.header_hash_bytes.iter() {
                sum += F::from(*byte as u64) * base;
                base *= F::from(256u64);
            }
            sum
        };
        let header_hash_commit = poseidon_hash(&[signature_int, hash_int]);
        vec![vec![public_key_hash, header_hash_commit]]
    }
}

impl<F: PrimeField> SenderSignVerifyCircuit<F> {
    pub const DEFAULT_E: u128 = 65537;
    pub const LIMB_BITS: usize = 64;
}

#[derive(Debug, Clone)]
pub struct SenderHeaderConfig<F: PrimeField> {
    sha256_config: Sha256DynamicConfig<F>,
    regex_sha2_config: RegexSha2Config<F>,
    public_input: Column<Instance>,
}

#[derive(Debug, Clone)]
pub struct SenderHeaderCircuit<F: PrimeField> {
    pub header_bytes: Vec<u8>,
    pub from_relayer_rand: F,
    pub signature: BigUint,
}

impl<F: PrimeField> Circuit<F> for SenderHeaderCircuit<F> {
    type Config = SenderHeaderConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            header_bytes: vec![0; self.header_bytes.len()],
            from_relayer_rand: F::one(),
            signature: self.signature.clone(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let params = read_default_circuit_config_params();
        let range_config = RangeConfig::configure(
            meta,
            Vertical,
            &[params.num_flex_advice],
            &[params.num_range_lookup_advice],
            params.num_flex_advice,
            params.range_lookup_bits,
            0,
            params.degree as usize,
        );
        let header_params = params.header_config.expect("header_config is required");
        let sha256_config = params.sha256_config.expect("sha256_config is required");
        assert_eq!(
            header_params.allstr_filepathes.len(),
            header_params.substr_filepathes.len()
        );
        let sha256_config = Sha256DynamicConfig::configure(
            meta,
            vec![header_params.max_variable_byte_size],
            range_config.clone(),
            sha256_config.num_bits_lookup,
            sha256_config.num_advice_columns,
            false,
        );
        let header_regex_defs = header_params
            .allstr_filepathes
            .iter()
            .zip(header_params.substr_filepathes.iter())
            .map(|(allstr_path, substr_pathes)| {
                let allstr = AllstrRegexDef::read_from_text(&allstr_path);
                let substrs = substr_pathes
                    .into_iter()
                    .map(|path| SubstrRegexDef::read_from_text(&path))
                    .collect_vec();
                RegexDefs { allstr, substrs }
            })
            .collect_vec();
        let regex_sha2_config = RegexSha2Config::configure(
            meta,
            header_params.max_variable_byte_size,
            header_params.skip_prefix_bytes_size.unwrap_or(0),
            range_config,
            header_regex_defs,
        );

        let public_input = meta.instance_column();
        meta.enable_equality(public_input);
        Self::Config {
            sha256_config,
            regex_sha2_config,
            public_input,
        }
    }

    fn synthesize(
        &self,
        mut config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config
            .sha256_config
            .range()
            .load_lookup_table(&mut layouter)?;
        config.sha256_config.load(&mut layouter)?;
        config.regex_sha2_config.load(&mut layouter)?;
        let mut first_pass = SKIP_FIRST_PASS;
        let mut public_input_cell = vec![];
        // let params = read_default_circuit_config_params();
        // let sign_verify_params = params
        //     .sign_verify_config
        //     .expect("sign_verify_config is required");
        layouter.assign_region(
            || "zkemail",
            |region| {
                if first_pass {
                    first_pass = false;
                    return Ok(());
                }
                let ctx = &mut config.sha256_config.new_context(region);
                // let sha256_result = config.sha256_config.digest(ctx, &self.header_bytes)?;

                let range = config.sha256_config.range().clone();
                let gate = range.gate();
                let poseidon = PoseidonChipBn254_8_58::new(ctx, &gate);

                // Assert `fromRelayerHash==POSEIDON_HASH(fromRelayerR)`.
                let assigned_relayer_rand =
                    gate.load_witness(ctx, Value::known(self.from_relayer_rand));
                let from_relayer_hash =
                    poseidon.hash_elements(ctx, gate, &[assigned_relayer_rand])?;
                public_input_cell.push(from_relayer_hash.to_assigned()[0].cell());

                // Let `headerHash=SHA256(emailHeader)`.
                // Extract the substring `fromEmailAddr` from `emailHeaderBytes`.
                // Extract the substring `subjectStr` from `emailHeaderBytes`.
                // Extract the substring `subjectEmailAddr` from `subjectStr`.
                let header_result = config.regex_sha2_config.match_and_hash(
                    ctx,
                    &mut config.sha256_config,
                    &self.header_bytes,
                )?;
                let assigned_header_hash = header_result.hash_bytes;
                let assigned_from_email_addr =
                    self.shift_substr(ctx, gate, &header_result.regex, Self::FROM_SUBSTR_ID);
                let assigned_subject_before_email =
                    self.shift_substr(ctx, gate, &header_result.regex, Self::SUBJECT_SUBSTR0);
                let assigned_subject_email_addr =
                    self.shift_substr(ctx, gate, &header_result.regex, Self::SUBJECT_SUBSTR1);
                let assigned_subject_after_email =
                    self.shift_substr(ctx, gate, &header_result.regex, Self::SUBJECT_SUBSTR2);

                // let assigned_subject_emai_addr =
                //     assign_str(ctx, &range, &subject_email_addr.1, Self::EMAIL_MAX_BYTES);

                // let assigned_from_email_addr = header_result.regex.

                // let assigned_hash_bytes = self
                //     .header_hash_bytes
                //     .iter()
                //     .map(|byte| gate.load_witness(ctx, Value::known(F::from(*byte as u64))))
                //     .collect_vec();
                // let public_key = RSAPublicKey::<F>::new(
                //     Value::known(self.public_key_n.clone()),
                //     RSAPubE::Fix(BigUint::from(Self::DEFAULT_E)),
                // );
                // let signature = RSASignature::<F>::new(Value::known(self.signature.clone()));
                // let (assigned_public_key, assigned_signature) = config
                //     .sign_verify_config
                //     .verify_signature(ctx, &assigned_hash_bytes, public_key, signature)?;
                // let mut hash_bytes = self.header_hash_bytes.to_vec();
                // hash_bytes.reverse();
                // // let bytes_bits = hash_bytes.len() * 8;
                // let limb_bits = Self::LIMB_BITS;
                // let limb_bytes = limb_bits / 8;
                // let mut hashed_u64s = vec![];
                // // let bases = (0..limb_bytes)
                // //     .map(|i| F::from((1u64 << (8 * i)) as u64))
                // //     .map(QuantumCell::Constant)
                // //     .collect::<Vec<QuantumCell<F>>>();
                // for i in 0..(hash_bytes.len() / limb_bytes) {
                //     let mut hashed_u64 = 0;
                //     for j in 0..limb_bytes {
                //         hashed_u64 += (hash_bytes[limb_bytes * i + j] as u64) << (8 * j);
                //     }
                //     let assigned = gate.load_witness(ctx, Value::known(F::from(hashed_u64)));
                //     hashed_u64s.push(assigned);
                // }
                // let public_key = RSAPublicKey::<F>::new(
                //     Value::known(self.public_key_n.clone()),
                //     RSAPubE::Fix(BigUint::from(Self::DEFAULT_E)),
                // );
                // let signature = RSASignature::<F>::new(Value::known(self.signature.clone()));
                // let assigned_public_key = config.rsa_config.assign_public_key(ctx, public_key)?;
                // let assigned_signature = config.rsa_config.assign_signature(ctx, signature)?;
                // let is_sign_valid = config.rsa_config.verify_pkcs1v15_signature(
                //     ctx,
                //     &assigned_public_key,
                //     &hashed_u64s,
                //     &assigned_signature,
                // )?;
                // gate.assert_is_const(ctx, &is_sign_valid, F::one());
                // let poseidon = PoseidonChipBn254_8_58::new(ctx, &gate);
                // {
                //     let public_key_hash_input = assigned_public_key.n.limbs();
                //     let public_key_hash =
                //         poseidon.hash_elements(ctx, gate, public_key_hash_input)?;
                //     public_input_cell.push(public_key_hash.to_assigned()[0].cell());
                // }
                // {
                //     let signature_limbs = assigned_signature.c.limbs();
                //     let sign_limbs = vec![
                //         signature_limbs[0].clone(),
                //         signature_limbs[1].clone(),
                //         signature_limbs[2].clone(),
                //         slice_first_7bytes_from_u64(ctx, range, &signature_limbs[3]),
                //     ];
                //     let signature_int = assigned_u64s_to_31bytes_field(ctx, range, &sign_limbs);
                //     let hash_int =
                //         assigned_bytes_to_31bytes_field(ctx, range, &assigned_hash_bytes[0..31]);
                //     let header_hash_commit =
                //         poseidon.hash_elements(ctx, gate, &[signature_int, hash_int])?;
                //     public_input_cell.push(header_hash_commit.to_assigned()[0].cell());
                // }

                // let assigned_public_key_bytes = assigned_public_key
                //     .n
                //     .limbs()
                //     .into_iter()
                //     .flat_map(|limb| {
                //         let limb_val = value_to_option(limb.value()).unwrap();
                //         let bytes = decompose_fe_to_u64_limbs(limb_val, 64 / 8, 8);
                //         let mut sum = gate.load_zero(ctx);
                //         let assigned = bytes
                //             .into_iter()
                //             .enumerate()
                //             .map(|(idx, byte)| {
                //                 let assigned = gate.load_witness(ctx, Value::known(F::from(byte)));
                //                 range.range_check(ctx, &assigned, 8);
                //                 sum = gate.mul_add(
                //                     ctx,
                //                     QuantumCell::Existing(&assigned),
                //                     QuantumCell::Constant(F::from(1u64 << (8 * idx))),
                //                     QuantumCell::Existing(&sum),
                //                 );
                //                 assigned
                //             })
                //             .collect_vec();
                //         gate.assert_equal(
                //             ctx,
                //             QuantumCell::Existing(&sum),
                //             QuantumCell::Existing(limb),
                //         );
                //         assigned
                //     })
                //     .collect_vec();
                // let public_key_hash_result = config.sha256_config.digest(
                //     ctx,
                //     &value_to_option(self.public_key.n.clone())
                //         .unwrap()
                //         .to_bytes_le(),
                // )?;
                // for (a, b) in public_key_hash_result.input_bytes[0..assigned_public_key_bytes.len()]
                //     .into_iter()
                //     .map(|v| v.cell())
                //     .collect_vec()
                //     .into_iter()
                //     .zip(assigned_public_key_bytes.into_iter())
                // {
                //     ctx.region.constrain_equal(a, b.cell())?;
                // }

                // debug_assert_eq!(public_key_hash_result.output_bytes.len(), 32);
                // let mut packed_public_hash = gate.load_zero(ctx);
                // let mut coeff = F::from(1u64);
                // for byte in public_key_hash_result.output_bytes[0..31].iter() {
                //     packed_public_hash = gate.mul_add(
                //         ctx,
                //         QuantumCell::Existing(byte),
                //         QuantumCell::Constant(coeff),
                //         QuantumCell::Existing(&packed_public_hash),
                //     );
                //     coeff *= F::from(256u64);
                // }
                // config.sha256_config.range().finalize(ctx);
                // public_input_cell.push(header_bytes_poseidon.to_assigned()[0].cell());
                // public_input_cell.push(header_hash_poseidon.to_assigned()[0].cell());
                // public_input_cell.push(packed_public_hash.cell());
                Ok(())
            },
        )?;
        layouter.constrain_instance(public_input_cell[0], config.public_input, 0)?;
        layouter.constrain_instance(public_input_cell[1], config.public_input, 1)?;
        Ok(())
    }
}

impl<F: PrimeField> CircuitExt<F> for SenderHeaderCircuit<F> {
    fn num_instance(&self) -> Vec<usize> {
        vec![2]
    }

    fn instances(&self) -> Vec<Vec<F>> {
        // let mut hash_bytes = self.header_hash_bytes.to_vec();
        // hash_bytes.reverse();
        // let params = read_default_circuit_config_params();
        // let sign_verify_params = params
        //     .sign_verify_config
        //     .expect("sign_verify_config is required");
        // let bytes_bits = hash_bytes.len() * 8;
        // let limb_bits = Self::LIMB_BITS;
        // let limb_bytes = limb_bits / 8;
        // let mut hashed_u64s = vec![];
        // for i in 0..(hash_bytes.len() / limb_bytes) {
        //     let mut hashed_u64 = 0;
        //     for j in 0..limb_bytes {
        //         hashed_u64 += (hash_bytes[limb_bytes * i + j] as u64) << (8 * j);
        //     }
        //     hashed_u64s.push(F::from(hashed_u64));
        // }
        // let public_key_hash_input: Vec<F> = decompose_biguint(
        //     &self.public_key_n,
        //     sign_verify_params.public_key_bits / Self::LIMB_BITS,
        //     Self::LIMB_BITS,
        // );
        // let public_key_hash = poseidon_hash(&public_key_hash_input);
        // let signature_int = {
        //     let mut sum = F::zero();
        //     let mut base = F::one();
        //     for byte in self.signature.to_bytes_le().iter() {
        //         sum += F::from(*byte as u64) * base;
        //         base *= F::from_u128(1u128 << 64);
        //     }
        //     sum
        // };
        // let hash_int = {
        //     let mut sum = F::zero();
        //     let mut base = F::one();
        //     for byte in self.header_hash_bytes.iter() {
        //         sum += F::from(*byte as u64) * base;
        //         base *= F::from(256u64);
        //     }
        //     sum
        // };
        // let header_hash_commit = poseidon_hash(&[signature_int, hash_int]);
        vec![vec![]]
    }
}

impl<F: PrimeField> SenderHeaderCircuit<F> {
    pub const EMAIL_MAX_BYTES: usize = 256;
    pub const SUBJECT_MAX_BYTES: usize = 1024;
    pub const FROM_SUBSTR_ID: u64 = 1;
    pub const SUBJECT_SUBSTR0: u64 = 2;
    pub const SUBJECT_SUBSTR1: u64 = 3;
    pub const SUBJECT_SUBSTR2: u64 = 4;
    // pub const FROM_REGEX: &'static str = r"(?<=from:).*@.*(?=\r)";
    // pub const SUBJECT_REGEX: &'static str = r"(?<=subject:).*(?=\r)";
    // pub const SUBJECT_EMAIL_REGEX: &'static str = r"(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|0|1|2|3|4|5|6|7|8|9|_|\\.|-)+@(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z|0|1|2|3|4|5|6|7|8|9|_|\\.|-)+";

    fn shift_substr<'a, 'b: 'a>(
        &self,
        ctx: &mut Context<'b, F>,
        gate: &FlexGateConfig<F>,
        regex_result: &AssignedRegexResult<'a, F>,
        target_substr_id: u64,
    ) -> Vec<AssignedValue<'a, F>> {
        let mut shift_value = gate.load_zero(ctx);
        let mut is_target_found = gate.load_zero(ctx);
        for (idx, assigned_substr_id) in regex_result.all_substr_ids.iter().enumerate() {
            let is_target = gate.is_equal(
                ctx,
                QuantumCell::Existing(assigned_substr_id),
                QuantumCell::Constant(F::from(target_substr_id)),
            );
            is_target_found = gate.select(
                ctx,
                QuantumCell::Constant(F::one()),
                QuantumCell::Existing(&is_target_found),
                QuantumCell::Existing(&is_target),
            );
            shift_value = gate.select(
                ctx,
                QuantumCell::Existing(&shift_value),
                QuantumCell::Constant(F::from((idx + 1) as u64)),
                QuantumCell::Existing(&is_target_found),
            );
        }
        self.shift_variable(
            ctx,
            gate,
            regex_result.masked_characters.len(),
            &regex_result.masked_characters,
            &shift_value,
        )
    }

    fn shift_variable<'a, 'b: 'a>(
        &self,
        ctx: &mut Context<'b, F>,
        gate: &FlexGateConfig<F>,
        max_byte_size: usize,
        inputs: &[AssignedValue<'a, F>],
        shift_value: &AssignedValue<'a, F>,
    ) -> Vec<AssignedValue<'a, F>> {
        // const MAX_SHIFT_BITS: usize = 64;
        debug_assert_eq!(inputs.len(), max_byte_size);
        let max_shift_bits: usize = 64 - max_byte_size.leading_zeros() as usize;
        let shift_value_bits = gate.num_to_bits(ctx, shift_value, max_shift_bits);
        let mut prev_tmp = inputs.to_vec();
        let max_len = inputs.len();
        let mut new_tmp = (0..max_len)
            .into_iter()
            .map(|_| gate.load_zero(ctx))
            .collect::<Vec<AssignedValue<F>>>();
        for log_offset in 0..max_shift_bits {
            for position in 0..max_len {
                let offset = (position + (1 << log_offset)) % max_len;
                let value_offset = gate.select(
                    ctx,
                    QuantumCell::Existing(&prev_tmp[offset]),
                    QuantumCell::Existing(&prev_tmp[position]),
                    QuantumCell::Existing(&shift_value_bits[log_offset]),
                );
                new_tmp[position] = value_offset;
            }
            prev_tmp = new_tmp.to_vec();
        }
        new_tmp
    }
}
