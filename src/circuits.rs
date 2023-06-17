use crate::poseidon_chip::{HasherChip, HasherChipDigest, PoseidonChipBn254_8_58};
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
use halo2_zk_email::sign_verify::SignVerifyConfig;
use halo2_zk_email::utils::{get_email_substrs, read_default_circuit_config_params};
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

#[derive(Debug, Clone)]
pub struct HeaderSignVerifyConfig<F: PrimeField> {
    sha256_config: Sha256DynamicConfig<F>,
    sign_verify_config: SignVerifyConfig<F>,
    public_input: Column<Instance>,
}

#[derive(Debug, Clone)]
pub struct HeaderSignVerifyCircuit<F: PrimeField> {
    pub header_bytes: Vec<u8>,
    pub public_key: RSAPublicKey<F>,
    pub signature: RSASignature<F>,
}

impl<F: PrimeField> Circuit<F> for HeaderSignVerifyCircuit<F> {
    type Config = HeaderSignVerifyConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            header_bytes: vec![],
            public_key: self.public_key.clone(),
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
        let header_config = params.header_config.expect("header_config is required");
        let sign_verify_config = params
            .sign_verify_config
            .expect("sign_verify_config is required");
        let sha256_config = params.sha256_config.expect("sha256_config is required");
        assert_eq!(
            header_config.allstr_filepathes.len(),
            header_config.substr_filepathes.len()
        );
        let sha256_config = Sha256DynamicConfig::configure(
            meta,
            vec![
                header_config.max_byte_size,
                sign_verify_config.public_key_bits / 8 + 64, // RSA public key
            ],
            range_config.clone(),
            sha256_config.num_bits_lookup,
            sha256_config.num_advice_columns,
            false,
        );

        let sign_verify_config = SignVerifyConfig::configure(
            meta,
            range_config.clone(),
            sign_verify_config.public_key_bits,
        );

        let public_input = meta.instance_column();
        meta.enable_equality(public_input);
        HeaderSignVerifyConfig {
            sha256_config,
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
            .sha256_config
            .range()
            .load_lookup_table(&mut layouter)?;
        config.sha256_config.load(&mut layouter)?;
        let mut first_pass = SKIP_FIRST_PASS;
        let mut public_input_cell = vec![];
        let params = read_default_circuit_config_params();
        layouter.assign_region(
            || "zkemail",
            |region| {
                if first_pass {
                    first_pass = false;
                    return Ok(());
                }
                let ctx = &mut config.sha256_config.new_context(region);
                let sha256_result = config.sha256_config.digest(ctx, &self.header_bytes)?;

                let (assigned_public_key, _) = config.sign_verify_config.verify_signature(
                    ctx,
                    &sha256_result.output_bytes,
                    self.public_key.clone(),
                    self.signature.clone(),
                )?;
                let range = config.sha256_config.range().clone();
                let gate = range.gate().clone();
                let poseidon = PoseidonChipBn254_8_58::new(ctx, &gate);
                let header_bytes_poseidon =
                    poseidon.hash_elements(ctx, &gate, &sha256_result.input_bytes)?;
                let header_hash_poseidon =
                    poseidon.hash_elements(ctx, &gate, &sha256_result.output_bytes)?;
                let assigned_public_key_bytes = assigned_public_key
                    .n
                    .limbs()
                    .into_iter()
                    .flat_map(|limb| {
                        let limb_val = value_to_option(limb.value()).unwrap();
                        let bytes = decompose_fe_to_u64_limbs(limb_val, 64 / 8, 8);
                        let mut sum = gate.load_zero(ctx);
                        let assigned = bytes
                            .into_iter()
                            .enumerate()
                            .map(|(idx, byte)| {
                                let assigned = gate.load_witness(ctx, Value::known(F::from(byte)));
                                range.range_check(ctx, &assigned, 8);
                                sum = gate.mul_add(
                                    ctx,
                                    QuantumCell::Existing(&assigned),
                                    QuantumCell::Constant(F::from(1u64 << (8 * idx))),
                                    QuantumCell::Existing(&sum),
                                );
                                assigned
                            })
                            .collect_vec();
                        gate.assert_equal(
                            ctx,
                            QuantumCell::Existing(&sum),
                            QuantumCell::Existing(limb),
                        );
                        assigned
                    })
                    .collect_vec();
                let public_key_hash_result = config.sha256_config.digest(
                    ctx,
                    &value_to_option(self.public_key.n.clone())
                        .unwrap()
                        .to_bytes_le(),
                )?;
                for (a, b) in public_key_hash_result.input_bytes[0..assigned_public_key_bytes.len()]
                    .into_iter()
                    .map(|v| v.cell())
                    .collect_vec()
                    .into_iter()
                    .zip(assigned_public_key_bytes.into_iter())
                {
                    ctx.region.constrain_equal(a, b.cell())?;
                }

                debug_assert_eq!(public_key_hash_result.output_bytes.len(), 32);
                let mut packed_public_hash = gate.load_zero(ctx);
                let mut coeff = F::from(1u64);
                for byte in public_key_hash_result.output_bytes[0..31].iter() {
                    packed_public_hash = gate.mul_add(
                        ctx,
                        QuantumCell::Existing(byte),
                        QuantumCell::Constant(coeff),
                        QuantumCell::Existing(&packed_public_hash),
                    );
                    coeff *= F::from(256u64);
                }
                config.sha256_config.range().finalize(ctx);
                public_input_cell.push(header_bytes_poseidon.to_assigned()[0].cell());
                public_input_cell.push(header_hash_poseidon.to_assigned()[0].cell());
                public_input_cell.push(packed_public_hash.cell());
                Ok(())
            },
        )?;
        layouter.constrain_instance(public_input_cell[0], config.public_input, 0)?;
        layouter.constrain_instance(public_input_cell[1], config.public_input, 1)?;
        layouter.constrain_instance(public_input_cell[2], config.public_input, 2)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct HeaderEmailAddrConfig<F: PrimeField> {
    sha256_config: Option<Sha256DynamicConfig<F>>,
    regex_config: RegexVerifyConfig<F>,
    range_config: RangeConfig<F>,
    public_input: Column<Instance>,
}

#[derive(Debug, Clone)]
pub struct HeaderEmailAddrCircuit<F: PrimeField> {
    pub header_bytes: Vec<u8>,
    pub randomness: F,
    pub email_addr_substr_id: usize,
}

impl<F: PrimeField> Circuit<F> for HeaderEmailAddrCircuit<F> {
    type Config = HeaderEmailAddrConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            header_bytes: vec![],
            randomness: F::zero(),
            email_addr_substr_id: 0,
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
        let header_config = params.header_config.expect("header_config is required");
        let sha256_config = match params.sha256_config {
            Some(config) => Some(Sha256DynamicConfig::configure(
                meta,
                vec![2 * header_config.max_byte_size + 64],
                range_config.clone(),
                config.num_bits_lookup,
                config.num_advice_columns,
                false,
            )),
            None => None,
        };

        let regex_defs = header_config
            .allstr_filepathes
            .iter()
            .zip(header_config.substr_filepathes.iter())
            .map(|(allstr_path, substr_pathes)| {
                let allstr = AllstrRegexDef::read_from_text(&allstr_path);
                let substrs = substr_pathes
                    .into_iter()
                    .map(|path| SubstrRegexDef::read_from_text(&path))
                    .collect_vec();
                RegexDefs { allstr, substrs }
            })
            .collect_vec();
        assert_eq!(regex_defs.len(), 1);
        let regex_config = RegexVerifyConfig::configure(
            meta,
            header_config.max_byte_size,
            range_config.gate().clone(),
            regex_defs,
        );

        let public_input = meta.instance_column();
        meta.enable_equality(public_input);
        HeaderEmailAddrConfig {
            sha256_config,
            regex_config,
            range_config,
            public_input,
        }
    }

    fn synthesize(
        &self,
        mut config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.range_config.load_lookup_table(&mut layouter)?;
        config.regex_config.load(&mut layouter)?;
        let mut first_pass = SKIP_FIRST_PASS;
        let mut public_input_cell = vec![];
        let params = read_default_circuit_config_params();
        layouter.assign_region(
            || "zkemail",
            |region| {
                if first_pass {
                    first_pass = false;
                    return Ok(());
                }
                let ctx = &mut {
                    Context::new(
                        region,
                        ContextParams {
                            max_rows: config.range_config.gate.max_rows,
                            num_context_ids: 1,
                            fixed_columns: config.range_config.gate.constants.clone(),
                        },
                    )
                };
                let range = config.range_config.clone();
                let gate = range.gate().clone();
                let regex_result = config.regex_config.match_substrs(ctx, &self.header_bytes)?;
                let mut shift_value = gate.load_zero(ctx);
                let mut is_targets = vec![];
                {
                    let mut is_target_found = gate.load_zero(ctx);
                    for (idx, assigned_substr_id) in regex_result.all_substr_ids.iter().enumerate()
                    {
                        let is_target = gate.is_equal(
                            ctx,
                            QuantumCell::Existing(assigned_substr_id),
                            QuantumCell::Constant(F::from(self.email_addr_substr_id as u64)),
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
                        is_targets.push(is_target);
                    }
                }
                let header_params = params.header_config.as_ref().unwrap();
                let shifted_chars = self.shift_variable(
                    ctx,
                    &gate,
                    header_params.max_byte_size,
                    &regex_result.masked_characters,
                    &shift_value,
                );
                let mut email_addr_words = vec![];
                {
                    let mut word_idx = 0;
                    for (idx, assigned_char) in shifted_chars[0..Self::MAX_EMAIL_ADDR_BYTES]
                        .iter()
                        .enumerate()
                    {
                        let byte_idx = idx % 31;
                        if byte_idx == 0 {
                            email_addr_words.push(gate.load_zero(ctx));
                        }
                        email_addr_words[word_idx] = gate.mul_add(
                            ctx,
                            QuantumCell::Constant(F::from(1u64 << (8 * byte_idx))),
                            QuantumCell::Existing(assigned_char),
                            QuantumCell::Existing(&email_addr_words[word_idx]),
                        );
                        if byte_idx == 30 {
                            word_idx += 1;
                        }
                    }
                }

                let regex_result_sha256 = config.sha256_config.as_mut().map(|sha256_config| {
                    let assigned_masked_chars = regex_result
                        .masked_characters
                        .iter()
                        .zip(is_targets.iter())
                        .map(|(char, is_target)| {
                            gate.select(
                                ctx,
                                QuantumCell::Constant(F::zero()),
                                QuantumCell::Existing(char),
                                QuantumCell::Existing(is_target),
                            )
                        })
                        .collect_vec();
                    let mut masked_chars_val = vec![0u8; sha256_config.max_byte_sizes[0]];
                    let mut substr_ids_val = vec![0u8; sha256_config.max_byte_sizes[0]];
                    let substr_regexes = header_params.substr_regexes.clone();
                    let (header_substrs, _) = get_email_substrs(
                        &String::from_utf8(self.header_bytes.clone()).unwrap(),
                        "",
                        substr_regexes,
                        vec![],
                    );
                    for (substr_idx, m) in header_substrs.iter().enumerate() {
                        if substr_idx + 1 == self.email_addr_substr_id {
                            continue;
                        }
                        if let Some((start, chars)) = m {
                            for (idx, char) in chars.as_bytes().iter().enumerate() {
                                masked_chars_val[start + idx] = *char;
                                substr_ids_val[start + idx] = substr_idx as u8 + 1;
                            }
                        }
                    }
                    let sha256_result = sha256_config
                        .digest(ctx, &vec![masked_chars_val, substr_ids_val].concat())
                        .expect("sha256_config failed");
                    for (a, b) in sha256_result.input_bytes[0..assigned_masked_chars.len()]
                        .into_iter()
                        .map(|v| v.cell())
                        .collect_vec()
                        .into_iter()
                        .zip(assigned_masked_chars.into_iter())
                    {
                        ctx.region
                            .constrain_equal(a, b.cell())
                            .expect("sha256_result and assigned_masked_chars are different.");
                    }
                    debug_assert_eq!(sha256_result.output_bytes.len(), 32);
                    let mut packed_public_hash = gate.load_zero(ctx);
                    let mut coeff = F::from(1u64);
                    for byte in sha256_result.output_bytes[0..31].iter() {
                        packed_public_hash = gate.mul_add(
                            ctx,
                            QuantumCell::Existing(byte),
                            QuantumCell::Constant(coeff),
                            QuantumCell::Existing(&packed_public_hash),
                        );
                        coeff *= F::from(256u64);
                    }
                    packed_public_hash
                });

                let poseidon = PoseidonChipBn254_8_58::new(ctx, &gate);
                let randomness = gate.load_witness(ctx, Value::known(self.randomness));
                let relayer_hash = poseidon.hash_elements(ctx, &gate, &[randomness.clone()])?;
                let salt = poseidon.hash_elements(
                    ctx,
                    &gate,
                    &vec![&[randomness.clone()][..], &email_addr_words[..]].concat(),
                )?;
                let header_hash = Sha256::digest(&self.header_bytes)
                    .to_vec()
                    .into_iter()
                    .map(|byte| gate.load_witness(ctx, Value::known(F::from(byte as u64))))
                    .collect_vec();
                let email_nullifier = poseidon.hash_elements(
                    ctx,
                    &gate,
                    &vec![&email_addr_words[..], &header_hash[..]].concat(),
                )?;
                let header_bytes_poseidon =
                    poseidon.hash_elements(ctx, &gate, &regex_result.all_characters)?;
                let header_hash_poseidon = poseidon.hash_elements(ctx, &gate, &header_hash)?;

                config.range_config.finalize(ctx);
                public_input_cell.push(header_bytes_poseidon.to_assigned()[0].cell());
                public_input_cell.push(header_hash_poseidon.to_assigned()[0].cell());
                public_input_cell.push(relayer_hash.to_assigned()[0].cell());
                public_input_cell.push(salt.to_assigned()[0].cell());
                public_input_cell.push(email_nullifier.to_assigned()[0].cell());
                if let Some(regex_result_sha256) = regex_result_sha256 {
                    public_input_cell.push(regex_result_sha256.cell());
                }
                Ok(())
            },
        )?;
        for idx in 0..5 {
            layouter.constrain_instance(public_input_cell[idx], config.public_input, idx)?;
        }
        if config.sha256_config.is_some() {
            layouter.constrain_instance(public_input_cell[5], config.public_input, 5)?;
        }

        Ok(())
    }
}

impl<F: PrimeField> HeaderEmailAddrCircuit<F> {
    const MAX_EMAIL_ADDR_BYTES: usize = 256;
    fn shift_variable<'v: 'a, 'a>(
        &self,
        ctx: &mut Context<'v, F>,
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
