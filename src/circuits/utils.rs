use crate::circuits::poseidon_chip::{
    poseidon_hash_bytes, HasherChip, HasherChipDigest, PoseidonChipBn254_8_58,
};
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
use std::marker::PhantomData;

pub(crate) fn slice_first_7bytes_from_u64<'a, F: PrimeField>(
    ctx: &mut Context<F>,
    range: &RangeConfig<F>,
    limb: &AssignedValue<F>,
) -> AssignedValue<'a, F> {
    let gate = range.gate();
    let frist7 = limb
        .value()
        .map(|v| F::from((v.get_lower_128() & ((1u128 << 56) - 1)) as u64));
    let last1 = limb
        .value()
        .map(|v| F::from((v.get_lower_128() >> 56) as u64));
    let assigned_first7 = gate.load_witness(ctx, frist7);
    let assigned_last1 = gate.load_witness(ctx, last1);
    let composed = gate.mul_add(
        ctx,
        QuantumCell::Existing(&assigned_last1),
        QuantumCell::Constant(F::from(1u64 << (8 * 7))),
        QuantumCell::Existing(&assigned_first7),
    );
    gate.assert_equal(
        ctx,
        QuantumCell::Existing(limb),
        QuantumCell::Existing(&composed),
    );
    assigned_first7
}

pub(crate) fn slice_last_7bytes_from_u64<'a, F: PrimeField>(
    ctx: &mut Context<F>,
    range: &RangeConfig<F>,
    limb: &AssignedValue<F>,
) -> AssignedValue<'a, F> {
    let gate = range.gate();
    let frist1 = limb
        .value()
        .map(|v| F::from((v.get_lower_128() & 255) as u64));
    let last7 = limb
        .value()
        .map(|v| F::from((v.get_lower_128() >> 8) as u64));
    let assigned_first1 = gate.load_witness(ctx, frist1);
    let assigned_last7 = gate.load_witness(ctx, last7);
    let composed = gate.mul_add(
        ctx,
        QuantumCell::Existing(&assigned_last7),
        QuantumCell::Constant(F::from(256)),
        QuantumCell::Existing(&assigned_first1),
    );
    gate.assert_equal(
        ctx,
        QuantumCell::Existing(limb),
        QuantumCell::Existing(&composed),
    );
    assigned_last7
}

pub(crate) fn assigned_u64s_to_31bytes_field<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    limbs: &[AssignedValue<'b, F>],
) -> AssignedValue<'a, F> {
    debug_assert_eq!(limbs.len(), 4);
    let gate = range.gate();
    let mut sum = gate.load_zero(ctx);
    let mut base = F::one();
    for (i, limb) in limbs.iter().enumerate() {
        sum = gate.mul_add(
            ctx,
            QuantumCell::Existing(&limb),
            QuantumCell::Constant(base),
            QuantumCell::Existing(&sum),
        );
        base *= F::from_u128(1u128 << 64);
    }
    sum
}

pub(crate) fn assigned_bytes_to_31bytes_field<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    bytes: &[AssignedValue<'b, F>],
) -> AssignedValue<'a, F> {
    debug_assert_eq!(bytes.len(), 31);
    let gate = range.gate();
    let mut sum = gate.load_zero(ctx);
    let mut base = F::one();
    for (i, byte) in bytes.iter().enumerate() {
        sum = gate.mul_add(
            ctx,
            QuantumCell::Existing(&byte),
            QuantumCell::Constant(base),
            QuantumCell::Existing(&sum),
        );
        base *= F::from(256);
    }
    sum
}
