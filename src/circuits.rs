use ark_crypto_primitives::snark::{FromFieldElementsGadget, SNARKGadget, SNARK};
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ff::{fields::Fp256, Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::uint8::UInt8,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::ops::Mul;

use core::{borrow::Borrow, marker::PhantomData};
use derivative::Derivative;

// pub trait Nova<F: PrimeField> {}

pub trait Config<Fq: PrimeField, Fr: PrimeField> {
    type AugmentedFunctionCircuit: SNARK<Fq>; // F'
    type FunctionCircuit: ConstraintSynthesizer<Fq>; // F
    type DummyStepCircuit: SNARK<Fr>;
}

pub struct AugmentedFCircuit<
    Fq: PrimeField,
    Fr: PrimeField,
    C: CurveGroup,
    GC: CurveVar<C, Fq>,
    Cfg: Config<Fq, Fr>,
> {
    pub dummystep_vk: Option<<Cfg::DummyStepCircuit as SNARK<Fr>>::VerifyingKey>,
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<Fq: PrimeField, Fr: PrimeField, C: CurveGroup, GC: CurveVar<C, Fq>, Cfg: Config<Fq, Fr>>
    ConstraintSynthesizer<Fq> for AugmentedFCircuit<Fq, Fr, C, GC, Cfg>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        unimplemented!();
    }
}

pub struct NIFSGadget<F: PrimeField, C: CurveGroup, GC: CurveVar<C, F>> {
    _f: PhantomData<F>,
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<F: PrimeField, C: CurveGroup, GC: CurveVar<C, F>> NIFSGadget<F, C, GC> {
    // implements the constraints for NIFS.V
    pub fn verify(
        r: FpVar<F>,
        cmT: GC,
        // phi1, phi2 and phi3
        cmE1: GC,
        cmE2: GC,
        cmE3: GC,
        u1: FpVar<F>,
        u2: FpVar<F>,
        u3: FpVar<F>,
        cmW1: GC,
        cmW2: GC,
        cmW3: GC,
        // x's size will depend on the num_publicinputs of F circuit
        x1: Vec<FpVar<F>>,
        x2: Vec<FpVar<F>>,
        x3: Vec<FpVar<F>>,
    ) -> Result<Boolean<F>, SynthesisError> {
        let r2 = r.square()?;
        cmE3.is_eq(
            &(cmE1
                + cmT.scalar_mul_le(r.to_bits_le()?.iter())?
                + cmE2.scalar_mul_le(r2.to_bits_le()?.iter())?),
        )?;
        u3.is_eq(&(u1 + r.clone() * u2))?;
        cmW3.is_eq(&(cmW1 + cmW2.scalar_mul_le(r.to_bits_le()?.iter())?))

        // TODO x's check
    }
}
