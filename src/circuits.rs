use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, Group};
use ark_ff::{fields::Fp256, BigInteger, Field, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::uint8::UInt8,
    boolean::Boolean,
    eq::EqGadget,
    fields::{
        fp::{AllocatedFp, FpVar},
        nonnative::NonNativeFieldVar,
        FieldVar,
    },
    groups::curves::short_weierstrass::ProjectiveVar,
    groups::GroupOpsBounds,
    prelude::CurveVar,
    ToBitsGadget, ToBytesGadget, ToConstraintFieldGadget,
};
// use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::ops::{Add, Mul, Sub};

use ark_crypto_primitives::crh::poseidon::{
    constraints::{CRHGadget, CRHParametersVar},
    CRH,
};
use ark_crypto_primitives::crh::{CRHScheme, CRHSchemeGadget};
use ark_crypto_primitives::snark::{FromFieldElementsGadget, SNARKGadget, SNARK};
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
use ark_crypto_primitives::sponge::poseidon::{
    constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge,
};

use core::{borrow::Borrow, marker::PhantomData};
use derivative::Derivative;

use crate::nifs::Phi;

pub type ConstraintF<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

#[derive(Debug, Derivative)]
#[derivative(Clone(bound = "C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>"))]
pub struct PhiVar<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>>
where
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    _c: PhantomData<C>,
    cmE: GC,
    u: NonNativeFieldVar<C::ScalarField, ConstraintF<C>>,
    cmW: GC,
    x: NonNativeFieldVar<C::ScalarField, ConstraintF<C>>,
}

impl<C, GC> AllocVar<Phi<C>, ConstraintF<C>> for PhiVar<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    fn new_variable<T: Borrow<Phi<C>>>(
        cs: impl Into<Namespace<ConstraintF<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();

            let u = NonNativeFieldVar::<C::ScalarField, ConstraintF<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().u),
                mode,
            )?;
            let cmE = GC::new_variable(cs.clone(), || Ok(val.borrow().cmE.0), mode)?;
            let cmW = GC::new_variable(cs.clone(), || Ok(val.borrow().cmW.0), mode)?;

            let x = NonNativeFieldVar::<C::ScalarField, ConstraintF<C>>::new_variable(
                cs.clone(),
                || Ok(val.borrow().x),
                mode,
            )?;

            Ok(Self {
                _c: PhantomData,
                cmE,
                u,
                cmW,
                x,
            })
        })
    }
}

pub struct NIFSGadget<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>> {
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,
}

impl<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>> NIFSGadget<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
{
    // implements the constraints for NIFS.V
    pub fn verify(
        r: NonNativeFieldVar<C::ScalarField, ConstraintF<C>>,
        cmT: GC,
        phi1: PhiVar<C, GC>,
        phi2: PhiVar<C, GC>,
        phi3: PhiVar<C, GC>,
    ) -> Result<Boolean<ConstraintF<C>>, SynthesisError> {
        let r2 = r.square()?;

        phi3.cmE.is_eq(
            &(phi1.cmE
                + cmT.scalar_mul_le(r.to_bits_le()?.iter())?
                + phi2.cmE.scalar_mul_le(r2.to_bits_le()?.iter())?),
        )?;
        phi3.u.is_eq(&(phi1.u + r.clone() * phi2.u))?;
        phi3.cmW
            .is_eq(&(phi1.cmW + phi2.cmW.scalar_mul_le(r.to_bits_le()?.iter())?))?;

        // wip x's check
        phi3.x.is_eq(&(phi1.x + r.clone() * phi2.x))
    }
}

use ark_crypto_primitives::sponge::Absorb;
pub struct AugmentedFCircuit<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>>
where
    <<C as CurveGroup>::BaseField as Field>::BasePrimeField: Absorb,
{
    _c: PhantomData<C>,
    _gc: PhantomData<GC>,

    pub poseidon_native: PoseidonSponge<ConstraintF<C>>,
    pub poseidon_config: PoseidonConfig<ConstraintF<C>>,
    pub i: Option<C::BaseField>,
    pub z_0: Option<C::BaseField>,
    pub z_i: Option<C::BaseField>,
    pub phi: Option<Phi<C>>, // phi in the paper sometimes appears as phi (φ) and others as 𝗎
    pub phiBig: Option<Phi<C>>,
    pub phiOut: Option<Phi<C>>,
    pub cmT: Option<C>,
    pub r: Option<C::ScalarField>, // This will not be an input and derived from a hash internally in the circuit (poseidon transcript)
}

impl<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>> ConstraintSynthesizer<ConstraintF<C>>
    for AugmentedFCircuit<C, GC>
where
    C: CurveGroup,
    GC: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
    <C as CurveGroup>::BaseField: PrimeField,
    <<C as CurveGroup>::BaseField as Field>::BasePrimeField: Absorb,
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF<C>>,
    ) -> Result<(), SynthesisError> {
        let i = FpVar::<ConstraintF<C>>::new_witness(cs.clone(), || Ok(self.i.unwrap()))?;
        let z_0 = FpVar::<ConstraintF<C>>::new_witness(cs.clone(), || Ok(self.z_0.unwrap()))?;
        let z_i = FpVar::<ConstraintF<C>>::new_witness(cs.clone(), || Ok(self.z_i.unwrap()))?;

        let phi = PhiVar::<C, GC>::new_witness(cs.clone(), || Ok(self.phi.unwrap()))?;
        let phiBig = PhiVar::<C, GC>::new_witness(cs.clone(), || Ok(self.phiBig.unwrap()))?;
        let phiOut = PhiVar::<C, GC>::new_witness(cs.clone(), || Ok(self.phiOut.unwrap()))?;

        let cmT = GC::new_witness(cs.clone(), || Ok(self.cmT.unwrap()))?;
        let r =
            NonNativeFieldVar::<C::ScalarField, ConstraintF<C>>::new_witness(cs.clone(), || {
                Ok(self.r.unwrap())
            })?; // r will come from transcript

        // 1. phi.x == H(vk_nifs, i, z_0, z_i, phiBig)
        let mut sponge =
            PoseidonSpongeVar::<ConstraintF<C>>::new(cs.clone(), &self.poseidon_config);
        let input = vec![i, z_0, z_i];
        sponge.absorb(&input)?;
        let input = vec![
            phiBig.u.to_constraint_field()?,
            phiBig.x.to_constraint_field()?,
        ];
        sponge.absorb(&input)?;
        let input = vec![phiBig.cmE.to_bytes()?, phiBig.cmW.to_bytes()?];
        sponge.absorb(&input)?;
        let h = sponge.squeeze_field_elements(1).unwrap();
        let x_CF = phi.x.to_constraint_field()?; // phi.x on the ConstraintF<C>
        x_CF[0].is_eq(&h[0])?; // review

        // // 2. phi.cmE==0, phi.u==1
        // <GC as CurveVar<C, ConstraintF<C>>>::is_zero(&phi.cmE)?;
        phi.cmE.is_zero()?;
        phi.u.is_one()?;

        // 3. nifs.verify
        NIFSGadget::<C, GC>::verify(r, cmT, phi, phiBig, phiOut)?;

        // 4. zksnark.V(vk_snark, phi_new, proof_phi)

        Ok(())
    }
}

//////////

// pub struct Nova<MainField: PrimeField, SecondField: PrimeField, C1: CurveGroup, C2: CurveGroup> {}
// pub trait SNARKs<MainField: PrimeField, SecondField: PrimeField> {
//     type AugmentedFunctionSNARK: SNARK<MainField>;
//     // type FunctionSNARK: ConstraintSynthesizer<Fr>; // F
//     type DummyStepSNARK: SNARK<SecondField>;
//
//     type AugmentedFunctionCircuit: SNARKGadget<MainField, SecondField, Self::AugmentedFunctionSNARK>; // F'
//     type FunctionCircuit: ConstraintSynthesizer<MainField>; // F
//     type DummyStepCircuit: SNARKGadget<SecondField, MainField, Self::DummyStepSNARK>;
// }
// pub struct TS<
//     MainField: PrimeField,
//     SecondField: PrimeField,
//     Config: SNARKs<MainField, SecondField>,
// > {
//     augmentedF_pk: <Config::AugmentedFunctionSNARK as SNARK<MainField>>::ProvingKey,
//     augmentedF_vk: <Config::AugmentedFunctionSNARK as SNARK<MainField>>::VerifyingKey,
//
//     dummy_pk: <Config::DummyStepSNARK as SNARK<SecondField>>::ProvingKey,
//     dummy_vk: <Config::DummyStepSNARK as SNARK<SecondField>>::VerifyingKey,
// }

#[cfg(test)]
mod test {
    use super::*;

    use crate::transcript::Transcript;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{
        rand::{Rng, RngCore},
        UniformRand,
    };

    use crate::nifs;
    use crate::pedersen;
    use ark_ec::CurveGroup;
    // use ark_ed_on_mnt4_298::{constraints::EdwardsVar, EdwardsProjective};
    use crate::pedersen::Commitment;
    use ark_mnt4_298::{constraints::G1Var as MNT4G1Var, Fq, Fr, G1Projective as MNT4G1Projective};
    use ark_mnt6_298::{constraints::G1Var as MNT6G1Var, G1Projective as MNT6G1Projective};
    use ark_std::{One, Zero};

    // mnt4's Fr is the Constraint Field,
    // while mnt4's Fq is the Field where we work, which is the C::ScalarField for C==MNT6G1

    #[test]
    fn test_phi_var() {
        let mut rng = ark_std::test_rng();

        let phi = Phi::<MNT6G1Projective> {
            cmE: Commitment(MNT6G1Projective::generator()),
            u: Fq::one(),
            cmW: Commitment(MNT6G1Projective::generator()),
            x: Fq::one(),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        let phiVar =
            PhiVar::<MNT6G1Projective, MNT6G1Var>::new_witness(cs.clone(), || Ok(phi)).unwrap();
        // println!("num_constraints={:?}", cs.num_constraints());
    }

    #[test]
    fn test_nifs_gadget() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = pedersen::Pedersen::<MNT6G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec

        let cs = ConstraintSystem::<Fr>::new_ref();

        let (r1cs, w1, w2, _, x1, x2, _) = nifs::gen_test_values::<_, Fq>(&mut rng);
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let r = Fq::rand(&mut rng); // this would come from the transcript

        let fw1 = nifs::FWit::<MNT6G1Projective>::new(w1.clone(), A.len());
        let fw2 = nifs::FWit::<MNT6G1Projective>::new(w2.clone(), A.len());
        let mut transcript_p = Transcript::<Fq>::new();
        let (fw3, phi1, phi2, T, cmT) = nifs::NIFS::<MNT6G1Projective>::P(
            &mut transcript_p,
            &pedersen_params,
            r,
            &r1cs,
            fw1,
            fw2,
        );
        let phi3 = nifs::NIFS::<MNT6G1Projective>::V(r, &phi1, &phi2, &cmT);

        let phi1Var =
            PhiVar::<MNT6G1Projective, MNT6G1Var>::new_witness(cs.clone(), || Ok(phi1)).unwrap();
        let phi2Var =
            PhiVar::<MNT6G1Projective, MNT6G1Var>::new_witness(cs.clone(), || Ok(phi2)).unwrap();
        let phi3Var =
            PhiVar::<MNT6G1Projective, MNT6G1Var>::new_witness(cs.clone(), || Ok(phi3)).unwrap();

        let cmTVar = MNT6G1Var::new_witness(cs.clone(), || Ok(cmT.0)).unwrap();
        let rVar = NonNativeFieldVar::<Fq, Fr>::new_witness(cs.clone(), || Ok(r)).unwrap();

        let valid = NIFSGadget::<MNT6G1Projective, MNT6G1Var>::verify(
            rVar, cmTVar, phi1Var, phi2Var, phi3Var,
        );
        println!("num_constraints={:?}", cs.num_constraints());
    }
}
