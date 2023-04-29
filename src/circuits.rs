use ark_crypto_primitives::snark::{FromFieldElementsGadget, SNARKGadget, SNARK};
use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, Group};
use ark_ff::{fields::Fp256, Field, PrimeField};
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
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::ops::Mul;

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

////

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
