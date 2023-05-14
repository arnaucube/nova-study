use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, Field, PrimeField, ToConstraintField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::uint8::UInt8,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, nonnative::NonNativeFieldVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    R1CSVar,
    ToBitsGadget,
    ToBytesGadget,
    ToConstraintFieldGadget,
    // groups::curves::short_weierstrass::ProjectiveVar,
};
use ark_serialize::CanonicalSerialize;
use ark_std::{One, Zero};
// use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};

// use ark_crypto_primitives::crh::poseidon::{
//     constraints::{CRHGadget, CRHParametersVar},
//     CRH,
// };
// use ark_crypto_primitives::crh::{CRHScheme, CRHSchemeGadget};
// use ark_crypto_primitives::snark::{FromFieldElementsGadget, SNARKGadget, SNARK};
use ark_crypto_primitives::sponge::poseidon::{
    constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, Absorb, CryptographicSponge,
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
                cs,
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
    ) -> Result<(), SynthesisError> {
        let r2 = r.square()?;

        phi3.cmE.enforce_equal(
            &(phi1.cmE
                + cmT.scalar_mul_le(r.to_bits_le()?.iter())?
                + phi2.cmE.scalar_mul_le(r2.to_bits_le()?.iter())?),
        )?;
        phi3.u.enforce_equal(&(phi1.u + r.clone() * phi2.u))?;
        phi3.cmW
            .enforce_equal(&(phi1.cmW + phi2.cmW.scalar_mul_le(r.to_bits_le()?.iter())?))?;

        phi3.x.enforce_equal(&(phi1.x + r * phi2.x))?;
        Ok(())
    }
}

pub trait FCircuit<F: PrimeField>: ConstraintSynthesizer<F> + Copy {
    // method that returns z_i (input), z_i1 (output)
    fn public(self) -> (F, F);
}

pub struct AugmentedFCircuit<
    C: CurveGroup,
    GC: CurveVar<C, ConstraintF<C>>,
    FC: FCircuit<ConstraintF<C>>,
> where
    <<C as CurveGroup>::BaseField as Field>::BasePrimeField: Absorb,
{
    pub _c: PhantomData<C>,
    pub _gc: PhantomData<GC>,

    // pub poseidon_native: PoseidonSponge<ConstraintF<C>>,
    pub poseidon_config: PoseidonConfig<ConstraintF<C>>,
    pub i: Option<C::BaseField>, // TODO rm Option in all params
    pub z_0: Option<C::BaseField>,
    pub z_i: Option<C::BaseField>,
    pub z_i1: Option<C::BaseField>, // z_{i+1}
    pub phi: Option<Phi<C>>, // phi_i in the paper sometimes appears as phi (φ_i) and others as 𝗎
    pub phiBig: Option<Phi<C>>, // ϕ_i
    pub phiBigOut: Option<Phi<C>>, // ϕ_{i+1}
    pub cmT: Option<C>,
    pub r: Option<C::ScalarField>, // This will not be an input and derived from a hash internally in the circuit (poseidon transcript)
    pub F: FC,                     // F circuit
    pub x: ConstraintF<C>,         // pub input (φ_{i+1}.x)
}

impl<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>, FC: FCircuit<ConstraintF<C>>>
    ConstraintSynthesizer<ConstraintF<C>> for AugmentedFCircuit<C, GC, FC>
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
        let i = FpVar::<ConstraintF<C>>::new_input(cs.clone(), || Ok(self.i.unwrap()))?;
        let z_0 = FpVar::<ConstraintF<C>>::new_input(cs.clone(), || Ok(self.z_0.unwrap()))?;
        let z_i = FpVar::<ConstraintF<C>>::new_input(cs.clone(), || Ok(self.z_i.unwrap()))?;
        let z_i1 = FpVar::<ConstraintF<C>>::new_input(cs.clone(), || Ok(self.z_i1.unwrap()))?;

        let phi = PhiVar::<C, GC>::new_witness(cs.clone(), || Ok(self.phi.unwrap()))?;
        let phiBig = PhiVar::<C, GC>::new_witness(cs.clone(), || Ok(self.phiBig.unwrap()))?;
        let phiBigOut = PhiVar::<C, GC>::new_witness(cs.clone(), || Ok(self.phiBigOut.unwrap()))?;

        let cmT = GC::new_witness(cs.clone(), || Ok(self.cmT.unwrap()))?;

        let r =
            NonNativeFieldVar::<C::ScalarField, ConstraintF<C>>::new_witness(cs.clone(), || {
                Ok(self.r.unwrap())
            })?; // r will come from transcript

        let x = FpVar::<ConstraintF<C>>::new_input(cs.clone(), || Ok(self.x))?;

        // if i=0, output (φ_{i+1}.x), phiOut.x = H(vk_nifs, 1, z_0, z_i1, phi)
        let phiOut_x_first_iter = AugmentedFCircuit::<C, GC, FC>::phi_x_hash_var(
            cs.clone(),
            self.poseidon_config.clone(),
            FpVar::<ConstraintF<C>>::one(),
            z_0.clone(),
            z_i1.clone(),
            phiBigOut.clone(),
        )?;
        // TODO WIP: x is the output when i=0

        // 1. phi.x == H(vk_nifs, i, z_0, z_i, phiBig)
        let h = AugmentedFCircuit::<C, GC, FC>::phi_x_hash_var(
            cs.clone(),
            self.poseidon_config.clone(),
            i.clone(),
            z_0.clone(),
            z_i.clone(),
            phiBig.clone(),
        )?;
        // check that h == phi.x.
        // Note: phi.x is in ScalarField, while h is in ConstraintF (BaseField), that's why bytes
        // are used in the comparison.
        (phi.x.to_bytes()?).enforce_equal(&h.to_bytes()?)?; // TODO review

        // 2. phi.cmE==cm(0), phi.u==1
        // (phi.cmE.is_zero()?).enforce_equal(&Boolean::TRUE)?; // TODO not cmE=0, but check that cmE = cm(0)
        (phi.u.is_one()?).enforce_equal(&Boolean::TRUE)?;

        // 3. nifs.verify, checks that folding phi & phiBig obtains phiBigOut
        NIFSGadget::<C, GC>::verify(r, cmT, phi, phiBig, phiBigOut.clone())?;

        // 4. zksnark.V(vk_snark, phi_new, proof_phi)
        // 5. (φ_{i+1}.x) phiOut.x == H(i+1, z_0, z_i+1, phiBigOut)
        let phiOut_x = AugmentedFCircuit::<C, GC, FC>::phi_x_hash_var(
            cs.clone(),
            self.poseidon_config.clone(),
            i + FpVar::<ConstraintF<C>>::one(),
            z_0.clone(),
            z_i1.clone(),
            phiBigOut.clone(),
        )?; // WIP

        // check that inputed 'x' is equal to phiOut_x_first_iter or phiOut_x depending if we're at
        // i=0 or not.
        // if i==0: check x==phiOut_x_first_iter
        phiOut_x_first_iter.enforce_equal(&x)?;
        // else: check x==phiOut_x

        // WIP assert that z_i1 == F(z_i).z_i1
        self.F.generate_constraints(cs.clone())?;

        Ok(())
    }
}

impl<C: CurveGroup, GC: CurveVar<C, ConstraintF<C>>, FC: FCircuit<ConstraintF<C>>>
    AugmentedFCircuit<C, GC, FC>
where
    C: CurveGroup,
    GC: CurveVar<C, ConstraintF<C>>,
    for<'a> &'a GC: GroupOpsBounds<'a, C, GC>,
    <<C as CurveGroup>::BaseField as Field>::BasePrimeField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    fn phi_x_hash_var(
        cs: ConstraintSystemRef<ConstraintF<C>>,
        poseidon_config: PoseidonConfig<ConstraintF<C>>,
        i: FpVar<ConstraintF<C>>,
        z_0: FpVar<ConstraintF<C>>,
        z_i: FpVar<ConstraintF<C>>,
        phi: PhiVar<C, GC>,
    ) -> Result<FpVar<ConstraintF<C>>, SynthesisError> {
        // note: this method can be optimized if instead of bytes representations we hash finite
        // field elements (in the constraint field)
        let mut sponge = PoseidonSpongeVar::<ConstraintF<C>>::new(cs.clone(), &poseidon_config);

        let input = vec![i, z_0, z_i];
        sponge.absorb(&input)?;

        let input: Vec<Vec<UInt8<ConstraintF<C>>>> = vec![phi.u.to_bytes()?, phi.x.to_bytes()?];
        sponge.absorb(&input)?;

        let input = vec![phi.cmE.to_bytes()?, phi.cmW.to_bytes()?];
        sponge.absorb(&input)?;

        let h = sponge.squeeze_field_elements(1).unwrap();
        Ok(h[0].clone())
    }
    fn phi_x_hash(
        poseidon_config: PoseidonConfig<ConstraintF<C>>,
        i: ConstraintF<C>,
        z_0: ConstraintF<C>,
        z_i: ConstraintF<C>,
        phi: Phi<C>,
    ) -> ConstraintF<C> {
        let mut sponge = PoseidonSponge::<ConstraintF<C>>::new(&poseidon_config);

        let input: Vec<ConstraintF<C>> = vec![i, z_0, z_i];
        sponge.absorb(&input);

        let input: Vec<Vec<u8>> = vec![
            phi.u.into_bigint().to_bytes_le(),
            phi.x.into_bigint().to_bytes_le(),
        ];
        sponge.absorb(&input);

        let cmE_bytes = Self::to_bytes_cs_compat(phi.cmE.0);
        let cmW_bytes = Self::to_bytes_cs_compat(phi.cmW.0);
        let input = vec![cmE_bytes, cmW_bytes];
        sponge.absorb(&input);

        let h = sponge.squeeze_field_elements(1);
        h[0]
    }

    fn to_bytes_cs_compat(c: C) -> Vec<u8> {
        // note: this method has been implemented to be compatible with the arkworks/r1cs-std
        // short_weierstrass/ProjectiveVar ToBytesGadget implementation, as the
        // arkworks/algebra/serialize/SWCurveConfig version is not compatible.
        let a = c.into_affine();
        let x = a.x().unwrap();
        let y = a.y().unwrap();
        let mut x_bytes = Vec::new();
        x.serialize_uncompressed(&mut x_bytes).unwrap();
        let mut y_bytes = Vec::new();
        y.serialize_uncompressed(&mut y_bytes).unwrap();

        x_bytes.append(&mut vec![0, 0]);
        y_bytes.append(&mut vec![0, 0]);
        x_bytes.append(&mut y_bytes);
        x_bytes.push(0);
        x_bytes
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

#[derive(Clone, Copy, Debug)]
pub struct TestFCircuit<F: PrimeField> {
    z_i: F,  // z_i
    z_i1: F, // z_{i+1}
}
impl<F: PrimeField> FCircuit<F> for TestFCircuit<F> {
    fn public(self) -> (F, F) {
        (self.z_i, self.z_i1)
    }
}
impl<F: PrimeField> ConstraintSynthesizer<F> for TestFCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let z_i = FpVar::<F>::new_input(cs.clone(), || Ok(self.z_i))?;
        let z_i1 = FpVar::<F>::new_input(cs.clone(), || Ok(self.z_i1))?;
        let five = FpVar::<F>::new_constant(cs.clone(), F::from(5u32))?;

        let y = &z_i * &z_i * &z_i + &z_i + &five;
        y.enforce_equal(&z_i1)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::transcript::Transcript;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use crate::nifs;
    use crate::pedersen;
    use crate::transcript::poseidon_test_config;
    use ark_ec::Group;
    // use ark_ed_on_mnt4_298::{constraints::EdwardsVar, EdwardsProjective};
    use crate::pedersen::Commitment;
    use ark_mnt4_298::{constraints::G1Var as MNT4G1Var, Fq, Fr, G1Projective as MNT4G1Projective};
    use ark_mnt6_298::{constraints::G1Var as MNT6G1Var, G1Projective as MNT6G1Projective};
    use ark_std::One;

    // mnt4's Fr is the Constraint Field,
    // while mnt4's Fq is the Field where we work, which is the C::ScalarField for C==MNT6G1

    #[test]
    fn test_phi_var() {
        let phi = Phi::<MNT6G1Projective> {
            cmE: Commitment(MNT6G1Projective::generator()),
            u: Fq::one(),
            cmW: Commitment(MNT6G1Projective::generator()),
            x: Fq::one(),
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        let _phiVar =
            PhiVar::<MNT6G1Projective, MNT6G1Var>::new_witness(cs.clone(), || Ok(phi)).unwrap();
        // println!("num_constraints={:?}", cs.num_constraints());
    }

    #[test]
    fn test_phi_x_hash() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_test_config::<Fr>();

        let z_0 = Fr::from(0_u32);
        let z_i = Fr::from(3_u32);
        let phi = Phi::<MNT6G1Projective> {
            // cmE: Commitment(MNT6G1Projective::generator()),
            cmE: Commitment(MNT6G1Projective::rand(&mut rng)),
            u: Fq::one(),
            cmW: Commitment(MNT6G1Projective::generator()),
            x: Fq::one(),
        };
        let x = AugmentedFCircuit::<MNT6G1Projective, MNT6G1Var, TestFCircuit<Fr>>::phi_x_hash(
            poseidon_config.clone(),
            Fr::one(),
            z_0.clone(),
            z_i.clone(),
            phi.clone(),
        );

        let cs = ConstraintSystem::<Fr>::new_ref();
        let z_0Var = FpVar::<Fr>::new_witness(cs.clone(), || Ok(z_0)).unwrap();
        let z_iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(z_i)).unwrap();
        let phiVar =
            PhiVar::<MNT6G1Projective, MNT6G1Var>::new_witness(cs.clone(), || Ok(phi)).unwrap();

        let xVar =
            AugmentedFCircuit::<MNT6G1Projective, MNT6G1Var, TestFCircuit<Fr>>::phi_x_hash_var(
                cs.clone(),
                poseidon_config.clone(),
                FpVar::<Fr>::one(),
                z_0Var,
                z_iVar,
                phiVar,
            )
            .unwrap();
        println!("num_constraints={:?}", cs.num_constraints());

        assert_eq!(x, xVar.value().unwrap());
    }

    #[test]
    fn test_nifs_gadget() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = pedersen::Pedersen::<MNT6G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec
        let poseidon_config = poseidon_test_config::<Fq>();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let (r1cs, ws, _) = nifs::gen_test_values::<Fq>(2);
        let (A, _, _) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let r = Fq::rand(&mut rng); // this would come from the transcript

        let fw1 = nifs::FWit::<MNT6G1Projective>::new(ws[0].clone(), A.len());
        let fw2 = nifs::FWit::<MNT6G1Projective>::new(ws[1].clone(), A.len());

        let mut transcript_p = Transcript::<Fq, MNT6G1Projective>::new(&poseidon_config);

        let (_fw3, phi1, phi2, _T, cmT) = nifs::NIFS::<MNT6G1Projective>::P(
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

        NIFSGadget::<MNT6G1Projective, MNT6G1Var>::verify(rVar, cmTVar, phi1Var, phi2Var, phi3Var)
            .unwrap();
        // println!("num_constraints={:?}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn test_augmented_f_circuit() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = pedersen::Pedersen::<MNT6G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec
        let poseidon_config_Fq = poseidon_test_config::<Fq>();
        let poseidon_config_Fr = poseidon_test_config::<Fr>();

        let cs = ConstraintSystem::<Fr>::new_ref();

        // note: gen_test_values ws is the F (internal) circuit witness only
        let (r1cs, ws, _) = nifs::gen_test_values::<Fq>(2);
        let A = r1cs.A.clone();

        let r = Fq::rand(&mut rng); // this would come from the transcript

        let fw1 = nifs::FWit::<MNT6G1Projective>::new(ws[0].clone(), A.len());
        let fw2 = nifs::FWit::<MNT6G1Projective>::new(ws[1].clone(), A.len());

        let mut transcript_p = Transcript::<Fq, MNT6G1Projective>::new(&poseidon_config_Fq);

        let (_fw3, mut phi1, phi2, _T, cmT) = nifs::NIFS::<MNT6G1Projective>::P(
            &mut transcript_p,
            &pedersen_params,
            r,
            &r1cs,
            fw1,
            fw2,
        );
        // println!("phi1 {:?}", phi1.cmE);

        let i = Fr::from(0_u32);
        let z_0 = Fr::from(0_u32);
        let z_i = Fr::from(3_u32);
        let z_i1 = Fr::from(35_u32);
        let test_F_circuit = TestFCircuit::<Fr> { z_i, z_i1 };

        // TODO maybe phi.x should be set from fw1 (few lines above)
        let phi1_x: Fr =
            AugmentedFCircuit::<MNT6G1Projective, MNT6G1Var, TestFCircuit<Fr>>::phi_x_hash(
                poseidon_config_Fr.clone(),
                i,
                z_0.clone(),
                z_i.clone(),
                phi2.clone(), // phiBig
            );
        phi1.x = Fq::from_le_bytes_mod_order(&phi1_x.into_bigint().to_bytes_le());

        // fold committed instance phi3
        let phi3 = nifs::NIFS::<MNT6G1Projective>::V(r, &phi1, &phi2, &cmT);

        let x = AugmentedFCircuit::<MNT6G1Projective, MNT6G1Var, TestFCircuit<Fr>>::phi_x_hash(
            poseidon_config_Fr.clone(),
            i + Fr::one(),
            z_0.clone(),
            z_i1.clone(),
            phi3.clone(),
        );

        let augmentedF = AugmentedFCircuit::<MNT6G1Projective, MNT6G1Var, TestFCircuit<Fr>> {
            _c: PhantomData,
            _gc: PhantomData,
            poseidon_config: poseidon_config_Fr.clone(),
            i: Some(i),
            z_0: Some(z_0),
            z_i: Some(z_i),
            z_i1: Some(z_i1),
            phi: Some(phi1),
            phiBig: Some(phi2),
            phiBigOut: Some(phi3.clone()),
            cmT: Some(cmT.0),
            r: Some(r),
            F: test_F_circuit,
            x,
        };
        augmentedF.generate_constraints(cs.clone()).unwrap();
        println!("num_constraints={:?}", cs.num_constraints());

        assert!(cs.is_satisfied().unwrap());
    }
}
