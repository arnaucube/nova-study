use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{CurveGroup, Group};
use ark_ff::{Field, PrimeField};
use std::marker::PhantomData;

use ark_crypto_primitives::sponge::poseidon::{PoseidonConfig, PoseidonSponge};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

use crate::circuits::{AugmentedFCircuit, ConstraintF};
use crate::nifs::{FWit, Phi, NIFS, R1CS};
use crate::pedersen::{Commitment, Params as PedersenParams, Pedersen, Proof as PedersenProof};
use crate::transcript::Transcript;

use ark_std::{One, Zero};
use core::ops::Deref;

pub struct IVCProof<C1: CurveGroup, C2: CurveGroup> {
    phi: Phi<C1>,
    // w: FWit<C1>,
    w: Vec<C1::ScalarField>,
    phiBig: Phi<C2>,
    // W: FWit<C2>,
    W: Vec<C2::ScalarField>,
}

pub struct IVC<
    C1: CurveGroup,
    GC1: CurveVar<C1, ConstraintF<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, ConstraintF<C2>>,
> where
    C1: CurveGroup<BaseField = <C2 as Group>::ScalarField>,
    C2: CurveGroup<BaseField = <C1 as Group>::ScalarField>,
{
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,

    pub poseidon_config: PoseidonConfig<ConstraintF<C2>>,
    pub pedersen_params_C1: PedersenParams<C1>,
    pub pedersen_params_C2: PedersenParams<C2>,
}

impl<
        C1: CurveGroup,
        GC1: CurveVar<C1, ConstraintF<C1>>,
        C2: CurveGroup,
        GC2: CurveVar<C2, ConstraintF<C2>>,
    > IVC<C1, GC1, C2, GC2>
where
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
    C1: CurveGroup<BaseField = <C2 as Group>::ScalarField>,
    C2: CurveGroup<BaseField = <C1 as Group>::ScalarField>,

    <C1 as Group>::ScalarField: Absorb,
    <C1 as CurveGroup>::BaseField: Absorb,
    <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField: Absorb,
    <C1 as CurveGroup>::BaseField: PrimeField,
    // 2
    <C2 as Group>::ScalarField: Absorb,
    <C2 as CurveGroup>::BaseField: Absorb,
    <<C2 as CurveGroup>::BaseField as Field>::BasePrimeField: Absorb,
    <C2 as CurveGroup>::BaseField: PrimeField,
{
    pub fn prove(
        &self,
        cs: ConstraintSystemRef<ConstraintF<C2>>,
        tr1: &mut Transcript<C1::ScalarField, C1>,
        tr2: &mut Transcript<C2::ScalarField, C2>,
        r1cs: &R1CS<C2::ScalarField>,
        i: C1::ScalarField,
        z_0: C1::ScalarField,
        z_i: C1::ScalarField,
        // phi1: &Phi<C>,
        // phi2: &Phi<C>,
        fw1: FWit<C2>,
        fw2: FWit<C2>,
    ) -> Result<IVCProof<C1, C2>, SynthesisError> {
        tr1.get_challenge();
        let r = tr2.get_challenge(); // TODO transcript usage is still WIP, will update with expected adds & gets

        // fold phi_i and phiBig_i
        let (fw3, phi1, phi2, _T, cmT) =
            NIFS::<C2>::P(tr2, &self.pedersen_params_C2, r, r1cs, fw1, fw2);
        let phi3 = NIFS::<C2>::V(r, &phi1, &phi2, &cmT);

        // TODO compute z_{i+1}
        let z_i1 = z_i.clone(); // WIP this will be the actual computed z_{i+1}

        let c = AugmentedFCircuit::<C2, GC2> {
            _c: PhantomData,
            _gc: PhantomData,
            poseidon_config: self.poseidon_config.clone(),
            i: Some(i),
            z_0: Some(z_0),
            z_i: Some(z_i),
            z_i1: Some(z_i1),
            phi: Some(phi1),
            phiBig: Some(phi2),
            phiOut: Some(phi3.clone()),
            cmT: Some(cmT.0),
            r: Some(r),
        };

        c.generate_constraints(cs.clone())?;

        // get w_{i+1}
        let cs1 = cs.borrow().unwrap();
        let cs2 = cs1.deref();
        let w_i1 = cs2.witness_assignment.clone();
        let x_i1 = cs2.instance_assignment.clone();

        let rW = tr1.get_challenge();
        let _ = tr2.get_challenge();

        // phi_{i+1} small
        let phi = Phi::<C1> {
            cmE: Commitment::<C1>(C1::zero()),
            u: C1::ScalarField::one(),
            cmW: Pedersen::commit(&self.pedersen_params_C1, &w_i1, &rW),
            x: x_i1[0], // check if pos 0 is 1
        };

        Ok(IVCProof {
            phiBig: phi3,
            W: fw3.W,
            phi,     // phi_{i+1}
            w: w_i1, // w_{i+1}
        })
    }
}
