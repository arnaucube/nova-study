use ark_ec::AffineRepr;
use ark_std::ops::Add;
use std::marker::PhantomData;

use crate::pedersen::Commitment;
use crate::r1cs::*;
use crate::transcript::Transcript;
use crate::utils::*;

// Phi: φ in the paper (later 𝖴), a folded instance
pub struct Phi<C: AffineRepr> {
    cmE: Commitment<C>,
    u: C::ScalarField,
    cmW: Commitment<C>,
    x: Vec<C::ScalarField>,
}

// FWit: Folded Witness
pub struct FWit<C: AffineRepr> {
    E: Vec<C::ScalarField>,
    rE: C::ScalarField,
    W: Vec<C::ScalarField>,
    rW: C::ScalarField,
}

pub struct NIFS<C: AffineRepr> {
    _phantom: PhantomData<C>,
}

impl<C: AffineRepr> NIFS<C> {
    pub fn fold_witness(
        r: C::ScalarField,
        fw1: FWit<C>,
        fw2: FWit<C>,
        T: Vec<C::ScalarField>,
    ) -> FWit<C> {
        let r2 = r * r;
        let E: Vec<C::ScalarField> = vec_add(
            // TODO this syntax will be simplified with future operators impl
            vec_add(fw1.E, vector_elem_product(&T, &r)),
            vector_elem_product(&fw2.E, &r2),
        );
        let rE = fw1.rE + r * fw2.rE;
        let W = vec_add(fw1.W, vector_elem_product(&fw2.W, &r));
        let rW = fw1.rW + r * fw2.rW;
        FWit::<C> {
            E: E.into(),
            rE,
            W: W.into(),
            rW,
        }
    }

    pub fn fold_instance(
        r: C::ScalarField,
        phi1: Phi<C>,
        phi2: Phi<C>,
        cmT: Commitment<C>,
    ) -> Phi<C> {
        let r2 = r * r;

        let cmE = phi1.cmE.cm + cmT.cm.mul(r) + phi2.cmE.cm.mul(r2);
        let u = phi1.u + r * phi2.u;
        let cmW = phi1.cmW.cm + phi2.cmW.cm.mul(r);
        let x = vec_add(phi1.x, vector_elem_product(&phi2.x, &r));

        Phi::<C> {
            cmE: Commitment::<C> {
                cm: cmE.into(),
                r: phi1.cmE.r,
            },
            u,
            cmW: Commitment::<C> {
                cm: cmW.into(),
                r: phi1.cmW.r,
            },
            x,
        }
    }
}
