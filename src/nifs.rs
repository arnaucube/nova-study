use ark_ec::AffineRepr;
use ark_std::ops::Add;
use ark_std::One;
use std::marker::PhantomData;

use crate::pedersen::{Commitment, CommitmentVec, Params as PedersenParams, Pedersen};
use crate::r1cs::*;
use crate::transcript::Transcript;
use crate::utils::*;
use ark_std::{
    rand::{Rng, RngCore},
    UniformRand,
};

// Phi: φ in the paper (later 𝖴), a folded instance
pub struct Phi<C: AffineRepr> {
    // cmE: CommitmentVec<C>, // TODO not Commitment but directly C (without rE)
    cmE: C,
    u: C::ScalarField,
    // cmW: CommitmentVec<C>, // TODO not Commitment but directly C (without rW)
    cmW: C,
    x: Vec<C::ScalarField>,
}

// FWit: Folded Witness
pub struct FWit<C: AffineRepr> {
    E: Vec<C::ScalarField>,
    rE: C::ScalarField,
    W: Vec<C::ScalarField>,
    rW: C::ScalarField,
}

impl<C: AffineRepr> FWit<C> {
    pub fn commit<R: Rng>(
        &self,
        rng: &mut R,
        params: &PedersenParams<C>,
        x: Vec<C::ScalarField>,
    ) -> Phi<C> {
        // TODO instead of rand r, use self.rE and self.rW for the commit_vec
        let cmE = Pedersen::commit_vec(rng, &params, &self.E);
        let cmW = Pedersen::commit_vec(rng, &params, &self.W);
        Phi {
            cmE: cmE.cm,
            u: C::ScalarField::one(),
            cmW: cmW.cm,
            x,
        }
    }
}

pub struct NIFS<C: AffineRepr> {
    _phantom: PhantomData<C>,
}

impl<C: AffineRepr> NIFS<C> {
    pub fn comp_T(
        cs1: RelaxedR1CS<C::ScalarField>,
        cs2: RelaxedR1CS<C::ScalarField>,
        z1: &Vec<C::ScalarField>,
        z2: &Vec<C::ScalarField>,
    ) -> Vec<C::ScalarField> {
        // assuming cs1.R1CS == cs2.R1CS
        let (A, B, C) = (cs1.ABC.A, cs1.ABC.B, cs1.ABC.C);

        // this is parallelizable (for the future)
        let Az1 = matrix_vector_product(&A, &z1);
        let Bz1 = matrix_vector_product(&B, &z1);
        let Cz1 = matrix_vector_product(&C, &z1);
        let Az2 = matrix_vector_product(&A, &z2);
        let Bz2 = matrix_vector_product(&B, &z2);
        let Cz2 = matrix_vector_product(&C, &z2);

        let Az1_Bz2 = hadamard_product(Az1, Bz2);
        let Az2_Bz1 = hadamard_product(Az2, Bz1);
        let u1Cz2 = vector_elem_product(&Cz2, &cs1.u);
        let u2Cz1 = vector_elem_product(&Cz1, &cs2.u);

        // let T = vec_sub(vec_sub(vec_add(Az1_Bz2, Az2_Bz1), u1Cz2), u2Cz1);
        let T = ((Ve(Az1_Bz2) + Ve(Az2_Bz1)) - Ve(u1Cz2)) - Ve(u2Cz1);
        T.0
    }

    pub fn fold_witness(
        r: C::ScalarField,
        fw1: &FWit<C>,
        fw2: &FWit<C>,
        T: Vec<C::ScalarField>,
    ) -> FWit<C> {
        let r2 = r * r;
        let E: Vec<C::ScalarField> = vec_add(
            // this syntax will be simplified with future operators impl (or at least a method
            // for r-lin)
            vec_add(fw1.E.clone(), vector_elem_product(&T, &r)),
            // rlin(fw1.E.clone(), T, r),
            vector_elem_product(&fw2.E, &r2),
        );
        let rE = fw1.rE + r2 * fw2.rE; // TODO rT
        let W = vec_add(fw1.W.clone(), vector_elem_product(&fw2.W, &r));
        // let W = rlin(fw1.W.clone(), fw2.W.clone(), r);
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
        cmT: CommitmentVec<C>,
    ) -> Phi<C> {
        let r2 = r * r;

        let cmE = phi1.cmE + cmT.cm.mul(r) + phi2.cmE.mul(r2);
        let u = phi1.u + r * phi2.u;
        let cmW = phi1.cmW + phi2.cmW.mul(r);
        let x = vec_add(phi1.x, vector_elem_product(&phi2.x, &r));
        // let x = rlin(phi1.x, phi2.x, r);

        Phi::<C> {
            // cmE: Commitment::<C> {
            //     cm: cmE.into(),
            //     r: phi1.cmE.r,
            // },
            cmE: cmE.into(),
            u,
            // cmW: Commitment::<C> {
            //     cm: cmW.into(),
            //     r: phi1.cmW.r,
            // },
            cmW: cmW.into(),
            x,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pedersen::Pedersen;
    use ark_bn254::{g1::G1Affine, Fr};
    use ark_ec::CurveGroup;
    use ark_std::{
        rand::{Rng, RngCore},
        UniformRand,
    };
    use ark_std::{One, Zero};
    use std::ops::Mul;

    #[test]
    fn test_simple_folding() {
        let mut rng = ark_std::test_rng();

        // R1CS for: x^3 + x + 5 = y (example from article
        // https://www.vitalik.ca/general/2016/12/10/qap.html )
        let A = to_F_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let B = to_F_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
        ]);
        let C = to_F_matrix::<Fr>(vec![
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![0, 0, 1, 0, 0, 0],
        ]);
        let z1 = to_F_vec::<Fr>(vec![1, 3, 35, 9, 27, 30]);
        let x1 = to_F_vec::<Fr>(vec![35]);
        let z2 = to_F_vec::<Fr>(vec![1, 4, 73, 16, 64, 68]);
        let x2 = to_F_vec::<Fr>(vec![73]);

        let relaxed_r1cs_1 = R1CS::<Fr> {
            A: A.clone(),
            B: B.clone(),
            C: C.clone(),
        }
        .relax();
        let relaxed_r1cs_2 = R1CS::<Fr> {
            A: A.clone(),
            B: B.clone(),
            C: C.clone(),
        }
        .relax();

        let T = NIFS::<G1Affine>::comp_T(relaxed_r1cs_1, relaxed_r1cs_2, &z1, &z2);
        let params = Pedersen::<G1Affine>::new_params(&mut rng);
        let cmT = Pedersen::commit_vec(&mut rng, &params, &T);

        let r = Fr::rand(&mut rng); // this would come from the transcript

        // WIP TMP
        let fw1 = FWit::<G1Affine> {
            E: vec![Fr::zero(); T.len()],
            rE: Fr::zero(),
            W: z1,
            rW: Fr::zero(),
        };
        let fw2 = FWit::<G1Affine> {
            E: vec![Fr::zero(); T.len()],
            rE: Fr::zero(),
            W: z2,
            rW: Fr::zero(),
        };

        // fold witness
        let folded_witness = NIFS::<G1Affine>::fold_witness(r, &fw1, &fw2, T);

        let pedersen_params = Pedersen::<G1Affine>::new_params(&mut rng);
        let phi1 = fw1.commit(&mut rng, &pedersen_params, x1); // wip
        let phi2 = fw2.commit(&mut rng, &pedersen_params, x2);
        // fold instance
        let folded_instance = NIFS::<G1Affine>::fold_instance(r, phi1, phi2, cmT);

        // naive check that the folded witness satisfies the relaxed r1cs
        let Az = matrix_vector_product(&A, &folded_witness.W);
        let Bz = matrix_vector_product(&B, &folded_witness.W);
        let Cz = matrix_vector_product(&C, &folded_witness.W);
        assert_eq!(
            hadamard_product(Az, Bz),
            vec_add(
                vector_elem_product(&Cz, &folded_instance.u),
                folded_witness.E
            )
        );
    }
}
