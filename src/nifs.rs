use ark_ec::AffineRepr;
use ark_ff::fields::PrimeField;
use ark_std::{
    rand::{Rng, RngCore},
    UniformRand,
};
use ark_std::{One, Zero};
use std::marker::PhantomData;

use crate::pedersen::{Commitment, Params as PedersenParams, Pedersen, Proof as PedersenProof};
use crate::transcript::Transcript;
use crate::utils::*;

pub struct R1CS<F: PrimeField> {
    pub A: Vec<Vec<F>>,
    pub B: Vec<Vec<F>>,
    pub C: Vec<Vec<F>>,
}

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

impl<C: AffineRepr> FWit<C> {
    pub fn new(z: Vec<C::ScalarField>, e_len: usize) -> Self {
        FWit::<C> {
            E: vec![C::ScalarField::zero(); e_len],
            rE: C::ScalarField::one(),
            W: z,
            rW: C::ScalarField::one(),
        }
    }
    pub fn commit(&self, params: &PedersenParams<C>) -> Phi<C> {
        let cmE = Pedersen::commit(&params, &self.E, &self.rE);
        let cmW = Pedersen::commit(&params, &self.W, &self.rW);
        Phi {
            cmE,
            u: C::ScalarField::one(),
            cmW,
            x: self.W.clone(),
        }
    }
}

pub struct NIFS<C: AffineRepr> {
    _phantom: PhantomData<C>,
}

impl<C: AffineRepr> NIFS<C> {
    // comp_T: compute cross-terms T
    pub fn comp_T(
        r1cs: &R1CS<C::ScalarField>,
        u1: C::ScalarField,
        u2: C::ScalarField,
        z1: &Vec<C::ScalarField>,
        z2: &Vec<C::ScalarField>,
    ) -> Vec<C::ScalarField> {
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        // this is parallelizable (for the future)
        let Az1 = matrix_vector_product(&A, &z1);
        let Bz1 = matrix_vector_product(&B, &z1);
        let Cz1 = matrix_vector_product(&C, &z1);
        let Az2 = matrix_vector_product(&A, &z2);
        let Bz2 = matrix_vector_product(&B, &z2);
        let Cz2 = matrix_vector_product(&C, &z2);

        let Az1_Bz2 = hadamard_product(Az1, Bz2);
        let Az2_Bz1 = hadamard_product(Az2, Bz1);
        let u1Cz2 = vector_elem_product(&Cz2, &u1);
        let u2Cz1 = vector_elem_product(&Cz1, &u2);

        // let T = vec_sub(vec_sub(vec_add(Az1_Bz2, Az2_Bz1), u1Cz2), u2Cz1);
        let T = ((Ve(Az1_Bz2) + Ve(Az2_Bz1)) - Ve(u1Cz2)) - Ve(u2Cz1);
        T.0
    }

    pub fn fold_witness(
        r: C::ScalarField,
        fw1: &FWit<C>,
        fw2: &FWit<C>,
        T: &Vec<C::ScalarField>,
        rT: C::ScalarField,
    ) -> FWit<C> {
        let r2 = r * r;
        let E: Vec<C::ScalarField> = vec_add(
            // this syntax will be simplified with future operators impl (or at least a method
            // for r-lin)
            &vec_add(&fw1.E, &vector_elem_product(&T, &r)),
            &vector_elem_product(&fw2.E, &r2),
        );
        let rE = fw1.rE + r * rT + r2 * fw2.rE;
        let W = vec_add(&fw1.W, &vector_elem_product(&fw2.W, &r));
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
        phi1: &Phi<C>,
        phi2: &Phi<C>,
        cmT: &Commitment<C>,
    ) -> Phi<C> {
        let r2 = r * r;

        let cmE = phi1.cmE.0 + cmT.0.mul(r) + phi2.cmE.0.mul(r2);
        let u = phi1.u + r * phi2.u;
        let cmW = phi1.cmW.0 + phi2.cmW.0.mul(r);
        let x = vec_add(&phi1.x, &vector_elem_product(&phi2.x, &r));
        // let x = rlin(phi1.x, phi2.x, r);

        Phi::<C> {
            cmE: Commitment(cmE.into()),
            u,
            cmW: Commitment(cmW.into()),
            x,
        }
    }

    // NIFS.P
    pub fn P(
        tr: &mut Transcript<C::ScalarField>,
        pedersen_params: &PedersenParams<C>,
        r: C::ScalarField,
        r1cs: &R1CS<C::ScalarField>,
        fw1: FWit<C>,
        fw2: FWit<C>,
    ) -> (FWit<C>, Phi<C>, Phi<C>, Vec<C::ScalarField>, Commitment<C>) {
        // compute committed instances
        let phi1 = fw1.commit(&pedersen_params); // wip
        let phi2 = fw2.commit(&pedersen_params);

        // compute cross terms
        let T = Self::comp_T(&r1cs, phi1.u, phi2.u, &fw1.W, &fw2.W);
        let rT = tr.get_challenge(b"rT");
        let cmT = Pedersen::commit(&pedersen_params, &T, &rT);

        // fold witness
        let fw3 = NIFS::<C>::fold_witness(r, &fw1, &fw2, &T, rT);

        // fold committed instancs
        // let phi3 = NIFS::<C>::fold_instance(r, &phi1, &phi2, &cmT);
        return (fw3, phi1, phi2, T, cmT); // maybe return phi3
    }

    // NIFS.V
    pub fn V(r: C::ScalarField, phi1: &Phi<C>, phi2: &Phi<C>, cmT: &Commitment<C>) -> Phi<C> {
        NIFS::<C>::fold_instance(r, &phi1, &phi2, &cmT)
    }

    // verify commited folded instance (phi) relations
    pub fn verify(
        r: C::ScalarField,
        phi1: &Phi<C>,
        phi2: &Phi<C>,
        phi3: &Phi<C>,
        cmT: &Commitment<C>,
    ) -> bool {
        let r2 = r * r;
        if phi3.cmE.0 != (phi1.cmE.0 + cmT.0.mul(r) + phi2.cmE.0.mul(r2)).into() {
            return false;
        }
        if phi3.u != phi1.u + r * phi2.u {
            return false;
        }
        if phi3.cmW.0 != (phi1.cmW.0 + phi2.cmW.0.mul(r)).into() {
            return false;
        }
        if phi3.x != vec_add(&phi1.x, &vector_elem_product(&phi2.x, &r)) {
            return false;
        }
        true
    }

    pub fn open_commitments(
        tr: &mut Transcript<C::ScalarField>,
        pedersen_params: &PedersenParams<C>,
        fw: &FWit<C>,
        phi: &Phi<C>,
        T: Vec<C::ScalarField>,
        rT: C::ScalarField,
        cmT: &Commitment<C>,
    ) -> (PedersenProof<C>, PedersenProof<C>, PedersenProof<C>) {
        let cmE_proof = Pedersen::prove(&pedersen_params, tr, &phi.cmE, &fw.E, &fw.rE);
        let cmW_proof = Pedersen::prove(&pedersen_params, tr, &phi.cmW, &fw.W, &fw.rW);
        let cmT_proof = Pedersen::prove(&pedersen_params, tr, &cmT, &T, &rT);
        (cmE_proof, cmW_proof, cmT_proof)
    }
    pub fn verify_commitments(
        tr: &mut Transcript<C::ScalarField>,
        pedersen_params: &PedersenParams<C>,
        phi: Phi<C>,
        cmT: Commitment<C>,
        cmE_proof: PedersenProof<C>,
        cmW_proof: PedersenProof<C>,
        cmT_proof: PedersenProof<C>,
    ) -> bool {
        if !Pedersen::verify(&pedersen_params, tr, phi.cmE, cmE_proof) {
            return false;
        }
        if !Pedersen::verify(&pedersen_params, tr, phi.cmW, cmW_proof) {
            return false;
        }
        if !Pedersen::verify(&pedersen_params, tr, cmT, cmT_proof) {
            return false;
        }
        true
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

    fn gen_test_values<R: Rng>(
        rng: &mut R,
    ) -> (
        R1CS<Fr>,
        Vec<Fr>,
        Vec<Fr>,
        Vec<Fr>,
        Vec<Fr>,
        Vec<Fr>,
        Vec<Fr>,
    ) {
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
        // TODO in the future update this method to generate witness, and generate n witnesses
        // instances, x: pub
        let w1 = to_F_vec::<Fr>(vec![1, 3, 35, 9, 27, 30]);
        let x1 = to_F_vec::<Fr>(vec![35]);
        let w2 = to_F_vec::<Fr>(vec![1, 4, 73, 16, 64, 68]);
        let x2 = to_F_vec::<Fr>(vec![73]);
        let w3 = to_F_vec::<Fr>(vec![1, 5, 135, 25, 125, 130]);
        let x3 = to_F_vec::<Fr>(vec![135]);

        let r1cs = R1CS::<Fr> {
            A: A.clone(),
            B: B.clone(),
            C: C.clone(),
        };
        (r1cs, w1, w2, w3, x1, x2, x3)
    }

    // fold 2 instances into one
    #[test]
    fn test_one_fold() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Affine>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec

        let (r1cs, w1, w2, _, x1, x2, _) = gen_test_values(&mut rng);
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let r = Fr::rand(&mut rng); // this would come from the transcript

        let fw1 = FWit::<G1Affine>::new(w1.clone(), A.len());
        let fw2 = FWit::<G1Affine>::new(w2.clone(), A.len());

        // get committed instances
        let phi1 = fw1.commit(&pedersen_params); // wip
        let phi2 = fw2.commit(&pedersen_params);

        let T = NIFS::<G1Affine>::comp_T(&r1cs, phi1.u, phi2.u, &w1, &w2);
        let rT: Fr = Fr::rand(&mut rng);
        let cmT = Pedersen::commit(&pedersen_params, &T, &rT);

        // fold witness
        let fw3 = NIFS::<G1Affine>::fold_witness(r, &fw1, &fw2, &T, rT);

        // fold instance
        let phi3 = NIFS::<G1Affine>::fold_instance(r, &phi1, &phi2, &cmT);

        // naive check that the folded witness satisfies the relaxed r1cs
        let Az = matrix_vector_product(&A, &fw3.W);
        let Bz = matrix_vector_product(&B, &fw3.W);
        let Cz = matrix_vector_product(&C, &fw3.W);
        assert_eq!(
            hadamard_product(Az, Bz),
            vec_add(&vector_elem_product(&Cz, &phi3.u), &fw3.E)
        );

        // check that folded commitments from folded instance (phi) are equal to folding the
        // use folded rE, rW to commit fw3
        let phi3_expected = fw3.commit(&pedersen_params);
        assert_eq!(phi3_expected.cmE.0, phi3.cmE.0);
        assert_eq!(phi3_expected.cmW.0, phi3.cmW.0);

        // NIFS.Verify:
        assert!(NIFS::<G1Affine>::verify(r, &phi1, &phi2, &phi3, &cmT));

        // init Prover's transcript
        let mut transcript_p: Transcript<Fr> = Transcript::<Fr>::new();
        // init Verifier's transcript
        let mut transcript_v: Transcript<Fr> = Transcript::<Fr>::new();

        // check openings of phi3.cmE, phi3.cmW and cmT
        let (cmE_proof, cmW_proof, cmT_proof) = NIFS::<G1Affine>::open_commitments(
            &mut transcript_p,
            &pedersen_params,
            &fw3,
            &phi3,
            T,
            rT,
            &cmT,
        );
        let v = NIFS::<G1Affine>::verify_commitments(
            &mut transcript_v,
            &pedersen_params,
            phi3,
            cmT,
            cmE_proof,
            cmW_proof,
            cmT_proof,
        );
    }

    // fold i_1, i_2 instances into i_12, and then i_12, i_3 into i_123
    #[test]
    fn test_two_fold() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Affine>::new_params(&mut rng, 6);

        let (r1cs, w1, w2, w3, x1, x2, x3) = gen_test_values(&mut rng);

        let u1: Fr = Fr::one();
        let u2: Fr = Fr::one();

        let T_12 = NIFS::<G1Affine>::comp_T(&r1cs, u1, u2, &w1, &w2);
        let rT_12: Fr = Fr::rand(&mut rng);
        let cmT_12 = Pedersen::commit(&pedersen_params, &T_12, &rT_12);

        let r = Fr::rand(&mut rng); // this would come from the transcript

        let fw1 = FWit::<G1Affine>::new(w1, T_12.len());
        let fw2 = FWit::<G1Affine>::new(w2, T_12.len());

        // fold witness
        let fw_12 = NIFS::<G1Affine>::fold_witness(r, &fw1, &fw2, &T_12, rT_12);

        // get committed instances
        let phi1 = fw1.commit(&pedersen_params); // wip
        let phi2 = fw2.commit(&pedersen_params);

        // fold instance
        let phi_12 = NIFS::<G1Affine>::fold_instance(r, &phi1, &phi2, &cmT_12);

        // NIFS.Verify:
        assert!(NIFS::<G1Affine>::verify(r, &phi1, &phi2, &phi_12, &cmT_12));

        //----
        // 2nd fold
        let fw3 = FWit::<G1Affine>::new(w3, r1cs.A.len());

        // compute cross terms
        let T_123 = NIFS::<G1Affine>::comp_T(&r1cs, phi_12.u, Fr::one(), &fw_12.W, &fw3.W);
        let rT_123: Fr = Fr::rand(&mut rng);
        let cmT_123 = Pedersen::commit(&pedersen_params, &T_123, &rT_123);

        // V sets rand challenge r
        let r = Fr::rand(&mut rng); // this would come from the transcript

        // fold witness
        let fw_123 = NIFS::<G1Affine>::fold_witness(r, &fw_12, &fw3, &T_123, rT_123);

        // get committed instances
        // phi_12 is already known for Verifier from folding phi1, phi2
        // rm: let phi_12 = fw_12.commit(&pedersen_params); // wip
        let phi3 = fw3.commit(&pedersen_params);

        // fold instance
        let phi_123 = NIFS::<G1Affine>::fold_instance(r, &phi_12, &phi3, &cmT_123);

        // NIFS.Verify:
        assert!(NIFS::<G1Affine>::verify(
            r, &phi_12, &phi3, &phi_123, &cmT_123
        ));

        // naive check that the folded witness satisfies the relaxed r1cs
        let Az = matrix_vector_product(&r1cs.A, &fw_123.W);
        let Bz = matrix_vector_product(&r1cs.B, &fw_123.W);
        let Cz = matrix_vector_product(&r1cs.C, &fw_123.W);
        assert_eq!(
            hadamard_product(Az, Bz),
            vec_add(&vector_elem_product(&Cz, &phi_123.u), &fw_123.E)
        );

        // check that folded commitments from folded instance (phi) are equal to folding the
        // use folded rE, rW to commit fw3
        let phi_123_expected = fw_123.commit(&pedersen_params);
        assert_eq!(phi_123_expected.cmE.0, phi_123.cmE.0);
        assert_eq!(phi_123_expected.cmW.0, phi_123.cmW.0);

        // init Prover's transcript
        let mut transcript_p: Transcript<Fr> = Transcript::<Fr>::new();
        // init Verifier's transcript
        let mut transcript_v: Transcript<Fr> = Transcript::<Fr>::new();

        // check openings of phi_123.cmE, phi_123.cmW and cmT_123
        let (cmE_proof, cmW_proof, cmT_proof) = NIFS::<G1Affine>::open_commitments(
            &mut transcript_p,
            &pedersen_params,
            &fw_123,
            &phi_123,
            T_123,
            rT_123,
            &cmT_123,
        );
        let v = NIFS::<G1Affine>::verify_commitments(
            &mut transcript_v,
            &pedersen_params,
            phi_123,
            cmT_123,
            cmE_proof,
            cmW_proof,
            cmT_proof,
        );
        assert!(v);
    }

    #[test]
    fn test_nifs_interface() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Affine>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec

        let (r1cs, w1, w2, _, x1, x2, _) = gen_test_values(&mut rng);
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let r = Fr::rand(&mut rng); // this would come from the transcript

        let fw1 = FWit::<G1Affine>::new(w1.clone(), A.len());
        let fw2 = FWit::<G1Affine>::new(w2.clone(), A.len());

        // init Prover's transcript
        let mut transcript_p: Transcript<Fr> = Transcript::<Fr>::new();

        // NIFS.P
        let (fw3, phi1, phi2, T, cmT) =
            NIFS::<G1Affine>::P(&mut transcript_p, &pedersen_params, r, &r1cs, fw1, fw2);

        // init Verifier's transcript
        let mut transcript_v: Transcript<Fr> = Transcript::<Fr>::new();

        // NIFS.V
        let phi3 = NIFS::<G1Affine>::V(r, &phi1, &phi2, &cmT);

        assert!(NIFS::<G1Affine>::verify(r, &phi1, &phi2, &phi3, &cmT));
    }
}
