// use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, Group};
use ark_ff::fields::PrimeField;
use ark_std::{One, Zero};
use std::marker::PhantomData;

use crate::pedersen::{Commitment, Params as PedersenParams, Pedersen, Proof as PedersenProof};
use crate::transcript::Transcript;
use crate::utils::*;
use ark_crypto_primitives::sponge::Absorb;

pub struct R1CS<F: PrimeField> {
    pub A: Vec<Vec<F>>,
    pub B: Vec<Vec<F>>,
    pub C: Vec<Vec<F>>,
}

// Phi: φ in the paper (later 𝖴), a folded instance
#[derive(Clone, Debug)]
pub struct Phi<C: CurveGroup> {
    pub cmE: Commitment<C>,
    pub u: C::ScalarField,
    pub cmW: Commitment<C>,
    pub x: C::ScalarField,
}

// FWit: Folded Witness
pub struct FWit<C: CurveGroup> {
    pub E: Vec<C::ScalarField>,
    pub rE: C::ScalarField,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
}

impl<C: CurveGroup> FWit<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn new(z: Vec<C::ScalarField>, e_len: usize) -> Self {
        FWit::<C> {
            E: vec![C::ScalarField::zero(); e_len],
            rE: C::ScalarField::one(),
            W: z,
            rW: C::ScalarField::one(),
        }
    }
    pub fn commit(&self, params: &PedersenParams<C>) -> Phi<C> {
        let cmE = Pedersen::commit(params, &self.E, &self.rE);
        let cmW = Pedersen::commit(params, &self.W, &self.rW);
        Phi {
            cmE,
            u: C::ScalarField::one(),
            cmW,
            x: self.W[0], // TODO WIP review
        }
    }
}

pub struct NIFS<C: CurveGroup> {
    _phantom: PhantomData<C>,
}

impl<C: CurveGroup> NIFS<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    // comp_T: compute cross-terms T
    pub fn comp_T(
        r1cs: &R1CS<C::ScalarField>,
        u1: C::ScalarField,
        u2: C::ScalarField,
        z1: &[C::ScalarField],
        z2: &[C::ScalarField],
    ) -> Vec<C::ScalarField> {
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        // this is parallelizable (for the future)
        let Az1 = matrix_vector_product(&A, z1);
        let Bz1 = matrix_vector_product(&B, z1);
        let Cz1 = matrix_vector_product(&C, z1);
        let Az2 = matrix_vector_product(&A, z2);
        let Bz2 = matrix_vector_product(&B, z2);
        let Cz2 = matrix_vector_product(&C, z2);

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
            &vec_add(&fw1.E, &vector_elem_product(T, &r)),
            &vector_elem_product(&fw2.E, &r2),
        );
        let rE = fw1.rE + r * rT + r2 * fw2.rE;
        let W = vec_add(&fw1.W, &vector_elem_product(&fw2.W, &r));
        let rW = fw1.rW + r * fw2.rW;
        FWit::<C> { E, rE, W, rW }
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
        // let x = vec_add(&phi1.x, &vector_elem_product(&phi2.x, &r));
        let x = phi1.x + r * phi2.x;

        Phi::<C> {
            cmE: Commitment(cmE),
            u,
            cmW: Commitment(cmW),
            x,
        }
    }

    // NIFS.P
    #[allow(clippy::type_complexity)]
    pub fn P(
        tr: &mut Transcript<C::ScalarField, C>,
        pedersen_params: &PedersenParams<C>,
        r: C::ScalarField,
        r1cs: &R1CS<C::ScalarField>,
        fw1: FWit<C>,
        fw2: FWit<C>,
    ) -> (FWit<C>, Phi<C>, Phi<C>, Vec<C::ScalarField>, Commitment<C>) {
        // compute committed instances
        let phi1 = fw1.commit(pedersen_params); // wip
        let phi2 = fw2.commit(pedersen_params);

        // compute cross terms
        let T = Self::comp_T(r1cs, phi1.u, phi2.u, &fw1.W, &fw2.W);
        let rT = tr.get_challenge(); // r_T
        let cmT = Pedersen::commit(pedersen_params, &T, &rT);

        // fold witness
        let fw3 = NIFS::<C>::fold_witness(r, &fw1, &fw2, &T, rT);

        // fold committed instancs
        // let phi3 = NIFS::<C>::fold_instance(r, &phi1, &phi2, &cmT);
        (fw3, phi1, phi2, T, cmT) // maybe return phi3
    }

    // NIFS.V
    pub fn V(r: C::ScalarField, phi1: &Phi<C>, phi2: &Phi<C>, cmT: &Commitment<C>) -> Phi<C> {
        NIFS::<C>::fold_instance(r, phi1, phi2, cmT)
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
        if phi3.cmE.0 != (phi1.cmE.0 + cmT.0.mul(r) + phi2.cmE.0.mul(r2)) {
            return false;
        }
        if phi3.u != phi1.u + r * phi2.u {
            return false;
        }
        if phi3.cmW.0 != (phi1.cmW.0 + phi2.cmW.0.mul(r)) {
            return false;
        }
        // if phi3.x != vec_add(&phi1.x, &vector_elem_product(&phi2.x, &r)) {
        if phi3.x != phi1.x + r * phi2.x {
            return false;
        }
        true
    }

    pub fn open_commitments(
        tr: &mut Transcript<C::ScalarField, C>,
        pedersen_params: &PedersenParams<C>,
        fw: &FWit<C>,
        phi: &Phi<C>,
        T: Vec<C::ScalarField>,
        rT: C::ScalarField,
        cmT: &Commitment<C>,
    ) -> (PedersenProof<C>, PedersenProof<C>, PedersenProof<C>) {
        let cmE_proof = Pedersen::prove(pedersen_params, tr, &phi.cmE, &fw.E, &fw.rE);
        let cmW_proof = Pedersen::prove(pedersen_params, tr, &phi.cmW, &fw.W, &fw.rW);
        let cmT_proof = Pedersen::prove(pedersen_params, tr, cmT, &T, &rT);
        (cmE_proof, cmW_proof, cmT_proof)
    }
    pub fn verify_commitments(
        tr: &mut Transcript<C::ScalarField, C>,
        pedersen_params: &PedersenParams<C>,
        phi: Phi<C>,
        cmT: Commitment<C>,
        cmE_proof: PedersenProof<C>,
        cmW_proof: PedersenProof<C>,
        cmT_proof: PedersenProof<C>,
    ) -> bool {
        if !Pedersen::verify(pedersen_params, tr, phi.cmE, cmE_proof) {
            return false;
        }
        if !Pedersen::verify(pedersen_params, tr, phi.cmW, cmW_proof) {
            return false;
        }
        if !Pedersen::verify(pedersen_params, tr, cmT, cmT_proof) {
            return false;
        }
        true
    }
}

// only for tests across different files
pub fn gen_test_values<F: PrimeField>(n: usize) -> (R1CS<F>, Vec<Vec<F>>, Vec<Vec<F>>) {
    // R1CS for: x^3 + x + 5 = y (example from article
    // https://www.vitalik.ca/general/2016/12/10/qap.html )
    let A = to_F_matrix::<F>(vec![
        vec![0, 1, 0, 0, 0, 0],
        vec![0, 0, 0, 1, 0, 0],
        vec![0, 1, 0, 0, 1, 0],
        vec![5, 0, 0, 0, 0, 1],
    ]);
    let B = to_F_matrix::<F>(vec![
        vec![0, 1, 0, 0, 0, 0],
        vec![0, 1, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0],
        vec![1, 0, 0, 0, 0, 0],
    ]);
    let C = to_F_matrix::<F>(vec![
        vec![0, 0, 0, 1, 0, 0],
        vec![0, 0, 0, 0, 1, 0],
        vec![0, 0, 0, 0, 0, 1],
        vec![0, 0, 1, 0, 0, 0],
    ]);

    // generate n witnesses
    let mut w: Vec<Vec<F>> = Vec::new();
    let mut x: Vec<Vec<F>> = Vec::new();
    for i in 0..n {
        let input = 3 + i;
        let w_i = to_F_vec::<F>(vec![
            1,
            input,
            input * input * input + input + 5, // x^3 + x + 5
            input * input,                     // x^2
            input * input * input,             // x^2 * x
            input * input * input + input,     // x^3 + x
        ]);
        w.push(w_i.clone());
        let x_i = to_F_vec::<F>(vec![input * input * input + input + 5]);
        x.push(x_i.clone());
    }

    let r1cs = R1CS::<F> { A, B, C };
    (r1cs, w, x)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pedersen::Pedersen;
    use crate::transcript::poseidon_test_config;
    use ark_mnt4_298::{Fr, G1Projective};
    use ark_std::One;
    use ark_std::UniformRand;

    // fold 2 instances into one
    #[test]
    fn test_one_fold() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec
        let poseidon_config = poseidon_test_config::<Fr>();

        let (r1cs, ws, _) = gen_test_values(2);
        let (A, B, C) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let r = Fr::rand(&mut rng); // this would come from the transcript

        let fw1 = FWit::<G1Projective>::new(ws[0].clone(), A.len());
        let fw2 = FWit::<G1Projective>::new(ws[1].clone(), A.len());

        // get committed instances
        let phi1 = fw1.commit(&pedersen_params); // wip
        let phi2 = fw2.commit(&pedersen_params);

        let T = NIFS::<G1Projective>::comp_T(&r1cs, phi1.u, phi2.u, &ws[0], &ws[1]);
        let rT: Fr = Fr::rand(&mut rng);
        let cmT = Pedersen::commit(&pedersen_params, &T, &rT);

        // fold witness
        let fw3 = NIFS::<G1Projective>::fold_witness(r, &fw1, &fw2, &T, rT);

        // fold instance
        let phi3 = NIFS::<G1Projective>::fold_instance(r, &phi1, &phi2, &cmT);

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
        assert!(NIFS::<G1Projective>::verify(r, &phi1, &phi2, &phi3, &cmT));

        // init Prover's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        // check openings of phi3.cmE, phi3.cmW and cmT
        let (cmE_proof, cmW_proof, cmT_proof) = NIFS::<G1Projective>::open_commitments(
            &mut transcript_p,
            &pedersen_params,
            &fw3,
            &phi3,
            T,
            rT,
            &cmT,
        );
        let v = NIFS::<G1Projective>::verify_commitments(
            &mut transcript_v,
            &pedersen_params,
            phi3,
            cmT,
            cmE_proof,
            cmW_proof,
            cmT_proof,
        );
        assert!(v);
    }

    // fold i_1, i_2 instances into i_12, and then i_12, i_3 into i_123
    #[test]
    fn test_two_fold() {
        let mut rng = ark_std::test_rng();
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, 6);
        let poseidon_config = poseidon_test_config::<Fr>();

        let (r1cs, ws, _) = gen_test_values(3);

        let u1: Fr = Fr::one();
        let u2: Fr = Fr::one();

        let T_12 = NIFS::<G1Projective>::comp_T(&r1cs, u1, u2, &ws[0], &ws[1]);
        let rT_12: Fr = Fr::rand(&mut rng);
        let cmT_12 = Pedersen::commit(&pedersen_params, &T_12, &rT_12);

        let r = Fr::rand(&mut rng); // this would come from the transcript

        let fw1 = FWit::<G1Projective>::new(ws[0].clone(), T_12.len());
        let fw2 = FWit::<G1Projective>::new(ws[1].clone(), T_12.len());

        // fold witness
        let fw_12 = NIFS::<G1Projective>::fold_witness(r, &fw1, &fw2, &T_12, rT_12);

        // get committed instances
        let phi1 = fw1.commit(&pedersen_params); // wip
        let phi2 = fw2.commit(&pedersen_params);

        // fold instance
        let phi_12 = NIFS::<G1Projective>::fold_instance(r, &phi1, &phi2, &cmT_12);

        // NIFS.Verify:
        assert!(NIFS::<G1Projective>::verify(
            r, &phi1, &phi2, &phi_12, &cmT_12
        ));

        //----
        // 2nd fold
        let fw3 = FWit::<G1Projective>::new(ws[2].clone(), r1cs.A.len());

        // compute cross terms
        let T_123 = NIFS::<G1Projective>::comp_T(&r1cs, phi_12.u, Fr::one(), &fw_12.W, &fw3.W);
        let rT_123: Fr = Fr::rand(&mut rng);
        let cmT_123 = Pedersen::commit(&pedersen_params, &T_123, &rT_123);

        // V sets rand challenge r
        let r = Fr::rand(&mut rng); // this would come from the transcript

        // fold witness
        let fw_123 = NIFS::<G1Projective>::fold_witness(r, &fw_12, &fw3, &T_123, rT_123);

        // get committed instances
        // phi_12 is already known for Verifier from folding phi1, phi2
        // rm: let phi_12 = fw_12.commit(&pedersen_params); // wip
        let phi3 = fw3.commit(&pedersen_params);

        // fold instance
        let phi_123 = NIFS::<G1Projective>::fold_instance(r, &phi_12, &phi3, &cmT_123);

        // NIFS.Verify:
        assert!(NIFS::<G1Projective>::verify(
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
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);
        // init Verifier's transcript
        let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        // check openings of phi_123.cmE, phi_123.cmW and cmT_123
        let (cmE_proof, cmW_proof, cmT_proof) = NIFS::<G1Projective>::open_commitments(
            &mut transcript_p,
            &pedersen_params,
            &fw_123,
            &phi_123,
            T_123,
            rT_123,
            &cmT_123,
        );
        let v = NIFS::<G1Projective>::verify_commitments(
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
        let pedersen_params = Pedersen::<G1Projective>::new_params(&mut rng, 100); // 100 is wip, will get it from actual vec
        let poseidon_config = poseidon_test_config::<Fr>();

        let (r1cs, ws, _) = gen_test_values(3);
        let (A, _, _) = (r1cs.A.clone(), r1cs.B.clone(), r1cs.C.clone());

        let r = Fr::rand(&mut rng); // this would come from the transcript

        let fw1 = FWit::<G1Projective>::new(ws[0].clone(), A.len());
        let fw2 = FWit::<G1Projective>::new(ws[1].clone(), A.len());

        // init Prover's transcript
        let mut transcript_p = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        // NIFS.P
        let (_fw3, phi1, phi2, _T, cmT) =
            NIFS::<G1Projective>::P(&mut transcript_p, &pedersen_params, r, &r1cs, fw1, fw2);

        // init Verifier's transcript
        // let mut transcript_v = Transcript::<Fr, G1Projective>::new(&poseidon_config);

        // NIFS.V
        let phi3 = NIFS::<G1Projective>::V(r, &phi1, &phi2, &cmT);

        assert!(NIFS::<G1Projective>::verify(r, &phi1, &phi2, &phi3, &cmT));
    }
}
