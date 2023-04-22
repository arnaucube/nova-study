use ark_ec::AffineRepr;
use ark_std::{
    rand::{Rng, RngCore},
    UniformRand,
};
use std::marker::PhantomData;

use crate::transcript::Transcript;
use crate::utils::{naive_msm, vec_add, vector_elem_product};

pub struct Proof_elem<C: AffineRepr> {
    R: C,
    t1: C::ScalarField,
    t2: C::ScalarField,
}
pub struct Proof<C: AffineRepr> {
    R: C,
    u_: Vec<C::ScalarField>,
    ru_: C::ScalarField,
}

pub struct Params<C: AffineRepr> {
    g: C,
    h: C,
    pub r_vec: Vec<C>,
}

pub struct Pedersen<C: AffineRepr> {
    _phantom: PhantomData<C>,
}

impl<C: AffineRepr> Pedersen<C> {
    pub fn new_params<R: Rng>(rng: &mut R, max: usize) -> Params<C> {
        let h_scalar = C::ScalarField::rand(rng);
        let g: C = C::generator();
        let r_vec: Vec<C> = vec![C::rand(rng); max];
        let params: Params<C> = Params::<C> {
            g,
            h: g.mul(h_scalar).into(),
            r_vec, // will need 2 r: rE, rW
        };
        params
    }

    pub fn commit_elem<R: RngCore>(
        rng: &mut R,
        params: &Params<C>,
        v: &C::ScalarField,
    ) -> CommitmentElem<C> {
        let r = C::ScalarField::rand(rng);
        let cm: C = (params.g.mul(v) + params.h.mul(r)).into();
        CommitmentElem::<C> { cm, r }
    }
    pub fn commit(
        params: &Params<C>,
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField, // random value is provided, in order to be choosen by other parts of the protocol
    ) -> Commitment<C> {
        let cm = params.h.mul(r) + naive_msm(v, &params.r_vec);
        Commitment::<C>(cm.into())
    }

    pub fn prove_elem(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        cm: C,
        v: C::ScalarField,
        r: C::ScalarField,
    ) -> Proof_elem<C> {
        let r1 = transcript.get_challenge(b"r_1");
        let r2 = transcript.get_challenge(b"r_2");

        let R: C = (params.g.mul(r1) + params.h.mul(r2)).into();

        transcript.add(b"cm", &cm);
        transcript.add(b"R", &R);
        let e = transcript.get_challenge(b"e");

        let t1 = r1 + v * e;
        let t2 = r2 + r * e;

        Proof_elem::<C> { R, t1, t2 }
    }
    pub fn prove(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        cm: &Commitment<C>, // TODO maybe it makes sense to not have a type wrapper and use directly C
        v: &Vec<C::ScalarField>,
        r: &C::ScalarField,
    ) -> Proof<C> {
        let r1 = transcript.get_challenge(b"r_1");
        let d = transcript.get_challenge_vec(b"d", v.len());

        let R: C = (params.h.mul(r1) + naive_msm(&d, &params.r_vec)).into();

        transcript.add(b"cm", &cm.0);
        transcript.add(b"R", &R);
        let e = transcript.get_challenge(b"e");

        let u_ = vec_add(&vector_elem_product(&v, &e), &d);
        let ru_ = e * r + r1;

        Proof::<C> { R, u_, ru_ }
    }
    pub fn verify(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        cm: Commitment<C>,
        proof: Proof<C>,
    ) -> bool {
        // r1, d just to match Prover's transcript
        transcript.get_challenge(b"r_1");
        transcript.get_challenge_vec(b"d", proof.u_.len());

        transcript.add(b"cm", &cm.0);
        transcript.add(b"R", &proof.R);
        let e = transcript.get_challenge(b"e");
        let lhs = proof.R + cm.0.mul(e);
        let rhs = params.h.mul(proof.ru_) + naive_msm(&proof.u_, &params.r_vec);
        if lhs != rhs {
            return false;
        }
        true
    }

    pub fn verify_elem(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        cm: C,
        proof: Proof_elem<C>,
    ) -> bool {
        // s1, s2 just to match Prover's transcript
        transcript.get_challenge(b"r_1");
        transcript.get_challenge(b"r_2");

        transcript.add(b"cm", &cm);
        transcript.add(b"R", &proof.R);
        let e = transcript.get_challenge(b"e");
        let lhs = proof.R + cm.mul(e);
        let rhs = params.g.mul(proof.t1) + params.h.mul(proof.t2);
        if lhs != rhs {
            return false;
        }
        true
    }
}

pub struct Commitment<C: AffineRepr>(pub C);

pub struct CommitmentElem<C: AffineRepr> {
    pub cm: C,
    pub r: C::ScalarField,
}
impl<C: AffineRepr> CommitmentElem<C> {
    pub fn prove(
        &self,
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        v: C::ScalarField,
    ) -> Proof_elem<C> {
        Pedersen::<C>::prove_elem(params, transcript, self.cm, v, self.r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{g1::G1Affine, Fr};
    use ark_ec::CurveGroup;
    use std::ops::Mul;

    #[test]
    fn test_pedersen_single_element() {
        let mut rng = ark_std::test_rng();

        // setup params
        let params = Pedersen::<G1Affine>::new_params(
            &mut rng, 0, /* 0, as here we don't use commit_vec */
        );

        // init Prover's transcript
        let mut transcript_p: Transcript<Fr> = Transcript::<Fr>::new();
        // init Verifier's transcript
        let mut transcript_v: Transcript<Fr> = Transcript::<Fr>::new();

        let v = Fr::rand(&mut rng);

        let cm = Pedersen::commit_elem(&mut rng, &params, &v);
        let proof = cm.prove(&params, &mut transcript_p, v);
        // also can use:
        // let proof = Pedersen::prove_elem(&params, &mut transcript_p, cm.cm, v, cm.r);
        let v = Pedersen::verify_elem(&params, &mut transcript_v, cm.cm, proof);
        assert!(v);
    }
    #[test]
    fn test_pedersen_vector() {
        let mut rng = ark_std::test_rng();

        const n: usize = 10;
        // setup params
        let params = Pedersen::<G1Affine>::new_params(&mut rng, n);

        // init Prover's transcript
        let mut transcript_p: Transcript<Fr> = Transcript::<Fr>::new();
        // init Verifier's transcript
        let mut transcript_v: Transcript<Fr> = Transcript::<Fr>::new();

        let v: Vec<Fr> = vec![Fr::rand(&mut rng); n];
        let r: Fr = Fr::rand(&mut rng);
        let cm = Pedersen::commit(&params, &v, &r);
        let proof = Pedersen::prove(&params, &mut transcript_p, &cm, &v, &r);
        let v = Pedersen::verify(&params, &mut transcript_v, cm, proof);
        assert!(v);
    }
}
