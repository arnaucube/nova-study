use ark_ec::AffineRepr;
use ark_std::{
    rand::{Rng, RngCore},
    UniformRand,
};
use std::marker::PhantomData;

use crate::transcript::Transcript;
use crate::utils::naive_msm;

pub struct Proof<C: AffineRepr> {
    R: C,
    t1: C::ScalarField,
    t2: C::ScalarField,
}

pub struct Params<C: AffineRepr> {
    g: C,
    h: C,
}

pub struct Pedersen<C: AffineRepr> {
    _phantom: PhantomData<C>,
}

impl<C: AffineRepr> Pedersen<C> {
    pub fn new_params<R: Rng>(rng: &mut R) -> Params<C> {
        let h_scalar = C::ScalarField::rand(rng);
        let g: C = C::generator();
        let params: Params<C> = Params::<C> {
            g,
            h: g.mul(h_scalar).into(),
        };
        params
    }

    pub fn commit_elem<R: RngCore>(
        rng: &mut R,
        params: &Params<C>,
        v: &C::ScalarField,
    ) -> Commitment<C> {
        let r = C::ScalarField::rand(rng);
        let cm: C = (params.g.mul(v) + params.h.mul(r)).into();
        Commitment::<C> { cm, r }
    }
    pub fn commit_vec<R: RngCore>(
        rng: &mut R,
        params: &Params<C>,
        v: &Vec<C::ScalarField>,
    ) -> CommitmentVec<C> {
        let r: Vec<C> = vec![C::rand(rng); v.len()]; // wip
        let cm = naive_msm(v, &r);
        CommitmentVec::<C> { cm, r }
    }

    pub fn prove(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        cm: C,
        v: C::ScalarField,
        r: C::ScalarField,
    ) -> Proof<C> {
        let s1 = transcript.get_challenge(b"s_1");
        let s2 = transcript.get_challenge(b"s_2");

        let R: C = (params.g.mul(s1) + params.h.mul(s2)).into();

        transcript.add(b"cm", &cm);
        transcript.add(b"R", &R);
        let c = transcript.get_challenge(b"c");

        let t1 = s1 + v * c;
        let t2 = s2 + r * c;

        Proof::<C> { R, t1, t2 }
    }

    pub fn verify(
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        cm: C,
        proof: Proof<C>,
    ) -> bool {
        // s1, s2 just to match Prover's transcript
        transcript.get_challenge(b"s_1");
        transcript.get_challenge(b"s_2");

        transcript.add(b"cm", &cm);
        transcript.add(b"R", &proof.R);
        let c = transcript.get_challenge(b"c");
        let lhs = proof.R + cm.mul(c);
        let rhs = params.g.mul(proof.t1) + params.h.mul(proof.t2);
        if lhs != rhs {
            return false;
        }
        true
    }
}

pub struct CommitmentVec<C: AffineRepr> {
    // WIP
    pub cm: C,
    pub r: Vec<C>,
}
pub struct Commitment<C: AffineRepr> {
    pub cm: C,
    pub r: C::ScalarField,
}
impl<C: AffineRepr> Commitment<C> {
    pub fn prove(
        &self,
        params: &Params<C>,
        transcript: &mut Transcript<C::ScalarField>,
        v: C::ScalarField,
    ) -> Proof<C> {
        Pedersen::<C>::prove(params, transcript, self.cm, v, self.r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{g1::G1Affine, Fr};
    use ark_ec::CurveGroup;
    use std::ops::Mul;

    #[test]
    fn test_pedersen() {
        let mut rng = ark_std::test_rng();

        // setup params
        let params = Pedersen::<G1Affine>::new_params(&mut rng);

        // init Prover's transcript
        let mut transcript_p: Transcript<Fr> = Transcript::<Fr>::new();
        // init Verifier's transcript
        let mut transcript_v: Transcript<Fr> = Transcript::<Fr>::new();

        let v = Fr::rand(&mut rng);

        let cm = Pedersen::commit_elem(&mut rng, &params, &v);
        let proof = cm.prove(&params, &mut transcript_p, v);
        // also can use:
        // let proof = Pedersen::prove(&params, &mut transcript_p, cm.cm, v, cm.r);
        let v = Pedersen::verify(&params, &mut transcript_v, cm.cm, proof);
        assert!(v);
    }
}
