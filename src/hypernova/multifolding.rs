use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use ark_ec::{CurveGroup, Group};
use ark_ff::fields::PrimeField;
use ark_poly::{
    evaluations::multivariate::multilinear::{MultilinearExtension, SparseMultilinearExtension},
    multivariate::{SparsePolynomial, SparseTerm, Term},
    univariate::DensePolynomial,
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
};
use ark_std::log2;

use std::marker::PhantomData;

use crate::hypernova::ccs::CCS;
use crate::hypernova::sumcheck::{Point, SumCheck};
use crate::pedersen::Commitment;
use crate::transcript::Transcript;

use ark_std::{One, Zero};

// Committed CCS instance
pub struct CCCS<C: CurveGroup> {
    C: Commitment<C>,
    x: Vec<C::ScalarField>,
}

// Linearized Committed CCS instance
pub struct LCCCS<C: CurveGroup> {
    C: Commitment<C>,
    u: C::ScalarField,
    x: Vec<C::ScalarField>,
    r: Vec<C::ScalarField>,
    v: Vec<C::ScalarField>,
}

// NIMFS: Non Interactive Multifolding Scheme
pub struct NIMFS<C: CurveGroup> {
    _c: PhantomData<C>,
}

impl<C: CurveGroup> NIMFS<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as CurveGroup>::BaseField: Absorb,
{
    // proof method folds and returns the proof of the multifolding
    pub fn proof(
        tr: &mut Transcript<C::ScalarField, C>,
        poseidon_config: &PoseidonConfig<C::ScalarField>,
        ccs: CCS<C::ScalarField>,
        lcccs: LCCCS<C>,
        cccs: CCCS<C>,
        z1: Vec<C::ScalarField>,
        z2: Vec<C::ScalarField>,
    ) -> LCCCS<C> {
        let s = log2(ccs.m) as usize; // s
        let s_ = log2(ccs.n) as usize; // s'
        let gamma = tr.get_challenge();
        let beta = tr.get_challenge_vec(s);

        // get MLE of M_i
        let mut MLEs: Vec<SparseMultilinearExtension<C::ScalarField>> = Vec::new();
        let n_vars = (s + s_) as usize;
        for i in 0..ccs.M.len() {
            let M_i_MLE = matrix_to_mle(n_vars, ccs.m, ccs.n, &ccs.M[i]);
            MLEs.push(M_i_MLE);
        }
        // get MLE of z1 & z2
        let z1_MLE = vector_to_mle(s_, ccs.n, z1);
        let z2_MLE = vector_to_mle(s_, ccs.n, z2);

        // compute Lj = eq(r_x,x) * \sum Mj * z1
        let mut Lj_evals: Vec<(usize, C::ScalarField)> = Vec::new();
        for i in 0..s_ {}
        // compute Q = eq(beta, x) * ( \sum c_i * \prod( \sum Mj * z1 ) )
        // compute g
        // let g: SparsePolynomial<C::ScalarField, SparseTerm>;
        // let proof = SC::<C>::prove(&poseidon_config, g);
        // fold C, u, x, v, w

        unimplemented!();
    }
}

fn matrix_to_mle<F: PrimeField>(
    n_vars: usize, // log2(m) + log2(n)
    m: usize,
    n: usize,
    M: &Vec<Vec<F>>,
) -> SparseMultilinearExtension<F> {
    let mut M_evals: Vec<(usize, F)> = Vec::new();
    for i in 0..m {
        for j in 0..n {
            if !M[i][j].is_zero() {
                M_evals.push((i * n + j, M[i][j]));
            }
        }
    }
    SparseMultilinearExtension::<F>::from_evaluations(n_vars, M_evals.iter())
}

fn vector_to_mle<F: PrimeField>(s: usize, n: usize, z: Vec<F>) -> SparseMultilinearExtension<F> {
    let mut z_evals: Vec<(usize, F)> = Vec::new();
    for i in 0..n {
        if !z[i].is_zero() {
            z_evals.push((i, z[i]));
        }
    }
    SparseMultilinearExtension::<F>::from_evaluations(s, z_evals.iter())
}

type SC<C: CurveGroup> = SumCheck<
    C::ScalarField,
    C,
    DensePolynomial<C::ScalarField>,
    SparsePolynomial<C::ScalarField, SparseTerm>,
>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::poseidon_test_config;
    use ark_mnt4_298::{Fr, G1Projective};
    use ark_std::One;
    use ark_std::UniformRand;

    use crate::nifs::gen_test_values;

    type P = Point<Fr>;

    #[test]
    fn test_cccs_mles() {
        let (r1cs, ws, _) = gen_test_values(2);
        let z1: Vec<Fr> = ws[0].clone();
        println!("z1 {:?}", z1);

        let ccs = r1cs.to_ccs();
        let s = log2(ccs.m) as usize; // s
        let s_ = log2(ccs.n) as usize; // s'
        let pow_s_ = (2 as usize).pow(s_ as u32);

        let mut M_MLEs: Vec<SparseMultilinearExtension<Fr>> = Vec::new();
        let n_vars = (s + s_) as usize;
        for i in 0..ccs.M.len() {
            let M_i_MLE = matrix_to_mle(n_vars, ccs.m, ccs.n, &ccs.M[i]);
            println!("i:{}, M_i_mle: {:?}", i, M_i_MLE);
            M_MLEs.push(M_i_MLE);
        }

        let z1_MLE = vector_to_mle(s_, ccs.n, z1);
        println!("z1_MLE: {:?}", z1_MLE);

        let beta = Point::<Fr>::point_normal(s, 2); // imagine that this comes from random
        println!("beta: {:?}", beta);

        // check Committed CCS relation
        let mut r: Fr = Fr::zero();
        for i in 0..ccs.q {
            let mut prod_res = Fr::one();
            // for j in 0..ccs.S.len() {
            for j in ccs.S[i].clone() {
                let mut Mj_z_eval = Fr::zero();
                // for k in 0..s_ {
                // over the boolean hypercube un s' vars, but only the combinations that lead to
                // some non-zero z()
                for k in 0..ccs.n {
                    // over the whole boolean hypercube on s' vars
                    // for k in 0..pow_s_ {
                    let point_in_s_ = Point::<Fr>::point_normal(s_, k);
                    // println!("point_in_s {:?}", point_in_s_);
                    let z_eval = z1_MLE.evaluate(&point_in_s_).unwrap();
                    // println!("  ===================================z_eval {:?}", z_eval);

                    // let point_in_s_plus_s_ = Point::<Fr>::point_complete(beta.clone(), s + s_, k);
                    let mut point_in_s_plus_s_ = Point::<Fr>::point_normal(s_, k);
                    point_in_s_plus_s_.append(&mut beta.clone());
                    // println!("point_in_s_plus_s_ {:?}", point_in_s_plus_s_);
                    // println!("j: {}, Mj {:?}", j, M_MLEs[j]);
                    let Mj_eval = M_MLEs[j].evaluate(&point_in_s_plus_s_).unwrap();

                    if Mj_eval * z_eval != Fr::zero() {
                        println!("  j: {}, Mj_eval {:?}", j, Mj_eval);
                        println!("  z_eval {:?}", z_eval);
                        println!("      =(Mj*z)_eval {:?}", Mj_eval * z_eval);
                    }

                    Mj_z_eval += Mj_eval * z_eval;
                }
                println!("j: {}, {:?}\n", j, Mj_z_eval);
                prod_res += Mj_z_eval;
            }
            println!("i:{}, c: {:?}, {:?}\n", i, ccs.c[i], prod_res);
            r += ccs.c[i] * prod_res;
        }
        println!("r {:?}", r);
        // assert!(r.is_zero());
    }
}
