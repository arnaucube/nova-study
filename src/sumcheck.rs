// Sum-check protocol initial implementation, not used by the rest of the repo but implemented as
// an exercise and might be used in the future.

use ark_ff::{BigInteger, PrimeField};
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm, Term},
    univariate::DensePolynomial,
    DenseMVPolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain, Polynomial,
    SparseMultilinearExtension,
};
use ark_std::cfg_into_iter;
use ark_std::log2;
use ark_std::marker::PhantomData;
use ark_std::ops::Mul;
use ark_std::{rand::Rng, UniformRand};

pub struct SumCheck<
    F: PrimeField,
    UV: Polynomial<F> + DenseUVPolynomial<F>,
    MV: Polynomial<F> + DenseMVPolynomial<F>,
> {
    _f: PhantomData<F>,
    _uv: PhantomData<UV>,
    _mv: PhantomData<MV>,
}

impl<
        F: PrimeField,
        UV: Polynomial<F> + DenseUVPolynomial<F>,
        MV: Polynomial<F> + DenseMVPolynomial<F>,
    > SumCheck<F, UV, MV>
{
    fn partial_evaluate(g: &MV, point: &[Option<F>]) -> UV {
        assert!(point.len() >= g.num_vars(), "Invalid evaluation domain");
        // TODO: add check: there can only be 1 'None' value in point
        if g.is_zero() {
            return UV::from_coefficients_vec(vec![F::zero()]);
        }

        // note: this can be parallelized with cfg_into_iter
        let mut univ_terms: Vec<(F, SparseTerm)> = vec![];
        for (coef, term) in g.terms().iter() {
            // partial_evaluate each term
            let mut new_coef = F::one();
            let mut new_term = Vec::new();
            for (var, power) in term.iter() {
                match point[*var] {
                    Some(v) => {
                        if v.is_zero() {
                            new_coef = F::zero();
                            new_term = vec![];
                            break;
                        } else {
                            new_coef = new_coef * v.pow([(*power) as u64]);
                        }
                    }
                    _ => {
                        new_term.push((*var, *power));
                    }
                };
            }
            let new_term = SparseTerm::new(new_term);
            let new_coef = new_coef * coef;
            univ_terms.push((new_coef, new_term));
        }
        let mv_poly: SparsePolynomial<F, SparseTerm> =
            DenseMVPolynomial::<F>::from_coefficients_vec(g.num_vars(), univ_terms.clone());

        let mut univ_coeffs: Vec<F> = vec![F::zero(); mv_poly.degree() + 1];
        for (coef, term) in univ_terms {
            if term.is_empty() {
                univ_coeffs[0] += coef;
                continue;
            }
            for (_, power) in term.iter() {
                univ_coeffs[*power] += coef;
            }
        }
        UV::from_coefficients_vec(univ_coeffs)
    }

    fn point_complete(challenges: Vec<F>, n_elems: usize, iter_num: usize) -> Vec<F> {
        let p = Self::point(challenges, false, n_elems, iter_num);
        // let mut r = Vec::new();
        let mut r = vec![F::zero(); n_elems];
        for i in 0..n_elems {
            // r.push(p[i].unwrap());
            r[i] = p[i].unwrap();
        }
        r
    }
    fn point(challenges: Vec<F>, none: bool, n_elems: usize, iter_num: usize) -> Vec<Option<F>> {
        let mut n_vars = n_elems - challenges.len();
        assert!(n_vars >= log2(iter_num + 1) as usize);

        if none {
            // WIP
            if n_vars == 0 {
                panic!("err");
            }
            n_vars -= 1;
        }
        let none_pos = if none {
            challenges.len() + 1
        } else {
            challenges.len()
        };
        let mut p: Vec<Option<F>> = vec![None; n_elems];
        for i in 0..challenges.len() {
            p[i] = Some(challenges[i]);
        }
        for i in 0..n_vars {
            let k = F::from(iter_num as u64).into_bigint().to_bytes_le();
            let bit = k[(i / 8) as usize] & (1 << (i % 8));
            if bit == 0 {
                p[none_pos + i] = Some(F::zero());
            } else {
                p[none_pos + i] = Some(F::one());
            }
        }
        p
    }

    pub fn prove(g: MV) -> (F, Vec<UV>, F)
    where
        <MV as Polynomial<F>>::Point: From<Vec<F>>,
    {
        let v = g.num_vars();

        let r = vec![F::from(2_u32), F::from(3_u32), F::from(6_u32)]; // TMP will come from transcript

        // compute H
        let mut H = F::zero();
        for i in 0..(2_u64.pow(v as u32) as usize) {
            let p = Self::point_complete(vec![], v, i);

            H = H + g.evaluate(&p.into());
        }

        let mut ss: Vec<UV> = Vec::new();
        for i in 0..v {
            let var_slots = v - 1 - i;
            let n_points = 2_u64.pow(var_slots as u32) as usize;
            let mut s_i = UV::zero();
            let r_round = r.as_slice()[..i].to_vec();
            for j in 0..n_points {
                let point = Self::point(r_round.clone(), true, v, j);
                s_i = s_i + Self::partial_evaluate(&g, &point);
            }
            ss.push(s_i);
        }

        let point_last = r;
        let last_g_eval = g.evaluate(&point_last.into());
        (H, ss, last_g_eval)
    }

    pub fn verify(proof: (F, Vec<UV>, F)) -> bool {
        // let c: F, ss: Vec<UV>;
        let (c, ss, last_g_eval) = proof;

        let r = vec![F::from(2_u32), F::from(3_u32), F::from(6_u32)]; // TMP will come from transcript

        for (i, s) in ss.iter().enumerate() {
            // TODO check degree
            if i == 0 {
                if c != s.evaluate(&F::zero()) + s.evaluate(&F::one()) {
                    return false;
                }
                continue;
            }

            if ss[i - 1].evaluate(&r[i - 1]) != s.evaluate(&F::zero()) + s.evaluate(&F::one()) {
                return false;
            }
        }
        // last round
        if ss[ss.len() - 1].evaluate(&r[r.len() - 1]) != last_g_eval {
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::Fr; // scalar field

    #[test]
    fn test_new_point() {
        let f4 = Fr::from(4_u32);
        let f1 = Fr::from(1);
        let f0 = Fr::from(0);
        type SC = SumCheck<Fr, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let p = SC::point(vec![Fr::from(4_u32)], true, 5, 0);
        assert_eq!(vec![Some(f4), None, Some(f0), Some(f0), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], true, 5, 1);
        assert_eq!(vec![Some(f4), None, Some(f1), Some(f0), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], true, 5, 2);
        assert_eq!(vec![Some(f4), None, Some(f0), Some(f1), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], true, 5, 3);
        assert_eq!(vec![Some(f4), None, Some(f1), Some(f1), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], true, 5, 4);
        assert_eq!(vec![Some(f4), None, Some(f0), Some(f0), Some(f1),], p);

        // without None
        let p = SC::point(vec![], false, 4, 0);
        assert_eq!(vec![Some(f0), Some(f0), Some(f0), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], false, 5, 0);
        assert_eq!(vec![Some(f4), Some(f0), Some(f0), Some(f0), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], false, 5, 1);
        assert_eq!(vec![Some(f4), Some(f1), Some(f0), Some(f0), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], false, 5, 3);
        assert_eq!(vec![Some(f4), Some(f1), Some(f1), Some(f0), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], false, 5, 4);
        assert_eq!(vec![Some(f4), Some(f0), Some(f0), Some(f1), Some(f0),], p);

        let p = SC::point(vec![Fr::from(4_u32)], false, 5, 10);
        assert_eq!(vec![Some(f4), Some(f0), Some(f1), Some(f0), Some(f1),], p);

        let p = SC::point(vec![Fr::from(4_u32)], false, 5, 15);
        assert_eq!(vec![Some(f4), Some(f1), Some(f1), Some(f1), Some(f1),], p);

        // let p = SC::point(vec![Fr::from(4_u32)], false, 4, 16); // TODO expect error
    }

    #[test]
    fn test_partial_evaluate() {
        // g(X_0, X_1, X_2) = 2 X_0^3 + X_0 X_2 + X_1 X_2
        let terms = vec![
            (Fr::from(2u32), SparseTerm::new(vec![(0_usize, 3)])),
            (
                Fr::from(1u32),
                SparseTerm::new(vec![(0_usize, 1), (2_usize, 1)]),
            ),
            (
                Fr::from(1u32),
                SparseTerm::new(vec![(1_usize, 1), (2_usize, 1)]),
            ),
        ];
        let p = SparsePolynomial::from_coefficients_slice(3, &terms);

        type SC = SumCheck<Fr, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let e0 = SC::partial_evaluate(&p, &[Some(Fr::from(2_u32)), None, Some(Fr::from(0_u32))]);
        assert_eq!(e0.coeffs(), vec![Fr::from(16_u32)]);
        let e1 = SC::partial_evaluate(&p, &[Some(Fr::from(2_u32)), None, Some(Fr::from(1_u32))]);
        assert_eq!(e1.coeffs(), vec![Fr::from(18_u32), Fr::from(1)]);

        assert_eq!((e0 + e1).coeffs(), vec![Fr::from(34_u32), Fr::from(1)]);
    }

    #[test]
    fn test_flow_hardcoded_values() {
        let mut rng = ark_std::test_rng();
        // let p = SparsePolynomial::<Fr, SparseTerm>::rand(deg, 3, &mut rng);
        // let p = rand_poly(3, 3, &mut rng);

        // g(X_0, X_1, X_2) = 2 X_0^3 + X_0 X_2 + X_1 X_2
        let terms = vec![
            (Fr::from(2u32), SparseTerm::new(vec![(0_usize, 3)])),
            (
                Fr::from(1u32),
                SparseTerm::new(vec![(0_usize, 1), (2_usize, 1)]),
            ),
            (
                Fr::from(1u32),
                SparseTerm::new(vec![(1_usize, 1), (2_usize, 1)]),
            ),
        ];
        let p = SparsePolynomial::from_coefficients_slice(3, &terms);
        // println!("p {:?}", p);

        type SC = SumCheck<Fr, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let proof = SC::prove(p);
        assert_eq!(proof.0, Fr::from(12_u32));
        println!("proof {:?}", proof);

        let v = SC::verify(proof);
        assert!(v);
    }

    #[test]
    fn test_flow_rng() {
        let mut rng = ark_std::test_rng();
        let p = SparsePolynomial::<Fr, SparseTerm>::rand(3, 3, &mut rng);
        println!("p {:?}", p);

        type SC = SumCheck<Fr, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let proof = SC::prove(p);
        println!("proof.s len {:?}", proof.1.len());

        let v = SC::verify(proof);
        assert!(v);
    }
}
