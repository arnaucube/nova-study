// this file contains a sum-check protocol initial implementation, not used by the rest of the repo
// but implemented as an exercise and it will probably be used in the future.

use ark_ec::CurveGroup;
use ark_ff::{BigInteger, PrimeField};
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm, Term},
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
};
use ark_std::log2;
use ark_std::marker::PhantomData;

use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};

use crate::transcript::Transcript;

pub struct SumCheck<
    F: PrimeField + Absorb,
    C: CurveGroup,
    UV: Polynomial<F> + DenseUVPolynomial<F>,
    MV: Polynomial<F> + DenseMVPolynomial<F>,
> {
    _f: PhantomData<F>,
    _c: PhantomData<C>,
    _uv: PhantomData<UV>,
    _mv: PhantomData<MV>,
}

impl<
        F: PrimeField + Absorb,
        C: CurveGroup,
        UV: Polynomial<F> + DenseUVPolynomial<F>,
        MV: Polynomial<F> + DenseMVPolynomial<F>,
    > SumCheck<F, C, UV, MV>
where
    <C as CurveGroup>::BaseField: Absorb,
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
                            new_coef *= v.pow([(*power) as u64]);
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
        let mut r = vec![F::zero(); n_elems];
        for i in 0..n_elems {
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
                panic!("err"); // or return directly challenges vector
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
            let bit = k[i / 8] & (1 << (i % 8));
            if bit == 0 {
                p[none_pos + i] = Some(F::zero());
            } else {
                p[none_pos + i] = Some(F::one());
            }
        }
        p
    }

    pub fn prove(poseidon_config: &PoseidonConfig<F>, g: MV) -> (F, Vec<UV>, F)
    where
        <MV as Polynomial<F>>::Point: From<Vec<F>>,
    {
        // init transcript
        let mut transcript = Transcript::<F, C>::new(poseidon_config);

        let v = g.num_vars();

        // compute H
        let mut H = F::zero();
        for i in 0..(2_u64.pow(v as u32) as usize) {
            let p = Self::point_complete(vec![], v, i);

            H += g.evaluate(&p.into());
        }
        transcript.add(&H);

        let mut ss: Vec<UV> = Vec::new();
        let mut r: Vec<F> = vec![];
        for i in 0..v {
            let r_i = transcript.get_challenge();
            r.push(r_i);

            let var_slots = v - 1 - i;
            let n_points = 2_u64.pow(var_slots as u32) as usize;

            let mut s_i = UV::zero();
            for j in 0..n_points {
                let point = Self::point(r[..i].to_vec(), true, v, j);
                s_i = s_i + Self::partial_evaluate(&g, &point);
            }
            transcript.add_vec(s_i.coeffs());
            ss.push(s_i);
        }

        let last_g_eval = g.evaluate(&r.into());
        (H, ss, last_g_eval)
    }

    pub fn verify(poseidon_config: &PoseidonConfig<F>, proof: (F, Vec<UV>, F)) -> bool {
        // init transcript
        let mut transcript = Transcript::<F, C>::new(poseidon_config);
        transcript.add(&proof.0);

        let (c, ss, last_g_eval) = proof;

        let mut r: Vec<F> = vec![];
        for (i, s) in ss.iter().enumerate() {
            // TODO check degree
            if i == 0 {
                if c != s.evaluate(&F::zero()) + s.evaluate(&F::one()) {
                    return false;
                }
                let r_i = transcript.get_challenge();
                r.push(r_i);
                transcript.add_vec(s.coeffs());
                continue;
            }

            let r_i = transcript.get_challenge();
            r.push(r_i);
            if ss[i - 1].evaluate(&r[i - 1]) != s.evaluate(&F::zero()) + s.evaluate(&F::one()) {
                return false;
            }
            transcript.add_vec(s.coeffs());
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
    use crate::transcript::poseidon_test_config;
    use ark_mnt4_298::{Fr, G1Projective}; // scalar field
    use ark_poly::{
        multivariate::{SparsePolynomial, SparseTerm, Term},
        univariate::DensePolynomial,
        DenseMVPolynomial, DenseUVPolynomial,
    };
    use ark_std::{rand::Rng, UniformRand};

    #[test]
    fn test_new_point() {
        let f4 = Fr::from(4_u32);
        let f1 = Fr::from(1);
        let f0 = Fr::from(0);
        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

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

        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let e0 = SC::partial_evaluate(&p, &[Some(Fr::from(2_u32)), None, Some(Fr::from(0_u32))]);
        assert_eq!(e0.coeffs(), vec![Fr::from(16_u32)]);
        let e1 = SC::partial_evaluate(&p, &[Some(Fr::from(2_u32)), None, Some(Fr::from(1_u32))]);
        assert_eq!(e1.coeffs(), vec![Fr::from(18_u32), Fr::from(1)]);

        assert_eq!((e0 + e1).coeffs(), vec![Fr::from(34_u32), Fr::from(1)]);
    }

    #[test]
    fn test_flow_hardcoded_values() {
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

        let poseidon_config = poseidon_test_config::<Fr>();
        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let proof = SC::prove(&poseidon_config, p);
        assert_eq!(proof.0, Fr::from(12_u32));
        // println!("proof {:?}", proof);

        let v = SC::verify(&poseidon_config, proof);
        assert!(v);
    }

    fn rand_poly<R: Rng>(l: usize, d: usize, rng: &mut R) -> SparsePolynomial<Fr, SparseTerm> {
        // This method is from the arkworks/algebra/poly/multivariate test:
        // https://github.com/arkworks-rs/algebra/blob/bc991d44c5e579025b7ed56df3d30267a7b9acac/poly/src/polynomial/multivariate/sparse.rs#L303
        let mut random_terms = Vec::new();
        let num_terms = rng.gen_range(1..1000);
        // For each term, randomly select up to `l` variables with degree
        // in [1,d] and random coefficient
        random_terms.push((Fr::rand(rng), SparseTerm::new(vec![])));
        for _ in 1..num_terms {
            let term = (0..l)
                .map(|i| {
                    if rng.gen_bool(0.5) {
                        Some((i, rng.gen_range(1..(d + 1))))
                    } else {
                        None
                    }
                })
                .flatten()
                .collect();
            let coeff = Fr::rand(rng);
            random_terms.push((coeff, SparseTerm::new(term)));
        }
        SparsePolynomial::from_coefficients_slice(l, &random_terms)
    }

    #[test]
    fn test_flow_rng() {
        let mut rng = ark_std::test_rng();
        // let p = SparsePolynomial::<Fr, SparseTerm>::rand(3, 3, &mut rng);
        let p = rand_poly(3, 3, &mut rng);
        // println!("p {:?}", p);

        let poseidon_config = poseidon_test_config::<Fr>();
        type SC = SumCheck<Fr, G1Projective, DensePolynomial<Fr>, SparsePolynomial<Fr, SparseTerm>>;

        let proof = SC::prove(&poseidon_config, p);
        // println!("proof.s len {:?}", proof.1.len());

        let v = SC::verify(&poseidon_config, proof);
        assert!(v);
    }
}
