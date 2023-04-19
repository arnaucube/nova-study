use ark_ec::AffineRepr;
use ark_ff::fields::PrimeField;
use core::ops::{Add, Sub};
use std::fmt;

pub fn vector_elem_product<F: PrimeField>(a: &Vec<F>, e: &F) -> Vec<F> {
    // maybe move this method to operator a * e
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] * e;
    }
    r
}
pub fn matrix_vector_product<F: PrimeField>(M: &Vec<Vec<F>>, z: &Vec<F>) -> Vec<F> {
    // TODO assert len
    let mut r: Vec<F> = vec![F::zero(); M.len()];
    for i in 0..M.len() {
        for j in 0..M[i].len() {
            r[i] += M[i][j] * z[j];
        }
    }
    r
}
pub fn hadamard_product<F: PrimeField>(a: Vec<F>, b: Vec<F>) -> Vec<F> {
    // maybe move this method to operator a * b
    // TODO assert equals len
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] * b[i];
    }
    r
}

// rlin: random linear combination
// pub fn rlin<F: PrimeField>(a: Vec<F>, b: Vec<F>, r: F) -> Vec<F> {
//     vec_add(a, vector_elem_product(&b, &r)) // WIP probably group loops
// }

pub fn naive_msm<C: AffineRepr>(s: &Vec<C::ScalarField>, p: &Vec<C>) -> C {
    // TODO check lengths, or at least check s.len()>= p.len()

    let mut r = p[0].mul(s[0]);
    for i in 1..s.len() {
        r = p[i].mul(s[i]);
    }
    r.into()
}

pub fn vec_add<F: PrimeField>(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] + b[i];
    }
    r
}
pub fn vec_sub<F: PrimeField>(a: Vec<F>, b: Vec<F>) -> Vec<F> {
    let mut r: Vec<F> = vec![F::zero(); a.len()];
    for i in 0..a.len() {
        r[i] = a[i] - b[i];
    }
    r
}

// instead of vec_{add/sub} can use Ve wrapper which has '+', '-' operators
#[derive(Debug, Clone, PartialEq)]
pub struct Ve<F: PrimeField>(pub Vec<F>);

impl<F: PrimeField> fmt::Display for Ve<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, e) in self.0.iter().enumerate() {
            if i == self.0.len() - 1 {
                write!(f, "{}", e)?;
                break;
            }
            write!(f, "{}, ", e)?;
        }
        Ok(())
    }
}

impl<F: PrimeField> Add<Ve<F>> for Ve<F> {
    type Output = Ve<F>;
    fn add(self, rhs_vec: Self) -> Ve<F> {
        let lhs = self.0.clone();
        let rhs = rhs_vec.0.clone();
        let mut r: Vec<F> = vec![F::zero(); lhs.len()];
        for i in 0..self.0.len() {
            r[i] = lhs[i] + rhs[i];
        }
        Ve(r)
    }
}
impl<F: PrimeField> Sub<Ve<F>> for Ve<F> {
    type Output = Ve<F>;
    fn sub(self, rhs_vec: Self) -> Ve<F> {
        let lhs = self.0.clone();
        let rhs = rhs_vec.0.clone();
        let mut r: Vec<F> = vec![F::zero(); lhs.len()];
        for i in 0..self.0.len() {
            r[i] = lhs[i] - rhs[i];
        }
        Ve(r)
    }
}

pub fn to_F_matrix<F: PrimeField>(M: Vec<Vec<usize>>) -> Vec<Vec<F>> {
    let mut R: Vec<Vec<F>> = vec![Vec::new(); M.len()];
    for i in 0..M.len() {
        R[i] = vec![F::zero(); M[i].len()];
        for j in 0..M[i].len() {
            R[i][j] = F::from(M[i][j] as u64);
        }
    }
    R
}
pub fn to_F_vec<F: PrimeField>(z: Vec<usize>) -> Vec<F> {
    let mut r: Vec<F> = vec![F::zero(); z.len()];
    for i in 0..z.len() {
        r[i] = F::from(z[i] as u64);
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{g1::G1Affine, Fr};
    use ark_ec::CurveGroup;
    use ark_std::{One, Zero};
    use std::ops::Mul;

    #[test]
    fn test_matrix_vector_product() {
        let A = to_F_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let z = to_F_vec(vec![1, 3, 35, 9, 27, 30]);
        let Az = matrix_vector_product(&A, &z);
        assert_eq!(Az, to_F_vec(vec![3, 9, 30, 35]));
    }

    #[test]
    fn test_hadamard_product() {
        let a = to_F_vec::<Fr>(vec![1, 2, 3, 4, 5, 6]);
        let b = to_F_vec(vec![7, 8, 9, 10, 11, 12]);
        assert_eq!(
            hadamard_product(a, b),
            to_F_vec(vec![7, 16, 27, 40, 55, 72])
        );
    }
    #[test]
    fn test_vec_add() {
        let a: Vec<Fr> = to_F_vec::<Fr>(vec![1, 2, 3, 4, 5, 6]);
        let b: Vec<Fr> = to_F_vec(vec![7, 8, 9, 10, 11, 12]);
        assert_eq!(vec_add(&a, &b), (Ve(a) + Ve(b)).0);
    }

    #[test]
    fn test_ABC_hadamard() {
        let A = to_F_matrix::<Fr>(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 1, 0, 0, 1, 0],
            vec![5, 0, 0, 0, 0, 1],
        ]);
        let B = to_F_matrix(vec![
            vec![0, 1, 0, 0, 0, 0],
            vec![0, 1, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
            vec![1, 0, 0, 0, 0, 0],
        ]);
        let C = to_F_matrix(vec![
            vec![0, 0, 0, 1, 0, 0],
            vec![0, 0, 0, 0, 1, 0],
            vec![0, 0, 0, 0, 0, 1],
            vec![0, 0, 1, 0, 0, 0],
        ]);
        let z = to_F_vec(vec![1, 3, 35, 9, 27, 30]);

        let Az = matrix_vector_product(&A, &z);
        let Bz = matrix_vector_product(&B, &z);
        let Cz = matrix_vector_product(&C, &z);
        assert_eq!(hadamard_product(Az, Bz), Cz);
    }
}
