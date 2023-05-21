use ark_ff::fields::PrimeField;

use crate::nifs::R1CS;
use crate::utils::{hadamard_product, matrix_vector_product, vec_add, vector_elem_product};

pub struct CCS<F: PrimeField> {
    pub m: usize,
    pub n: usize,
    pub t: usize,
    pub q: usize,
    pub d: usize,
    pub S: Vec<Vec<usize>>,
    pub c: Vec<F>,
    pub M: Vec<Vec<Vec<F>>>,
}

impl<F: PrimeField> R1CS<F> {
    pub fn to_ccs(self) -> CCS<F> {
        CCS::<F> {
            m: self.A.len(),
            n: self.A[0].len(),
            t: 3,
            q: 2,
            d: 2,
            S: vec![vec![0, 1], vec![2]],
            c: vec![F::one(), F::one().neg()],
            M: vec![self.A, self.B, self.C],
        }
    }
}

impl<F: PrimeField> CCS<F> {
    pub fn check_relation(self, z: Vec<F>) -> bool {
        let mut r: Vec<F> = vec![F::zero(); self.m];
        for i in 0..self.q {
            let mut hadamard_output = vec![F::one(); self.m];
            for j in self.S[i].clone() {
                hadamard_output =
                    hadamard_product(hadamard_output, matrix_vector_product(&self.M[j], &z));
            }
            r = vec_add(&r, &vector_elem_product(&hadamard_output, &self.c[i]));
        }

        let zero: Vec<F> = vec![F::zero(); self.m];

        r == zero
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transcript::poseidon_test_config;
    use ark_mnt4_298::{Fr, G1Projective};
    use ark_std::One;
    use ark_std::UniformRand;

    use crate::nifs::gen_test_values;

    #[test]
    fn test_r1cs_to_ccs() {
        let (r1cs, ws, _) = gen_test_values(2);
        let w: Vec<Fr> = ws[0].clone();

        let ccs = r1cs.to_ccs();

        assert!(ccs.check_relation(w));
    }
}
