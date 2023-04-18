use crate::pedersen;

use ark_ff::fields::PrimeField;
use core::ops::Add;

// this file contains an abstraction of R1CS struct, to later be plugged from arkworks
// ConstraintSystem or something similar.

pub struct R1CS<F: PrimeField> {
    pub A: Vec<Vec<F>>,
    pub B: Vec<Vec<F>>,
    pub C: Vec<Vec<F>>,
}

pub struct RelaxedR1CS<F: PrimeField> {
    pub ABC: R1CS<F>,
    pub u: F,
    pub E: F,
}

impl<F: PrimeField> R1CS<F> {
    pub fn relax(self) -> RelaxedR1CS<F> {
        RelaxedR1CS::<F> {
            ABC: self,
            u: F::one(),
            E: F::zero(),
        }
    }
}
impl<F: PrimeField> RelaxedR1CS<F> {
    pub fn fold(self, other: Self, r: F) -> Self {
        unimplemented!();
    }
}
