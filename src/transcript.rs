use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use std::marker::PhantomData;

use ark_r1cs_std::fields::fp::FpVar;

use ark_crypto_primitives::sponge::poseidon::{
    constraints::PoseidonSpongeVar, PoseidonConfig, PoseidonSponge,
};
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar, Absorb, CryptographicSponge,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

pub struct Transcript<F: PrimeField + Absorb, C: CurveGroup>
where
    <C as CurveGroup>::BaseField: Absorb,
{
    // where F is the Constraint Field (eq. C::ScalarField)
    sponge: PoseidonSponge<F>,
    _c: PhantomData<C>,
}
impl<F: PrimeField + Absorb, C: CurveGroup> Transcript<F, C>
where
    <C as CurveGroup>::BaseField: Absorb,
{
    pub fn new(poseidon_config: &PoseidonConfig<F>) -> Self {
        let sponge = PoseidonSponge::<F>::new(poseidon_config);
        Transcript {
            sponge,
            _c: PhantomData,
        }
    }
    pub fn add(&mut self, v: &F) {
        self.sponge.absorb(&v);
    }
    pub fn add_vec(&mut self, v: &[F]) {
        self.sponge.absorb(&v);
    }
    pub fn add_point(&mut self, v: &C) {
        let v_affine = v.into_affine();
        let xy = v_affine.xy().unwrap(); // WIP
        self.sponge.absorb(&vec![xy.0, xy.1]);
    }
    pub fn get_challenge(&mut self) -> F {
        let c = self.sponge.squeeze_field_elements(1);
        self.add(&c[0]);
        c[0]
    }
    pub fn get_challenge_vec(&mut self, n: usize) -> Vec<F> {
        let c = self.sponge.squeeze_field_elements(n);
        self.sponge.absorb(&c);
        c
    }
}

pub struct TranscriptVar<F: PrimeField> {
    // where F is the Constraint Field
    sponge: PoseidonSpongeVar<F>,
}
impl<F: PrimeField> TranscriptVar<F> {
    pub fn new(cs: ConstraintSystemRef<F>, poseidon_config: &PoseidonConfig<F>) -> Self {
        let sponge = PoseidonSpongeVar::<F>::new(cs, poseidon_config);
        Self { sponge }
    }
    pub fn add(&mut self, v: FpVar<F>) -> Result<(), SynthesisError> {
        self.sponge.absorb(&v)
    }
    pub fn get_challenge(&mut self) -> Result<FpVar<F>, SynthesisError> {
        let c = self.sponge.squeeze_field_elements(1)?;
        self.sponge.absorb(&c[0])?;
        Ok(c[0].clone())
    }
    pub fn get_challenge_vec(&mut self, n: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let c = self.sponge.squeeze_field_elements(n)?;
        self.sponge.absorb(&c)?;
        Ok(c)
    }
}

use ark_crypto_primitives::sponge::poseidon::find_poseidon_ark_and_mds;

// WARNING this is for test only
pub fn poseidon_test_config<F: PrimeField>() -> PoseidonConfig<F> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 5;
    let rate = 2;

    let (ark, mds) = find_poseidon_ark_and_mds::<F>(
        F::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_mnt4_298::{Fr, G1Projective}; // scalar field
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn test_transcript_and_transcriptvar() {
        let config = poseidon_test_config::<Fr>();
        let mut tr = Transcript::<Fr, G1Projective>::new(&config);
        tr.add(&Fr::from(42_u32));
        let c = tr.get_challenge();

        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut tr_var = TranscriptVar::<Fr>::new(cs.clone(), &config);
        let v = FpVar::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(42_u32))).unwrap();
        tr_var.add(v).unwrap();
        let c_var = tr_var.get_challenge().unwrap();

        assert_eq!(c, c_var.value().unwrap());
    }
}
