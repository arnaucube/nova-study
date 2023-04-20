use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use merlin::Transcript as MerlinTranscript;
use std::marker::PhantomData;

// This Transcript approach is a modified version from https://github.com/arkworks-rs/gemini ,
// using Merlin transcript (https://merlin.cool).
pub struct Transcript<F: PrimeField> {
    phantom: PhantomData<F>,
    transcript: MerlinTranscript,
}

impl<F: PrimeField> Transcript<F> {
    pub fn new() -> Self {
        Self {
            phantom: PhantomData::default(),
            transcript: MerlinTranscript::new(b"transcript"),
        }
    }
    pub fn add<S: CanonicalSerialize>(&mut self, label: &'static [u8], r: &S) {
        let mut msg = Vec::new();
        r.serialize_uncompressed(&mut msg).unwrap();
        self.transcript.append_message(label, &msg);
    }
    pub fn get_challenge(&mut self, label: &'static [u8]) -> F {
        let mut bytes = [0u8; 64];
        self.transcript.challenge_bytes(label, &mut bytes);
        let challenge = F::from_le_bytes_mod_order(bytes.as_ref());
        self.add(b"get challenge", &challenge);
        challenge
    }
    pub fn get_challenge_vec(&mut self, label: &'static [u8], n: usize) -> Vec<F> {
        let mut c: Vec<F> = vec![F::zero(); n];
        for i in 0..n {
            c[i] = self.get_challenge(label);
        }
        c
    }
}
