use super::super::scalar::Scalar;
use super::group::{
  CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul,
  GROUP_BASEPOINT_COMPRESSED,
};
use super::group_errors::GroupError;
use super::transcript::{AppendToTranscript, ProofTranscript};
use digest::{ExtendableOutput, Input};
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};
use sha3::Shake256;
use std::io::Read;

#[derive(Debug)]
pub struct ExtendedSchnorrGens {
  pub g1: GroupElement,
  pub g2: GroupElement,
}

impl ExtendedSchnorrGens {
  pub fn new(label: &[u8]) -> Self {
    let g1 = ExtendedSchnorrGens::generate_group_element(label, GROUP_BASEPOINT_COMPRESSED);
    let g2 = ExtendedSchnorrGens::generate_group_element(label, g1.compress());
    ExtendedSchnorrGens::from(g1, g2)
  }

  pub fn from(g1: GroupElement, g2: GroupElement) -> Self {
    ExtendedSchnorrGens { g1, g2 }
  }

  fn generate_group_element(label: &[u8], G: CompressedGroup) -> GroupElement {
    let mut shake = Shake256::default();
    shake.input(label);
    shake.input(G.as_bytes());

    let mut reader = shake.xof_result();
    let mut g_bytes = [0u8; 64];
    reader.read_exact(&mut g_bytes).unwrap();
    GroupElement::from_uniform_bytes(&g_bytes)
  }
}

#[derive(Debug)]
pub struct ExtendedSchnorr<'a> {
  alpha: Scalar,
  beta: Scalar,
  gens: &'a ExtendedSchnorrGens,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ExtendedSchnorrProof {
  R: CompressedGroup,
  s1: Scalar,
  s2: Scalar,
}

impl<'a> ExtendedSchnorr<'a> {
  fn protocol_name() -> &'static [u8] {
    b"extended schnorr protocol"
  }

  pub fn new(gens: &'a ExtendedSchnorrGens) -> Self {
    let mut csprng: OsRng = OsRng;
    ExtendedSchnorr::from(
      Scalar::random(&mut csprng),
      Scalar::random(&mut csprng),
      gens,
    )
  }

  pub fn from(alpha: Scalar, beta: Scalar, gens: &'a ExtendedSchnorrGens) -> Self {
    ExtendedSchnorr {
      alpha: alpha,
      beta: beta,
      gens: gens,
    }
  }

  pub fn create_pk(&self) -> CompressedGroup {
    GroupElement::vartime_multiscalar_mul(&[self.alpha, self.beta], &[self.gens.g1, self.gens.g2])
      .compress()
  }

  pub fn prove(&self, transcript: &mut Transcript) -> ExtendedSchnorrProof {
    transcript.append_protocol_name(ExtendedSchnorr::protocol_name());

    let pk = self.create_pk();
    pk.append_to_transcript(b"public key", transcript);

    let mut csprng: OsRng = OsRng;
    let delta = Scalar::random(&mut csprng);
    let epsilon = Scalar::random(&mut csprng);

    let R = GroupElement::vartime_multiscalar_mul(&[delta, epsilon], &[self.gens.g1, self.gens.g2])
      .compress();
    R.append_to_transcript(b"point R", transcript);

    let c = transcript.challenge_scalar(b"extended schnorr challenge");

    ExtendedSchnorrProof {
      R: R,
      s1: self.alpha * c + delta,
      s2: self.beta * c + epsilon,
    }
  }
}

impl ExtendedSchnorrProof {
  pub fn verify(
    &self,
    pk: &CompressedGroup,
    gens: &ExtendedSchnorrGens,
    transcript: &mut Transcript,
  ) -> Result<(), GroupError> {
    transcript.append_protocol_name(ExtendedSchnorr::protocol_name());
    pk.append_to_transcript(b"public key", transcript);
    self.R.append_to_transcript(b"point R", transcript);
    let c = transcript.challenge_scalar(b"extended schnorr challenge");

    let lhs = (c * pk.unpack()? + self.R.unpack()?).compress();
    let rhs =
      GroupElement::vartime_multiscalar_mul(&[self.s1, self.s2], &[gens.g1, gens.g2]).compress();

    if lhs == rhs {
      Ok(())
    } else {
      Err(GroupError::SchnorrProofError)
    }
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  #[test]
  fn test_EDL() {
    let gens = ExtendedSchnorrGens::new(b"test EDL");
    let pri = ExtendedSchnorr::new(&gens);
    let pk = pri.create_pk();

    let mut prover_transcript = Transcript::new(b"unit test");
    let proof = pri.prove(&mut prover_transcript);

    let mut verifier_transcript = Transcript::new(b"unit test");
    assert!(proof.verify(&pk, &gens, &mut verifier_transcript).is_ok());
  }
}
