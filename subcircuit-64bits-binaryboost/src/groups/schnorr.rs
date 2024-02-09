use super::super::scalar::Scalar;
use super::group::{CompressedGroup, CompressedGroupExt, GroupElement, GROUP_BASEPOINT_COMPRESSED};
use super::group_errors::GroupError;
use super::transcript::{AppendToTranscript, ProofTranscript};
use merlin::Transcript;
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

#[derive(Debug)]
pub struct Schnorr {
  pri: Scalar,
  g: GroupElement,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SchnorrProof {
  K: CompressedGroup,
  s: Scalar,
}

impl Schnorr {
  fn protocol_name() -> &'static [u8] {
    b"schnorr protocol"
  }

  pub fn new() -> Self {
    let mut csprng: OsRng = OsRng;
    Schnorr::from(
      Scalar::random(&mut csprng),
      GROUP_BASEPOINT_COMPRESSED.unpack().unwrap(),
    )
  }

  pub fn from(pri: Scalar, g: GroupElement) -> Self {
    Schnorr { pri, g }
  }

  pub fn create_pk(&self) -> CompressedGroup {
    (self.pri * self.g).compress()
  }

  pub fn prove(&self, transcript: &mut Transcript) -> SchnorrProof {
    transcript.append_protocol_name(Schnorr::protocol_name());

    let pk = self.create_pk();
    pk.append_to_transcript(b"public key", transcript);

    let mut csprng: OsRng = OsRng;
    let k = Scalar::random(&mut csprng);

    let K = (k * self.g).compress();
    K.append_to_transcript(b"point K", transcript);

    let c = transcript.challenge_scalar(b"schnorr challenge");

    SchnorrProof {
      K,
      s: self.pri * c + k,
    }
  }
}

impl SchnorrProof {
  pub fn verify(
    &self,
    pk: &CompressedGroup,
    G: &CompressedGroup,
    transcript: &mut Transcript,
  ) -> Result<(), GroupError> {
    transcript.append_protocol_name(Schnorr::protocol_name());
    pk.append_to_transcript(b"public key", transcript);
    self.K.append_to_transcript(b"point K", transcript);
    let c = transcript.challenge_scalar(b"schnorr challenge");

    let base_points: GroupElement = G.unpack().unwrap();
    let lhs = (self.s * base_points).compress();

    let rhs = (c * pk.unpack()? + self.K.unpack()?).compress();

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
    let schnorr = Schnorr::new();
    let pk = schnorr.create_pk();

    let mut prover_transcript = Transcript::new(b"unit test");
    let proof = schnorr.prove(&mut prover_transcript);

    let mut verifier_transcript = Transcript::new(b"unit test");
    assert!(proof
      .verify(&pk, &schnorr.g.compress(), &mut verifier_transcript)
      .is_ok());
  }
}
