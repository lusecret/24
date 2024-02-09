use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq)]
pub enum GroupError {
  #[error("Schnorr Proof verification failed")]
  SchnorrProofError,
  #[error("Compressed group element failed to decompress: {0:?}")]
  DecompressionError([u8; 32]),
  #[error("fail to check e in input mapping protocl")]
  InputMappingECheckedFailed,
  #[error("fail to verifyDL in input mapping protocl")]
  InputMappingVerifyDLFailed,
}

impl Default for GroupError {
  fn default() -> Self {
    GroupError::SchnorrProofError
  }
}
