use super::groups::group_errors;
use super::polycommit::commit_errors;
use super::polycompute::poly_errors;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq)]
pub enum SubCircuitError {
  #[error("illegal parameters")]
  IllegalParameters,
  #[error("proof verification failed")]
  InternalError,
  #[error("computer subcircuit_keys failed")]
  PolyComputeError(poly_errors::PolyError),
  #[error("tau validation failed")]
  TauValidationFailed,
  #[error("input mapping protocol validation failed")]
  InputMappingValidationFailed(group_errors::GroupError),
  #[error("y1 & y2 validation failed in booleanity protocol")]
  BooleanY1Y2ValidationFailed,
  #[error("univariate polynomial protocol validation failed in booleanity protocol")]
  BooleanUniPolyValidationFailed(commit_errors::CommitError),
  #[error("a_prime & b_prime not match in boolean-subcircuit protocol")]
  BooleanAPrimeBPrimeNotMatch,
}

impl Default for SubCircuitError {
  fn default() -> Self {
    SubCircuitError::InternalError
  }
}
