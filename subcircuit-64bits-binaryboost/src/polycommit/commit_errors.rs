use core::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq)]
pub enum CommitError {
  #[error("Proof verification failed")]
  InternalError,
}

impl Default for CommitError {
  fn default() -> Self {
    CommitError::InternalError
  }
}
