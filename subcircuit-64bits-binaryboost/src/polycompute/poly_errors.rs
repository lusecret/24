use super::polyntt_ffi;
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PolyError {
  InternalError,
  IllegalParameter,
  NttTableEmpty,
  MemoryAllocationFailure,
  OutOfNttRange,
}

impl fmt::Display for PolyError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      PolyError::InternalError => write!(f, "InternalError"),
      PolyError::IllegalParameter => write!(f, "IllegalParameter"),
      PolyError::NttTableEmpty => write!(f, "NttTableEmpty"),
      PolyError::MemoryAllocationFailure => write!(f, "MemoryAllocationFailure"),
      PolyError::OutOfNttRange => write!(f, "OutOfNttRange"),
    }
  }
}

impl PolyError {
  pub fn error_factory(value: i32) -> PolyError {
    match value {
      polyntt_ffi::ERROR => PolyError::InternalError,
      polyntt_ffi::ERROR_ILLEGAL_PARAMETER => PolyError::IllegalParameter,
      polyntt_ffi::ERROR_NTT_TABLE_EMPTY => PolyError::NttTableEmpty,
      polyntt_ffi::ERROR_MEMORY_ALLOCATION => PolyError::MemoryAllocationFailure,
      polyntt_ffi::ERROR_OUT_OF_NTT_RANGE => PolyError::OutOfNttRange,
      _ => panic!("Unknown value: {}", value),
    }
  }
}
