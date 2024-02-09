pub mod poly_errors;
pub mod polyntt_ffi;

use poly_errors::PolyError;
use polyntt_ffi::*;

use lazy_static::lazy_static;

lazy_static! {
  pub static ref POLYCOMPUTER: PolyComputer = PolyComputer::new();
}

pub struct PolyComputer {}

#[derive(Debug)]
pub struct SubCircuitKeys {
  pub r: u64,
  pub epsilon: u64,
  pub tau_vec: Vec<u64>,
}

impl PolyComputer {
  fn new() -> Self {
    let ret = rust_init_ntt_table();
    if SUCCESS != ret {
      panic!("sub circuit init error: {}", PolyError::error_factory(ret));
    };

    PolyComputer {}
  }

  pub fn computer_subcircuit_keys(
    &self,
    a_vec: &[u64],
    alpha_vec: &[u64],
  ) -> Result<SubCircuitKeys, PolyError> {
    if a_vec.len() == 0 || a_vec.len() != alpha_vec.len() {
      return Err(PolyError::IllegalParameter);
    }

    let ployins: Vec<RPoly> = a_vec
      .into_iter()
      .zip(alpha_vec.into_iter())
      .map(|(&a, &alpha)| RPoly::from(&[a, alpha]))
      .collect();

    let ploy_num = ployins.len();
    let out_coff_num = 2 << (ploy_num.ilog2());
    let mut ployout: RPoly = RPoly::new(out_coff_num as usize);

    let ret = rust_poly_mul_all(ployins.as_ptr(), ploy_num as u32, &mut ployout);
    if SUCCESS != ret {
      return Err(PolyError::error_factory(ret));
    };

    let coefs = ployout.to_vec();

    return Ok(SubCircuitKeys {
      r: *coefs.get(0).unwrap(),
      epsilon: *coefs.get(1).unwrap(),
      tau_vec: coefs[2..].to_vec(),
    });
  }

  fn drop(&mut self) {
    rust_destroy_ntt_table();
  }
}

#[cfg(test)]
mod tests {

  use super::super::montgomery::random64_mod;
  use rand::rngs::OsRng;

  use super::POLYCOMPUTER;

  #[test]
  fn test_computer_subcircuit_keys() {
    const DEFAULT_SIZE: usize = 1024;
    let mut csprng: OsRng = OsRng;

    let a: Vec<u64> = vec![27; DEFAULT_SIZE];
    let alpha: Vec<u64> = (0..DEFAULT_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();

    let ret = POLYCOMPUTER
      .computer_subcircuit_keys(a.as_slice(), alpha.as_slice())
      .unwrap();

    let exp: u64 = 756068593914473144;
    assert_eq!(exp, ret.r);
  }
}
