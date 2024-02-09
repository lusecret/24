#![allow(non_snake_case)]
extern crate libc;

use libc::{c_int, c_uint, c_ulonglong};

use crate::scalar::Scalar;

pub const SUCCESS: i32 = 0;
pub const ERROR: i32 = -1;
pub const ERROR_ILLEGAL_PARAMETER: i32 = -2;
pub const ERROR_NTT_TABLE_EMPTY: i32 = -3;
pub const ERROR_MEMORY_ALLOCATION: i32 = -4;
pub const ERROR_OUT_OF_NTT_RANGE: i32 = -5;

#[repr(C)]
pub struct RPoly {
  pub coef: *mut c_ulonglong,
  pub len: c_uint,
}

impl RPoly {
  pub fn from(c: &[u64]) -> Self {
    let mut coef_vec: Vec<u64> = Vec::with_capacity(c.len());

    for item in c {
      coef_vec.push(*item);
    }
    let boxed_slice: Box<[u64]> = coef_vec.into_boxed_slice();
    let raw_ptr = Box::into_raw(boxed_slice) as *mut u64;
    RPoly {
      coef: raw_ptr,
      len: c.len() as c_uint,
    }
  }

  pub fn new(capacity: usize) -> Self {
    let vec: Vec<u64> = vec![0; capacity];
    RPoly::from(&vec[..])
  }

  pub fn get_coef(&self, index: usize) -> Option<u64> {
    if index < (self.len as usize) {
      unsafe { Some(*self.coef.add(index)) }
    } else {
      None
    }
  }

  pub fn to_vec(&self) -> Vec<u64> {
    unsafe {
      let coef_slice = std::slice::from_raw_parts(self.coef, self.len as usize);
      let coef_vec: Vec<u64> = coef_slice.to_vec();
      coef_vec
    }
  }
}

pub trait U64ToScalar {
  fn to_scalar(&self) -> Vec<Scalar>;
}

impl U64ToScalar for Vec<u64> {
  fn to_scalar(&self) -> Vec<Scalar> {
    let mut s: Vec<Scalar> = Vec::new();
    for val in self.iter() {
      s.push(Scalar::from_raw([*val, 0, 0, 0]));
    }
    s
  }
}

#[link(name = "polyntt64bits")]
extern "C" {

  fn init_ntt_table() -> c_int;

  fn destroy_ntt_table();

  fn poly_mul_eval(
    ins: *const RPoly,
    poly_nums: c_uint,
    outp: *mut RPoly,
    x: c_ulonglong,
    y_prime: *mut c_ulonglong,
  ) -> i32;

  fn poly_mul_all(ins: *const RPoly, poly_nums: c_uint, outp: *mut RPoly) -> i32;

}

pub fn rust_init_ntt_table() -> i32 {
  unsafe { init_ntt_table() }
}

pub fn rust_destroy_ntt_table() {
  unsafe { destroy_ntt_table() }
}

pub fn rust_poly_mul_eval(
  ins: *const RPoly,
  poly_nums: u32,
  outp: *mut RPoly,
  x: u64,
  y_prime: &mut u64,
) -> i32 {
  unsafe { poly_mul_eval(ins, poly_nums, outp, x, y_prime as *mut u64) }
}

pub fn rust_poly_mul_all(ins: *const RPoly, poly_nums: u32, outp: *mut RPoly) -> i32 {
  unsafe { poly_mul_all(ins, poly_nums, outp) }
}

#[cfg(test)]
mod tests {

  use super::super::polyntt_ffi::*;

  #[test]
  fn test_correctness_of_poly_multiplication() {
    assert_eq!(SUCCESS, rust_init_ntt_table());

    let exp: [[u64; 3]; 2] = [
      [0x1eee11, 0x135f948, 0x4a35ed38],
      [0x0ce394e60d2b52c0, 0x0656e62fc437cea0, 0x1532f65622a98019],
    ];

    let ploy_nums: [u32; 2] = [8, 1024];

    for i in 0..ploy_nums.len() {
      let mut ployins: Vec<RPoly> = Vec::new();
      let ploy_num: u32 = ploy_nums[i];

      let mut co: u64 = 1;
      for _ in 0..ploy_num {
        let coffs: Vec<u64> = vec![co, co + 1];
        co += 2;
        ployins.push(RPoly::from(&coffs[..]));
      }

      let out_coff_num = 2 << (ploy_num.ilog2());
      let mut ployout: RPoly = RPoly::new(out_coff_num);

      let x = 1;
      let mut gamma = 0;

      let ret = rust_poly_mul_eval(ployins.as_ptr(), ploy_num, &mut ployout, x, &mut gamma);
      assert_eq!(SUCCESS, ret);
      assert_eq!((out_coff_num >> 1) + 1, ployout.len as usize);
      assert_eq!(ployout.get_coef(0).unwrap(), exp[i][0]);
      assert_eq!(ployout.get_coef(1).unwrap(), exp[i][1]);
      assert_eq!(gamma, exp[i][2]);
    }

    rust_destroy_ntt_table();
  }
}
