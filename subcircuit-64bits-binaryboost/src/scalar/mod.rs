mod ristretto255;

pub type Scalar = ristretto255::Scalar;
pub type ScalarBytes = curve25519_dalek::scalar::Scalar;

pub const S_MODULUS: [u8; 32] = [
  0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

// q^{-1} in ECC
pub const Q_INV: [u8; 32] = [
  0x8e, 0x6f, 0xc3, 0xf1, 0x78, 0x23, 0xcf, 0xbc, 0x6b, 0x98, 0xde, 0x7d, 0x11, 0x5f, 0x65, 0x3a, 
  0xbf, 0x22, 0x33, 0xd9, 0xb2, 0xe6, 0x2f, 0xd5, 0x55, 0x9b, 0x17, 0x23, 0xab, 0xf2, 0x83, 0x02,
];

pub trait ScalarFromPrimitives {
  fn to_scalar(self) -> Scalar;
}

impl ScalarFromPrimitives for usize {
  #[inline]
  fn to_scalar(self) -> Scalar {
    (0..self).map(|_i| Scalar::one()).sum()
  }
}

impl ScalarFromPrimitives for bool {
  #[inline]
  fn to_scalar(self) -> Scalar {
    if self {
      Scalar::one()
    } else {
      Scalar::zero()
    }
  }
}

pub trait ScalarBytesFromScalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes;
  fn decompress_vector(s: &[Scalar]) -> Vec<ScalarBytes>;
}

impl ScalarBytesFromScalar for Scalar {
  fn decompress_scalar(s: &Scalar) -> ScalarBytes {
    ScalarBytes::from_bytes_mod_order(s.to_bytes())
  }

  fn decompress_vector(s: &[Scalar]) -> Vec<ScalarBytes> {
    (0..s.len())
      .map(|i| Scalar::decompress_scalar(&s[i]))
      .collect::<Vec<ScalarBytes>>()
  }
}
