use crate::montgomery;

use super::super::scalar::{Scalar, S_MODULUS};
use super::group::{
  CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul,
  GROUP_BASEPOINT_COMPRESSED,
};
use super::group_errors::GroupError;
use super::transcript::ProofTranscript;
use merlin::Transcript;
use rand::rngs::OsRng;

use digest::{ExtendableOutput, Input};
use num_bigint::BigUint;
use sha3::Shake256;
use std::io::Read;

use super::schnorr::{Schnorr, SchnorrProof};

#[derive(Debug)]
pub struct InputMappingSystem {
  g: GroupElement,
  h: GroupElement,
}

#[derive(Debug)]
pub struct InputMappingSetup {
  pub alpha: Vec<u64>,
  pub omega: Vec<Scalar>,
  pub S: Vec<CompressedGroup>,
  pub T: Vec<CompressedGroup>,
}

#[derive(Debug, PartialEq)]
pub struct InputMappingInternalProof {
  pub e_vec: Vec<BigUint>,
  pub tr: SchnorrProof,
}

#[derive(Debug)]
pub struct InputMappingProof {
  S: Vec<CompressedGroup>,
  T: Vec<CompressedGroup>,
  a_prime: Vec<u64>,
  in_proof: InputMappingInternalProof,
}

impl InputMappingSystem {
  pub fn new(label: &[u8]) -> Self {
    let mut shake = Shake256::default();
    shake.input(label);
    shake.input(GROUP_BASEPOINT_COMPRESSED.as_bytes());

    let mut reader = shake.xof_result();
    let mut g_bytes = [0u8; 64];

    reader.read_exact(&mut g_bytes).unwrap();

    Self::from(
      GROUP_BASEPOINT_COMPRESSED.unpack().unwrap(),
      GroupElement::from_uniform_bytes(&g_bytes),
    )
  }

  pub fn from(g: GroupElement, h: GroupElement) -> Self {
    InputMappingSystem { g, h }
  }

  fn protocol_name() -> &'static [u8] {
    b"input mapping protocol"
  }

  pub fn compute_pederson(&self, a_vec: &Vec<u64>, v_vec: &Vec<Scalar>) -> Vec<CompressedGroup> {
    a_vec
      .iter()
      .zip(v_vec)
      .map(|(a, v)| {
        let a_s = Scalar::from(*a);
        (a_s * self.g + v * self.h).compress()
      })
      .collect()
  }

  pub fn setup_from(&self, v_vec: &Vec<Scalar>, alpha: &Vec<u64>) -> InputMappingSetup {
    let n: usize = v_vec.len();
    let mut csprng: OsRng = OsRng;

    let omega: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut csprng)).collect();

    let q = Scalar::from(montgomery::get_Q());

    let S: Vec<CompressedGroup> = omega
      .iter()
      .map(|o| {
        let r = q * o;
        (r * self.g).compress()
      })
      .collect();

    let T: Vec<CompressedGroup> = v_vec
      .iter()
      .zip(alpha)
      .map(|(vi, alpha_i)| {
        let alpha_s = Scalar::from(*alpha_i);
        let r = vi - alpha_s;
        (r * self.g).compress()
      })
      .collect();

    InputMappingSetup {
      alpha: alpha.clone(),
      omega,
      S,
      T,
    }
  }

  fn setup(&self, v_vec: &Vec<Scalar>) -> InputMappingSetup {
    let n: usize = v_vec.len();
    let mut csprng: OsRng = OsRng;

    let alpha: Vec<u64> = (0..n)
      .map(|_| montgomery::random64_mod(&mut csprng))
      .collect();
    self.setup_from(v_vec, &alpha)
  }

  fn generate_transformed_inputs(
    &self,
    a_vec: &Vec<u64>,
    alpha_vec: &Vec<u64>,
    x: u64,
  ) -> Vec<u64> {
    let xm = montgomery::enter_mont(x);

    a_vec
      .into_iter()
      .zip(alpha_vec)
      .map(|(a, alpha)| {
        let am = montgomery::enter_mont(*a);
        let alpham = montgomery::enter_mont(*alpha);
        let mut alpha_xm = montgomery::mont_mul_mod(xm, alpham);
        alpha_xm = am + alpha_xm;

        montgomery::back_from_mont(alpha_xm)
      })
      .collect()
  }

  fn compute_e(
    &self,
    a_vec: Vec<u64>,
    alpha_vec: Vec<u64>,
    omega_vec: Vec<Scalar>,
    x: u64,
  ) -> Vec<BigUint> {
    let xm = montgomery::enter_mont(x);

    let xalpha_vec: Vec<u64> = alpha_vec
      .iter()
      .map(|alpha| {
        let alpham = montgomery::enter_mont(*alpha);
        let x_alpham = montgomery::mont_mul_mod(xm, alpham);
        montgomery::back_from_mont(x_alpham)
      })
      .collect();

    let n: usize = a_vec.len();
    let mut e_vec: Vec<BigUint> = Vec::new();

    for i in 0..n {
      let alphas = BigUint::from(alpha_vec[i]);
      let x_alphas = BigUint::from(xalpha_vec[i]);

      let omegas = BigUint::from_bytes_le(&omega_vec[i].to_bytes());

      let xs: BigUint = BigUint::from(x);
      let qs: BigUint = BigUint::from(montgomery::get_Q());

      let mut ei = omegas * &qs + x_alphas * &xs;
      ei = ei - &xs * alphas * &xs;

      if (a_vec[i] + xalpha_vec[i]) > montgomery::get_Q() {
        ei = ei - qs * &xs;
      }
      e_vec.push(ei);
    }

    e_vec
  }

  fn transfer_e_scalar(&self, e_vec: &Vec<BigUint>) -> Vec<Scalar> {
    let s_module: BigUint = BigUint::from_bytes_le(&S_MODULUS);

    let n: usize = e_vec.len();
    let mut es_vec: Vec<Scalar> = Vec::new();
    for i in 0..n {
      let es = &e_vec[i] % &s_module;
      let data = es.to_bytes_le();

      let array_ref: [u8; 32] = {
        let a_slice = data.as_slice();

        let mut array: [u8; 32] = [0; 32];
        array[..a_slice.len()].copy_from_slice(a_slice);
        array
      };
      es_vec.push(Scalar::from_bytes(&array_ref).unwrap());
    }

    es_vec
  }

  fn compute_k_pow(&self, e_vec: &Vec<Scalar>, transcript: &mut Transcript) -> Vec<Scalar> {
    e_vec.iter().enumerate().for_each(|(_, ei)| {
      transcript.append_scalar(b"scalar e", ei);
    });

    let k = transcript.challenge_scalar(b"input mapping challenge k");

    let k_vec: Vec<Scalar> = (0..e_vec.len())
      .scan(Scalar::one(), |acc, _| {
        *acc = *acc * k;
        Some(*acc)
      })
      .collect();

    k_vec
  }

  pub fn internal_prove(
    &self,
    a_vec: Vec<u64>,
    v_vec: Vec<Scalar>,
    alpha_vec: Vec<u64>,
    omega_vec: Vec<Scalar>,
    x: u64,
    transcript: &mut Transcript,
  ) -> InputMappingInternalProof {
    let eb_vec: Vec<BigUint> = self.compute_e(a_vec, alpha_vec, omega_vec, x);

    let es_vec: Vec<Scalar> = self.transfer_e_scalar(&eb_vec);

    let k_vec: Vec<Scalar> = self.compute_k_pow(&es_vec, transcript);

    let xs: Scalar = Scalar::from(x);

    let mut vt: Scalar = v_vec.into_iter().zip(k_vec).map(|(v, k)| v * k).sum();
    vt = vt * xs;

    let h_gx = self.h - xs * self.g;
    let schnorr = Schnorr::from(vt, h_gx);

    InputMappingInternalProof {
      e_vec: eb_vec,
      tr: schnorr.prove(transcript),
    }
  }

  pub fn internal_verify(
    &self,
    a_prime: Vec<u64>,
    in_proof: &InputMappingInternalProof,
    S: &Vec<CompressedGroup>,
    T: &Vec<CompressedGroup>,
    P: Vec<CompressedGroup>,
    x: u64,
    transcript: &mut Transcript,
  ) -> Result<(), GroupError> {
    // 1. check e_vec:
    let Qbig: BigUint = BigUint::from(montgomery::get_Q());
    let zero: BigUint = BigUint::from(0 as u32);

    let n: usize = in_proof.e_vec.len();
    for i in 0..n {
      let ybig: BigUint = &in_proof.e_vec[i] % &Qbig;
      if ybig != zero {
        return Err(GroupError::InputMappingECheckedFailed);
      }
    }

    let es_vec: Vec<Scalar> = self.transfer_e_scalar(&in_proof.e_vec);

    // 2. check Schnorr Protocol:
    let k_vec: Vec<Scalar> = self.compute_k_pow(&es_vec, transcript);
    let xs: Scalar = Scalar::from(x);
    let xs2: Scalar = xs * xs;

    let as_prime: Vec<Scalar> = a_prime.into_iter().map(|a| Scalar::from(a)).collect();

    let mut pk_vt: Vec<GroupElement> = Vec::new();
    for i in 0..n {
      let aprime_x_e = es_vec[i] - as_prime[i] * xs; // negtive
      let s_vec: Vec<Scalar> = vec![xs, aprime_x_e, xs2.neg(), Scalar::one().neg()];
      let p_vec: Vec<GroupElement> = vec![
        P[i].unpack().unwrap(),
        self.g,
        T[i].unpack().unwrap(),
        S[i].unpack().unwrap(),
      ];

      let pk_vti: GroupElement = GroupElement::vartime_multiscalar_mul(s_vec, p_vec);
      pk_vt.push(pk_vti);
    }

    let PK: GroupElement = GroupElement::vartime_multiscalar_mul(k_vec, pk_vt);

    let h_gx = self.h - Scalar::from(x) * self.g;
    in_proof
      .tr
      .verify(&PK.compress(), &h_gx.compress(), transcript)
  }

  fn prove(
    &self,
    a_vec: Vec<u64>,
    v_vec: Vec<Scalar>,
    transcript: &mut Transcript,
  ) -> InputMappingProof {
    transcript.append_protocol_name(Self::protocol_name());

    let setup = self.setup(&v_vec);

    setup.S.iter().enumerate().for_each(|(_, Si)| {
      transcript.append_point(b"point S", Si);
    });
    setup.T.iter().enumerate().for_each(|(_, Ti)| {
      transcript.append_point(b"point T", Ti);
    });

    let x = transcript.challenge_mont(b"input mapping challenge x");

    let aprime_vec = self.generate_transformed_inputs(&a_vec, &setup.alpha, x);

    let in_proof = self.internal_prove(a_vec, v_vec, setup.alpha, setup.omega, x, transcript);

    InputMappingProof {
      S: setup.S,
      T: setup.T,
      a_prime: aprime_vec,
      in_proof: in_proof,
    }
  }

  fn verify(
    &self,
    proof: InputMappingProof,
    P: Vec<CompressedGroup>,
    transcript: &mut Transcript,
  ) -> Result<(), GroupError> {
    transcript.append_protocol_name(Self::protocol_name());

    proof.S.iter().enumerate().for_each(|(_, Si)| {
      transcript.append_point(b"point S", Si);
    });
    proof.T.iter().enumerate().for_each(|(_, Ti)| {
      transcript.append_point(b"point T", Ti);
    });

    let x = transcript.challenge_mont(b"input mapping challenge x");

    self.internal_verify(
      proof.a_prime,
      &proof.in_proof,
      &proof.S,
      &proof.T,
      P,
      x,
      transcript,
    )
  }
}

#[cfg(test)]
mod tests {

  use super::montgomery;
  use super::*;

  #[test]
  fn test_input_mapping_protocol() {
    let n: usize = 4;

    let case_nums: usize = 100;
    for _ in 0..case_nums {
      let mut csprng: OsRng = OsRng;

      let a: Vec<u64> = (0..n)
        .map(|_| montgomery::random64_mod(&mut csprng))
        .collect();
      let v: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut csprng)).collect();

      let system = InputMappingSystem::new(b"unit test");
      let P = system.compute_pederson(&a, &v);

      let mut prover_transcript = Transcript::new(b"proof");
      let proof = system.prove(a, v, &mut prover_transcript);

      let mut verifier_transcript = Transcript::new(b"proof");
      assert_eq!(system.verify(proof, P, &mut verifier_transcript), Ok(()));
    }
  }
}
