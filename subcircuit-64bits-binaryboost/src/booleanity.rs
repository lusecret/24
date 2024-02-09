use super::groups::group::GroupElement;
use super::groups::random::RandomTape;
use super::groups::transcript::{AppendToTranscript, ProofTranscript};
use super::polycommit::univariate_poly::{
  UnivariatePoly, UnivariatePolyBlinds, UnivariatePolyCommit, UnivariatePolyGens,
  UnivariatePolyProof,
};
use super::scalar::Scalar;
use super::subcircuit_errors::SubCircuitError;
use crate::montgomery;
use merlin::Transcript;

#[derive(Debug)]
pub struct BooleanitySystem {
  gens: UnivariatePolyGens,
}

#[derive(Debug)]
pub struct BooleanitySetup {
  delta1: Vec<u64>,
  delta2: Vec<u64>,
  pub comms: UnivariatePolyCommit,
}

#[derive(Clone, Debug, PartialEq, serde_derive::Deserialize, serde_derive::Serialize)]
pub struct BooleanityProof {
  pub y1: u64,
  pub y2: u64,
  pub b_prime: Vec<u64>,
  pub poly_proof: UnivariatePolyProof,
}

impl BooleanitySystem {
  fn protocol_name() -> &'static [u8] {
    b"protocol booleanity"
  }

  pub fn new(nums: usize, label: &'static [u8]) -> BooleanitySystem {
    let (_, n) = UnivariatePoly::compute_m_n(2 * nums);
    let gens = UnivariatePolyGens::new(n, label);
    BooleanitySystem { gens }
  }

  pub fn from(Gs: Vec<GroupElement>, h: GroupElement) -> BooleanitySystem {
    let gens = UnivariatePolyGens::new_from(Gs, h);
    BooleanitySystem { gens }
  }

  pub fn setup(
    &self,
    b: &Vec<u64>,
    beta: &Vec<u64>,
  ) -> Result<(BooleanitySetup, UnivariatePolyBlinds), SubCircuitError> {
    if b.len() == 0 || b.len() != beta.len() {
      return Err(SubCircuitError::IllegalParameters);
    }

    let bm: Vec<u64> = b
      .into_iter()
      .map(|bi| montgomery::enter_mont(*bi))
      .collect();
    let betam: Vec<u64> = beta
      .into_iter()
      .map(|betai| montgomery::enter_mont(*betai))
      .collect();

    let delta1: Vec<u64> = bm
      .iter()
      .zip(&betam)
      .map(|(bi, betai)| {
        let mut b_beta = montgomery::mont_mul_mod(*bi, *betai);
        b_beta = b_beta + b_beta;
        let dalta1i = if b_beta > *betai {
          b_beta - (*betai)
        } else {
          b_beta + montgomery::get_Q() - (*betai)
        };
        montgomery::back_from_mont(dalta1i)
      })
      .collect();

    let delta2: Vec<u64> = betam
      .into_iter()
      .map(|betai| {
        let beta_square = montgomery::mont_mul_mod(betai, betai);
        montgomery::back_from_mont(beta_square)
      })
      .collect();

    let delta_combined: Vec<u64> = delta1
      .clone()
      .into_iter()
      .chain(delta2.clone().into_iter())
      .collect();

    let deltas: Vec<Scalar> = delta_combined.iter().map(|d| Scalar::from(*d)).collect();

    let polys = UnivariatePoly::new(deltas);

    let mut random_tape = RandomTape::new(Self::protocol_name());

    let (comms, blinds) = polys.commit(&self.gens, &mut random_tape);
    Ok((
      BooleanitySetup {
        delta1,
        delta2,
        comms,
      },
      blinds,
    ))
  }

  pub fn prove(
    &self,
    s: &BooleanitySetup,
    blinds: UnivariatePolyBlinds,
    b: &Vec<u64>,
    beta: &Vec<u64>,
    x: u64,
    transcript: &mut Transcript,
  ) -> BooleanityProof {
    transcript.append_protocol_name(Self::protocol_name());
    for C in s.comms.C.iter() {
      C.append_to_transcript(b"poly commitment", transcript);
    }
    s.comms
      .U
      .append_to_transcript(b"poly commitment", transcript);

    let k = transcript.challenge_mont(Self::protocol_name());
    let n = s.delta1.len();

    let km: u64 = montgomery::enter_mont(k);
    let one: u64 = montgomery::mont_one();

    let km_vec: Vec<u64> = (0..n)
      .scan(one, |acc, _| {
        *acc = montgomery::mont_mul_mod(*acc, km);
        Some(*acc)
      })
      .collect();

    let y1: u64 = Self::poly_eval(&s.delta1, &km_vec);
    let y2: u64 = Self::poly_eval(&s.delta2, &km_vec);

    let b_prime = montgomery::compute_aprime(&b, &beta, x);

    let delta_combined: Vec<u64> = s
      .delta1
      .clone()
      .into_iter()
      .chain(s.delta2.clone().into_iter())
      .collect();
    let deltas: Vec<Scalar> = delta_combined.iter().map(|d| Scalar::from(*d)).collect();
    let polys = UnivariatePoly::new(deltas);

    let poly_proof = UnivariatePolyProof::prove(&polys, &blinds, transcript);

    BooleanityProof {
      y1,
      y2,
      b_prime,
      poly_proof,
    }
  }

  pub fn verify(
    &self,
    comms: &UnivariatePolyCommit,
    proof: &BooleanityProof,
    x: u64,
    transcript: &mut Transcript,
  ) -> Result<(), SubCircuitError> {
    transcript.append_protocol_name(Self::protocol_name());
    for C in comms.C.iter() {
      C.append_to_transcript(b"poly commitment", transcript);
    }
    comms.U.append_to_transcript(b"poly commitment", transcript);

    let k: u64 = transcript.challenge_mont(Self::protocol_name());

    // check b_prime && y1 & y2
    let lhs: u64 = Self::compute_y1x_y2x2(proof.y1, proof.y2, x);

    let n = proof.b_prime.len();
    let km: u64 = montgomery::enter_mont(k);
    let one: u64 = montgomery::mont_one();
    let km_vec: Vec<u64> = (0..n)
      .scan(one, |acc, _| {
        *acc = montgomery::mont_mul_mod(*acc, km);
        Some(*acc)
      })
      .collect();

    let rhs: u64 = Self::compute_bprime_kvec(&proof.b_prime, &km_vec);
    if lhs != rhs {
      return Err(SubCircuitError::BooleanY1Y2ValidationFailed);
    }

    // check poly-commit
    let ret = proof.poly_proof.verify(&comms, &self.gens, transcript);
    match ret {
      Ok(()) => return Ok(()),
      Err(e) => return Err(SubCircuitError::BooleanUniPolyValidationFailed(e)),
    };
  }

  fn poly_eval(delta: &Vec<u64>, km_vec: &Vec<u64>) -> u64 {
    let y_vec: Vec<u128> = km_vec
      .iter()
      .zip(delta)
      .map(|(km, deltai)| {
        let dm = montgomery::enter_mont(*deltai);
        montgomery::mont_mul_mod(*km, dm) as u128
      })
      .collect();

    let y: u128 = y_vec.iter().sum();
    let y: u64 = (y % (montgomery::get_Q() as u128)) as u64;

    montgomery::back_from_mont(y)
  }

  fn compute_y1x_y2x2(y1: u64, y2: u64, x: u64) -> u64 {
    let xm: u64 = montgomery::enter_mont(x);
    let y1m: u64 = montgomery::enter_mont(y1);
    let y2m: u64 = montgomery::enter_mont(y2);

    let y1xm: u64 = montgomery::mont_mul_mod(y1m, xm);
    let x2m: u64 = montgomery::mont_mul_mod(xm, xm);

    let y2x2m: u64 = montgomery::mont_mul_mod(y2m, x2m);
    montgomery::back_from_mont(y1xm + y2x2m)
  }

  fn compute_bprime_kvec(b_prime: &Vec<u64>, km_vec: &Vec<u64>) -> u64 {
    let d_vec: Vec<u128> = b_prime
      .iter()
      .zip(km_vec.iter())
      .map(|(&b, &km)| {
        let bm: u64 = montgomery::enter_mont(b);
        let mut b2m: u64 = montgomery::mont_mul_mod(bm, bm);

        if b2m > bm {
          b2m = b2m - bm;
        } else {
          b2m = b2m + montgomery::get_Q() - bm;
        }
        montgomery::mont_mul_mod(b2m, km) as u128
      })
      .collect();

    let r: u128 = d_vec.iter().sum();
    let r: u64 = (r % (montgomery::get_Q() as u128)) as u64;

    montgomery::back_from_mont(r)
  }
}

#[cfg(test)]
mod tests {

  use super::super::montgomery::random64_mod;
  use super::*;
  use rand::rngs::OsRng;

  #[test]
  fn test_booleanity() {
    let test_len: usize = 960;

    for _ in 0..20 {
      let mut csprng: OsRng = OsRng;

      let s: BooleanitySystem = BooleanitySystem::new(test_len, b"unit test");

      let b: Vec<u64> = (0..test_len)
        .map(|_| random64_mod(&mut csprng) & 1)
        .collect();
      let beta: Vec<u64> = (0..test_len).map(|_| random64_mod(&mut csprng)).collect();

      let (setup, blinds) = s.setup(&b, &beta).unwrap();

      let mut prover_transcript = Transcript::new(b"unit test");
      let x = random64_mod(&mut csprng);
      let proof = s.prove(&setup, blinds, &b, &beta, x, &mut prover_transcript);

      let mut verifier_transcript = Transcript::new(b"unit test");

      assert_eq!(
        s.verify(&setup.comms, &proof, x, &mut verifier_transcript),
        Ok(())
      );
    }
  }

  use super::super::montgomery;
  use rand_core::{CryptoRng, RngCore};

  fn split_alpha<Rng: RngCore + CryptoRng>(alpha: u64, rng: &mut Rng) -> Vec<u64> {
    let betam: Vec<u64> = (0..31).map(|_| random64_mod(rng)).collect();

    let betam_2pow: Vec<u128> = betam
      .iter()
      .enumerate()
      .map(|(i, &bm)| montgomery::mont_mul_mod(montgomery::POW_TWO[i], bm) as u128)
      .collect();

    let beta1_31m: u128 = betam_2pow.iter().sum();
    let beta1_31m: u64 = (beta1_31m % (montgomery::get_Q() as u128)) as u64;

    let mut beta_lastm: u64;
    let alpham: u64 = montgomery::enter_mont(alpha);
    if alpham > beta1_31m {
      beta_lastm = alpham - beta1_31m;
    } else {
      beta_lastm = alpham + montgomery::get_Q() - beta1_31m;
    }
    beta_lastm = montgomery::mont_mul_mod(beta_lastm, montgomery::INV_POW_OF_TWO);
    let beta_last: u64 = montgomery::back_from_mont(beta_lastm);

    let mut beta: Vec<u64> = betam
      .into_iter()
      .map(|bm| montgomery::back_from_mont(bm))
      .collect();
    beta.push(beta_last);

    beta
  }

  #[test]
  fn test_split_alpha() {
    let mut csprng: OsRng = OsRng;

    let alpha = random64_mod(&mut csprng);

    let n = 32;

    let pow_2: Vec<u64> = (0..32).map(|exp| 2u64.pow(exp)).collect();

    let mut csprng: OsRng = OsRng;
    let beta: Vec<u64> = split_alpha(alpha, &mut csprng);

    // check 1:
    let mut sum: u128 = 0;
    for i in 0..n {
      sum = sum + (beta[i] as u128) * (pow_2[i] as u128);
    }

    let sum: u64 = (sum % (montgomery::get_Q() as u128)) as u64;

    assert_eq!(sum, alpha);

    // check 2:
    let mut sum: u128 = 0;
    for i in 0..n {
      sum = sum + ((beta[i] as u128) << (i as u32));
    }

    let sum: u64 = (sum % (montgomery::get_Q() as u128)) as u64;

    assert_eq!(sum, alpha);
  }

  #[test]
  fn test_split_alpha_vec() {
    let mut csprng: OsRng = OsRng;

    let alpha_vec: Vec<u64> = (0..30).map(|_| random64_mod(&mut csprng)).collect();

    let beta_vec: Vec<u64> = alpha_vec
      .iter()
      .flat_map(|&al| split_alpha(al, &mut csprng))
      .collect();

    println!("len = {:?}", beta_vec.len());

    // check:
    let pow_2: Vec<u64> = (0..32).map(|exp| 2u64.pow(exp)).collect();

    let mut sum: u128 = 0;
    for i in 0..32 {
      sum = sum + (beta_vec[i + 32] as u128) * (pow_2[i] as u128);
    }

    let sum: u64 = (sum % (montgomery::get_Q() as u128)) as u64;

    assert_eq!(sum, alpha_vec[1]);
  }
}
