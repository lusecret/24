use super::booleanity::{BooleanityProof, BooleanitySystem};
use super::groups::group::{CompressedGroup, GroupElement, VartimeMultiscalarMul};
use super::groups::transcript::{AppendToTranscript, ProofTranscript};
use super::groups::input_mapping::{InputMappingInternalProof};
use super::montgomery;
use super::polycommit::univariate_poly::UnivariatePolyCommit;
use super::scalar::{Scalar, Q_INV};
use super::subcircuit::{SubCircuitProof, SubCircuitProofShort, SubCircuitSystem};
use super::subcircuit_errors::SubCircuitError;
use num_bigint::BigUint;
use merlin::Transcript;
use rand::rngs::OsRng;
use rand_core::{CryptoRng, RngCore};
use std::mem;

const TB: usize = 32;

#[derive(Debug)]
pub struct BinaryBoostCircuitSystem {
  pub cir: SubCircuitSystem,
  pub bs: BooleanitySystem,
}

impl BinaryBoostCircuitSystem {
  pub fn new(label: &[u8], n: usize, bool_degrees: usize) -> Self {
    let cir = SubCircuitSystem::new(label, n);

    let label_static: &'static [u8] = unsafe { mem::transmute(label) };
    let bs = BooleanitySystem::new(bool_degrees + cir.get_mblen(), label_static);

    BinaryBoostCircuitSystem { cir, bs }
  }

  fn protocol_name() -> &'static [u8] {
    b"sub-protocol for circuit validatioin"
  }

  fn split_a(a: u32) -> Vec<u64> {
    let mut b: Vec<u64> = Vec::with_capacity(32);

    for i in 0..32 {
      let bit = (a >> i) & 1;
      b.push(bit as u64);
    }
    b
  }

  fn split_alpha<Rng: RngCore + CryptoRng>(alpha: u64, rng: &mut Rng) -> Vec<u64> {
    let betam: Vec<u64> = (0..31).map(|_| montgomery::random64_mod(rng)).collect();

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

  fn compute_gamma(tau_vecs: &Vec<Vec<u64>>) -> Vec<Vec<Scalar>> {
    let mb = tau_vecs.len();
    let b = tau_vecs[0].len();
    let xloop = mb / TB;

    let mut results: Vec<Vec<Scalar>> = Vec::new();

    let mut pow2: Vec<Scalar> = vec![Scalar::from(0); TB];
    for (index, elem) in pow2.iter_mut().enumerate() {
        *elem = Scalar::from(1 << index);
    }

    (0..b).for_each(|k| {
      let mut res: Vec<Scalar> = vec![Scalar::from(0); xloop]; 

      let tau_column: Vec<u64> = tau_vecs
        .iter()
        .map(|vec: &Vec<u64>| vec[k])
        .collect();

      for i in 0..(tau_column.len() / TB) {
          for j in 0..TB {
            res[i] += Scalar::from(tau_column[j + i * TB]) * pow2[j]; // equivalent to multiplying by 2^j
          }
      }
      results.push(res)
    });
    results
  }

  pub fn scale_input(a: &Vec<u64>, n: usize, blen: usize) -> Vec<u64> {
    let pen_len = n - (n / blen - 1);

    let alen = a.len();
    let quotient = pen_len / alen;
    let remainder = pen_len % alen;

    // Repeat a quotient times
    let mut extended_vec: Vec<u64> = a.iter().cloned().cycle().take(alen * quotient).collect();

    // Add the first remainder elements from a to extended_vec
    for i in 0..remainder {
        extended_vec.push(a[i]);
    }
    extended_vec
  }

}

#[derive(Debug, PartialEq)]
pub struct BinaryBoostCircuitProof {
  cir_proof: SubCircuitProof,
  bool_commit: UnivariatePolyCommit,
  bool_proof: BooleanityProof,
  b_prime: Vec<u64>,
  y: Vec<u64>,  // new
  vi_primes: Vec<Scalar>,  // new
}

#[derive(Clone, Debug, serde_derive::Deserialize, serde_derive::Serialize)]
pub struct BinaryBoostCircuitProofShort {
  cir_proof: SubCircuitProofShort,
  bool_commit: UnivariatePolyCommit,
  bool_proof: BooleanityProof,
  y: Vec<u64>,  // new
  vi_primes: Vec<Scalar>,  // new
}

impl BinaryBoostCircuitSystem {
  pub fn prove(
    &self,
    ao_vec: &Vec<u64>,
    alphao_vec: &Vec<u64>,
    v_vec: &Vec<Scalar>,
    phi: Scalar,
    n: usize,
    transcript: &mut Transcript,
  ) -> Result<BinaryBoostCircuitProof, SubCircuitError> {

    if !ao_vec.iter().all(|&a| a <= u32::MAX as u64) {
      return Err(SubCircuitError::IllegalParameters);
    }

    // uum2bits a & alpha && scale result: 
    let b_vec: Vec<u64> = ao_vec
      .iter()
      .flat_map(|&a| Self::split_a(a as u32))
      .collect();

    let mut csprng: OsRng = OsRng;
    let beta_vec: Vec<u64> = alphao_vec
      .iter()
      .flat_map(|&al| Self::split_alpha(al, &mut csprng))
      .collect();

    let bs_vec = Self::scale_input(&b_vec, n, self.cir.get_blen());
    let betas_vec = Self::scale_input(&beta_vec, n, self.cir.get_blen());
    /////////////scale end//////////////

    let (tau_vecs, mu_vecs, r_vec, epsilon_vec,  R) = self
      .cir
      .prove_stage1(&bs_vec, &betas_vec, v_vec, phi, n, transcript)?;

    // compute C:
    let gammas: Vec<Vec<Scalar>> = Self::compute_gamma(&tau_vecs);

    let bloop = tau_vecs[0].len();
    let mbtb_len = gammas[0].len();
    assert_eq!(mbtb_len, self.cir.get_mblen()/TB);

    let mut Cs: Vec<CompressedGroup> = Vec::new();
    (0..bloop).for_each(|k| {
      
      let C = GroupElement::vartime_multiscalar_mul(&gammas[k], &self.cir.get_gens().G[0..mbtb_len]).compress();
      Cs.push(C);

      C.append_to_transcript(b"point C", transcript);
    });

    // compute M: M is called 'B' in submission paper
    let mut M_vec: Vec<Scalar> = Vec::new(); // M_vec's len = mb/tb。

    for i in 0..mbtb_len {
      let mut r: Scalar = Scalar::from(0);
      for j in 0..TB {
        r += mu_vecs[i*TB + j] * Scalar::from(1 << j);
      }
      M_vec.push(r);
    }

    let M: curve25519_dalek::ristretto::CompressedRistretto =
    GroupElement::vartime_multiscalar_mul(&M_vec, &self.cir.get_gens().G[0..mbtb_len]).compress();

    // new for binary boost: 
    let mut combine_b: Vec<u64> = b_vec.clone();
    combine_b.extend(r_vec.clone());

    let mut combine_beta: Vec<u64> = beta_vec.clone();
    combine_beta.extend(epsilon_vec.clone());

    let (bool_setup, bool_blinds) = self.bs.setup(&combine_b, &combine_beta).unwrap();

    for C in bool_setup.comms.C.iter() {
      C.append_to_transcript(b"poly commitment in bool-subcircuit", transcript);
    }
    bool_setup
      .comms
      .U
      .append_to_transcript(b"poly commitment in bool-subcircuit", transcript);

    let x = transcript.challenge_mont(Self::protocol_name());

    // compute y_prime:
    let ys_prime = SubCircuitSystem::compute_yprime(&tau_vecs, &mu_vecs, x);
    let y = SubCircuitSystem::compute_y(&ys_prime, x); 

    // compute vi_prime:
    let q_inv: Scalar = Scalar::from_bytes(&Q_INV).unwrap();
    let Qbig: BigUint = BigUint::from(montgomery::get_Q());
    let vi_primes: Vec<Scalar> = ys_prime.chunks(TB)  
        .map(|chunk| {
            let vi:Scalar = chunk.iter().enumerate()  
                .map(|(i, ys)| {

                  let mut yp_big: BigUint = BigUint::from_bytes_le(&ys.to_bytes());
                  yp_big = yp_big % &Qbig;
                  let ymodq = Scalar::from(yp_big.to_u64_digits()[0]);
                  let mut v: Scalar = ys - ymodq;
                  v = v * Scalar::from(1 << i); // multiply by 2^i
                  v
                })  
                .sum();

            vi * q_inv    
        })
        .collect();   

    // next compute: 
    let cir_proof = self.cir.prove_stage2(
      ao_vec, alphao_vec, v_vec, phi, x, *r_vec.last().unwrap(), *epsilon_vec.last().unwrap(), M, R, Cs, transcript, ys_prime, 
    )?;

    let bool_proof = self
      .bs
      .prove(&bool_setup, bool_blinds, &combine_b, &combine_beta, x, transcript);
    let b_prime = montgomery::compute_aprime(&b_vec, &beta_vec, x);

    Ok(BinaryBoostCircuitProof {
      cir_proof,
      bool_commit: bool_setup.comms,
      bool_proof,
      b_prime,
      y, 
      vi_primes, 
    })
  }

  pub fn verify(
    &self,
    pedersen: &Vec<CompressedGroup>,
    n: usize,
    proof: &BinaryBoostCircuitProof,
    transcript: &mut Transcript,
  ) -> Result<(), SubCircuitError> {
    transcript.append_protocol_name(SubCircuitSystem::protocol_name());
    proof
      .cir_proof
      .R
      .append_to_transcript(b"point R", transcript);

    for C in proof.cir_proof.Cs.iter() {
      C.append_to_transcript(b"point C", transcript);
    }

    for C in proof.bool_commit.C.iter() {
      C.append_to_transcript(b"poly commitment in bool-subcircuit", transcript);
    }
    proof
      .bool_commit
      .U
      .append_to_transcript(b"poly commitment in bool-subcircuit", transcript);

    let x = transcript.challenge_mont(Self::protocol_name());

    // compute z:
    let x_inv = montgomery::inv(x);
    let xm_inv: u64 = montgomery::enter_mont(x_inv);

    let z_vec: Vec<Scalar> = proof.y.chunks(TB)
    .map(|chunk| {

      let zi:Scalar = chunk.iter().enumerate()  
      .map(|(i, y)| {

        let ym: u64 = montgomery::enter_mont(*y);
        let yxm: u64 = montgomery::mont_mul_mod(ym, xm_inv);
        let yx: u64 = montgomery::back_from_mont(yxm);
        let mut ys: Scalar = Scalar::from(yx);
        ys = ys * Scalar::from(1 << i);
        ys
      })  
      .sum();
      zi
    }).collect();

    let qs: Scalar = Scalar::from(montgomery::get_Q());
    let z_vec: Vec<Scalar> = z_vec.iter()
    .zip(proof.vi_primes.iter())
    .map(|(&zi, &vi)| zi + vi * qs)
    .collect();

    // next compute:
    let mb: usize = proof.y.len();
    let mbtb_len = mb / TB;
    let lhs: GroupElement = GroupElement::vartime_multiscalar_mul(&z_vec, &self.cir.get_gens().G[0..mbtb_len]);

    // scale b_prime: 
    let b_prime_extend = Self::scale_input(&proof.b_prime, n, self.cir.get_blen());
    let bm_prime_extend = b_prime_extend.into_iter().map(|x| montgomery::enter_mont(x)).collect();

    self
      .cir
      .internal_verify(pedersen, x, bm_prime_extend, &proof.cir_proof, transcript, lhs, &proof.y)?;

    self
      .bs
      .verify(&proof.bool_commit, &proof.bool_proof, x, transcript)?;

    let alen: usize = proof.cir_proof.ao_prime.len();
    if alen * 32 != proof.b_prime.len() {
      return Err(SubCircuitError::BooleanAPrimeBPrimeNotMatch);
    };

    let mut index = 0;
    while index + 32 <= proof.b_prime.len() {
      let chunk = &proof.b_prime[index..index + 32];
      let mut sum: u128 = 0;

      for (i, &num) in chunk.iter().enumerate() {
        sum += (num as u128) << (i as u32);
      }

      let sum: u64 = (sum % (montgomery::get_Q() as u128)) as u64;
      let a_exp = proof.cir_proof.ao_prime[index >> 5];
      if sum != a_exp {
        return Err(SubCircuitError::BooleanAPrimeBPrimeNotMatch);
      }

      index += 32;
    }

    Ok(())
  }


  pub fn simulate_write_read_file(&self, proof: &BinaryBoostCircuitProof, chunksize: usize) -> BinaryBoostCircuitProof {
    let y_prime_length = (61 + 61 + chunksize.ilog2()) / 8 + 2; //y_prime in bytes; tau_i and x are 61-bits, y_prime is at most 61+61+chunksize bits
  //  println!("chunksize: {}", chunksize);
  //  println!("y_prime_length: {}", y_prime_length);

    let short_y_primes = proof.cir_proof
      .ys_prime
      .iter()
      .map(|x| x.to_bytes()[0..y_prime_length as usize].try_into().unwrap())
      .collect();
    let e_vec_bytes: Vec<Vec<u8>> = proof.cir_proof
      .mapping_proof
      .e_vec
      .iter()
      .map(|u| u.to_bytes_le())
      .collect();

    let SubCircuitProof_short: SubCircuitProofShort = SubCircuitProofShort {
      ys_prime: short_y_primes, // 17 * 1024 =
      ao_prime: proof.cir_proof.ao_prime.clone(), //30
      M: proof.cir_proof.M.clone(),
      R: proof.cir_proof.R.clone(),   //1
      Cs: proof.cir_proof.Cs.clone(), // 1023
      S: proof.cir_proof.S.clone(),   //31
      T: proof.cir_proof.T.clone(),   //31
      e_vec: e_vec_bytes,   //31
      tr: proof.cir_proof.mapping_proof.tr.clone(),
    };

    let short_proof_out: BinaryBoostCircuitProofShort = BinaryBoostCircuitProofShort {
      cir_proof: SubCircuitProof_short,
      bool_commit: proof.bool_commit.clone(),
      bool_proof: proof.bool_proof.clone(),
      y: proof.y.clone(),  // new
      vi_primes: proof.vi_primes.clone(), // new
    };

    let encoded: Vec<u8> = bincode::serialize(&short_proof_out).unwrap();

    let expected_proof_size = short_proof_out.cir_proof.ys_prime.len() * 17 // ys_prime
    + short_proof_out.cir_proof.ao_prime.len() * 8  // ao_prime
    + 1 * 32                            // B,  32bytes
    + short_proof_out.cir_proof.Cs.len() * 32       // Cs, 32bytes each
    + short_proof_out.cir_proof.S.len() * 32        // S,  32bytes each
    + short_proof_out.cir_proof.T.len() * 32        // T,  32bytes each
    + short_proof_out.cir_proof.e_vec.len() * 40    // mapping_proof.e_vec, 40bytes each for n= 2^20
    + 2 * 32 // mapping_proof.tr, 64bytes (Schnorr signature)
    + short_proof_out.bool_commit.C.len() * 32
    + 1 * 32 //short_proof_out.bool_commit.U, 32bytes
    + 2 * 8 // short_proof_out.bool_proof.y1 + y2, 8bytes each
    + short_proof_out.bool_proof.b_prime.len() * 8 
    + short_proof_out.bool_proof.poly_proof.t_col.len() * 32
    + short_proof_out.y.len() * 8
    + short_proof_out.vi_primes.len() * 32
    + 1 * 32; //short_proof_out.bool_proof.poly_proof.tau 32bytes //

    println!("Actual proof size (bytes): {}", expected_proof_size);
    println!("Proof size after encoding (bytes): {}", encoded.len());

    let decoded: BinaryBoostCircuitProofShort = bincode::deserialize(&encoded[..]).unwrap();

    let y_prime_in: Vec<Scalar> = decoded.cir_proof
      .ys_prime
      .iter()
      .map(|x| Scalar::from_bytes(&SubCircuitSystem::concat_index2(x.to_vec())).unwrap())
      .collect();
    let e_vec_biguint: Vec<BigUint> = decoded.cir_proof
      .e_vec
      .iter()
      .map(|b| BigUint::from_bytes_le(b))
      .collect();

    let proofSubCircuitIn: SubCircuitProof = SubCircuitProof {
      ys_prime: y_prime_in, // 17 * 1024 =
      ao_prime: decoded.cir_proof.ao_prime.clone(), //30
      M: decoded.cir_proof.M.clone(),             //1
      R: decoded.cir_proof.R.clone(),             //1
      Cs: decoded.cir_proof.Cs.clone(),           // 1023
      S: decoded.cir_proof.S.clone(),             //31
      T: decoded.cir_proof.T.clone(),             //31
      mapping_proof: InputMappingInternalProof {
        e_vec: e_vec_biguint,
        tr: decoded.cir_proof.tr.clone(),
      },
    };

    let proofIn = BinaryBoostCircuitProof {
      cir_proof: proofSubCircuitIn,
      bool_commit: decoded.bool_commit,
      bool_proof: decoded.bool_proof.clone(), //lazy short-cut
      b_prime: proof.b_prime.clone(), //lazy short-cut
      y: decoded.y.clone(), 
      vi_primes: decoded.vi_primes.clone(), 
    };

    assert_eq!(proofIn.cir_proof.ys_prime, proof.cir_proof.ys_prime);
    assert_eq!(proofIn.cir_proof.ao_prime, proof.cir_proof.ao_prime);
    assert_eq!(proofIn.cir_proof.M, proof.cir_proof.M);
    assert_eq!(proofIn.cir_proof.R, proof.cir_proof.R);
    assert_eq!(proofIn.cir_proof.Cs, proof.cir_proof.Cs);
    assert_eq!(proofIn.cir_proof.S, proof.cir_proof.S);
    assert_eq!(proofIn.cir_proof.T, proof.cir_proof.T);
    assert_eq!(proofIn.cir_proof.mapping_proof, proof.cir_proof.mapping_proof);
    proofIn
  }

}



#[cfg(test)]
mod tests {

  use super::super::montgomery::random64_mod;
  use super::*;
  use rand::rngs::OsRng;
  use super::super::subcircuit::HYPOTHESIS_SIZE;

  #[test]
  fn test_binary_circuit() {
    let n = (2_usize).pow(10 as u32); //validate values are even numbers 2, 4, 8,....20
    
    println!("Circuit size: {}", n);

    let sc = BinaryBoostCircuitSystem::new(b"unit test", n, HYPOTHESIS_SIZE * 32);

    let mut prover_transcript = Transcript::new(b"unit test");

    let mut csprng: OsRng = OsRng;

    let a: Vec<u64> = vec![csprng.next_u32() as u64; HYPOTHESIS_SIZE];
    let alpha: Vec<u64> = (0..HYPOTHESIS_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();
    let v: Vec<Scalar> = (0..HYPOTHESIS_SIZE)
      .map(|_| Scalar::random(&mut csprng))
      .collect();

    let pedersen: Vec<CompressedGroup> = sc.cir.get_mapping().compute_pederson(&a, &v);

    let phi = Scalar::random(&mut csprng);

    let proof: BinaryBoostCircuitProof = sc
      .prove(&a, &alpha, &v, phi, n, &mut prover_transcript)
      .unwrap();

    let proof_from_file = sc.simulate_write_read_file(&proof, (n as f64).sqrt() as usize);
    assert_eq!(proof_from_file, proof);
    
    let mut verifier_transcript = Transcript::new(b"unit test");

    assert_eq!(
      sc.verify(&pedersen, n, &proof, &mut verifier_transcript),
      Ok(())
    );
    
  }
}