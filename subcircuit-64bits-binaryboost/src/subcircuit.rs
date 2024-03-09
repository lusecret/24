use super::groups::group::{
  CompressedGroup, CompressedGroupExt, GroupElement, VartimeMultiscalarMul,
  GROUP_BASEPOINT_COMPRESSED,
};
use super::groups::input_mapping::{InputMappingInternalProof, InputMappingSystem};
use super::groups::transcript::{AppendToTranscript, ProofTranscript};
use super::math::Math;
use super::montgomery;
use super::polycommit::commitments::MultiCommitGens;
use super::polycompute::POLYCOMPUTER;
use super::scalar::Scalar;
use super::subcircuit_errors::SubCircuitError;
use super::groups::schnorr::SchnorrProof;
use digest::{ExtendableOutput, Input};
use merlin::Transcript;
use num_bigint::BigUint;
use sha3::Shake256;
use std::io::Read;
use rand_core::{OsRng, RngCore};

pub const HYPOTHESIS_SIZE: usize = 30;

#[derive(Debug)]
pub struct SubCircuitSystem {
  g: GroupElement,
  h: GroupElement,
  n: usize,
  mblen: usize, 
  blen: usize, 
  gens: MultiCommitGens,
  mapping: InputMappingSystem,
}

macro_rules! combine_slices {
  ($a_slice:expr, $b:expr) => {{
    let mut new_vec: Vec<_> = $a_slice.to_vec();
    new_vec.push($b);
    new_vec
  }};
}

impl SubCircuitSystem {
  pub fn new(label: &[u8], n: usize) -> Self {
    const IN_LABEL: &[u8] = b"sub circuit system internal label";

    let mut shake = Shake256::default();
    shake.input(label);
    shake.input(GROUP_BASEPOINT_COMPRESSED.as_bytes());

    let g = GROUP_BASEPOINT_COMPRESSED.unpack().unwrap();

    let mut reader = shake.xof_result();
    let mut h_bytes = [0u8; 64];
    reader.read_exact(&mut h_bytes).unwrap();
    let h = GroupElement::from_uniform_bytes(&h_bytes);
    reader.read_exact(&mut h_bytes).unwrap();
    let u = GroupElement::from_uniform_bytes(&h_bytes);

    assert!(Self::check_n(n));
    let log_nums = n.ilog2() as usize;
    let mblen = 2u32.pow((log_nums / 2 + 1) as u32) as usize;
    let blen = 2u32.pow((log_nums / 2 - 1) as u32) as usize;

    let gens = MultiCommitGens::new(mblen, &[label, IN_LABEL].concat());

    let mapping = InputMappingSystem::from(g, h, u);

    SubCircuitSystem {
      g,
      h,
      n,
      mblen,
      blen,
      gens,
      mapping,
    }
  }

  pub fn get_mapping(&self) -> &InputMappingSystem {
    &self.mapping
  }

  pub fn get_gens(&self) -> &MultiCommitGens {
    &self.gens
  }

  pub fn get_blen(&self) -> usize {
    self.blen
  }

  pub fn get_mblen(&self) -> usize {
    self.mblen
  }

  pub fn get_n(&self) -> usize {
    self.n
  }


  pub fn protocol_name() -> &'static [u8] {
    b"sub-protocol for circuit validatioin"
  }

  fn check_n(n: usize) -> bool {
    let log_nums = n.ilog2() as usize;
    // only 2^x form expected && x only supports even number
    if n != log_nums.pow2() || log_nums & 1 != 0 {
      return false;
    }
    true
  }

  pub fn scale_input(a: &Vec<u64>, n: usize, blen: usize) -> Vec<u64> {
    let pen_len = n - (n / blen - 1);
    let a_sum: u128 = a.iter().map(|&x| x as u128).sum();
    let result: u64 = (a_sum % (montgomery::get_Q() as u128)) as u64;
    vec![result; pen_len]
  }

  pub fn compute_x_pow(x: u64, n: usize) -> Vec<Scalar> {
    let xm: u64 = montgomery::enter_mont(x);
    let one: u64 = montgomery::mont_one();

    // calculate xm^{bloop}, xm_vec = [xm, xm^2, ..., xm^{bloop}]
    let xm_vec: Vec<u64> = (0..n)
      .scan(one, |acc, _| {
        *acc = montgomery::mont_mul_mod(*acc, xm);
        Some(*acc)
      })
      .collect();

    let x_vec: Vec<Scalar> = xm_vec
      .into_iter()
      .map(|xm| {
        let x = montgomery::back_from_mont(xm);
        Scalar::from(x)
      })
      .collect();

    x_vec
  }

  pub fn compute_yprime(tau_vecs: &Vec<Vec<u64>>, mu_vecs: &Vec<Scalar>, x: u64) -> Vec<Scalar> {
    let bloop = tau_vecs[0].len();

    let xm_vec: Vec<Scalar> = Self::compute_x_pow(x, bloop);

    let ys_prime: Vec<Scalar> = tau_vecs
      .iter()
      .map(|taus| {
        taus
          .iter()
          .zip(&xm_vec)
          .map(|(&tau, &x)| {
            let taum = Scalar::from(tau);
            taum * x
          })
          .sum()
      })
      .collect();

    let ys_prime_blinded = ys_prime
      .iter()
      .zip(mu_vecs.iter())
      .map(|(&y_i, &mu_i)| y_i + mu_i)
      .collect();

    ys_prime_blinded
  }
  
  pub fn generate_blinding_vec(num_degrees: usize, num_bits: usize) -> Vec<Scalar> {
    let mut csprng: OsRng = OsRng;
    let betas_vec: Vec<Scalar> = (0..num_degrees)
      .map(|_i| {
        let mut limbs = [0u8; 32];
        csprng.fill_bytes(&mut limbs[0..(num_bits / 8)]);
        let s = Scalar::from_bytes(&limbs).unwrap();        
        s
      })
      .collect::<Vec<Scalar>>();

    betas_vec
  }

  pub fn compute_y(ys_prime: &Vec<Scalar>, x: u64) -> Vec<u64> {

    let xs: Scalar = Scalar::from(x);
    let Qbig: BigUint = BigUint::from(montgomery::get_Q());

    let y = ys_prime.iter().map(|yp| {
      let yx: Scalar = xs * yp;
      let mut yxbig: BigUint = BigUint::from_bytes_le(&yx.to_bytes());
      yxbig = yxbig % &Qbig;
      let yx = yxbig.to_u64_digits()[0];
      yx
    }).collect();
    y
  }
}

impl SubCircuitSystem {
  pub fn prove_stage1(
    &self,
    as_vec: &Vec<u64>,
    alphas_vec: &Vec<u64>,
    v_vec: &Vec<Scalar>,
    phi: Scalar,
    n: usize,
    transcript: &mut Transcript,
  ) -> Result<
    (
      Vec<Vec<u64>>,
      Vec<Scalar>,
      Vec<u64>,
      Vec<u64>,
      CompressedGroup,
    ),
    SubCircuitError,
  > {
    if v_vec.len() == 0
      || as_vec.len() != alphas_vec.len()
      || !Self::check_n(n)
    {
      return Err(SubCircuitError::IllegalParameters);
    }

    transcript.append_protocol_name(Self::protocol_name());

    // 1. compute subcircuit keys:
    let chunk_size = self.blen - 1;
    let num_iterations = self.mblen;

    let (a0, a_vec) = as_vec.split_at(1);
    let (alpha0, alpha_vec) = alphas_vec.split_at(1);

    let mut a_iter = a_vec.chunks(chunk_size);
    let mut alpha_iter = alpha_vec.chunks(chunk_size);

    let mut r = a0[0];
    let mut epsilon = alpha0[0];

    let mut r_vec: Vec<u64> = Vec::new();
    let mut epsilon_vec: Vec<u64> = Vec::new();

    //gerenate blinding keys mu_i (in submission this is called beta_i)
    let Qbig: BigUint = BigUint::from(montgomery::get_Q());
    let y_length = ((61 + 61 + chunk_size.ilog2()) / 8 + 1) * 8;

    let mu_vecs = SubCircuitSystem::generate_blinding_vec(num_iterations, y_length as usize);

    let mut iteration_count = 0;
    let mut mu_i: Scalar; // = betas.get(iteration_count).unwrap().clone();
    let mut mu_i_big: BigUint; //; = BigUint::from_bytes_le(&beta_i.to_bytes());
    let mut epsilon_big: BigUint; //= BigUint::from_bytes_le(&epsilon.to_le_bytes());

    let mut tau_vecs: Vec<Vec<u64>> = Vec::new();

    for _ in 0..num_iterations {
      if let (Some(a_chunk), Some(alpha_chunks)) = (a_iter.next(), alpha_iter.next()) {
        let a_combined: Vec<u64> = std::iter::once(r).chain(a_chunk.iter().cloned()).collect();
        let alpha_combined: Vec<u64> = std::iter::once(epsilon)
          .chain(alpha_chunks.iter().cloned())
          .collect();

        let result = POLYCOMPUTER.computer_subcircuit_keys(&a_combined, &alpha_combined);
        let result = match result {
          Ok(s) => s,
          Err(e) => return Err(SubCircuitError::PolyComputeError(e)),
        };

        r = result.r;
        epsilon = result.epsilon;
        tau_vecs.push(result.tau_vec);

        //Begin adding blinding keys
        mu_i = mu_vecs.get(iteration_count).unwrap().clone();
        mu_i_big = BigUint::from_bytes_le(&mu_i.to_bytes());
        epsilon_big = BigUint::from_bytes_le(&epsilon.to_le_bytes());
        epsilon_big = (&Qbig + epsilon_big - (mu_i_big % &Qbig)) % &Qbig;
        epsilon = epsilon_big.to_u64_digits()[0];
        iteration_count += 1;

        r_vec.push(r);
        epsilon_vec.push(epsilon);
      }
    }

    // 2. compute R:
    let R =
      GroupElement::vartime_multiscalar_mul(&[Scalar::from(r), phi], &[self.g, self.h]).compress();

    R.append_to_transcript(b"point R", transcript);

     Ok((tau_vecs, mu_vecs, r_vec, epsilon_vec, R))
  }

  pub fn prove_stage2(
    &self,
    ao_vec: &Vec<u64>,
    alphao_vec: &Vec<u64>,
    v_vec: &Vec<Scalar>,
    phi: Scalar,
    x: u64,
    r: u64,
    epsilon: u64,
    M: CompressedGroup,
    R: CompressedGroup,
    Cs: Vec<CompressedGroup>,
    transcript: &mut Transcript,
    ys_prime: Vec<Scalar>, 
  ) -> Result<SubCircuitProof, SubCircuitError> {

    // 3. compute inputmapping:
    // r --> a, phi --> v, epsilon --> alpha
    let (rv, phiv, epsilonv) = (
      combine_slices!(ao_vec, r),
      combine_slices!(v_vec, phi),
      combine_slices!(alphao_vec, epsilon),
    );

    let mapping_setup = self.mapping.setup_from(&phiv, &epsilonv);

    let mapping_proof: InputMappingInternalProof =
      self
        .mapping
        .internal_prove(rv, phiv, epsilonv, mapping_setup.omega, x, transcript);

    // 4. compute as:
    let ao_prime = montgomery::compute_aprime(&ao_vec, &alphao_vec, x);

    return Ok(SubCircuitProof {
      ys_prime,
      ao_prime,
      M,
      R,
      Cs,
      S: mapping_setup.S,
      T: mapping_setup.T,
      mapping_proof,
    });
  }

  pub fn internal_verify(
    &self,
    pedersen: &Vec<CompressedGroup>,
    x: u64,
    am_vec: Vec<u64>,
    proof: &SubCircuitProof,
    transcript: &mut Transcript,
    lhs: GroupElement,
    y: &Vec<u64>, 
  ) -> Result<(), SubCircuitError> {
    // 2. verify tau correctness：

    let bloop = proof.Cs.len();
    let x_vec: Vec<Scalar> = Self::compute_x_pow(x, bloop);

    let C_decompressed = proof.Cs.iter().map(|pt| pt.decompress().unwrap());

    let rhs = GroupElement::vartime_multiscalar_mul(&x_vec, C_decompressed);

    // add blinding vector commitment M (called B in the submission)
    let M_decompressed = proof.M.decompress().unwrap();
    let rhs_M = rhs + M_decompressed;

    if lhs != rhs_M {
      return Err(SubCircuitError::TauValidationFailed);
    }

    // 3. verify sub-cirucuit computation correctness：
    // 3.1 compute sub circuit
    let chunk_size = self.blen - 1;
    let num_iterations = self.mblen;

    let (a0, am_vec) = am_vec.split_at(1);

    let mut a_iter = am_vec.chunks(chunk_size);

    let mut rm_prime = a0[0];

    for i in 0..num_iterations {
      if let Some(am_chunk) = a_iter.next() {
        let am_combined: Vec<u64> = std::iter::once(rm_prime)
          .chain(am_chunk.iter().cloned())
          .collect();

        let om = montgomery::mont_accumu_mul(&am_combined);
        let ym = montgomery::enter_mont(y[i]);

        if om >= ym {
          rm_prime = om - ym;
        } else {
          rm_prime = om + montgomery::get_Q() - ym;
        }
      }
    }
    let r_prime = Scalar::from(montgomery::back_from_mont(rm_prime));

    let (P, a_prime) = (
      combine_slices!(pedersen, proof.R),
      combine_slices!(proof.ao_prime, r_prime.to_u64()[0]),
    );

    // 3.2 verify input mapping:
    self
      .mapping
      .internal_verify(
        a_prime,
        &proof.mapping_proof,
        &proof.S,
        &proof.T,
        P,
        x,
        transcript,
      )
      .map_err(|e| SubCircuitError::InputMappingValidationFailed(e))?;

    Ok(())
  }
}

impl SubCircuitSystem {
  pub fn prove(
    &self,
    ao_vec: &Vec<u64>,
    alphao_vec: &Vec<u64>,
    v_vec: &Vec<Scalar>,
    phi: Scalar,
    n: usize,
    transcript: &mut Transcript,
  ) -> Result<SubCircuitProof, SubCircuitError> {

    // scale a & alpha to n
    let as_vec = Self::scale_input(ao_vec, n, self.blen);
    let alphas_vec = Self::scale_input(alphao_vec, n, self.blen);

    let (tau_vecs, mu_vecs, r_vec, epsilon_vec, R) =
      self.prove_stage1(&as_vec, &alphas_vec, v_vec, phi, n, transcript)?;

    // compute C:
    let bloop = tau_vecs[0].len();
    // assert_eq!(bloop, self.blen);

    let mut Cs: Vec<CompressedGroup> = Vec::new();
    (0..bloop).for_each(|b| {
      let tau_column: Vec<Scalar> = tau_vecs
        .iter()
        .map(|vec: &Vec<u64>| Scalar::from(vec[b]))
        .collect();
      let C = GroupElement::vartime_multiscalar_mul(&tau_column, &self.gens.G).compress();
      Cs.push(C);

      C.append_to_transcript(b"point C", transcript);
    });

    // M is called 'B' in submission paper
    let M: curve25519_dalek::ristretto::CompressedRistretto =
    GroupElement::vartime_multiscalar_mul(&mu_vecs, &self.gens.G).compress();

    let x = transcript.challenge_mont(b"sub-protocol challenge");

    // compute y_prime:
    let ys_prime = Self::compute_yprime(&tau_vecs, &mu_vecs, x);

    self.prove_stage2(
      ao_vec, alphao_vec, v_vec,  phi, x, *r_vec.last().unwrap(), *epsilon_vec.last().unwrap(), M, R, Cs, transcript, ys_prime,
    )
  }

  pub fn verify(
    &self,
    pedersen: &Vec<CompressedGroup>,
    n: usize,
    proof: &SubCircuitProof,
    transcript: &mut Transcript,
  ) -> Result<(), SubCircuitError> {
    transcript.append_protocol_name(SubCircuitSystem::protocol_name());
    proof.R.append_to_transcript(b"point R", transcript);

    for C in proof.Cs.iter() {
      C.append_to_transcript(b"point C", transcript);
    }

    let x = transcript.challenge_mont(b"sub-protocol challenge");

    let lhs: GroupElement = GroupElement::vartime_multiscalar_mul(&proof.ys_prime, &self.gens.G);
    let y: Vec<u64> = Self::compute_y(&proof.ys_prime, x);

    let pen_len = n - (n / self.blen - 1);

    let sum: u128 = proof.ao_prime.iter().map(|a| *a as u128).sum();
    let a_prime: u64 = (sum % (montgomery::get_Q() as u128)) as u64;

    let am_prime: u64 = montgomery::enter_mont(a_prime);
    let am_vec: Vec<u64> = vec![am_prime; pen_len];

    self.internal_verify(pedersen, x, am_vec, proof, transcript, lhs, &y)
  }

  pub fn write_file(&self, proof: SubCircuitProof, chunksize: usize) -> SubCircuitProof {
    let y_prime_length = (61 + 61 + chunksize.ilog2()) / 8 + 1; //y_prime in bytes; tau_i and x are 61-bits, y_prime is at most 61+61+chunksize bits
    //println!("chunksize: {}", chunksize);
    //println!("y_prime_length: {}", y_prime_length);

    let short_y_primes = proof
      .ys_prime
      .iter()
      .map(|x| x.to_bytes()[0..y_prime_length as usize].try_into().unwrap())
      .collect();
    let e_vec_bytes: Vec<Vec<u8>> = proof
      .mapping_proof
      .e_vec
      .iter()
      .map(|u| u.to_bytes_le())
      .collect();

    let shortProofOut: SubCircuitProofShort = SubCircuitProofShort {
      ys_prime: short_y_primes, // 17 * 1024 =
      ao_prime: proof.ao_prime.clone(), //30
      M: proof.M.clone(),
      R: proof.R.clone(),   //1
      Cs: proof.Cs.clone(), // 1023
      S: proof.S.clone(),   //31
      T: proof.T.clone(),   //31
      e_vec: e_vec_bytes,   //31
      tr: proof.mapping_proof.tr.clone(),
    };
    //let encodedProof: Vec<u8> = bincode::serialize(&proof).unwrap();
    //let entity = Entity { x: 1.5, y: 1.5 };
    let encoded: Vec<u8> = bincode::serialize(&shortProofOut).unwrap();

    println!(
      "shortProof.ys_prime.len(): {}",
      shortProofOut.ys_prime.len()
    );
    println!("shortProof.ao_prime.len: {}", shortProofOut.ao_prime.len());
    println!("shortProof.Cs.len: {}", shortProofOut.Cs.len());
    println!("shortProof.S.len: {}", shortProofOut.S.len());
    println!("shortProof.T.len: {}", shortProofOut.T.len());
    println!("shortProof.e_vec.len: {}", shortProofOut.e_vec.len());

    let expected_proof_size = shortProofOut.ys_prime.len() * 17 // ys_prime
    + shortProofOut.ao_prime.len() * 8  // ao_prime
    + 1 * 32                            // B,  32bytes
    + shortProofOut.Cs.len() * 32       // Cs, 32bytes each
    + shortProofOut.S.len() * 32        // S,  32bytes each
    + shortProofOut.T.len() * 32        // T,  32bytes each
    + shortProofOut.e_vec.len() * 40    // mapping_proof.e_vec, 40bytes each for n= 2^20
    + 2 * 32; // mapping_proof.tr, 64bytes (Schnorr signature)

    println!("Expected proof size (bytes): {}", expected_proof_size);
    println!("Actual encoding size (bytes): {}", encoded.len());

    let decoded: SubCircuitProofShort = bincode::deserialize(&encoded[..]).unwrap();

    let y_prime_in: Vec<Scalar> = decoded
      .ys_prime
      .iter()
      .map(|x| Scalar::from_bytes(&Self::concat_index2(x.to_vec())).unwrap())
      .collect();
    let e_vec_biguint: Vec<BigUint> = decoded
      .e_vec
      .iter()
      .map(|b| BigUint::from_bytes_le(b))
      .collect();

    let proofIn: SubCircuitProof = SubCircuitProof {
      ys_prime: y_prime_in, // 17 * 1024 =
      ao_prime: proof.ao_prime.clone(), //30
      M: decoded.M.clone(),             //1
      R: decoded.R.clone(),             //1
      Cs: decoded.Cs.clone(),           // 1023
      S: decoded.S.clone(),             //31
      T: decoded.T.clone(),             //31
      mapping_proof: InputMappingInternalProof {
        e_vec: e_vec_biguint,
        tr: decoded.tr.clone(),
      },
    };

    proofIn
  }

  pub fn concat_index2(y_prime_bytes: Vec<u8>) -> [u8; 32] {
    let mut y_prime_bytes_vec = y_prime_bytes;

    let zeros_base: [u8; 32] = [0u8; 32];
    let mut zeros = zeros_base[0..32 - y_prime_bytes_vec.len()].to_vec();
    //  println!("y_prime_bytes_vec {:?}", y_prime_bytes_vec);
    y_prime_bytes_vec.append(&mut zeros);

    let return_val: [u8; 32] = y_prime_bytes_vec.try_into().unwrap();
    //  println!("return_val {:?}", return_val);
    return_val
  }
}

#[derive(Debug, PartialEq)]
pub struct SubCircuitProof {
  pub ys_prime: Vec<Scalar>,
  pub ao_prime: Vec<u64>,
  pub M: CompressedGroup,
  pub R: CompressedGroup,
  pub Cs: Vec<CompressedGroup>,
  pub S: Vec<CompressedGroup>,
  pub T: Vec<CompressedGroup>,
  pub mapping_proof: InputMappingInternalProof,
}

#[derive(Clone, Debug, serde_derive::Deserialize, serde_derive::Serialize)]
pub struct SubCircuitProofShort {
  pub ys_prime: Vec<Vec<u8>>,
  pub ao_prime: Vec<u64>,
  pub M: CompressedGroup,
  pub R: CompressedGroup,
  pub Cs: Vec<CompressedGroup>,
  pub S: Vec<CompressedGroup>,
  pub T: Vec<CompressedGroup>,
  pub e_vec: Vec<Vec<u8>>,
  pub tr: SchnorrProof,
}

#[cfg(test)]
mod tests {

  use super::super::montgomery::random64_mod;
  use super::*;
  use rand::rngs::OsRng;

  #[test]
  fn test_arithmetic_circuit() {
    let n = (2_usize).pow(10 as u32); //validate values are even numbers 2, 4, 8,....20

    println!("Circuit size: {}", n);

    let sc = SubCircuitSystem::new(b"unit test", n);

    let mut prover_transcript = Transcript::new(b"unit test");

    let mut csprng: OsRng = OsRng;

    let a: Vec<u64> = vec![random64_mod(&mut csprng); HYPOTHESIS_SIZE];
    let alpha: Vec<u64> = (0..HYPOTHESIS_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();
    let v: Vec<Scalar> = (0..HYPOTHESIS_SIZE)
      .map(|_| Scalar::random(&mut csprng))
      .collect();

    let pedersen: Vec<CompressedGroup> = sc.mapping.compute_pederson(&a, &v);

    let phi = Scalar::random(&mut csprng);

    let proof = sc
      .prove(&a, &alpha, &v, phi, n, &mut prover_transcript)
      .unwrap();

    let mut verifier_transcript = Transcript::new(b"unit test");
    assert_eq!(
      sc.verify(&pedersen, n, &proof, &mut verifier_transcript),
      Ok(())
    );
  }
}
