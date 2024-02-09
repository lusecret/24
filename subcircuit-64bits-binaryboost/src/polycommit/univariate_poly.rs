use super::super::groups::group::{CompressedGroup, CompressedGroupExt, GroupElement};
use super::super::groups::random::RandomTape;
use super::super::groups::transcript::ProofTranscript;
use super::super::math::Math;
use super::super::scalar::Scalar;
use super::super::scalar::ScalarFromPrimitives;
use super::commit_errors::CommitError;
use super::commitments::{Commitments, MultiCommitGens};
use merlin::Transcript;
use rand_core::OsRng;


#[derive(Debug)]
pub struct UnivariatePoly {
  num_degrees: usize, // the number of degrees in the polynomial
  n: usize,
  m: usize,
  Co: Vec<Scalar>, // coefficients of polynomial
}

#[derive(Debug)]
pub struct UnivariatePolyGens {
  pub gens: MultiCommitGens, // n+1 G points
}

#[derive(Debug)]
pub struct UnivariatePolyBlinds {
  blinds: Vec<Scalar>,   // m+1 elements
  blind_us: Vec<Scalar>, // n-1 elements
}

#[derive(Clone, Debug, PartialEq, serde_derive::Deserialize, serde_derive::Serialize)]
pub struct UnivariatePolyCommit {
  pub C: Vec<CompressedGroup>,
  pub U: CompressedGroup,
}

impl UnivariatePolyGens {
  pub fn new(nums: usize, label: &'static [u8]) -> UnivariatePolyGens {
    let gens = MultiCommitGens::new(nums, label);
    UnivariatePolyGens { gens }
  }

  pub fn new_from(Gs: Vec<GroupElement>, h: GroupElement) -> UnivariatePolyGens {
    let gens = MultiCommitGens::from(Gs, h);
    UnivariatePolyGens { gens }
  }
}

impl UnivariatePoly {
  pub fn compute_m_n(num_degrees: usize) -> (usize, usize) {
    let log_nums = num_degrees.ilog2() as usize;

    if num_degrees == log_nums.pow2() {
      // 2^x form
      if log_nums & 1 != 0 {
        // odd number
        return ((log_nums >> 1).pow2(), ((log_nums >> 1) + 1).pow2());
      } else {
        // even number
        return ((log_nums >> 1).pow2(), (log_nums >> 1).pow2());
      }
    } else {
      // first try:
      let mut m = num_degrees.square_root();
      let mut n = num_degrees / m;
      if num_degrees != n * m {
        // second try:
        m = (m.ilog2() as usize).pow2();
        n = num_degrees / m;
      }

      return (m, n);
    }
  }

  pub fn new(Co: Vec<Scalar>) -> Self {
    let num_degrees: usize = Co.len();
    let (m, n) = Self::compute_m_n(num_degrees);
    assert_eq!(num_degrees, m * n);

    UnivariatePoly {
      num_degrees: Co.len() as usize,
      n: n,
      m: m,
      Co,
    }
  }

  pub fn new_fromsize(num_degrees: usize) -> Self {
    let mut csprng: OsRng = OsRng;

    let Co: Vec<Scalar> = (0..num_degrees)
      .map(|_i| Scalar::random(&mut csprng))
      .collect::<Vec<Scalar>>();

    UnivariatePoly::new(Co)
  }

  pub fn get_n(&self) -> usize {
    self.n
  }

  pub fn get_m(&self) -> usize {
    self.m
  }

  pub fn get_degrees(&self) -> usize {
    self.num_degrees
  }

  fn commit_inner(
    &self,
    blinds: &[Scalar],
    blind_us: &[Scalar],
    gens: &MultiCommitGens,
  ) -> Vec<CompressedGroup> {
    let blind_0us = [vec![Scalar::zero()], blind_us.to_vec()].concat();

    let Co0: Vec<Scalar> = (0..self.n).map(|i| self.Co[i] - blind_0us[i]).collect();

    let C0 = Co0.commit(&blinds[0], gens).compress();

    let C = (1..self.m)
      .map(|i| {
        self.Co[self.n * i..self.n * (i + 1)]
          .commit(&blinds[i], gens)
          .compress()
      })
      .collect();
    [vec![C0], C].concat()
  }

  fn commit_u(
    &self,
    blinds: &[Scalar],
    blind_us: &[Scalar],
    gens: &MultiCommitGens,
  ) -> CompressedGroup {
    let blind_us0 = [blind_us, &vec![Scalar::zero()]].concat();
    blind_us0.commit(&blinds[self.m], &gens).compress()
  }

  pub fn commit(
    &self,
    gens: &UnivariatePolyGens,
    random_tape: &mut RandomTape,
  ) -> (UnivariatePolyCommit, UnivariatePolyBlinds) {
    let blinds = UnivariatePolyBlinds {
      blinds: random_tape.random_vector(b"univaratepoly_blinds", self.m + 1),
      blind_us: random_tape.random_vector(b"univaratepoly_blind_us", self.n - 1),
    };

    let C = self.commit_inner(&blinds.blinds, &blinds.blind_us, &gens.gens);

    // calculate U:
    let U = self.commit_u(&blinds.blinds, &blinds.blind_us, &gens.gens);

    (UnivariatePolyCommit { C: C, U: U }, blinds)
  }

  // debug print:
  pub fn uni_poly_co_print(&self) {
    let mut total_size: usize = self.num_degrees;
    if total_size > 8 {
      total_size = 8;
    }
    // for i in 0..total_size {
    //   println!("coefficients[{:?}] = [{:?}]", i, self.Co[i].to_bytes());
    // }
    println!(
      "PolyCommitment total size = {}, log2(total_size) = {}, m = {}, n = {}",
      total_size,
      total_size.ilog2(),
      self.get_m(),
      self.get_n()
    );
  }
}

#[derive(Clone, Debug, PartialEq, serde_derive::Deserialize, serde_derive::Serialize)]
pub struct UnivariatePolyProof {
  pub t_col: Vec<Scalar>, // n elements
  pub tau: Scalar,
}

impl UnivariatePolyProof {
  fn scalar_pow(x: Scalar, n: usize) -> Scalar {
    let mut exp: [u64; 4] = [
      0x0000000000000000,
      0x0000000000000000,
      0x0000000000000000,
      0x0000000000000000,
    ];

    exp[0] = exp[0] + (n as u64);

    x.pow_vartime(&exp)
  }

  fn generate_zxm(x: Scalar, n: usize, m: usize) -> Vec<Scalar> {
    let xn = UnivariatePolyProof::scalar_pow(x, n);

    let mut Zx: Vec<Scalar> = Vec::new();
    Zx.push((1_usize).to_scalar());
    for _ in 1..m {
      let ret = Zx.last().unwrap();
      let result = ret.mul(&xn);
      Zx.push(result);
    }
    Zx
  }

  fn generate_zx(x: Scalar, n: usize, m: usize) -> Vec<Scalar> {
    let mut Zx = UnivariatePolyProof::generate_zxm(x, n, m);
    Zx.push(x);
    Zx
  }

  fn generate_xxn(x: Scalar, n: usize) -> Vec<Scalar> {
    let mut Xx: Vec<Scalar> = Vec::new();
    Xx.push((1_usize).to_scalar());
    for _ in 1..n {
      let ret = Xx.last().unwrap();
      let result = ret.mul(&x);
      Xx.push(result);
    }
    Xx
  }

  pub fn prove(
    poly: &UnivariatePoly,
    blinds: &UnivariatePolyBlinds,
    transcript: &mut Transcript,
  ) -> UnivariatePolyProof {
    // 1. generate challenge：
    let x = transcript.challenge_scalar(b"univariate_poly_proof");

    // 2. calculate: Z(x) = [1, x^n, x^{2n}, ..., x^{m-1}*n, x], m + 1 elements
    let Zx = UnivariatePolyProof::generate_zx(x, poly.n, poly.m);

    let blind_0us0 = [
      vec![Scalar::zero()],
      blinds.blind_us.to_vec(),
      vec![Scalar::zero()],
    ]
    .concat(); //n+1 elements

    let Tcol = (0..poly.n)
      .map(|i| {
        (0..=poly.m)
          .map(|j| match j {
            j if j == 0 => poly.Co[i] - blind_0us0[i],
            j if j == poly.m => blind_0us0[i + 1] * Zx[poly.m],
            _ => poly.Co[poly.n * j + i] * Zx[j],
          })
          .sum()
      })
      .collect::<Vec<Scalar>>();

    let tau: Scalar = (0..=poly.m).map(|j| blinds.blinds[j] * Zx[j]).sum();

    UnivariatePolyProof {
      t_col: Tcol,
      tau: tau,
    }
  }

  pub fn verify(
    &self,
    comm: &UnivariatePolyCommit,
    gens: &UnivariatePolyGens,
    transcript: &mut Transcript,
  ) -> Result<(), CommitError> {
    let m = comm.C.len();
    let n = self.t_col.len();

    // 1. calculate left: Com(\vec{t}, \tau)
    let lhs = self.t_col.commit(&self.tau, &gens.gens).compress();

    // 2. calculate right: (\sum\limits^{m-1}_0(T_i)*x^{in}) + U*x
    let x = transcript.challenge_scalar(b"univariate_poly_proof");

    let Zxm = UnivariatePolyProof::generate_zxm(x, n, m);

    let Gs: Vec<GroupElement> = comm.C.iter().map(|C| C.unpack().unwrap()).collect();

    let ti_gens = MultiCommitGens::from(Gs, comm.U.unpack().unwrap());
    let rhs = Zxm.commit(&x, &ti_gens).compress();

    // 3. compare result:
    if lhs == rhs {
      Ok(())
    } else {
      Err(CommitError::InternalError)
    }
  }

  pub fn evaluate(&self, transcript: Option<&mut Transcript>) -> Scalar {
    let n = self.t_col.len();

    let x = if let Some(t) = transcript {
      t.challenge_scalar(b"univariate_poly_proof_df")
    } else {
      // debug
      (2_usize).to_scalar()
    };

    let Xx = UnivariatePolyProof::generate_xxn(x, n);

    (0..n).map(|i| self.t_col[i] * Xx[i]).sum()
  }
}

#[cfg(test)]
mod tests {

  use super::super::super::groups::random::RandomTape;
  use super::UnivariatePoly;
  use super::UnivariatePolyGens;
  use super::UnivariatePolyProof;
  use merlin::Transcript;

  #[test]
  fn test_polyeval_verify() {
    let num_degrees = 16 as usize;
    let mut random_tape = RandomTape::new(b"proof");

    // 1. create polynomials
    let polys = UnivariatePoly::new_fromsize(num_degrees);

    // 2. create generations
    let gens = UnivariatePolyGens::new(polys.n, b"gens_polyeval_verify");

    // 3. generate commitments
    let (comms, blinds) = polys.commit(&gens, &mut random_tape);

    // 4. create proof
    let mut prover_transcript = Transcript::new(b"example");
    let proof = UnivariatePolyProof::prove(&polys, &blinds, &mut prover_transcript);

    // 5. verify:
    let mut verifier_transcript = Transcript::new(b"example");
    assert!(proof
      .verify(&comms, &gens, &mut verifier_transcript)
      .is_ok());
  }
}
