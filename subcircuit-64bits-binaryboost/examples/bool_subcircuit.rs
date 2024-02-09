#![feature(int_log)]
use libsubcircuit_64bits::groups::group::CompressedGroup;
use libsubcircuit_64bits::montgomery::random64_mod;
use libsubcircuit_64bits::scalar::Scalar;
use libsubcircuit_64bits::binary_boost;
use libsubcircuit_64bits::subcircuit::HYPOTHESIS_SIZE;
use merlin::Transcript;
use rand::rngs::OsRng;
use rand_core::RngCore;

fn main() {
  for &s in [10, 12, 14, 16, 18, 20].iter() {
    let n = (2_usize).pow(s as u32);

    let sc: binary_boost::BinaryBoostCircuitSystem = binary_boost::BinaryBoostCircuitSystem::new(b"example", n, HYPOTHESIS_SIZE * 32);
    println!("binary_boost: n = {:?}, mb = {:?}, b = {:?}, ", sc.cir.get_n(), sc.cir.get_mblen(), sc.cir.get_blen());

    let mut prover_transcript = Transcript::new(b"example");

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

    let proof = sc
      .prove(&a, &alpha, &v, phi, n, &mut prover_transcript)
      .unwrap();

    let mut verifier_transcript = Transcript::new(b"example");
    assert_eq!(
      sc.verify(&pedersen, n, &proof, &mut verifier_transcript),
      Ok(())
    );
  }
  println!("Example run completed!");
}
