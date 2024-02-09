#![feature(int_log)]
use libsubcircuit_64bits::groups::group::CompressedGroup;
use libsubcircuit_64bits::montgomery::random64_mod;
use libsubcircuit_64bits::scalar::Scalar;
use libsubcircuit_64bits::subcircuit;
use merlin::Transcript;
use rand::rngs::OsRng;

fn main() {
  for &s in [10, 12, 14, 16, 18, 20].iter() {
    let n = (2_usize).pow(s as u32);

    let sc: subcircuit::SubCircuitSystem = subcircuit::SubCircuitSystem::new(b"example", n);

    println!("n = {:?}, mb = {:?}, b = {:?}, ", sc.get_n(), sc.get_mblen(), sc.get_blen());

    let mut prover_transcript = Transcript::new(b"example");

    let mut csprng: OsRng = OsRng;

    let a: Vec<u64> = vec![random64_mod(&mut csprng); subcircuit::HYPOTHESIS_SIZE];
    let alpha: Vec<u64> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();
    let v: Vec<Scalar> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| Scalar::random(&mut csprng))
      .collect();
    let pedersen: Vec<CompressedGroup> = sc.get_mapping().compute_pederson(&a, &v);
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
