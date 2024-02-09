#![feature(int_log)]
use criterion::*;
use libsubcircuit_64bits::groups::group::CompressedGroup;
use libsubcircuit_64bits::montgomery::random64_mod;
use libsubcircuit_64bits::scalar::Scalar;
use libsubcircuit_64bits::subcircuit;
use libsubcircuit_64bits::binary_boost;
use merlin::Transcript;
use rand::rngs::OsRng;
use rand_core::RngCore;

fn ari_circuit_prove_benchmark(c: &mut Criterion) {
  for &s in [20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("commits_verify_benchmark");
    group.plot_config(plot_config);

    let num_degrees = (2_usize).pow(s as u32);

    let sc = subcircuit::SubCircuitSystem::new(b"proof", num_degrees);

    let mut csprng: OsRng = OsRng;
    let a: Vec<u64> = vec![random64_mod(&mut csprng); subcircuit::HYPOTHESIS_SIZE];
    let alpha: Vec<u64> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();
    let v: Vec<Scalar> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| Scalar::random(&mut csprng))
      .collect();
    let phi = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"proof");

    let name = format!("ari_circuit_prove_{}", num_degrees);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let _ = sc.prove(
          black_box(&a),
          black_box(&alpha),
          black_box(&v),
          black_box(phi),
          black_box(num_degrees),
          black_box(&mut prover_transcript),
        );
      });
    });
    group.finish();
  }
}

fn ari_circuit_verify_benchmark(c: &mut Criterion) {
  for &s in [20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("commits_verify_benchmark");
    group.plot_config(plot_config);

    let num_degrees = (2_usize).pow(s as u32);

    let sc = subcircuit::SubCircuitSystem::new(b"proof", num_degrees);

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

    let mut prover_transcript = Transcript::new(b"proof");
    let proof = sc
      .prove(&a, &alpha, &v, phi, num_degrees, &mut prover_transcript)
      .unwrap();

    let name = format!("ari_circuit_verify_{}", num_degrees);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"proof");
        assert_eq!(
          sc.verify(
            black_box(&pedersen),
            black_box(num_degrees),
            black_box(&proof),
            black_box(&mut verifier_transcript)
          ),
          Ok(())
        );
      });
    });
    group.finish();
  }
}

fn bboost_circuit_prove_benchmark(c: &mut Criterion) {
  for &s in [16,18,20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("commits_verify_benchmark");
    group.plot_config(plot_config);

    let num_degrees = (2_usize).pow(s as u32);

    let sc = binary_boost::BinaryBoostCircuitSystem::new(b"proof", num_degrees, subcircuit::HYPOTHESIS_SIZE * 32);

    let mut csprng: OsRng = OsRng;
    let a: Vec<u64> = vec![csprng.next_u32() as u64; subcircuit::HYPOTHESIS_SIZE];
    let alpha: Vec<u64> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();
    let v: Vec<Scalar> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| Scalar::random(&mut csprng))
      .collect();
    let phi = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"proof");

    let name = format!("binary_circuit_prove for {} sequential multiplications", num_degrees);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let _ = sc.prove(
          black_box(&a),
          black_box(&alpha),
          black_box(&v),
          black_box(phi),
          black_box(num_degrees),
          black_box(&mut prover_transcript),
        );
      });
    });
    group.finish();
  }
}

fn bboost_circuit_verify_benchmark(c: &mut Criterion) {
  for &s in [16,18,20].iter() {
    let plot_config = PlotConfiguration::default().summary_scale(AxisScale::Logarithmic);
    let mut group = c.benchmark_group("commits_verify_benchmark");
    group.plot_config(plot_config);

    let num_degrees = (2_usize).pow(s as u32);

    let sc = binary_boost::BinaryBoostCircuitSystem::new(b"proof", num_degrees, subcircuit::HYPOTHESIS_SIZE * 32);

    let mut csprng: OsRng = OsRng;
    let a: Vec<u64> = vec![csprng.next_u32() as u64; subcircuit::HYPOTHESIS_SIZE];
    let alpha: Vec<u64> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| random64_mod(&mut csprng))
      .collect();
    let v: Vec<Scalar> = (0..subcircuit::HYPOTHESIS_SIZE)
      .map(|_| Scalar::random(&mut csprng))
      .collect();
    let pedersen: Vec<CompressedGroup> = sc.cir.get_mapping().compute_pederson(&a, &v);
    let phi = Scalar::random(&mut csprng);

    let mut prover_transcript = Transcript::new(b"proof");
    let proof = sc
      .prove(&a, &alpha, &v, phi, num_degrees, &mut prover_transcript)
      .unwrap();

    let name = format!("binary_circuit_verify for {} sequential multiplications", num_degrees);
    group.bench_function(&name, move |b| {
      b.iter(|| {
        let mut verifier_transcript = Transcript::new(b"proof");
        assert_eq!(
          sc.verify(
            black_box(&pedersen),
            black_box(num_degrees),
            black_box(&proof),
            black_box(&mut verifier_transcript)
          ),
          Ok(())
        );
      });
    });
    group.finish();
  }
}

fn set_duration() -> Criterion {
  Criterion::default().sample_size(10)
}

criterion_group! {
name = benches_snark;
config = set_duration();
//targets = ari_circuit_prove_benchmark, ari_circuit_verify_benchmark, 
targets = bboost_circuit_prove_benchmark, bboost_circuit_verify_benchmark
//targets = bboost_circuit_verify_benchmark
}

criterion_main!(benches_snark);
