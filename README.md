# Submission 63

## Configure Environment 

Download rust and run the following command to set  it to the correct nightly build version:

`rustup override set nightly-2022-08-11-x86_64`

## Get code compiled

1. Open your terminal and CD to poly-mul-over-64bits-prime folder and type `make lib` command to create the C library libpolyntt64bits.dylib (Mac) or libpolyntt64bits.so (Linux). While our protocol is coded in Rust, the comput_(sub)circuit_keys operations are mostly coded in C to leverage open-source code for fast NTT implementation ( https://github.com/IBM/optimized-number-theoretic- transform-implementations).

3. Make sure the  .so or .dylib file you created from the earlier step is in the path of rustc.
   

 
## Benchmark - Prover and Verifier Runtime

Make sure `"-C", "target-cpu=native",` flags are turned on (.cargo/config file)

1. Goto subcircuit-64bits-binaryboost directory and type `cargo bench` to benchmark the prover/verifier runtime 


Benchmarking commits_verify_benchmark/binary_circuit_prove for 1048576 sequentia                                                                              
commits_verify_benchmark/binary_circuit_prove for 1048576 sequential multiplications
      time:   [866.14 ms 869.76 ms 874.56 ms]
      change: [-1.5112% -1.0732% -0.4841%] (p = 0.00 < 0.05)
      Change within noise threshold.
Found 1 outliers among 10 measurements (10.00%)
  1 (10.00%) high mild


Benchmarking commits_verify_benchmark/binary_circuit_verify for 1048576 sequential multiplications: Collecting 10 sam                                                                                                                     
commits_verify_benchmark/binary_circuit_verify for 1048576 sequential multiplications                                          
  time:   [16.967 ms 17.030 ms 17.096 ms]
  change: [-1.0206% +1.5018% +3.8182%] (p = 0.26 > 0.05)
  No change in performance detected.

## Random circuit

The random circuit we use in benchmarking takes all input bits (b') and then performs `n` sequential multiplications on itself.
