#pragma once

#include <stdlib.h>

#include "fast_mul_operators.h"
#include "pre_compute.h"

EXTERNC_BEGIN

typedef struct aligned64_ptr_s {
  void *    base; 
  uint64_t *ptr;
} aligned64_ptr_t;

typedef struct ntt_pre_table_s {
  // These parameters are predefined
  uint64_t m;     
  uint64_t q;     
  uint64_t w;
  uint64_t w_inv; // w^(-1) mod q
  mul_op_t n_inv; // 2^(-m) mod q

  // These parameters are dinamically computed based on the above values.
  uint64_t        n;
  uint64_t        qneg;
  uint64_t        q2;
  uint64_t        q4;
  aligned64_ptr_t w_powers;
  aligned64_ptr_t w_powers_con;
  aligned64_ptr_t w_inv_powers;
  aligned64_ptr_t w_inv_powers_con;

  // For radix-4 tests
  aligned64_ptr_t w_powers_r4;
  aligned64_ptr_t w_powers_con_r4;
  aligned64_ptr_t w_inv_powers_r4;
  aligned64_ptr_t w_inv_powers_con_r4;

} ntt_pre_table_t;

int init_ntt_table();
void destroy_ntt_table();

const ntt_pre_table_t* get_ntt_table();

int table_len();



EXTERNC_END