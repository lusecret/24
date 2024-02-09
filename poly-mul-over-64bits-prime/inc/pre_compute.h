// Copyright IBM Inc. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <string.h>

#include "defs.h"

EXTERNC_BEGIN

// We dont care about the performance of the functions
// in this file, as all of their output serves as
// precomputaitons that we can cache for the NTT computations.

static inline uint64_t bit_rev_idx(uint64_t idx, uint64_t width)
{
  uint64_t ret = 0;
  while(width > 0) {
    width--;
    ret += ((idx & 1) << width);
    idx >>= 1;
  }

  return ret;
}

static inline void bit_rev(uint64_t       w_powers[],
                           const uint64_t w[],
                           const uint64_t N,
                           const uint64_t width)
{
  for(size_t i = 0; i < N; i++) {
    w_powers[bit_rev_idx(i, width)] = w[i];
  }
}

static inline void calc_w(uint64_t       w_powers_rev[],
                          const uint64_t w,
                          const uint64_t N,
                          const uint64_t q,
                          const uint64_t width)
{
  uint64_t w_powers[N];
  w_powers[0] = 1;
  for(size_t i = 1; i < N; i++) {
    w_powers[i] = (uint64_t)(((__uint128_t)w_powers[i - 1] * w) % q);
  }
  
  bit_rev(w_powers_rev, w_powers, N, width);
}

static inline void calc_w_inv(uint64_t       w_inv_rev[],
                              const uint64_t w_inv,
                              const uint64_t N,
                              const uint64_t q,
                              const uint64_t width)
{
  uint64_t w_inv_powers[N];
  w_inv_powers[0] = 1;
  for(size_t i = 1; i < N; i++) {
    w_inv_powers[i] = (uint64_t)(((__uint128_t)w_inv_powers[i - 1] * w_inv) % q);
  }

  bit_rev(w_inv_rev, w_inv_powers, N, width);
}

static inline void calc_w_con(uint64_t       w_con[],
                              const uint64_t w[],
                              const uint64_t N,
                              const uint64_t q,
                              const uint64_t word_size)
{
  for(size_t i = 0; i < N; i++) {
    w_con[i] = ((__uint128_t)w[i] << word_size) / q;
  }
}

static inline uint64_t
calc_ninv_con(const uint64_t Ninv, const uint64_t q, const uint64_t word_size)
{
  return ((__uint128_t)Ninv << word_size) / q;
}

static inline void expand_w(uint64_t       w_expanded[],
                            const uint64_t w[],
                            const uint64_t N,
                            const uint64_t q)
{
  w_expanded[0] = w[0];
  w_expanded[1] = 0;
  w_expanded[2] = w[1];
  w_expanded[3] = 0;
  for(size_t i = 4; i < 2 * N; i += 2) {
    w_expanded[i] = w[i / 2];

    if(i % 4 == 0) {
      const __uint128_t t = w_expanded[i / 2];
      w_expanded[i + 1]   = (t * w[i / 2]) % q;
    } else {
      const __uint128_t t = w_expanded[(i - 2) / 2];
      w_expanded[i + 1]   = q - ((t * w[i / 2]) % q);
    }
  }
}


EXTERNC_END
