
#pragma once

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "../inc/ntt_init.h"
#include "../inc/mul_support.h"
#include "../inc/ntt_radix4.h"
#include "../inc/ntt_reference.h"
#include "../inc/ntt_seal.h"
#include "../inc/poly_ref.h"
#include "../inc/poly_mul.h"

EXTERNC_BEGIN


static inline void random_buf(uint64_t *values, const uint64_t n, const uint64_t q) {
  for(uint64_t i = 0; i < n; i++) {
    uint32_t h = random();
    uint32_t l = random();

    values[i] = ((uint64_t)h << 32) + l ;
  }
  for(uint64_t i = 0; i < n; i++) {
    values[i] = values[i] % q;
  }
}


EXTERNC_END
