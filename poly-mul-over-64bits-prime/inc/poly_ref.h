#pragma once

#include "defs.h"
#include "ntt_init.h"

EXTERNC_BEGIN


typedef struct poly_s {
  uint64_t *coef;
  uint32_t len; 
} poly_t;

uint64_t evaluate_poly(uint64_t co[], uint32_t len, uint64_t x);

void polynomial_mul_redix2(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]);

void polynomial_mul_redix4(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]);

void polynomial_mul_normal(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]);

void poly_factory(poly_t p[], uint32_t poly_nums, uint32_t coff_len, uint64_t buf[]);

uint32_t bit_num(uint32_t n);

int poly_mul_continuous(const ntt_pre_table_t *t, const poly_t ins[], uint32_t poly_nums, poly_t *os);

EXTERNC_END
