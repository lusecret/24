#include "poly_ref.h"
#include "mul_support.h"
#include "ntt_radix4.h"
#include "ntt_reference.h"
#include "ntt_seal.h"

typedef void (*polynomial_mul_function)(const ntt_pre_table_t *, const uint64_t a[], const uint64_t b[], uint64_t c[]);

uint64_t evaluate_poly(uint64_t co[], uint32_t len, uint64_t x) {
  
  uint64_t sum = enter_mont(co[0]);
  uint64_t mul = enter_mont(1);
  uint64_t xm = enter_mont(x);

  for (uint32_t i = 1; i < len; i++) {
    uint64_t com = enter_mont(co[i]);
    mul = mont_mul_mod(xm, mul);
    uint64_t tmp = mont_mul_mod(mul, com);
    sum += tmp; 
    sum = sum % get_Q();
  }
  return back_from_mont(sum);
}

void polynomial_mul_redix2(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]) {

  uint64_t at[t->n];
  uint64_t bt[t->n];

  size_t len = t->n >> 1;
  memcpy(at, a, len * sizeof(uint64_t));
  memcpy(bt, b, len * sizeof(uint64_t));
  memset(at + len, 0, len * sizeof(uint64_t));
  memset(bt + len, 0, len * sizeof(uint64_t));

  fwd_ntt_ref_harvey(at, t->n, t->q, t->w_powers.ptr, t->w_powers_con.ptr);

  fwd_ntt_ref_harvey(bt, t->n, t->q, t->w_powers.ptr, t->w_powers_con.ptr);

  for (uint64_t i = 0; i < t->n; i++) {
    c[i] = mul_mod_withmont(at[i], bt[i]);
  }

  inv_ntt_ref_harvey(c, t->n, t->q, t->n_inv, WORD_SIZE, t->w_inv_powers.ptr,
                     t->w_inv_powers_con.ptr);
}

void polynomial_mul_redix4(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]) {

  uint64_t at[t->n];
  uint64_t bt[t->n];

  size_t len = t->n >> 1;
  memcpy(at, a, len * sizeof(uint64_t));
  memcpy(bt, b, len * sizeof(uint64_t));
  memset(at + len, 0, len * sizeof(uint64_t));
  memset(bt + len, 0, len * sizeof(uint64_t));

  fwd_ntt_radix4(at, t->n, t->q, t->w_powers_r4.ptr, t->w_powers_con_r4.ptr);

  fwd_ntt_radix4(bt, t->n, t->q, t->w_powers_r4.ptr, t->w_powers_con_r4.ptr);

  for (uint64_t i = 0; i < t->n; i++) {
    c[i] = mul_mod_withmont(at[i], bt[i]);
  }

  inv_ntt_radix4(c, t->n, t->q, t->n_inv, t->w_inv_powers_r4.ptr,
              t->w_inv_powers_con_r4.ptr);
}


void polynomial_mul_seal(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]) {

  uint64_t at[t->n];
  uint64_t bt[t->n];

  size_t len = t->n >> 1;
  memcpy(at, a, len * sizeof(uint64_t));
  memcpy(bt, b, len * sizeof(uint64_t));
  memset(at + len, 0, len * sizeof(uint64_t));
  memset(bt + len, 0, len * sizeof(uint64_t));

  fwd_ntt_seal(at, t->n, t->q, t->w_powers.ptr, t->w_powers_con.ptr);
  fwd_ntt_seal(bt, t->n, t->q, t->w_powers.ptr, t->w_powers_con.ptr);

  for (uint64_t i = 0; i < t->n; i++) {
    c[i] = mul_mod_withmont(at[i], bt[i]);
  }

  inv_ntt_seal(c, t->n, t->q, t->n_inv.op, t->n_inv.con,
                      t->w_inv_powers.ptr, t->w_inv_powers_con.ptr);            
}


void polynomial_mul_normal(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]) {

  memset(c, 0, t->n * sizeof(uint64_t));

  uint64_t len = t->n / 2;
  for (uint64_t i = 0; i < len; i++) {
    for (uint64_t j = 0; j < len; j++) {
       c[i + j] += mul_mod_withmont(a[i], b[j]);
    }
  }
}

void poly_copy(poly_t dst[], const poly_t src[], uint32_t poly_nums, uint64_t buf[]) {

  uint32_t coff_num = src[0].len;
  memset(buf, 0, sizeof(uint64_t) * coff_num);
  uint32_t offset = 0;

  for (size_t i = 0; i < poly_nums; i++) {
    dst[i].coef = &buf[offset];
    memcpy(dst[i].coef, src[i].coef, sizeof(uint64_t) * src[i].len);
    dst[i].len = src[i].len;
    offset += coff_num << 1;
  }
}

void poly_factory(poly_t p[], uint32_t poly_nums, uint32_t coff_len, uint64_t buf[]) {

  uint32_t offset = 0;
  for (size_t i = 0; i < poly_nums; i++) {
    p[i].coef = &buf[offset];
    p[i].len = coff_len;
    offset += coff_len;
  }
}

int poly_mul_twobytwo(const ntt_pre_table_t *t, const poly_t in[], uint32_t poly_nums, poly_t out[], polynomial_mul_function multiply) {

  size_t len = poly_nums >> 1;
  for (size_t i = 0; i < len; i ++) {
    multiply(t, in[i].coef, in[i + len].coef, out[i].coef);
  }
  return SUCCESS;
}

uint32_t bit_num(uint32_t n) {
    uint32_t num_bits = 0;
    while (n > 0) {
        n >>= 1;
        num_bits++;
    }
    return num_bits;
}

int poly_mul_continuous(const ntt_pre_table_t *t, const poly_t ins[], uint32_t poly_nums, poly_t *os) {

  uint64_t ping[PINGPONG_BUFFER_SIZE];
  uint64_t pong[PINGPONG_BUFFER_SIZE];
  poly_t in[poly_nums];
  poly_t out[poly_nums];
  memset(ping, 0, sizeof(uint64_t) * PINGPONG_BUFFER_SIZE);
  memset(pong, 0, sizeof(uint64_t) * PINGPONG_BUFFER_SIZE);

  poly_copy(in, ins, poly_nums, ping);

  uint32_t coff_nums = in[0].len;
  uint32_t next_coffs = 0;
  for (size_t num = poly_nums; num > 2; num = num >> 1) {
    next_coffs = coff_nums << 1;

    uint32_t next_poly_nums = num >> 1;
    poly_factory(out, next_poly_nums, next_coffs, pong);

    if (coff_nums <= 4) { 
      ntt_pre_table_t st;
      st.n = next_coffs;
      st.q = t[0].q;

      poly_mul_twobytwo(&st, in, num, out, polynomial_mul_normal); 
    } else {
      uint32_t num_bits = bit_num(coff_nums);
      poly_mul_twobytwo(&t[num_bits - 4], in, num, out, polynomial_mul_redix2); 
    }

    poly_copy(in, out, next_poly_nums, ping); 
    coff_nums = next_coffs;
  }

  // last time:
  poly_factory(out, 1, coff_nums << 1, pong);
  if (coff_nums <= 4) {
    ntt_pre_table_t st;
    st.n = coff_nums << 1;
    poly_mul_twobytwo(&st, in, 2, out, polynomial_mul_normal); 
  } else {
    uint32_t num_bits = bit_num(coff_nums);
    poly_mul_twobytwo(&t[num_bits - 4], in, 2, out, polynomial_mul_redix2); 
  }

  memcpy(os->coef, out[0].coef, sizeof(uint64_t) * out[0].len);
  os->len = out[0].len;

  return SUCCESS;
}
