#include "test.h"

#define NUM_TEST 500L

void polynomial_mul_standard(const ntt_pre_table_t *t, const uint64_t a[], const uint64_t b[], uint64_t c[]) {

  memset(c, 0, t->n * sizeof(uint64_t));

  uint64_t len = t->n / 2;
  for (uint64_t i = 0; i < len; i++) {
    for (uint64_t j = 0; j < len; j++) {
       c[i + j] += mul_mod_withmont(a[i], b[j]);
       c[i + j] = c[i + j] % t->q; 
    }
  }

  for (uint64_t i = 0; i < t->n; i++) {
    c[i] = c[i] % t->q;
  }
}

int test_ntt_radix2(const ntt_pre_table_t *t)
{
  uint64_t a_orig[t->n];
  random_buf(a_orig, t->n, t->q);
  uint64_t a[t->n];
  memcpy(a, a_orig, sizeof(a));

  fwd_ntt_ref_harvey(a, t->n, t->q, t->w_powers.ptr, t->w_powers_con.ptr);

  inv_ntt_ref_harvey(a, t->n, t->q, t->n_inv, WORD_SIZE, t->w_inv_powers.ptr,
                     t->w_inv_powers_con.ptr);

  GUARD_MSG(memcmp(a_orig, a, sizeof(a)), "Bad results after radix-2 inv\n");

  return SUCCESS;
}

int test_polynomial_mul(const ntt_pre_table_t *t) {

  uint64_t a[t->n];
  uint64_t b[t->n];
  uint64_t c1[t->n];
  uint64_t c2[t->n];

  uint64_t len = t->n / 2;

  // Method 1: Using NTT calculation
  memset(a, 0, sizeof(a));
  memset(b, 0, sizeof(b));
  memset(c1, 0, sizeof(c1));

  random_buf(a, len, t->q);       
  random_buf(b, len, t->q);   

  polynomial_mul_redix2(t, a, b, c1);

  // Method 2: Using standard calculation
  memset(c2, 0, sizeof(c2));

  polynomial_mul_standard(t, a, b, c2);
  for (uint64_t i = 0; i < t->n; i++) {
    if (c1[i] != c2[i]) {
       printf("Bad results with standard calculating verification, c1[%lu] = %lu, c2[%lu] = %lu, \n", i, c1[i], i, c2[i]);
       return ERROR; 
    }
  }

  return SUCCESS;
}

int test_poly_mul_eval() {

  // 1. Generate simulated input polynomials
  const uint64_t Q = get_Q();

  uint64_t ping[MAX_NTT_NUM], pong[MAX_NTT_NUM];

  // The form of polynomial is (a + bx)
  const uint32_t coff_nums = 2; 

  const uint32_t poly_nums[3] = {8, 512, MAX_POLY_NUMS}; 
  for (uint32_t i = 0; i < sizeof(poly_nums)/ sizeof(uint32_t); i++) {
    memset(ping, 0, sizeof(uint64_t) * MAX_NTT_NUM);
    memset(pong, 0, sizeof(uint64_t) * MAX_NTT_NUM);

    random_buf(ping, poly_nums[i] * coff_nums, Q);  

    poly_t ins[poly_nums[i]], outp;  
    poly_factory(ins, poly_nums[i], coff_nums, ping); 

    uint32_t out_coff_num = ins[0].len << (bit_num(poly_nums[i]) - 1);
    poly_factory(&outp, 1, out_coff_num, pong);

    // 2. Test API
    uint64_t x, gamma;
    random_buf(&x, 1, Q); 

    GUARD(poly_mul_eval(ins, poly_nums[i], &outp, x, &gamma))

    // Calculate the evaluation of entire polynomial
    uint64_t r1 = evaluate_poly(outp.coef, out_coff_num, x);

    // 3. Comparison verification
    uint64_t r2 = 1;

    for (size_t k = 0; k < poly_nums[i]; k++) {
      uint64_t tmp = evaluate_poly(ins[k].coef, ins[k].len, x);
      r2 = mul_mod_withmont(tmp, r2);
    }

    if (r1 != r2) {
      printf("failure to test test_poly_mul_eval case!\n");
      return ERROR;
    }
  }

  return SUCCESS;
}

int main() {

  srand((unsigned)time(NULL));

  GUARD(init_ntt_table())

  const ntt_pre_table_t *t = get_ntt_table();

  for (int i = 0; i < table_len(); i++) {
    for (int k = 0; k < NUM_TEST; k++) {
      GUARD(test_ntt_radix2(&t[i]))
      GUARD(test_polynomial_mul(&t[i]))
    }
  }

  for (int k = 0; k < NUM_TEST; k++) {
      GUARD(test_poly_mul_eval())
  }

  destroy_ntt_table();

  printf("case pass!\n");
  return SUCCESS;
}