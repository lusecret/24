#include "poly_mul.h"



static inline int is_power_of_two(uint32_t n) {
    if ((n & (n - 1)) == 0) {
        return 1;
    } else {
        return 0;
    }
}

int poly_mul_eval(const poly_t ins[], uint32_t poly_nums, poly_t *outp, const uint64_t x, uint64_t *y_prime) {

  if (poly_nums > MAX_POLY_NUMS || !is_power_of_two(poly_nums) || outp == NULL || outp->coef == NULL) {
    return ERROR_ILLEGAL_PARAMETER;
  }

  const ntt_pre_table_t *t = get_ntt_table();
  if (t == NULL) {
    return ERROR_NTT_TABLE_EMPTY;
  }
  uint32_t out_coff_num = ins[0].len << (bit_num(poly_nums) - 1);
  if (out_coff_num > MAX_NTT_NUM) {
    return ERROR_OUT_OF_NTT_RANGE;
  }

  GUARD(poly_mul_continuous(t, ins, poly_nums, outp))

  size_t half_len = outp->len >> 1;

  // only estimate polynomials from the third iterm to the highest iterm
  *y_prime = evaluate_poly(outp->coef + 2, half_len - 1, x);

  outp->len = half_len + 1;
  return SUCCESS;
}

int poly_mul_all(const poly_t ins[], uint32_t poly_nums, poly_t *outp) {

  if (poly_nums > MAX_POLY_NUMS || !is_power_of_two(poly_nums) || outp == NULL || outp->coef == NULL) {
    return ERROR_ILLEGAL_PARAMETER;
  }

  const ntt_pre_table_t *t = get_ntt_table();
  if (t == NULL) {
    return ERROR_NTT_TABLE_EMPTY;
  }
  uint32_t out_coff_num = ins[0].len << (bit_num(poly_nums) - 1);
  if (out_coff_num > MAX_NTT_NUM) {
    return ERROR_OUT_OF_NTT_RANGE;
  }

  GUARD(poly_mul_continuous(t, ins, poly_nums, outp))

  size_t half_len = outp->len >> 1;
  outp->len = half_len + 1;
  return SUCCESS;
}
