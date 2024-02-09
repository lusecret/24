#pragma once

#include "defs.h"
#include "poly_ref.h"

EXTERNC_BEGIN

int poly_mul_eval(const poly_t ins[], uint32_t poly_nums, poly_t *outp, const uint64_t x, uint64_t *y_prime);

int poly_mul_all(const poly_t ins[], uint32_t poly_nums, poly_t *outp);

EXTERNC_END