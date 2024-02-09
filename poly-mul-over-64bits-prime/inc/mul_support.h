#pragma once

#include <stdlib.h>

#include "fast_mul_operators.h"
#include "pre_compute.h"

EXTERNC_BEGIN

uint64_t mul_mod(uint64_t x, uint64_t y, uint64_t n);

uint64_t mul_mod_withmont(uint64_t x, uint64_t y);

uint64_t enter_mont(uint64_t x);
uint64_t back_from_mont(uint64_t x);
uint64_t mont_mul_mod(uint64_t x, uint64_t y);

uint64_t get_Q();

EXTERNC_END