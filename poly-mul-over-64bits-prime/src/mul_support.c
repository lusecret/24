#include "mul_support.h"

uint64_t mul_mod(uint64_t x, uint64_t y, uint64_t n) {
  return (__uint128_t)x * (__uint128_t)y % (__uint128_t)n;
}

/////////////////////////////////////////////////////////////////
static const uint64_t Q = 1945555039024054273;
static const uint64_t QP = 1945555039024054271;
static const uint64_t R2 = 269548777697434221; 

uint64_t mont_mul_mod(uint64_t x, uint64_t y) {
  
  __uint128_t xy = (__uint128_t)x * y;

  // following are montgomery reduction: 
  uint64_t c0 = (uint64_t)xy; 
  uint64_t c1 = (uint64_t)(xy >> 64); 

  uint64_t m = c0 * QP; 
  __uint128_t mn = (__uint128_t)m * Q;
  uint64_t m1 = (uint64_t)(mn >> 64); 
  if (c0 != 0) 
    m1++;
    
  uint64_t r = c1 + m1; 
  int64_t rn = r - Q; 
  if (rn > 0)
    r = rn;
  return r;
}

uint64_t enter_mont(uint64_t x) {
  return mont_mul_mod(x, R2);
}

uint64_t back_from_mont(uint64_t x) {
  return mont_mul_mod(x, 1);
}

uint64_t mul_mod_withmont(uint64_t x, uint64_t y) {
  x = enter_mont(x);
  y = enter_mont(y);
  uint64_t z = mont_mul_mod(x, y);

  return back_from_mont(z);
}

uint64_t get_Q() {
  return Q;
}