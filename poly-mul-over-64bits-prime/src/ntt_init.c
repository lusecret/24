#include "ntt_init.h"

static ntt_pre_table_t *ntt_table = NULL;

typedef struct param_s {
  uint64_t m;      
  uint64_t q;      
  uint64_t w;
  uint64_t w_inv; // w^(-1) mod q
  mul_op_t n_inv; // 2^(-m) mod q
} param_t;

static param_t params[] = {
  {.m = 4, .q = 1945555039024054273, .w = 303645048902088856, .w_inv = 1078230707361210486, .n_inv.op = 1823957849085050881}, 
  {.m = 5, .q = 1945555039024054273, .w = 12231171487184614, .w_inv = 1832583930548921823, .n_inv.op = 1884756444054552577}, 
  {.m = 6, .q = 1945555039024054273, .w = 7247923270434576, .w_inv = 781781381413375109, .n_inv.op = 1915155741539303425}, 
  {.m = 7, .q = 1945555039024054273, .w = 30482509304276252, .w_inv = 1104617846957566670, .n_inv.op = 1930355390281678849}, 
  {.m = 8, .q = 1945555039024054273, .w = 14301632482754718, .w_inv = 795955487084625818, .n_inv.op = 1937955214652866561}, 
  {.m = 9, .q = 1945555039024054273, .w = 6554929604637416, .w_inv = 148991015728414829, .n_inv.op = 1941755126838460417}, 
  {.m = 10, .q = 1945555039024054273, .w = 4841519701404995, .w_inv = 117831558396294910, .n_inv.op = 1943655082931257345}, 
  {.m = 11, .q = 1945555039024054273, .w = 787081436179323, .w_inv = 838324624550460183, .n_inv.op = 1944605060977655809}, 
};

static inline int allocate_aligned_array(aligned64_ptr_t *aptr, size_t qw_num) {
  size_t size_to_allocate = qw_num * sizeof(uint64_t) + 64;
  if(NULL == ((aptr->base) = malloc(size_to_allocate))) {
    printf("Allocation error");
    return ERROR;
  }
  aptr->ptr = (uint64_t *)(((uint64_t)aptr->base & (~0x3fULL)) + 64);
  return SUCCESS;
}

static inline void free_aligned_array(aligned64_ptr_t *aptr) {
  free(aptr->base);
  aptr->base = NULL;
  aptr->ptr  = NULL;
}

int init_ntt_table() {

  const size_t table_len = sizeof(params) / sizeof(param_t);

  // ntt_table
  if(NULL == (ntt_table = malloc(sizeof(ntt_pre_table_t) * table_len))) {
    printf("Allocation error");
    return ERROR_MEMORY_ALLOCATION;
  }

  for (size_t i = 0; i< table_len; i++) {

    // For brevity
    const uint64_t q     = params[i].q;
    const uint64_t w     = params[i].w;
    const uint64_t m     = params[i].m;
    const uint64_t w_inv = params[i].w_inv;
    const uint64_t n     = 1UL << params[i].m; 

    ntt_table[i].q = q;
    ntt_table[i].w = w;
    ntt_table[i].m = m;
    ntt_table[i].w_inv= w_inv;
    ntt_table[i].n_inv.op = params[i].n_inv.op;

    ntt_table[i].n        = n;
    ntt_table[i].n_inv.con = calc_ninv_con(ntt_table[i].n_inv.op, q, WORD_SIZE);
    ntt_table[i].q2        = 2 * q;
    ntt_table[i].q4        = 4 * q;

    // Prepare radix-2 w-powers
    allocate_aligned_array(&ntt_table[i].w_powers, n);
    calc_w(ntt_table[i].w_powers.ptr, w, n, q, m);

    allocate_aligned_array(&ntt_table[i].w_powers_con, n);
    calc_w_con(ntt_table[i].w_powers_con.ptr, ntt_table[i].w_powers.ptr, n, q, WORD_SIZE);

    allocate_aligned_array(&ntt_table[i].w_inv_powers, n);
    calc_w_inv(ntt_table[i].w_inv_powers.ptr, w_inv, n, q, m);

    allocate_aligned_array(&ntt_table[i].w_inv_powers_con, n);
    calc_w_con(ntt_table[i].w_inv_powers_con.ptr, ntt_table[i].w_inv_powers.ptr, n, q, WORD_SIZE);

    // Expand the list of powers to support the radix-4 case.
    allocate_aligned_array(&ntt_table[i].w_powers_r4, 2 * n);
    expand_w(ntt_table[i].w_powers_r4.ptr, ntt_table[i].w_powers.ptr, n, q);

    allocate_aligned_array(&ntt_table[i].w_powers_con_r4, 2 * n);
    calc_w_con(ntt_table[i].w_powers_con_r4.ptr, ntt_table[i].w_powers_r4.ptr, 2 * n, q, WORD_SIZE);

    allocate_aligned_array(&ntt_table[i].w_inv_powers_r4, 2 * n);
    expand_w(ntt_table[i].w_inv_powers_r4.ptr, ntt_table[i].w_inv_powers.ptr, n, q);

    allocate_aligned_array(&ntt_table[i].w_inv_powers_con_r4, 2 * n);
    calc_w_con(ntt_table[i].w_inv_powers_con_r4.ptr, ntt_table[i].w_inv_powers_r4.ptr, 2 * n, q,
              WORD_SIZE);
  }

  return SUCCESS;
}

void destroy_ntt_table() {
  for (size_t i = 0; i< sizeof(params) / sizeof(param_t); i++) {
    // for radix-2
    free_aligned_array(&ntt_table[i].w_powers);
    free_aligned_array(&ntt_table[i].w_powers_con);
    free_aligned_array(&ntt_table[i].w_inv_powers);
    free_aligned_array(&ntt_table[i].w_inv_powers_con);

    // for radix-4
    free_aligned_array(&ntt_table[i].w_powers_r4);
    free_aligned_array(&ntt_table[i].w_powers_con_r4);
    free_aligned_array(&ntt_table[i].w_inv_powers_r4);
    free_aligned_array(&ntt_table[i].w_inv_powers_con_r4);
  }
  
  free(ntt_table);
  ntt_table = NULL;
}

const ntt_pre_table_t* get_ntt_table() {
  return ntt_table;
}

int table_len() {
  return sizeof(params) / sizeof(param_t);
}