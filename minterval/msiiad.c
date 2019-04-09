#include "msiiad.h"

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t MSIIAD = 9;
uint64_t MAX_TRACE_LENGTH = 10000000;
uint64_t TWO_TO_THE_POWER_OF_32;

typedef unsigned __int128 uint128_t;
uint128_t UINT64_MAX_VALUE = 18446744073709551615U;
uint128_t TWO_TO_THE_POWER_OF_64;

// ---------- trace
uint64_t  tc         = 0;             // trace counter
uint64_t* pcs        = (uint64_t*) 0; // trace of program counter values
uint64_t* tcs        = (uint64_t*) 0; // trace of trace counters to previous values
uint64_t* values     = (uint64_t*) 0; // trace of values
uint64_t* data_types = (uint64_t*) 0; // memory range or integer interval
uint64_t* steps      = (uint64_t*) 0;
uint64_t* vaddrs     = (uint64_t*) 0; // trace of virtual addresses
uint64_t* addsub_corrs    = (uint64_t*) 0;
uint64_t* muldivrem_corrs = (uint64_t*) 0;
uint64_t* corr_validitys  = (uint64_t*) 0;
bool*     hasmns          = (bool*) 0;

// ---------- propagation
uint64_t* mr_sds          = (uint64_t*) 0; // most recent sd to
// propagation from left to right b = a + 1; (chain)
// ld_froms and ld_froms_tc
// propagation from right to left b = a + 1;
uint64_t* sd_to_idxs      = (uint64_t*) 0;
struct sd_to_tc {
  uint64_t tc[MAX_SD_TO_NUM];
} *sd_tos;
uint64_t lo_prop[MAX_NUM_OF_INTERVALS];
uint64_t up_prop[MAX_NUM_OF_INTERVALS];
uint8_t  mints_num_prop = 0;
uint64_t step_prop;

// ---------- read history
uint64_t  rc = 0; // read counter
uint64_t* read_values = (uint64_t*) 0;
uint64_t* read_los    = (uint64_t*) 0;
uint64_t* read_ups    = (uint64_t*) 0;

// ---------- registers
uint64_t* reg_steps    = (uint64_t*) 0; // step on register value
uint8_t*  reg_data_typ = (uint8_t*) 0; // memory range or integer interval
uint8_t   VALUE_T      = 0;
uint8_t   POINTER_T    = 1;
// register constraints on memory
uint8_t*  reg_symb_typ = (uint8_t*) 0; // register has constraint
uint8_t   CONCRETE   = 0;
uint8_t   SYMBOLIC_CONCRETE = 1;
uint8_t   SYMBOLIC   = 2;
bool*     reg_hasmn = (bool*) 0; // constraint has minuend
// corrections
uint64_t* reg_addsub_corr    = (uint64_t*) 0;
uint64_t* reg_muldivrem_corr = (uint64_t*) 0;
uint64_t* reg_corr_validity  = (uint64_t*) 0;
uint64_t  MUL_T  = 3;
uint64_t  DIVU_T = 4;
uint64_t  REMU_T = 5;

// ---------- operand's addresses
uint8_t* reg_addrs_idx = (uint8_t*) 0;
uint8_t* ld_froms_idx  = (uint8_t*) 0;
// struct addr {
//   uint64_t vaddrs[MAX_NUM_OF_OP_VADDRS];
// } *reg_addr, *ld_froms, *ld_froms_tc;

// ---------- multi intervals
uint8_t* reg_mints_idx = (uint8_t*) 0;
uint8_t* mints_idxs    = (uint8_t*) 0;
// struct minterval {
//   uint64_t los[MAX_NUM_OF_INTERVALS];
//   uint64_t ups[MAX_NUM_OF_INTERVALS];
// } *reg_mints, *mints;
uint64_t* mints_min_lo = (uint64_t*) 0;
// temporaries to pass as function parameters
uint64_t mint_lo_sym[MAX_NUM_OF_INTERVALS];
uint64_t mint_up_sym[MAX_NUM_OF_INTERVALS];
uint64_t mint_lo_crt[MAX_NUM_OF_INTERVALS];
uint64_t mint_up_crt[MAX_NUM_OF_INTERVALS];
uint8_t  mint_num_sym = 0;
uint64_t val_ptr[1];
// for minterval managment in eq/diseq
struct minterval mint_true_rs1;
struct minterval mint_true_rs2;
struct minterval mint_false_rs1;
struct minterval mint_false_rs2;
uint8_t mint_num_true_rs1;
uint8_t mint_num_true_rs2;
uint8_t mint_num_false_rs1;
uint8_t mint_num_false_rs2;
// for propagation defined above
// uint64_t lo_prop[MAX_NUM_OF_INTERVALS];
// uint64_t up_prop[MAX_NUM_OF_INTERVALS];
// uint8_t  mints_num_prop = 0;

// ---------- other globals
uint64_t current_rs1_tc = 0;
uint64_t current_rs2_tc = 0;

// trace counter of most recent constraint
uint64_t mrcc = 0;

// ==, !=, <, <=, >= detection
uint8_t  detected_conditional = 0;
uint8_t  LT   = 1;
uint8_t  LGTE = 2;
uint8_t  EQ   = 4;
uint8_t  DEQ  = 5;

// assertion
bool is_only_one_branch_reachable = false;
bool assert_zone = false;

// ------------------------- INITIALIZATION ------------------------

void init_symbolic_engine() {
  pcs                = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  tcs                = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  values             = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  data_types         = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  steps              = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  vaddrs             = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  addsub_corrs       = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  muldivrem_corrs    = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  corr_validitys     = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  hasmns             = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);

  ld_froms           = malloc(MAX_TRACE_LENGTH  * sizeof(struct addr));
  ld_froms_tc        = malloc(MAX_TRACE_LENGTH  * sizeof(struct addr));
  reg_addr           = malloc(NUMBEROFREGISTERS * sizeof(struct addr));
  ld_froms_idx       = malloc(MAX_TRACE_LENGTH  * sizeof(uint8_t));
  reg_addrs_idx      = zalloc(NUMBEROFREGISTERS * sizeof(uint8_t));

  mr_sds             = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);

  sd_to_idxs         = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  sd_tos             = malloc(MAX_TRACE_LENGTH  * sizeof(struct sd_to_tc));

  mints              = malloc(MAX_TRACE_LENGTH  * sizeof(struct minterval));
  reg_mints          = malloc(NUMBEROFREGISTERS * sizeof(struct minterval));
  mints_idxs         = malloc(MAX_TRACE_LENGTH  * sizeof(uint8_t));
  reg_mints_idx      = malloc(NUMBEROFREGISTERS * sizeof(uint8_t));
  mints_min_lo       = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);

  read_values        = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  read_los           = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);
  read_ups           = malloc(MAX_TRACE_LENGTH  * SIZEOFUINT64);

  reg_data_typ       = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_steps          = malloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_symb_typ       = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_hasmn          = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_addsub_corr    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_muldivrem_corr = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_corr_validity  = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);

  for (uint8_t i = 0; i < NUMBEROFREGISTERS; i++) {
    reg_steps[i]     = 1;
    reg_mints_idx[i] = 1;
  }

  pcs[0]             = 0;
  tcs[0]             = 0;
  values[0]          = 0;
  data_types[0]      = 0;
  mints[0].los[0]    = 0;
  mints[0].ups[0]    = 0;
  mints_idxs[0]      = 0;
  steps[0]           = 0;
  vaddrs[0]          = 0;
  addsub_corrs[0]    = 0;
  muldivrem_corrs[0] = 0;
  corr_validitys[0]  = 0;
  hasmns[0]          = 0;
  mr_sds[0]          = 0;
  sd_to_idxs[0]      = 0;
  ld_froms_idx[0]    = 0;
  mints_min_lo[0]    = 0;

  TWO_TO_THE_POWER_OF_32 = two_to_the_power_of(32);

  TWO_TO_THE_POWER_OF_64 = UINT64_MAX_VALUE + 1U;
}

////////////////////////////////////////////////////////////////////////////////
//                          auxiliary functions
////////////////////////////////////////////////////////////////////////////////

uint64_t gcd(uint64_t n1, uint64_t n2) {
  if (n1 == 0)
    return n2;

  return gcd(n2 % n1, n1);
}

uint64_t lcm(uint64_t n1, uint64_t n2) {
  if (n1 > n2)
    return (n1 / gcd(n1, n2)) * n2;
  else
    return (n2 / gcd(n1, n2)) * n1;
}

uint128_t gcd_128(uint128_t n1, uint128_t n2) {
  if (n1 == 0)
    return n2;

  return gcd(n2 % n1, n1);
}

uint128_t lcm_128(uint128_t n1, uint128_t n2) {
  // assert 0 <= n1, n2 <= 2^64-1
  return (n1 * n2) / gcd(n1, n2);
}

bool is_power_of_two(uint64_t v) {
  return v && (!(v & (v - 1)));
}

bool check_incompleteness(uint64_t gcd_steps) {
  uint64_t i_max;

  if (*(reg_steps + rs1) < *(reg_steps + rs2)) {
    if (*(reg_steps + rs1) == gcd_steps) {
      i_max = (reg_mints[rs1].ups[0] - reg_mints[rs1].los[0]) / *(reg_steps + rs1);
      if (i_max < *(reg_steps + rs2)/gcd_steps - 1)
        return 1;
    } else
      return 1;
  } else if (*(reg_steps + rs1) > *(reg_steps + rs2)) {
    if (*(reg_steps + rs2) == gcd_steps) {
      i_max = (reg_mints[rs2].ups[0] - reg_mints[rs2].los[0]) / *(reg_steps + rs2);
      if (i_max < *(reg_steps + rs1)/gcd_steps - 1)
        return 1;
    } else
      return 1;
  }

  return 0;
}

bool add_sub_condition(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  uint64_t c1;
  uint64_t c2;

  c1 = up1 - lo1;
  c2 = UINT64_MAX_T - (up2 - lo2);

  if (c1 <= c2)
    return 1;
  else
    return 0;
}

bool mul_condition(uint64_t lo, uint64_t up, uint64_t k) {
  uint64_t c1;
  uint64_t c2;

  if (k == 0)
    return true;

  c1 = up - lo;
  c2 = UINT64_MAX_T / k;

  if (c1 <= c2)
    return true;

  return false;
}

int remu_condition(uint64_t lo, uint64_t up, uint64_t step, uint64_t k) {
  uint64_t lcm;

  lcm = (step * k) / gcd(step, k);
  if (up/k == lo/k)
    return 0;
  else if (up - lo >= lcm - step)
    return 2;
  else if (up/k - lo/k == 1)
    return 1;
  else
    return -1;
}

uint64_t compute_upper_bound(uint64_t lo, uint64_t step, uint64_t value) {
  return lo + ((value - lo) / step) * step;
}

uint64_t compute_lower_bound(uint64_t lo, uint64_t step, uint64_t value) {
  if ((value - lo) % step)
    return lo + (((value - lo) / step) + 1) * step;
  else
    return value;
}

////////////////////////////////////////////////////////////////////////////////
//                                operations
////////////////////////////////////////////////////////////////////////////////

void constrain_lui() {
  if (rd != REG_ZR) {
    reg_data_typ[rd] = VALUE_T;

    // interval semantics of lui
    reg_mints[rd].los[0] = imm << 12;
    reg_mints[rd].ups[0] = imm << 12;
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    // rd has no constraint
    set_correction(rd, 0, 0, 0, 0, 0);
  }
}

void constrain_addi() {
  if (rd == REG_ZR)
    return;

  if (reg_data_typ[rs1] == POINTER_T) {
    reg_data_typ[rd]     = reg_data_typ[rs1];
    reg_mints[rd].los[0] = reg_mints[rs1].los[0];
    reg_mints[rd].ups[0] = reg_mints[rs1].ups[0];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    // rd has no constraint if rs1 is memory range
    set_correction(rd, 0, 0, 0, 0, 0);

    return;
  }

  reg_data_typ[rd] = VALUE_T;

  // interval semantics of addi
  if (reg_symb_typ[rs1] == SYMBOLIC) {
      // rd inherits rs1 constraint
      set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1] + imm, reg_muldivrem_corr[rs1],
        (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);
      set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

      reg_steps[rd] = reg_steps[rs1];
      for (uint8_t i = 0; i < reg_mints_idx[rs1]; i++) {
        reg_mints[rd].los[i] = reg_mints[rs1].los[i] + imm;
        reg_mints[rd].ups[i] = reg_mints[rs1].ups[i] + imm;
      }
      reg_mints_idx[rd] = reg_mints_idx[rs1];

  } else {
    // rd has no constraint if rs1 has none
    set_correction(rd, 0, 0, 0, 0, 0);

    reg_mints[rd].los[0] = reg_mints[rs1].los[0] + imm;
    reg_mints[rd].ups[0] = reg_mints[rd].los[0];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;
  }
}

bool constrain_add_pointer() {
  if (reg_data_typ[rs1] == POINTER_T) {
    if (reg_data_typ[rs2] == POINTER_T) {
      // adding two pointers is undefined
      printf("OUTPUT: undefined addition of two pointers at %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_data_typ[rd]     = reg_data_typ[rs1];
    reg_mints[rd].los[0] = reg_mints[rs1].los[0];
    reg_mints[rd].ups[0] = reg_mints[rs1].ups[0];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    // rd has no constraint if rs1 is memory range
    set_correction(rd, 0, 0, 0, 0, 0);

    return 1;
  } else if (reg_data_typ[rs2] == POINTER_T) {
    reg_data_typ[rd]     = reg_data_typ[rs2];
    reg_mints[rd].los[0] = reg_mints[rs2].los[0];
    reg_mints[rd].ups[0] = reg_mints[rs2].ups[0];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    // rd has no constraint if rs2 is memory range
    set_correction(rd, 0, 0, 0, 0, 0);

    return 1;
  }

  return 0;
}

void constrain_add() {
  uint64_t add_lo;
  uint64_t add_up;

  if (rd != REG_ZR) {
    if (constrain_add_pointer())
      return;

    reg_data_typ[rd] = VALUE_T;

    // interval semantics of add
    if (reg_symb_typ[rs1] == SYMBOLIC) {
      if (reg_symb_typ[rs2] == SYMBOLIC) {
        // we cannot keep track of more than one constraint for add but
        // need to warn about their earlier presence if used in comparisons
        set_correction(rd, SYMBOLIC, 0, 0, 0, 10);
        uint8_t rd_addr_idx = reg_addrs_idx[rs1] + reg_addrs_idx[rs2];
        set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);
        set_vaddrs(rd, reg_addr[rs2].vaddrs, reg_addrs_idx[rs1], rd_addr_idx);

        if (reg_mints_idx[rs1] > 1 || reg_mints_idx[rs2] > 1) {
          printf("OUTPUT: unsupported minterval 1 %x \n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        // interval semantics of add
        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("OUTPUT: steps in addition are not consistent at %x\n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        bool cnd = add_sub_condition(reg_mints[rs1].los[0], reg_mints[rs1].ups[0], reg_mints[rs2].los[0], reg_mints[rs2].ups[0]);
        if (cnd == false) {
          uint128_t rhs = (uint128_t) lcm_128(TWO_TO_THE_POWER_OF_64, (uint128_t) gcd_steps) - gcd_steps;
          uint128_t lhs = (uint128_t) (reg_mints[rs1].ups[0] - reg_mints[rs1].los[0]) + (reg_mints[rs2].ups[0] - reg_mints[rs2].los[0]);
          if (lhs >= rhs) {
            // assert: gcd_steps <= UINT64_MAX_T
            uint64_t gcd_step_k = gcd_128( (uint128_t) gcd_steps, TWO_TO_THE_POWER_OF_64);
            uint64_t lo = (reg_mints[rs1].los[0] + reg_mints[rs2].los[0]);
            add_lo    = lo - (lo / gcd_step_k) * gcd_step_k;
            add_up    = compute_upper_bound(add_lo, gcd_step_k, UINT64_MAX_T);
            gcd_steps = gcd_step_k;
          } else {
            printf("OUTPUT: cannot reason about overflowed add %x\n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        } else {
          add_lo = reg_mints[rs1].los[0] + reg_mints[rs2].los[0];
          add_up = reg_mints[rs1].ups[0] + reg_mints[rs2].ups[0];
        }

        reg_mints[rd].los[0] = add_lo;
        reg_mints[rd].ups[0] = add_up;
        reg_mints_idx[rd]    = 1;
        reg_steps[rd]        = gcd_steps;

      } else {
        // rd inherits rs1 constraint since rs2 has none
        set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1] + reg_mints[rs2].los[0], reg_muldivrem_corr[rs1],
          (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);
        set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

        reg_steps[rd] = reg_steps[rs1];
        for (uint8_t i = 0; i < reg_mints_idx[rs1]; i++) {
          reg_mints[rd].los[i] = reg_mints[rs1].los[i] + reg_mints[rs2].los[0];
          reg_mints[rd].ups[i] = reg_mints[rs1].ups[i] + reg_mints[rs2].ups[0];
        }
        reg_mints_idx[rd] = reg_mints_idx[rs1];
      }
    } else if (reg_symb_typ[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      set_correction(rd, reg_symb_typ[rs2], 0, reg_addsub_corr[rs2] + reg_mints[rs1].los[0], reg_muldivrem_corr[rs2],
        (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      set_vaddrs(rd, reg_addr[rs2].vaddrs, 0, reg_addrs_idx[rs2]);

      reg_steps[rd] = reg_steps[rs2];
      for (uint8_t i = 0; i < reg_mints_idx[rs2]; i++) {
        reg_mints[rd].los[i] = reg_mints[rs1].los[0] + reg_mints[rs2].los[i];
        reg_mints[rd].ups[i] = reg_mints[rs1].ups[0] + reg_mints[rs2].ups[i];
      }
      reg_mints_idx[rd] = reg_mints_idx[rs2];
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_correction(rd, 0, 0, 0, 0, 0);

      reg_mints[rd].los[0] = reg_mints[rs1].los[0] + reg_mints[rs2].los[0];
      reg_mints[rd].ups[0] = reg_mints[rd].los[0];
      reg_mints_idx[rd]    = 1;
      reg_steps[rd]        = 1;
      reg_addrs_idx[rd]    = 0;
    }
  }
}

bool constrain_sub_pointer() {
  if (reg_data_typ[rs1] == POINTER_T) {
    if (reg_data_typ[rs2] == POINTER_T) {
      if (reg_mints[rs1].los[0] == reg_mints[rs2].los[0])
        if (reg_mints[rs1].ups[0] == reg_mints[rs2].ups[0]) {
          reg_data_typ[rd] = POINTER_T;
          reg_mints[rd].los[0] = registers[rd];
          reg_mints[rd].ups[0] = registers[rd];
          reg_mints_idx[rd]    = 1;
          reg_steps[rd]        = 1;
          reg_addrs_idx[rd]    = 0;

          // rd has no constraint if rs1 and rs2 are memory range
          set_correction(rd, 0, 0, 0, 0, 0);

          return 1;
        }

      // subtracting incompatible pointers
      throw_exception(EXCEPTION_INVALIDADDRESS, 0);

      return 1;
    } else {
      reg_data_typ[rd] = reg_data_typ[rs1];
      reg_mints[rd].los[0] = reg_mints[rs1].los[0];
      reg_mints[rd].ups[0] = reg_mints[rs1].ups[0];
      reg_mints_idx[rd]    = 1;
      reg_steps[rd]        = 1;
      reg_addrs_idx[rd]    = 0;

      // rd has no constraint if rs1 is memory range
      set_correction(rd, 0, 0, 0, 0, 0);

      return 1;
    }
  } else if (reg_data_typ[rs2] == POINTER_T) {
    reg_data_typ[rd] = reg_data_typ[rs2];
    reg_mints[rd].los[0] = reg_mints[rs2].los[0];
    reg_mints[rd].ups[0] = reg_mints[rs2].ups[0];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    // rd has no constraint if rs2 is memory range
    set_correction(rd, 0, 0, 0, 0, 0);

    return 1;
  }

  return 0;
}

void constrain_sub() {
  uint64_t sub_lo;
  uint64_t sub_up;
  uint64_t sub_tmp;

  if (rd != REG_ZR) {
    if (constrain_sub_pointer())
      return;

    reg_data_typ[rd] = VALUE_T;

    // interval semantics of sub
    if (reg_symb_typ[rs1] == SYMBOLIC) {
      if (reg_symb_typ[rs2] == SYMBOLIC) {
        // we cannot keep track of more than one constraint for sub but
        // need to warn about their earlier presence if used in comparisons
        set_correction(rd, SYMBOLIC, 0, 0, 0, 10);
        uint8_t rd_addr_idx = reg_addrs_idx[rs1] + reg_addrs_idx[rs2];
        set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);
        set_vaddrs(rd, reg_addr[rs2].vaddrs, reg_addrs_idx[rs1], rd_addr_idx);

        if (reg_mints_idx[rs1] > 1 || reg_mints_idx[rs2] > 1) {
          printf("OUTPUT: unsupported minterval 2 %x \n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("%s\n", " steps in subtraction are not consistent");
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        bool cnd = add_sub_condition(reg_mints[rs1].los[0], reg_mints[rs1].ups[0], reg_mints[rs2].los[0], reg_mints[rs2].ups[0]);
        if (cnd == false) {
          printf("OUTPUT: cannot reason about overflowed sub %x\n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        sub_lo = reg_mints[rs2].los[0];
        sub_up = reg_mints[rs2].ups[0];
        reg_mints[rd].los[0] = reg_mints[rs1].los[0] - sub_up;
        reg_mints[rd].ups[0] = reg_mints[rs1].ups[0] - sub_lo;
        reg_mints_idx[rd]    = 1;
        reg_steps[rd]        = gcd_steps;

      } else {
        // rd inherits rs1 constraint since rs2 has none
        set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1] - reg_mints[rs2].los[0], reg_muldivrem_corr[rs1],
          (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);
        set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

        reg_steps[rd] = reg_steps[rs1];
        sub_lo = reg_mints[rs2].los[0];
        sub_up = reg_mints[rs2].ups[0];
        for (uint8_t i = 0; i < reg_mints_idx[rs1]; i++) {
          reg_mints[rd].los[i] = reg_mints[rs1].los[i] - sub_up;
          reg_mints[rd].ups[i] = reg_mints[rs1].ups[i] - sub_lo;
        }
        reg_mints_idx[rd] = reg_mints_idx[rs1];
      }
    } else if (reg_symb_typ[rs2] == SYMBOLIC) {
      if (*(reg_hasmn + rs2)) {
        // rs2 constraint has already minuend and can have another minuend
        set_correction(rd, reg_symb_typ[rs2], 0, reg_mints[rs1].los[0] - reg_addsub_corr[rs2], reg_muldivrem_corr[rs2],
          (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      } else {
        // rd inherits rs2 constraint since rs1 has none
        set_correction(rd, reg_symb_typ[rs2], 1, reg_mints[rs1].los[0] - reg_addsub_corr[rs2], reg_muldivrem_corr[rs2],
          (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      }

      set_vaddrs(rd, reg_addr[rs2].vaddrs, 0, reg_addrs_idx[rs2]);

      reg_steps[rd] = reg_steps[rs2];
      sub_lo = reg_mints[rs1].los[0];
      sub_up = reg_mints[rs1].ups[0];
      for (uint8_t i = 0; i < reg_mints_idx[rs2]; i++) {
        sub_tmp              = sub_lo - reg_mints[rs2].ups[i];
        reg_mints[rd].ups[i] = sub_up - reg_mints[rs2].los[i];
        reg_mints[rd].los[i] = sub_tmp;
      }
      reg_mints_idx[rd] = reg_mints_idx[rs2];
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_correction(rd, 0, 0, 0, 0, 0);

      reg_mints[rd].los[0] = reg_mints[rs1].los[0] - reg_mints[rs2].ups[0];
      reg_mints[rd].ups[0] = reg_mints[rd].los[0];
      reg_mints_idx[rd]    = 1;
      reg_steps[rd]        = 1;
      reg_addrs_idx[rd]    = 0;
    }
  }
}

void constrain_mul() {
  uint64_t mul_lo;
  uint64_t mul_up;
  bool     cnd;

  if (rd != REG_ZR) {
    reg_data_typ[rd] = VALUE_T;

    // interval semantics of mul
    if (reg_symb_typ[rs1] == SYMBOLIC) {
      if (reg_symb_typ[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        printf("OUTPUT: detected non-linear expression in mul at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);

      } else if (reg_hasmn[rs1]) {
        // correction does not work anymore
        printf("OUTPUT: correction does not work anymore e.g. (1 - [.]) * 10 at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1], reg_mints[rs2].los[0], reg_corr_validity[rs1] + MUL_T);
        set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

        if (reg_mints_idx[rs1] == 1) {
          cnd = mul_condition(reg_mints[rs1].los[0], reg_mints[rs1].ups[0], reg_mints[rs2].los[0]);
          if (cnd == true) {
            reg_steps[rd]        = reg_steps[rs1]        * reg_mints[rs2].los[0];
            reg_mints[rd].los[0] = reg_mints[rs1].los[0] * reg_mints[rs2].los[0];
            reg_mints[rd].ups[0] = reg_mints[rs1].ups[0] * reg_mints[rs2].ups[0];
            reg_mints_idx[rd]    = 1;
          } else {
            // potential of overflow
            // assert: reg_mints[rs2].los[0] * reg_steps[rs1] <= UINT64_MAX_T
            uint128_t lcm_ = lcm_128(TWO_TO_THE_POWER_OF_64, (uint128_t) reg_mints[rs2].los[0] * reg_steps[rs1]);
            uint128_t rhs = (uint128_t) (lcm_ - (uint128_t) reg_mints[rs2].los[0] * reg_steps[rs1]) / reg_mints[rs2].los[0];
            uint128_t lhs = (reg_mints[rs1].ups[0] - reg_mints[rs1].los[0]);
            if (lhs >= rhs) {
              uint64_t gcd_step_k = gcd_128( (uint128_t) reg_mints[rs2].los[0] * reg_steps[rs1], TWO_TO_THE_POWER_OF_64);
              uint64_t lo          = (reg_mints[rs1].los[0] * reg_mints[rs2].los[0]);
              reg_mints[rd].los[0] = lo - (lo / gcd_step_k) * gcd_step_k;
              reg_mints[rd].ups[0] = compute_upper_bound(reg_mints[rd].los[0], gcd_step_k, UINT64_MAX_T);
              reg_mints_idx[rd]    = 1;
              reg_steps[rd] = gcd_step_k;
              reg_corr_validity[rs1] += REMU_T;
            } else {
              printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
              exit(EXITCODE_SYMBOLICEXECUTIONERROR);
            }
          }
        } else {
          reg_steps[rd] = reg_steps[rs1] * reg_mints[rs2].los[0]; // correct when on (cnd == false) we do exit
          for (uint8_t i = 0; i < reg_mints_idx[rs1]; i++) {
            cnd = mul_condition(reg_mints[rs1].los[i], reg_mints[rs1].ups[i], reg_mints[rs2].los[0]);
            if (cnd == true) {
              reg_mints[rd].los[i] = reg_mints[rs1].los[i] * reg_mints[rs2].los[0];
              reg_mints[rd].ups[i] = reg_mints[rs1].ups[i] * reg_mints[rs2].ups[0];
              reg_mints_idx[rd]    = reg_mints_idx[rs1];
            } else {
              printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
              exit(EXITCODE_SYMBOLICEXECUTIONERROR);
            }
          }
        }
      }
    } else if (reg_symb_typ[rs2] == SYMBOLIC) {
      if (reg_hasmn[rs2]) {
        // correction does not work anymore
        printf("OUTPUT: correction does not work anymore e.g. 10 * (1 - [.]) at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs2 constraint since rs1 has none
        // assert: rs1 interval is singleton
        set_correction(rd, reg_symb_typ[rs2], 0, reg_addsub_corr[rs2], reg_mints[rs1].los[0], reg_corr_validity[rs2] + MUL_T);
        set_vaddrs(rd, reg_addr[rs2].vaddrs, 0, reg_addrs_idx[rs2]);

        if (reg_mints_idx[rs2] == 1) {
          cnd = mul_condition(reg_mints[rs2].los[0], reg_mints[rs2].ups[0], reg_mints[rs1].los[0]);
          if (cnd == true) {
            reg_steps[rd]        = reg_steps[rs2] * reg_mints[rs1].los[0];
            reg_mints[rd].los[0] = reg_mints[rs1].los[0] * reg_mints[rs2].los[0];
            reg_mints[rd].ups[0] = reg_mints[rs1].ups[0] * reg_mints[rs2].ups[0];
            reg_mints_idx[rd]    = 1;
          } else {
            // potential of overflow
            // assert: reg_mints[rs2].los[0] * reg_steps[rs1] <= UINT64_MAX_T
            uint128_t lcm_ = lcm_128(TWO_TO_THE_POWER_OF_64, (uint128_t) reg_mints[rs1].los[0] * reg_steps[rs2]);
            uint128_t rhs = (uint128_t) (lcm_ - (uint128_t) reg_mints[rs1].los[0] * reg_steps[rs2]) / reg_mints[rs1].los[0];
            uint128_t lhs = (reg_mints[rs2].ups[0] - reg_mints[rs2].los[0]);
            if (lhs >= rhs) {
              uint64_t gcd_step_k = gcd_128( (uint128_t) reg_mints[rs1].los[0] * reg_steps[rs2], TWO_TO_THE_POWER_OF_64);
              uint64_t lo          = (reg_mints[rs1].los[0] * reg_mints[rs2].los[0]);
              reg_mints[rd].los[0] = lo - (lo / gcd_step_k) * gcd_step_k;
              reg_mints[rd].ups[0] = compute_upper_bound(reg_mints[rd].los[0], gcd_step_k, UINT64_MAX_T);
              reg_mints_idx[rd]    = 1;
              reg_steps[rd] = gcd_step_k;
              reg_corr_validity[rs2] += REMU_T;
            } else {
              printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
              exit(EXITCODE_SYMBOLICEXECUTIONERROR);
            }
          }
        } else {
          reg_steps[rd] = reg_steps[rs2] * reg_mints[rs1].los[0]; // correct when on (cnd == false) we do exit
          for (uint8_t i = 0; i < reg_mints_idx[rs2]; i++) {
            cnd = mul_condition(reg_mints[rs2].los[i], reg_mints[rs2].ups[i], reg_mints[rs1].los[0]);
            if (cnd == true) {
              reg_mints[rd].los[i] = reg_mints[rs2].los[i] * reg_mints[rs1].los[0];
              reg_mints[rd].ups[i] = reg_mints[rs2].ups[i] * reg_mints[rs1].ups[0];
              reg_mints_idx[rd]    = reg_mints_idx[rs2];
            } else {
              printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
              exit(EXITCODE_SYMBOLICEXECUTIONERROR);
            }
          }
        }
      }
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_correction(rd, 0, 0, 0, 0, 0);

      reg_steps[rd]        = 1;
      reg_mints[rd].los[0] = reg_mints[rs1].los[0] * reg_mints[rs2].los[0];
      reg_mints[rd].ups[0] = reg_mints[rs1].ups[0] * reg_mints[rs2].ups[0];
      reg_mints_idx[rd]    = 1;
      reg_addrs_idx[rd]    = 0;
    }
  }
}

void constrain_divu() {
  uint64_t div_lo;
  uint64_t div_up;
  uint64_t step;

  if (reg_mints[rs2].los[0] != 0) {
    if (reg_mints[rs2].ups[0] >= reg_mints[rs2].los[0]) {
      // 0 is not in interval
      if (rd != REG_ZR) {
        reg_data_typ[rd] = VALUE_T;

        if (reg_mints_idx[rs1] > 1 || reg_mints_idx[rs2] > 1) {
          printf("OUTPUT: unsupported minterval 4 %x \n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        // interval semantics of divu
        div_lo = reg_mints[rs1].los[0] / reg_mints[rs2].ups[0];
        div_up = reg_mints[rs1].ups[0] / reg_mints[rs2].los[0];
        step   = reg_steps[rs1];

        if (reg_symb_typ[rs1] == SYMBOLIC) {
          if (reg_symb_typ[rs2] == SYMBOLIC) {
            // non-linear expressions are not supported
            printf("OUTPUT: detected non-linear expression in divu at %x\n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);

          } else if (reg_hasmn[rs1]) {
            // correction does not work anymore
            printf("OUTPUT: correction does not work anymore e.g. (1 - [.]) / 10 at %x\n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);

          } else {
            // rd inherits rs1 constraint since rs2 has none
            // assert: rs2 interval is singleton
            set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1], reg_mints[rs2].los[0], reg_corr_validity[rs1] + DIVU_T);
            set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

            // step computation
            if (reg_steps[rs1] < reg_mints[rs2].los[0]) {
              if (reg_mints[rs2].los[0] % reg_steps[rs1] != 0) {
                printf("OUTPUT: steps in divison are not consistent at %x\n", pc - entry_point);
                exit(EXITCODE_SYMBOLICEXECUTIONERROR);
              }
              reg_steps[rd] = 1;
            } else {
              if (reg_steps[rs1] % reg_mints[rs2].los[0] != 0) {
                printf("OUTPUT: steps in divison are not consistent at %x\n", pc - entry_point);
                exit(EXITCODE_SYMBOLICEXECUTIONERROR);
              }
              reg_steps[rd] = reg_steps[rs1] / reg_mints[rs2].los[0];
            }

            // interval semantics of divu
            if (reg_mints[rs1].los[0] > reg_mints[rs1].ups[0]) {
              // rs1 constraint is wrapped: [lo, UINT64_MAX_T], [0, up]
              uint64_t max = compute_upper_bound(reg_mints[rs1].los[0], step, UINT64_MAX_T);
              reg_mints[rd].los[0] = (max + step) / reg_mints[rs2].los[0];
              reg_mints[rd].los[0] = max          / reg_mints[rs2].ups[0];

              // lo/k == up/k (or) up/k + step_rd
              if (div_lo != div_up)
                if (div_lo > div_up + reg_steps[rd]) {
                  printf("OUTPUT: wrapped divison rsults two intervals at %x\n", pc - entry_point);
                  exit(EXITCODE_SYMBOLICEXECUTIONERROR);
                }
            } else {
              // rs1 constraint is not wrapped
              reg_mints[rd].los[0] = div_lo;
              reg_mints[rd].ups[0] = div_up;
            }

            reg_mints_idx[rd] = 1;

          }
        } else if (reg_symb_typ[rs2] == SYMBOLIC) {
          printf("OUTPUT: detected division of constant by interval at %x\n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);

        } else {
          // rd has no constraint if both rs1 and rs2 have no constraints
          set_correction(rd, 0, 0, 0, 0, 0);

          reg_mints[rd].los[0] = div_lo;
          reg_mints[rd].ups[0] = div_up;
          reg_mints_idx[rd]    = 1;
          reg_steps[rd]        = 1;
          reg_addrs_idx[rd]    = 0;
        }
      }
    } else
      throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
  }
}

void constrain_remu() {
  uint64_t rem_lo;
  uint64_t rem_up;
  uint64_t divisor;
  uint64_t step;

  if (reg_mints[rs2].los[0] == 0)
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);

  if (reg_symb_typ[rs2] == SYMBOLIC) {
    // rs2 has constraint
    printf("OUTPUT: constrained memory location in right operand of remu at %x\n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (rd == REG_ZR)
    return;

  if (reg_mints_idx[rs1] > 1 || reg_mints_idx[rs2] > 1) {
    printf("OUTPUT: unsupported minterval 5 %x\n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  reg_data_typ[rd] = VALUE_T;

  if (reg_symb_typ[rs1] == SYMBOLIC) {
    // interval semantics of remu
    divisor = reg_mints[rs2].los[0];
    step    = reg_steps[rs1];

    if (reg_mints[rs1].los[0] <= reg_mints[rs1].ups[0]) {
      // rs1 interval is not wrapped
      int rem_typ = remu_condition(reg_mints[rs1].los[0], reg_mints[rs1].ups[0], step, divisor);
      if (rem_typ == 0) {
        rem_lo        = reg_mints[rs1].los[0] % divisor;
        rem_up        = reg_mints[rs1].ups[0] % divisor;
        reg_steps[rd] = step;
      } else if (rem_typ == 1) {
        printf("OUTPUT: modulo results two intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (rem_typ == 2) {
        uint64_t gcd_step_k = gcd(step, divisor);
        rem_lo        = reg_mints[rs1].los[0]%divisor - ((reg_mints[rs1].los[0]%divisor) / gcd_step_k) * gcd_step_k;
        rem_up        = compute_upper_bound(rem_lo, gcd_step_k, divisor - 1);
        reg_steps[rd] = gcd_step_k;
      } else {
        printf("OUTPUT: modulo results many intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1], reg_mints[rs2].los[0], reg_corr_validity[rs1] + REMU_T);
      set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

    } else if (is_power_of_two(divisor)) {
      // rs1 interval is wrapped
      uint64_t gcd_step_k = gcd(step, divisor);
      uint64_t lcm        = (step * divisor) / gcd_step_k;

      if (reg_mints[rs1].ups[0] - reg_mints[rs1].los[0] < lcm - step) {
        printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      rem_lo        = reg_mints[rs1].los[0]%divisor - ((reg_mints[rs1].los[0]%divisor) / gcd_step_k) * gcd_step_k;
      rem_up        = compute_upper_bound(rem_lo, gcd_step_k, divisor - 1);
      reg_steps[rd] = gcd_step_k;

      set_correction(rd, reg_symb_typ[rs1], 0, reg_addsub_corr[rs1], reg_mints[rs2].los[0], reg_corr_validity[rs1] + REMU_T);
      set_vaddrs(rd, reg_addr[rs1].vaddrs, 0, reg_addrs_idx[rs1]);

    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (reg_hasmn[rs1]) {
      // correction does not work anymore
      printf("OUTPUT: correction does not work anymore e.g. (1 - [.]) mod 10 at %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_mints[rd].los[0] = rem_lo;
    reg_mints[rd].ups[0] = rem_up;
    reg_mints_idx[rd]    = 1;
  } else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    set_correction(rd, 0, 0, 0, 0, 0);

    reg_mints[rd].los[0] = reg_mints[rs1].los[0] % reg_mints[rs2].los[0];
    reg_mints[rd].ups[0] = reg_mints[rs1].ups[0] % reg_mints[rs2].ups[0];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;
  }
}

void constrain_sltu() {
  if (rd != REG_ZR) {
    if (reg_symb_typ[rs1] != SYMBOLIC && reg_symb_typ[rs2] != SYMBOLIC) {
      // concrete semantics of sltu
      registers[rd] = (registers[rs1] < registers[rs2]) ? 1 : 0;

      is_only_one_branch_reachable = true;

      reg_data_typ[rd]     = VALUE_T;
      reg_mints[rd].los[0] = registers[rd];
      reg_mints[rd].ups[0] = registers[rd];
      reg_mints_idx[rd]    = 1;
      reg_steps[rd]        = 1;
      reg_addrs_idx[rd]    = 0;

      set_correction(rd, 0, 0, 0, 0, 0);

      pc = pc + INSTRUCTIONSIZE;

      ic_sltu = ic_sltu + 1;
      return;
    }

    is_only_one_branch_reachable = false;

    if (reg_symb_typ[rs1])
      current_rs1_tc = load_symbolic_memory(pt, reg_addr[rs1].vaddrs[0]);

    if (reg_symb_typ[rs2])
      current_rs2_tc = load_symbolic_memory(pt, reg_addr[rs2].vaddrs[0]);

    if (reg_data_typ[rs1] == POINTER_T) {
      if (reg_data_typ[rs2] != POINTER_T) {
        create_constraints(registers[rs1], registers[rs1], reg_mints[rs2].los[0], reg_mints[rs2].ups[0], mrcc);
      }
    } else if (reg_data_typ[rs2] == POINTER_T) {
      create_constraints(reg_mints[rs1].los[0], reg_mints[rs1].ups[0], registers[rs2], registers[rs2], mrcc);
    } else {
      create_mconstraints(reg_mints[rs1].los, reg_mints[rs1].ups, reg_mints[rs2].los, reg_mints[rs2].ups, mrcc);
    }
  }

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
}


bool create_xor_true_false_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  bool cannot_handle = false;

  if (lo1 <= up1) {
    // rs1 non-wrapped
    if (lo2 <= up2) {
      // rs2 non-wrapped
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else if (up2 < lo1) {
        // rs2 interval is strictly less than rs1 interval
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else if (lo2 == up2) {
        // rs2 interval is a singleton
        /* one of the true cases are definitly happens since rs1 at least has two values. */
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;
        // true case 1
        if (lo2 != lo1) {
          // non empty
          mint_true_rs1.los[mint_num_true_rs1]   = lo1;
          mint_true_rs1.ups[mint_num_true_rs1++] = lo2 - 1;
        }
        // true case 2
        if (lo2 != up1) {
          // non empty
          mint_true_rs1.los[mint_num_true_rs1]   = lo2 + 1;
          mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        }

        // check emptiness of false case
        if ((lo2 - lo1) % reg_steps[rs1] == 0) {
          mint_false_rs1.los[mint_num_false_rs1]   = lo2;
          mint_false_rs1.ups[mint_num_false_rs1++] = up2;
          mint_false_rs2.los[mint_num_false_rs2]   = lo2;
          mint_false_rs2.ups[mint_num_false_rs2++] = up2;
        }

      } else if (lo1 == up1) {
        // rs1 interval is a singleton
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        // true case 1
        if (lo1 != lo2) {
          mint_true_rs2.los[mint_num_true_rs2]   = lo2;
          mint_true_rs2.ups[mint_num_true_rs2++] = lo1 - 1;
        }
        // true case 2
        if (lo1 != up2) {
          // non empty
          mint_true_rs2.los[mint_num_true_rs2]   = lo1 + 1;
          mint_true_rs2.ups[mint_num_true_rs2++] = up2;
        }

        // check emptiness of false case
        if ( (lo1 - lo2) % reg_steps[rs2] == 0) {
          mint_false_rs1.los[mint_num_false_rs1]   = lo1;
          mint_false_rs1.ups[mint_num_false_rs1++] = up1;
          mint_false_rs2.los[mint_num_false_rs2]   = lo1;
          mint_false_rs2.ups[mint_num_false_rs2++] = up1;
        }

      } else {
        // we cannot handle
        cannot_handle = true;
      }
    } else {
      // rs2 wrapped
      if (up1 < lo2 && up2 < lo1) {
        // true case
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else if (lo1 == up1) {
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        // true case 1
        if (lo1 != lo2) {
          // non empty
          mint_true_rs2.los[mint_num_true_rs2]   = lo2;
          mint_true_rs2.ups[mint_num_true_rs2++] = lo1 - 1;
        }
        // true case 2
        if (lo1 != up2) {
          // non empty
          mint_true_rs2.los[mint_num_true_rs2]   = lo1 + 1;
          mint_true_rs2.ups[mint_num_true_rs2++] = up2;
        }

        // check emptiness of false case
        if ((lo1 - lo2) % reg_steps[rs2] == 0) {
          mint_false_rs1.los[mint_num_false_rs1]   = lo1;
          mint_false_rs1.ups[mint_num_false_rs1++] = up1;
          mint_false_rs2.los[mint_num_false_rs2]   = lo1;
          mint_false_rs2.ups[mint_num_false_rs2++] = up1;
        }

      } else {
        // we cannot handle
        cannot_handle = true;
      }
    }

  } else if (lo2 <= up2) {
    // rs1 wrapped, rs2 non-wrapped
    if (up2 < lo1 && up1 < lo2) {
      // true case
      mint_true_rs1.los[mint_num_true_rs1]   = lo1;
      mint_true_rs1.ups[mint_num_true_rs1++] = up1;
      mint_true_rs2.los[mint_num_true_rs2]   = lo2;
      mint_true_rs2.ups[mint_num_true_rs2++] = up2;

    } else if (lo2 == up2) {
      mint_true_rs2.los[mint_num_true_rs2]   = lo2;
      mint_true_rs2.ups[mint_num_true_rs2++] = up2;
      // true case 1
      if (lo2 != lo1) {
        // non empty
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = lo2 - 1;
      }
      // true case 2
      if (lo2 != up1) {
        // non empty
        mint_true_rs1.los[mint_num_true_rs1]   = lo2 + 1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
      }

      // check emptiness of false case
      if ((lo2 - lo1) % reg_steps[rs1] == 0) {
        mint_false_rs1.los[mint_num_false_rs1]   = lo2;
        mint_false_rs1.ups[mint_num_false_rs1++] = up2;
        mint_false_rs2.los[mint_num_false_rs2]   = lo2;
        mint_false_rs2.ups[mint_num_false_rs2++] = up2;
      }

    } else {
      // we cannot handle
      cannot_handle = true;
    }

  } else {
    // rs1 wrapped, rs2 wrapped
    // we cannot handle: they have common vlaues and they canont be singleton
    cannot_handle = true;
  }

  return cannot_handle;
}

// multi intervals are managed
void create_xor_mconstraints(uint64_t* lo1_p, uint64_t* up1_p, uint64_t* lo2_p, uint64_t* up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo1;
  uint64_t up1;
  uint64_t lo2;
  uint64_t up2;

  mint_num_true_rs1  = 0;
  mint_num_true_rs2  = 0;
  mint_num_false_rs1 = 0;
  mint_num_false_rs2 = 0;

  for (uint8_t i = 0; i < reg_mints_idx[rs1]; i++) {
    lo1 = lo1_p[i];
    up1 = up1_p[i];
    for (uint8_t j = 0; j < reg_mints_idx[rs2]; j++) {
      lo2 = lo2_p[j];
      up2 = up2_p[j];
      cannot_handle = create_xor_true_false_constraints(lo1, up1, lo2, up2);
    }
  }

  if (cannot_handle) {
    if (reg_mints_idx[rs1] == 1 && reg_mints_idx[rs2] == 1) {
      if (steps[current_rs1_tc] > 1) {
        if (steps[current_rs2_tc] > 1) {
          uint64_t los_diff = (mints[current_rs1_tc].los[0] >= mints[current_rs2_tc].los[0]) ? (mints[current_rs1_tc].los[0] - mints[current_rs2_tc].los[0]) : (mints[current_rs2_tc].los[0] - mints[current_rs1_tc].los[0]);
          if ( los_diff % gcd(steps[current_rs1_tc], steps[current_rs2_tc]) != 0) {
            constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
            constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);

            is_only_one_branch_reachable = true;
            take_branch(1, 0);

            cannot_handle = false;
          }
        }
      }
    }

    if (cannot_handle) {
      printf("OUTPUT: detected non-singleton interval intersection %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

  } else {
    if (mint_num_true_rs1 > 0 && mint_num_true_rs2 > 0)
      true_reachable  = true;
    if (mint_num_false_rs1 > 0 && mint_num_false_rs2 > 0)
      false_reachable = true;

    if (true_reachable) {
      if (false_reachable) {
        constrain_memory(rs1, mint_true_rs1.los, mint_true_rs1.ups, mint_num_true_rs1, trb, false);
        constrain_memory(rs2, mint_true_rs2.los, mint_true_rs2.ups, mint_num_true_rs2, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, mint_false_rs1.los, mint_false_rs1.ups,mint_num_false_rs1, trb, false);
        constrain_memory(rs2, mint_false_rs2.los, mint_false_rs2.ups,mint_num_false_rs2, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, mint_true_rs1.los, mint_true_rs1.ups, mint_num_true_rs1, trb, true);
        constrain_memory(rs2, mint_true_rs2.los, mint_true_rs2.ups, mint_num_true_rs2, trb, true);
        is_only_one_branch_reachable = true;
        take_branch(1, 0);
      }
    } else if (false_reachable) {
      constrain_memory(rs1, mint_false_rs1.los, mint_false_rs1.ups,mint_num_false_rs1, trb, true);
      constrain_memory(rs2, mint_false_rs2.los, mint_false_rs2.ups,mint_num_false_rs2, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(0, 0);
    } else {
      printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }

}

void create_xor_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb) {
  bool cannot_handle = false;
  bool empty;

  if (reg_mints_idx[rs1] > 1 || reg_mints_idx[rs2] > 1) {
    printf("OUTPUT: unsupported minterval xor %x \n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  mint_num_sym = 0;

  if (rd == REG_ZR)
    return;

  if (lo1 <= up1) {
    // rs1 non-wrapped
    if (lo2 <= up2) {
      // rs2 non-wrapped
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        take_branch(1, 0);
        is_only_one_branch_reachable = true;

      } else if (up2 < lo1) {
        // rs2 interval is strictly less than rs1 interval
        constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        take_branch(1, 0);
        is_only_one_branch_reachable = true;

      } else if (lo2 == up2) {
        // rs2 interval is a singleton
        /* one of the true cases are definitly happens since rs1 at least has two values. */
        mint_lo_crt[0] = lo2;
        mint_up_crt[0] = up2;
        // true case 1
        if (lo2 != lo1) {
          // non empty
          mint_lo_sym[mint_num_sym]   = lo1;
          mint_up_sym[mint_num_sym++] = lo2 - 1;
        }
        // true case 2
        if (lo2 != up1) {
          // non empty
          mint_lo_sym[mint_num_sym]   = lo2 + 1;
          mint_up_sym[mint_num_sym++] = up1;
        }
        constrain_memory(rs1, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);
        constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1           , trb, false);

        // check emptiness of false case
        if ((lo2 - lo1) % reg_steps[rs1]) {
          // is empty
          take_branch(1, 0);
          is_only_one_branch_reachable = true;
        } else {
          take_branch(1, 1);

          // false case
          constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
          constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
          take_branch(0, 0);
        }

      } else if (lo1 == up1) {
        // rs1 interval is a singleton
        mint_lo_crt[0] = lo1;
        mint_up_crt[0] = up1;
        // true case 1
        if (lo1 != lo2) { // otherwise rhs is empty
          mint_lo_sym[mint_num_sym]   = lo2;
          mint_up_sym[mint_num_sym++] = lo1 - 1;
        }
        // true case 2
        if (lo1 != up2) {
          // non empty
          mint_lo_sym[mint_num_sym]   = lo1 + 1;
          mint_up_sym[mint_num_sym++] = up2;
        }
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1           , trb, false);
        constrain_memory(rs2, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);

        // check emptiness of false case
        if ( (lo1 - lo2) % reg_steps[rs2]) {
          // is empty
          take_branch(1, 0);
          is_only_one_branch_reachable = true;
        } else {
          take_branch(1, 1);

          // false case
          constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
          constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
          take_branch(0, 0);
        }

      } else {
        // we cannot handle
        cannot_handle = true;
      }
    } else {
      // rs2 wrapped
      if (up1 < lo2 && up2 < lo1) {
        // true case
        constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        take_branch(1, 0);
        is_only_one_branch_reachable = true;
      } else if (lo1 == up1) {
        mint_lo_crt[0] = lo1;
        mint_up_crt[0] = up1;
        // true case 1
        if (lo1 != lo2) {
          // non empty
          mint_lo_sym[mint_num_sym]   = lo2;
          mint_up_sym[mint_num_sym++] = lo1 - 1;
        }
        // true case 2
        if (lo1 != up2) {
          // non empty
          mint_lo_sym[mint_num_sym]   = lo1 + 1;
          mint_up_sym[mint_num_sym++] = up2;
        }
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1           , trb, false);
        constrain_memory(rs2, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);

        // check emptiness of false case
        if ((lo1 - lo2) % reg_steps[rs2]) {
          // flase case is empty
          take_branch(1, 0);
          is_only_one_branch_reachable = true;
        } else {
          take_branch(1, 1);

          // true case
          constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
          constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
          take_branch(0, 0);
        }

      } else {
        // we cannot handle
        cannot_handle = true;
      }
    }

  } else if (lo2 <= up2) {
    // rs1 wrapped, rs2 non-wrapped
    if (up2 < lo1 && up1 < lo2) {
      // true case
      constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
      constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
      take_branch(1, 0);
      is_only_one_branch_reachable = true;
    } else if (lo2 == up2) {
      mint_lo_crt[0] = lo2;
      mint_up_crt[0] = up2;
      // true case 1
      if (lo2 != lo1) {
        // non empty
        mint_lo_sym[mint_num_sym]   = lo1;
        mint_up_sym[mint_num_sym++] = lo2 - 1;
      }
      // true case 2
      if (lo2 != up1) {
        // non empty
        mint_lo_sym[mint_num_sym]   = lo2 + 1;
        mint_up_sym[mint_num_sym++] = up1;
      } // else empty
      constrain_memory(rs1, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);
      constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1           , trb, false);

      // check emptiness of false case
      if ((lo2 - lo1) % reg_steps[rs1]) {
        // is empty
        take_branch(1, 0);
        is_only_one_branch_reachable = true;
      } else {
        take_branch(1, 1);

        // construct constraint for true case
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
        constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
        take_branch(0, 0);
      }
    } else {
      // we cannot handle
      cannot_handle = true;
    }

  } else {
    // rs1 wrapped, rs2 wrapped
    // we cannot handle: they have common vlaues and they canont be singleton
    cannot_handle = true;
  }

  if (cannot_handle) {
    if (steps[current_rs1_tc] > 1) {
      if (steps[current_rs2_tc] > 1) {
        uint64_t los_diff = (mints[current_rs1_tc].los[0] >= mints[current_rs2_tc].los[0]) ? (mints[current_rs1_tc].los[0] - mints[current_rs2_tc].los[0]) : (mints[current_rs2_tc].los[0] - mints[current_rs1_tc].los[0]);
        if ( los_diff % gcd(steps[current_rs1_tc], steps[current_rs2_tc]) != 0) {
          constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
          constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);

          take_branch(1, 0);
          is_only_one_branch_reachable = true;

          cannot_handle = false;
        }
      }
    }

    if (cannot_handle) {
      printf("OUTPUT: detected non-singleton interval intersection %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }
}

void constrain_xor() {
  if (rd == REG_ZR)
    return;

  if (reg_symb_typ[rs1] != SYMBOLIC && reg_symb_typ[rs2] != SYMBOLIC) {
    // concrete semantics of xor
    registers[rd] = registers[rs1] ^ registers[rs2];

    reg_mints[rd].los[0] = registers[rd];
    reg_mints[rd].ups[0] = registers[rd];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    is_only_one_branch_reachable = true;
    set_correction(rd, 0, 0, 0, 0, 0);

    pc = pc + INSTRUCTIONSIZE;
    ic_xor = ic_xor + 1;

    return;
  }

  is_only_one_branch_reachable = false;

  if (reg_symb_typ[rs1])
    current_rs1_tc = load_symbolic_memory(pt, reg_addr[rs1].vaddrs[0]);

  if (reg_symb_typ[rs2])
    current_rs2_tc = load_symbolic_memory(pt, reg_addr[rs2].vaddrs[0]);

  if (reg_data_typ[rs1] == POINTER_T) {
    if (reg_data_typ[rs2] != POINTER_T) {
      create_xor_constraints(registers[rs1], registers[rs1], reg_mints[rs2].los[0], reg_mints[rs2].ups[0], mrcc);
    }
  } else if (reg_data_typ[rs2] == POINTER_T)
    create_xor_constraints(reg_mints[rs1].los[0], reg_mints[rs1].ups[0], registers[rs2], registers[rs2], mrcc);
  else
    create_xor_mconstraints(reg_mints[rs1].los, reg_mints[rs1].ups, reg_mints[rs2].los, reg_mints[rs2].ups, mrcc);

  pc = pc + INSTRUCTIONSIZE;

  ic_xor = ic_xor + 1;

}

uint64_t constrain_ld() {
  uint64_t vaddr;
  uint64_t mrvc;
  uint64_t a;

  // load double word

  vaddr = registers[rs1] + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (rd != REG_ZR) {
        mrvc = load_symbolic_memory(pt, vaddr);

        // it is important because we have prevousely freed stack addresses on the trace
        if (vaddr >= get_program_break(current_context))
          if (vaddr < *(registers + REG_SP)) {
            // free memory
            printf("OUTPUT: loading an uninitialized memory %x\n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }

        // interval semantics of ld
        *(reg_data_typ + rd) = *(data_types + mrvc);

        *(registers + rd) = *(values + mrvc);
        *(reg_steps + rd) = *(steps  + mrvc);
        reg_mints_idx[rd] = mints_idxs[mrvc];
        if (reg_mints_idx[rd] == 0) {
          printf("OUTPUT: reg_mints_idx is zero\n");
        }
        for (uint8_t i = 0; i < reg_mints_idx[rd]; i++) {
          reg_mints[rd].los[i] = mints[mrvc].los[i];
          reg_mints[rd].ups[i] = mints[mrvc].ups[i];
        }

        // assert: vaddr == *(vaddrs + mrvc)

        if (mints_idxs[mrvc] > 1) {
          set_correction(rd, SYMBOLIC, 0, 0, 0, 0);
          reg_addrs_idx[rd]      = 1;
          reg_addr[rd].vaddrs[0] = vaddr;
        } else if (is_symbolic_value(reg_data_typ[rd], reg_mints[rd].los[0], reg_mints[rd].ups[0])) {
          // vaddr is constrained by rd if value interval is not singleton
          set_correction(rd, SYMBOLIC, 0, 0, 0, 0);
          reg_addrs_idx[rd]      = 1;
          reg_addr[rd].vaddrs[0] = vaddr;
        } else {
          set_correction(rd, CONCRETE, 0, 0, 0, 0);
          reg_addrs_idx[rd]      = 0;
        }
      }

      // keep track of instruction address for profiling loads
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of loads in total
      ic_ld = ic_ld + 1;

      // and individually
      *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

uint64_t constrain_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = *(registers + rs1) + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // interval semantics of sd
      store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_typ[rs2], reg_mints[rs2].los, reg_mints[rs2].ups, reg_mints_idx[rs2], reg_steps[rs2], reg_addr[rs2].vaddrs, reg_addrs_idx[rs2], reg_hasmn[rs2], reg_addsub_corr[rs2], reg_muldivrem_corr[rs2], reg_corr_validity[rs2], mrcc, 0);

      // keep track of instruction address for profiling stores
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of stores in total
      ic_sd = ic_sd + 1;

      // and individually
      *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

void constrain_jal_jalr() {
  if (rd != REG_ZR) {
    reg_mints[rd].los[0] = registers[rd];
    reg_mints[rd].ups[0] = registers[rd];
    reg_mints_idx[rd]    = 1;
    reg_steps[rd]        = 1;
    reg_addrs_idx[rd]    = 0;

    set_correction(rd, 0, 0, 0, 0, 0);
  }
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void print_symbolic_memory(uint64_t svc) {

}

uint64_t is_symbolic_value(uint64_t type, uint64_t lo, uint64_t up) {
  if (type)
    // memory range
    return 0;
  else if (lo == up)
    // singleton interval
    return 0;
  else
    // non-singleton interval
    return 1;
}

uint64_t is_safe_address(uint64_t vaddr, uint64_t reg) {
  if (*(reg_data_typ + reg) == POINTER_T) {
    if (vaddr < reg_mints[reg].los[0])
      // memory access below start address of mallocated block
      return 0;
    else if (vaddr - reg_mints[reg].los[0] >= reg_mints[reg].ups[0])
      // memory access above end address of mallocated block
      return 0;
    else
      return 1;
  } else if (reg_mints[reg].los[0] == reg_mints[reg].ups[0])
    return 1;
  else {
    printf("OUTPUT: detected unsupported symbolic access of memory interval at %x\n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr) {
  uint64_t mrvc;

  // assert: vaddr is valid and mapped
  mrvc = load_virtual_memory(pt, vaddr);

  if (mrvc <= tc)
    return mrvc;
  else {
    printf("OUTPUT: detected most recent value counter %llu at vaddr %llx greater than current trace counter %llu\n", mrvc, vaddr, tc);
    // printf4((uint64_t*) "%s: detected most recent value counter %d at vaddr %x greater than current trace counter %d\n", exe_name, (uint64_t*) mrvc, (uint64_t*) vaddr, (uint64_t*) tc);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t is_trace_space_available() {
  return tc + 1 < MAX_TRACE_LENGTH;
}

void ealloc() {
  tc = tc + 1;
}

void efree() {
  // assert: tc > 0
  tc = tc - 1;
}

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint8_t data_type, uint64_t* lo, uint64_t* up, uint8_t mints_num, uint64_t step, uint64_t* ld_from, uint8_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb, uint64_t to_tc) {
  uint64_t mrvc;
  uint64_t idx;

  if (vaddr == 0)
    // tracking program break and size for malloc
    mrvc = 0;
  else if (vaddr < NUMBEROFREGISTERS)
    // tracking a register value for sltu
    mrvc = mrcc;
  else {
    // assert: vaddr is valid and mapped
    mrvc = load_symbolic_memory(pt, vaddr);
  }

  if (is_trace_space_available()) {
    // current value at vaddr is from before most recent branch,
    // track that value by creating a new trace event
    ealloc();

    *(pcs        + tc) = pc;
    *(tcs        + tc) = mrvc;
    *(data_types + tc) = data_type;
    *(values     + tc) = value;
    *(steps      + tc) = step;
    *(vaddrs     + tc) = vaddr;

    *(mints_idxs   + tc) = mints_num;
    *(mints_min_lo + tc) = lo[0];
    for (uint8_t i = 0; i < mints_num; i++) {
      mints[tc].los[i] = lo[i];
      mints[tc].ups[i] = up[i];
      if (lo[i] < mints_min_lo[tc])
        mints_min_lo[tc] = lo[i];
    }

    *(hasmns          + tc) = hasmn;
    *(addsub_corrs    + tc) = addsub_corr;
    *(muldivrem_corrs + tc) = muldivrem_corr;
    *(corr_validitys  + tc) = corr_validity;

    *(ld_froms_idx    + tc) = ld_from_num;
    for (uint8_t i = 0; i < ld_from_num; i++) {
      ld_froms[tc].vaddrs[i] = ld_from[i];
    }

    if (to_tc == 0) { // means SD instrs
      if (ld_from_num != 0 && reg_symb_typ[rs2] == SYMBOLIC) {
        for (uint8_t i = 0; i < ld_from_num; i++) {
          idx = load_symbolic_memory(pt, ld_from[i]);
          ld_froms_tc[tc].vaddrs[i] = idx;
          if (sd_to_idxs[idx] < MAX_SD_TO_NUM)
            sd_tos[idx].tc[sd_to_idxs[idx]++] = tc;
          else {
            printf("OUTPUT: maximum number of possible sd_to is reached at %x\n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        }
      } else {
        ld_froms_idx[tc] = 0;
      }
      sd_to_idxs[tc]  = 0;
      mr_sds[tc]      = tc;
    } else {
      sd_to_idxs[tc] = sd_to_idxs[to_tc];
      memcpy(sd_tos[tc].tc, sd_tos[to_tc].tc, sizeof(struct sd_to_tc));
      mr_sds[tc]     = mr_sds[mrvc];
      for (uint8_t i = 0; i < ld_from_num; i++) {
        ld_froms_tc[tc].vaddrs[i] = ld_froms_tc[mrvc].vaddrs[i];
      }
    }

    if (vaddr < NUMBEROFREGISTERS) {
      if (vaddr > 0)
        // register tracking marks most recent constraint
        mrcc = tc;
    } else
      // assert: vaddr is valid and mapped
      store_virtual_memory(pt, vaddr, tc);

    if (debug_symbolic) {
      printf("OUTPUT: storing\n");
      print_symbolic_memory(tc);
    }
  } else
    throw_exception(EXCEPTION_MAXTRACE, 0);
}

void store_constrained_memory(uint64_t vaddr, uint64_t* lo, uint64_t* up, uint8_t mints_num, uint64_t step, uint64_t* ld_from, uint8_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t to_tc) {
  uint64_t mrvc;

  // always track constrained memory by using tc as most recent branch
  store_symbolic_memory(pt, vaddr, lo[0], VALUE_T, lo, up, mints_num, step, ld_from, ld_from_num, hasmn, addsub_corr, muldivrem_corr, corr_validity, tc, to_tc);
}

void store_register_memory(uint64_t reg, uint64_t* value) {
  // always track register memory by using tc as most recent branch
  store_symbolic_memory(pt, reg, value[0], 0, value, value, 1, 1, 0, 0, 0, 0, 0, 0, tc, 0);
}

uint64_t reverse_division_up(uint64_t ups_mrvc, uint64_t up, uint64_t codiv) {
  if (ups_mrvc < up * codiv + (codiv - 1))
    return ups_mrvc - up * codiv;
  else
    return codiv - 1;
}

// consider y = x op a;
// mrvc is mrvc of x
// lo_before_op is previouse lo of y
void apply_correction(uint64_t* lo, uint64_t* up, uint8_t mints_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t* lo_before_op, uint64_t* up_before_op, uint64_t step, uint64_t mrvc) {
  uint64_t lo_p[MAX_NUM_OF_INTERVALS];
  uint64_t up_p[MAX_NUM_OF_INTERVALS];
  uint8_t  idxs[MAX_NUM_OF_INTERVALS];
  bool     is_lo_p_up_p_used = false;

  uint8_t j;
  // bool is_found;
  for (uint8_t i = 0; i < mints_num; i++) {
    // is_found = false;
    for (j = 0; j < mints_idxs[mrvc]; j++) {
      if (up_before_op[j] - lo_before_op[j] >= lo[i] - lo_before_op[j]) {
        // is_found = true;
        break;
      }
    }

    // assert: is_found == true
    // if (is_found == false) {
    //   printf("OUTPUT: lo_before_op not found at %x\n", pc - entry_point);
    //   exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    // }

    idxs[i] = j;
    lo_prop[i] = compute_lower_bound(lo_before_op[j], step, lo[i]);
    up_prop[i] = compute_upper_bound(lo_before_op[j], step, up[i]);
  }

  // add, sub
  if (hasmn) {
    uint64_t tmp;
    for (uint8_t i = 0; i < mints_num; i++) {
      tmp        = addsub_corr - up_prop[i];
      up_prop[i] = addsub_corr - lo_prop[i];
      lo_prop[i] = tmp;
    }
  } else {
    for (uint8_t i = 0; i < mints_num; i++) {
      lo_prop[i] = lo_prop[i] - addsub_corr;
      up_prop[i] = up_prop[i] - addsub_corr;
    }
  }

  // mul, div, rem
  if (corr_validity == MUL_T && muldivrem_corr != 0) { // muldivrem_corr == 0 when (x + 1)
    // <9223372036854775808, 2^64 - 1, 1> * 2 = <0, 2^64 - 2, 2>
    // <9223372036854775809, 15372286728091293014, 1> * 3 = <9223372036854775811, 9223372036854775810, 3>
    for (uint8_t i = 0; i < mints_num; i++) {
      lo_prop[i] = mints[mrvc].los[idxs[i]] + (lo_prop[i] - lo_before_op[idxs[i]]) / muldivrem_corr; // lo_op_before_cmp
      up_prop[i] = mints[mrvc].los[idxs[i]] + (up_prop[i] - lo_before_op[idxs[i]]) / muldivrem_corr; // lo_op_before_cmp
    }

  } else if (corr_validity == DIVU_T) {
    if (mints_num > 1) {
      printf("OUTPUT: backward propagation of minterval needed at %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    uint64_t divisor = muldivrem_corr;

    if (mints[mrvc].los[0] <= mints[mrvc].ups[0]) {
      // non-wrapped
      lo_prop[0] = (lo_prop[0] == 0) ? mints[mrvc].los[0] : lo_prop[0] * divisor;

      // if (lo * divisor >= los[mrvc])
      //   lo = compute_lower_bound(los[mrvc], steps[mrvc], lo * divisor);
      // else
      //   lo = los[mrvc];

      up_prop[0] = compute_upper_bound(mints[mrvc].los[0], steps[mrvc], up_prop[0] * divisor + reverse_division_up(mints[mrvc].ups[0], up_prop[0], divisor));
    } else {
      // wrapped
      uint64_t lo_1;
      uint64_t up_1;
      uint64_t lo_2;
      uint64_t up_2;
      uint64_t max = compute_upper_bound(mints[mrvc].los[0], steps[mrvc], UINT64_MAX_T);
      uint8_t  which_is_empty;

      lo_prop[0] = (lo_prop[0] == 0) ? (max + steps[mrvc]) : lo_prop[0] * divisor;
      up_prop[0] = compute_upper_bound(mints[mrvc].los[0], steps[mrvc], up_prop[0] * divisor + reverse_division_up(max, up_prop[0], divisor));

      which_is_empty = 0;
      if (lo_prop[0] <= mints[mrvc].ups[0]) {
        lo_1 = lo_prop[0];
        up_1 = (up_prop[0] < mints[mrvc].ups[0]) ? up_prop[0] : mints[mrvc].ups[0];
      } else {
        which_is_empty = 1;
      }

      if (up_prop[0] >= mints[mrvc].los[0]) {
        lo_2 = (lo_prop[0] > mints[mrvc].los[0]) ? lo_prop[0] : mints[mrvc].los[0];
        up_2 = up_prop[0];
      } else {
        which_is_empty = (which_is_empty == 1) ? 4 : 2;
      }

      if (which_is_empty == 4) {
        if (up_1 + steps[mrvc] >= lo_2) {
          lo_prop[0] = lo_1;
          up_prop[0] = up_2;
        } else {
          printf("OUTPUT: reverse of division results two intervals at %x\n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }
      }
    }

  } else if (corr_validity == REMU_T) {
    printf("OUTPUT: detected an unsupported remu in a conditional expression at %x\n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  } else if (corr_validity > 5) {
    printf("OUTPUT: detected an unsupported conditional expression at %x\n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  //////////////////////////////////////////////////////////////////////////////
  store_constrained_memory(vaddrs[mrvc], lo_prop, up_prop, mints_num, steps[mrvc], ld_froms[mrvc].vaddrs, ld_froms_idx[mrvc], hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], mrvc);

  // assert: (ld_froms_idx[mrvc] > 1) never reach here
  if (ld_froms_idx[mrvc]) {
    for (uint8_t i = 0; i < mints_num; i++) {
      lo_p[i] = lo_prop[i];
      up_p[i] = up_prop[i];
    }
    is_lo_p_up_p_used = true;
    propagate_backwards(vaddrs[mrvc], mints[mrvc].los, mints[mrvc].ups, mrvc);
  }

  if (sd_to_idxs[mrvc]) {
    if (is_lo_p_up_p_used) {
      for (uint8_t i = 0; i < mints_num; i++) {
        lo_prop[i] = lo_p[i];
        up_prop[i] = up_p[i];
      }
    }
    propagate_backwards_rhs(lo_prop, up_prop, mints_num, mrvc);
  }
  //////////////////////////////////////////////////////////////////////////////

}

void propagate_backwards_rhs(uint64_t* lo, uint64_t* up, uint8_t mints_num, uint64_t mrvc) {
  uint64_t to_tc;
  uint64_t mr_to_tc;
  uint64_t tmp;
  uint64_t lo_p[MAX_NUM_OF_INTERVALS];
  uint64_t up_p[MAX_NUM_OF_INTERVALS];

  for (uint8_t j = 0; j < mints_num; j++) {
    lo_p[j] = lo[j];
    up_p[j] = up[j];
  }

  mints_num_prop = mints_num;
  for (int i = 0; i < sd_to_idxs[mrvc]; i++) {
    to_tc = sd_tos[mrvc].tc[i];
    mr_to_tc = load_symbolic_memory(pt, vaddrs[to_tc]);
    mr_to_tc = mr_sds[mr_to_tc];
    if (mr_to_tc > to_tc) {
      continue;
    }

    for (uint8_t j = 0; j < mints_num; j++) {
      lo_prop[j] = lo_p[j];
      up_prop[j] = up_p[j];
    }
    step_prop = steps[to_tc];
    if (corr_validitys[to_tc] == MUL_T && muldivrem_corrs[to_tc] != 0) {
      // mul
      propagate_mul(steps[mrvc], muldivrem_corrs[to_tc]);
    } else if (corr_validitys[to_tc] == DIVU_T) {
      // divu
      propagate_divu(steps[mrvc], muldivrem_corrs[to_tc], step_prop);
    } else if (corr_validitys[to_tc] == REMU_T) {
      // remu
      propagate_remu(steps[mrvc], muldivrem_corrs[to_tc]);
    }

    if (hasmns[to_tc]) {
      // addsub_corrs[to_tc] -
      for (uint8_t j = 0; j < mints_num; j++) {
        tmp        = addsub_corrs[to_tc] - up_prop[j];
        up_prop[j] = addsub_corrs[to_tc] - lo_prop[j];
        lo_prop[j] = tmp;
      }
    } else {
      // + addsub_corrs[to_tc]
      for (uint8_t j = 0; j < mints_num; j++) {
        lo_prop[j] = lo_prop[j] + addsub_corrs[to_tc];
        up_prop[j] = up_prop[j] + addsub_corrs[to_tc];
      }
    }

    store_constrained_memory(vaddrs[to_tc], lo_prop, up_prop, mints_num, step_prop, ld_froms[to_tc].vaddrs, ld_froms_idx[to_tc], hasmns[to_tc], addsub_corrs[to_tc], muldivrem_corrs[to_tc], corr_validitys[to_tc], to_tc);
    if (sd_to_idxs[mr_to_tc]) {
      propagate_backwards_rhs(lo_prop, up_prop, mints_num, mr_to_tc);
    }
  }
}

// y = x op a;
// if (y)
// vaddr of y -> new y
// lo_before_op for y -> before new y
void propagate_backwards(uint64_t vaddr, uint64_t* lo_before_op, uint64_t* up_before_op, uint64_t original_mrvc_y) {
  uint64_t mrvc_y;
  uint64_t mrvc_x;

  mrvc_y = load_symbolic_memory(pt, vaddr);
  mrvc_x = load_symbolic_memory(pt, ld_froms[mrvc_y].vaddrs[0]);
  if (mr_sds[mrvc_x] > ld_froms_tc[mrvc_y].vaddrs[0]) {
    return;
  }
  // because same notion as use for current_rs1_tc and current_rs2_tc
  while (mrvc_x > original_mrvc_y) {
    mrvc_x = tcs[mrvc_x];
  }
  apply_correction(mints[mrvc_y].los, mints[mrvc_y].ups, mints_idxs[mrvc_y], hasmns[mrvc_y], addsub_corrs[mrvc_y], muldivrem_corrs[mrvc_y], corr_validitys[mrvc_y], lo_before_op, up_before_op, steps[mrvc_y], mrvc_x);
}

void constrain_memory(uint64_t reg, uint64_t* lo, uint64_t* up, uint8_t mints_num, uint64_t trb, bool only_reachable_branch) {
  uint64_t mrvc;

  if (reg_symb_typ[reg] == SYMBOLIC && assert_zone == false) {
    if (only_reachable_branch == true) {
      for (uint8_t i = 0; i < reg_addrs_idx[reg]; i++) {
        mrvc = load_symbolic_memory(pt, reg_addr[reg].vaddrs[i]);
        lo = mints[mrvc].los;
        up = mints[mrvc].ups;
        store_constrained_memory(reg_addr[reg].vaddrs[i], lo, up, mints_idxs[mrvc], steps[mrvc], ld_froms[mrvc].vaddrs, ld_froms_idx[mrvc], hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], mrvc);
      }
    } else {
      mrvc = (reg == rs1) ? current_rs1_tc : current_rs2_tc;
      apply_correction(lo, up, mints_num, reg_hasmn[reg], reg_addsub_corr[reg], reg_muldivrem_corr[reg], reg_corr_validity[reg], reg_mints[reg].los, reg_mints[reg].ups, reg_steps[reg], mrvc);
    }

  }
}

void set_vaddrs(uint64_t reg, uint64_t* vaddrs, uint8_t start_idx, uint8_t vaddr_num) {
  reg_addrs_idx[reg] = vaddr_num;
  for (uint8_t i = 0; i < vaddr_num; i++) {
    reg_addr[reg].vaddrs[start_idx++] = vaddrs[i];
  }
}

void set_correction(uint64_t reg, uint8_t hasco, uint8_t hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity) {
  reg_symb_typ[reg]       = hasco;
  reg_hasmn[reg]          = hasmn;
  reg_addsub_corr[reg]    = addsub_corr;
  reg_muldivrem_corr[reg] = muldivrem_corr;
  reg_corr_validity[reg]  = corr_validity;
}

void take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0 && assert_zone == false) {
    // record that we need to set rd to true
    val_ptr[0] = b;
    store_register_memory(rd, val_ptr);

    // record frame and stack pointer
    store_register_memory(REG_FP, registers + REG_FP);
    store_register_memory(REG_SP, registers + REG_SP);
  } else {
    *(reg_data_typ + rd) = VALUE_T;
    *(registers + rd) = b;
    *(reg_steps + rd) = 1;
    reg_mints[rd].los[0] = b;
    reg_mints[rd].ups[0] = b;
    reg_mints_idx[rd]    = 1;
    reg_addrs_idx[rd]    = 0;

    set_correction(rd, 0, 0, 0, 0, 0);
  }
}

void create_true_false_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  if (lo1 <= up1) {
    // rs1 interval is not wrapped around
    if (lo2 <= up2) {
      // both rs1 and rs2 intervals are not wrapped around
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else if (up2 <= lo1) {
        // rs2 interval is less than or equal to rs1 interval
        mint_false_rs1.los[mint_num_false_rs1]   = lo1;
        mint_false_rs1.ups[mint_num_false_rs1++] = up1;
        mint_false_rs2.los[mint_num_false_rs2]   = lo2;
        mint_false_rs2.ups[mint_num_false_rs2++] = up2;

      } else if (lo2 == up2) {
        // rs2 interval is a singleton
        // a case where lo1 = up1 shouldn't be reach here
        // false case
        mint_false_rs1.los[mint_num_false_rs1]   = lo2;
        mint_false_rs1.ups[mint_num_false_rs1++] = up1;
        mint_false_rs2.los[mint_num_false_rs2]   = lo2;
        mint_false_rs2.ups[mint_num_false_rs2++] = up2;

        // true case
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = lo2 - 1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else if (lo1 == up1) {
        // rs1 interval is a singleton
        // false case
        mint_false_rs1.los[mint_num_false_rs1]   = lo1;
        mint_false_rs1.ups[mint_num_false_rs1++] = up1;
        mint_false_rs2.los[mint_num_false_rs2]   = lo2;
        mint_false_rs2.ups[mint_num_false_rs2++] = lo1;

        // true case
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo1 + 1; // never overflow
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else {
        // be careful about case [10, 20] < [20, 30] where needs a relation
        // we cannot handle non-singleton interval intersections in comparison
        printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      // rs1 interval is not wrapped around but rs2 is
      if (up1 < lo2 && up2 <= lo1) {
        // false
        mint_false_rs1.los[mint_num_false_rs1]   = lo1;
        mint_false_rs1.ups[mint_num_false_rs1++] = up1;
        mint_false_rs2.los[mint_num_false_rs2]   = 0;
        mint_false_rs2.ups[mint_num_false_rs2++] = up2;

        // true
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;
        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = UINT64_MAX_T;

      } else if (lo1 == up1) {
        uint64_t lo_p;
        uint64_t up_p;

        if (lo1 >= lo2) { // upper part
          mint_false_rs1.los[mint_num_false_rs1]   = lo1;
          mint_false_rs1.ups[mint_num_false_rs1++] = up1;
          // non-empty false case 1
          mint_false_rs2.los[mint_num_false_rs2]   = lo2;
          mint_false_rs2.ups[mint_num_false_rs2++] = lo1;
          // non-empty false case 2
          mint_false_rs2.los[mint_num_false_rs2]   = 0;
          mint_false_rs2.ups[mint_num_false_rs2++] = up2;

          // true case
          if (lo1 != UINT64_MAX_T) {
            lo_p = compute_lower_bound(lo2, reg_steps[rs1], lo1 + 1);
            up_p = compute_upper_bound(lo1, reg_steps[rs1], UINT64_MAX_T);
            if (lo_p <= up_p) {
              mint_true_rs1.los[mint_num_true_rs1]   = lo1;
              mint_true_rs1.ups[mint_num_true_rs1++] = up1;
              mint_true_rs2.los[mint_num_true_rs2]   = lo_p;
              mint_true_rs2.ups[mint_num_true_rs2++] = up_p;
            }
          }

        } else { // lower part
          // false case
          lo_p = compute_lower_bound(lo2, reg_steps[rs1], 0);
          up_p = compute_upper_bound(lo1, reg_steps[rs1], lo1);
          if (lo_p <= up_p) {
            mint_false_rs1.los[mint_num_false_rs1]   = lo1;
            mint_false_rs1.ups[mint_num_false_rs1++] = up1;
            mint_false_rs2.los[mint_num_false_rs2]   = lo_p;
            mint_false_rs2.ups[mint_num_false_rs2++] = up_p;
          }

          mint_true_rs1.los[mint_num_true_rs1]   = lo1;
          mint_true_rs1.ups[mint_num_true_rs1++] = up1;
          // non-empty true case 1
          mint_true_rs2.los[mint_num_true_rs2]   = lo1 + 1;
          mint_true_rs2.ups[mint_num_true_rs2++] = up2;
          // non-empty true case 2
          mint_true_rs2.los[mint_num_true_rs2]   = lo2;
          mint_true_rs2.ups[mint_num_true_rs2++] = UINT64_MAX_T;
        }

      } else {
        // we cannot handle non-singleton interval intersections in comparison
        printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }
  } else if (lo2 <= up2) {
    // rs2 interval is not wrapped around but rs1 is
    if (up1 < lo2 && up2 <= lo1) {
      // false case
      mint_false_rs1.los[mint_num_false_rs1]   = lo1;
      mint_false_rs1.ups[mint_num_false_rs1++] = UINT64_MAX_T;
      mint_false_rs2.los[mint_num_false_rs2]   = lo2;
      mint_false_rs2.ups[mint_num_false_rs2++] = up2;

      // true case
      mint_true_rs1.los[mint_num_true_rs1]   = 0;
      mint_true_rs1.ups[mint_num_true_rs1++] = up1;
      mint_true_rs2.los[mint_num_true_rs2]   = lo2;
      mint_true_rs2.ups[mint_num_true_rs2++] = up2;
    } else if (lo2 == up2) {
      // construct constraint for true case
      uint64_t lo_p;
      uint64_t up_p;

      if (lo2 > lo1) { // upper part
        // false case
        lo_p = compute_lower_bound(lo1, reg_steps[rs1], lo2);
        up_p = compute_upper_bound(lo1, reg_steps[rs1], UINT64_MAX_T);
        if (lo_p <= up_p) {
          mint_false_rs1.los[mint_num_false_rs1]   = lo_p;
          mint_false_rs1.ups[mint_num_false_rs1++] = up_p;
          mint_false_rs2.los[mint_num_false_rs2]   = lo2;
          mint_false_rs2.ups[mint_num_false_rs2++] = up2;
        }

        // non-empty true 1
        mint_true_rs1.los[mint_num_true_rs1]   = lo1;
        mint_true_rs1.ups[mint_num_true_rs1++] = lo2 - 1; // never lo2 = 0
        // non-empty true 2
        mint_true_rs1.los[mint_num_true_rs1]   = 0;
        mint_true_rs1.ups[mint_num_true_rs1++] = up1;

        mint_true_rs2.los[mint_num_true_rs2]   = lo2;
        mint_true_rs2.ups[mint_num_true_rs2++] = up2;

      } else {
        // non-empty false case 1
        mint_false_rs1.los[mint_num_false_rs1]   = lo2;
        mint_false_rs1.ups[mint_num_false_rs1++] = up1;
        // non-empty false case 2
        mint_false_rs1.los[mint_num_false_rs1]   = lo1;
        mint_false_rs1.ups[mint_num_false_rs1++] = UINT64_MAX_T;

        mint_false_rs2.los[mint_num_false_rs2]   = lo2;
        mint_false_rs2.ups[mint_num_false_rs2++] = up2;

        // true case
        if (lo2 != 0) {
          lo_p = compute_lower_bound(lo1, reg_steps[rs1], 0);
          up_p = compute_upper_bound(lo1, reg_steps[rs1], lo2 - 1);
          if (lo_p <= up_p) {
            mint_true_rs1.los[mint_num_true_rs1]   = lo_p;
            mint_true_rs1.ups[mint_num_true_rs1++] = up_p;
            mint_true_rs2.los[mint_num_true_rs2]   = lo2;
            mint_true_rs2.ups[mint_num_true_rs2++] = up2;
          }
        }
      }

    } else {
      // we cannot handle non-singleton interval intersections in comparison
      printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

  } else {
    // both rs1 and rs2 intervals are wrapped around
    printf("OUTPUT: < of two non-wrapped intervals are not supported for now at %x \n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

// multi intervals are managed
void create_mconstraints(uint64_t* lo1_p, uint64_t* up1_p, uint64_t* lo2_p, uint64_t* up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo1;
  uint64_t up1;
  uint64_t lo2;
  uint64_t up2;

  mint_num_true_rs1  = 0;
  mint_num_true_rs2  = 0;
  mint_num_false_rs1 = 0;
  mint_num_false_rs2 = 0;

  for (uint8_t i = 0; i < reg_mints_idx[rs1]; i++) {
    lo1 = lo1_p[i];
    up1 = up1_p[i];
    for (uint8_t j = 0; j < reg_mints_idx[rs2]; j++) {
      lo2 = lo2_p[j];
      up2 = up2_p[j];
      create_true_false_constraints(lo1, up1, lo2, up2);
    }
  }

  if (mint_num_true_rs1 > 0 && mint_num_true_rs2 > 0)
    true_reachable  = true;
  if (mint_num_false_rs1 > 0 && mint_num_false_rs2 > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      constrain_memory(rs1, mint_true_rs1.los, mint_true_rs1.ups, mint_num_true_rs1, trb, false);
      constrain_memory(rs2, mint_true_rs2.los, mint_true_rs2.ups, mint_num_true_rs2, trb, false);
      take_branch(1, 1);
      constrain_memory(rs1, mint_false_rs1.los, mint_false_rs1.ups,mint_num_false_rs1, trb, false);
      constrain_memory(rs2, mint_false_rs2.los, mint_false_rs2.ups,mint_num_false_rs2, trb, false);
      take_branch(0, 0);
    } else {
      constrain_memory(rs1, mint_true_rs1.los, mint_true_rs1.ups, mint_num_true_rs1, trb, true);
      constrain_memory(rs2, mint_true_rs2.los, mint_true_rs2.ups, mint_num_true_rs2, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, mint_false_rs1.los, mint_false_rs1.ups,mint_num_false_rs1, trb, true);
    constrain_memory(rs2, mint_false_rs2.los, mint_false_rs2.ups,mint_num_false_rs2, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

}

void create_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb) {

  if (reg_mints_idx[rs1] > 1 || reg_mints_idx[rs2] > 1) {
    printf("OUTPUT: unsupported minterval 6 %x \n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  mint_num_sym = 0;

  if (lo1 <= up1) {
    // rs1 interval is not wrapped around
    if (lo2 <= up2) {
      // both rs1 and rs2 intervals are not wrapped around
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);

        is_only_one_branch_reachable = true;
        take_branch(1, 0);
      } else if (up2 <= lo1) {
        // rs2 interval is less than or equal to rs1 interval
        constrain_memory(rs1, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);
        constrain_memory(rs2, (uint64_t*) 0, (uint64_t*) 0, 0, trb, true);

        is_only_one_branch_reachable = true;
        take_branch(0, 0);
      } else if (lo2 == up2) {
        // rs2 interval is a singleton
        // a case where lo1 = up1 shouldn't be reach here
        // false case
        mint_lo_crt[0] = lo2;
        mint_up_crt[0] = up2;
        mint_lo_sym[0] = lo2;
        mint_up_sym[0] = up1;
        constrain_memory(rs1, mint_lo_sym, mint_up_sym, 1, trb, false);
        constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
        // record false
        take_branch(0, 1);

        // true case
        mint_lo_sym[0] = lo1;
        mint_up_sym[0] = lo2 - 1;
        constrain_memory(rs1, mint_lo_sym, mint_up_sym, 1, trb, false);
        constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
        take_branch(1, 0);
      } else if (lo1 == up1) {
        // rs1 interval is a singleton
        // false case
        mint_lo_crt[0] = lo1;
        mint_up_crt[0] = up1;
        mint_lo_sym[0] = lo2;
        mint_up_sym[0] = lo1;
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
        constrain_memory(rs2, mint_lo_sym, mint_up_sym, 1, trb, false);
        // record false
        take_branch(0, 1);

        // true case
        mint_lo_sym[0] = lo1 + 1;
        mint_up_sym[0] = up2;
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
        constrain_memory(rs2, mint_lo_sym, mint_up_sym, 1, trb, false); // never overflow
        take_branch(1, 0);
      } else {
        // be careful about case [10, 20] < [20, 30] where needs a relation
        // we cannot handle non-singleton interval intersections in comparison
        printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      // rs1 interval is not wrapped around but rs2 is
      if (up1 < lo2 && up2 <= lo1) {
        // false
        mint_lo_crt[0] = lo1;
        mint_up_crt[0] = up1;
        mint_lo_sym[0] = 0;
        mint_up_sym[0] = up2;
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
        constrain_memory(rs2, mint_lo_sym, mint_up_sym, 1, trb, false);
        // record false
        take_branch(0, 1);

        // true
        mint_lo_sym[0] = lo2;
        mint_up_sym[0] = UINT64_MAX_T;
        constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
        constrain_memory(rs2, mint_lo_sym, mint_up_sym, 1, trb, false);
        take_branch(1, 0);
      } else if (lo1 == up1) {
        uint64_t lo_p;
        uint64_t up_p;

        mint_lo_crt[0] = lo1;
        mint_up_crt[0] = up1;

        if (lo1 >= lo2) { // upper part
          // non-empty false case 1
          mint_lo_sym[mint_num_sym]   = lo2;
          mint_up_sym[mint_num_sym++] = lo1;

          // non-empty false case 2
          mint_lo_sym[mint_num_sym]   = 0;
          mint_up_sym[mint_num_sym++] = up2;
          constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1           , trb, false);
          constrain_memory(rs2, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);

          // true case
          if (lo1 != UINT64_MAX_T) {
            lo_p = compute_lower_bound(lo2, reg_steps[rs1], lo1 + 1);
            up_p = compute_upper_bound(lo1, reg_steps[rs1], UINT64_MAX_T);
            if (lo_p <= up_p) {
              take_branch(0, 1);

              mint_lo_sym[0] = lo_p;
              mint_up_sym[0] = up_p;
              constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
              constrain_memory(rs2, mint_lo_sym, mint_up_sym, 1, trb, false);
              take_branch(1, 0);

            } else {
              // else empty
              is_only_one_branch_reachable = true;
              take_branch(0, 0);
            }
          } else {
            // else empty
            is_only_one_branch_reachable = true;
            take_branch(0, 0);
          }

        } else { // lower part
          // false case
          lo_p = compute_lower_bound(lo2, reg_steps[rs1], 0);
          up_p = compute_upper_bound(lo1, reg_steps[rs1], lo1);
          if (lo_p <= up_p) {
            mint_lo_sym[0] = lo_p;
            mint_up_sym[0] = up_p;
            constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1, trb, false);
            constrain_memory(rs2, mint_lo_sym, mint_up_sym, 1, trb, false);
            take_branch(0, 1);

          } else {
            // else empty
            is_only_one_branch_reachable = true;
          }

          // non-empty true case 1
          mint_lo_sym[mint_num_sym]   = lo1 + 1;
          mint_up_sym[mint_num_sym++] = up2;
          // non-empty true case 2
          mint_lo_sym[mint_num_sym]   = lo2;
          mint_up_sym[mint_num_sym++] = UINT64_MAX_T;
          constrain_memory(rs1, mint_lo_crt, mint_up_crt, 1           , trb, false);
          constrain_memory(rs2, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);
          take_branch(1, 0);
        }

      } else {
        // we cannot handle non-singleton interval intersections in comparison
        printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }
  } else if (lo2 <= up2) {
    // rs2 interval is not wrapped around but rs1 is
    if (up1 < lo2 && up2 <= lo1) {
      // false case
      mint_lo_crt[0] = lo2;
      mint_up_crt[0] = up2;
      mint_lo_sym[0] = lo1;
      mint_up_sym[0] = UINT64_MAX_T;
      constrain_memory(rs1, mint_lo_sym, mint_up_sym, 1, trb, false);
      constrain_memory(rs2, mint_lo_crt  , mint_up_crt  , 1, trb, false);
      take_branch(0, 1);

      // true case
      mint_lo_sym[0] = 0;
      mint_up_sym[0] = up1;
      constrain_memory(rs1, mint_lo_sym, mint_up_sym, 1, trb, false);
      constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
      take_branch(1, 0);
    } else if (lo2 == up2) {
      // construct constraint for true case
      uint64_t lo_p;
      uint64_t up_p;

      mint_lo_crt[0] = lo2;
      mint_up_crt[0] = up2;

      if (lo2 > lo1) { // upper part
        // false case
        lo_p = compute_lower_bound(lo1, reg_steps[rs1], lo2);
        up_p = compute_upper_bound(lo1, reg_steps[rs1], UINT64_MAX_T);
        if (lo_p <= up_p) {
          mint_lo_sym[0] = lo_p;
          mint_up_sym[0] = up_p;
          constrain_memory(rs1, mint_lo_sym, mint_up_sym, 1, trb, false);
          constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
          take_branch(0, 1);
        } else {
          // else empty
          is_only_one_branch_reachable = true;
        }

        // non-empty true 1
        mint_lo_sym[mint_num_sym]   = lo1;
        mint_up_sym[mint_num_sym++] = lo2 - 1; // never lo2 = 0
        // non-empty true 2
        mint_lo_sym[mint_num_sym]   = 0;
        mint_up_sym[mint_num_sym++] = up1;
        constrain_memory(rs1, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);
        constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1           , trb, false);
        take_branch(1, 0);
      } else {
        // non-empty false case 1
        mint_lo_sym[mint_num_sym]   = lo2;
        mint_up_sym[mint_num_sym++] = up1;
        // non-empty false case 2
        mint_lo_sym[mint_num_sym]   = lo1;
        mint_up_sym[mint_num_sym++] = UINT64_MAX_T;
        constrain_memory(rs1, mint_lo_sym, mint_up_sym, mint_num_sym, trb, false);
        constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1           , trb, false);

        // true case
        if (lo2 != 0) {
          lo_p = compute_lower_bound(lo1, reg_steps[rs1], 0);
          up_p = compute_upper_bound(lo1, reg_steps[rs1], lo2 - 1);
          if (lo_p <= up_p) {
            take_branch(0, 1);

            mint_lo_sym[0] = lo_p;
            mint_up_sym[0] = up_p;
            constrain_memory(rs1, mint_lo_sym, mint_up_sym, 1, trb, false);
            constrain_memory(rs2, mint_lo_crt, mint_up_crt, 1, trb, false);
            take_branch(1, 0);
          } else {
            // else empty
            is_only_one_branch_reachable = true;
            take_branch(0, 0);
          }
        } else {
          // else empty 0 < 0
          is_only_one_branch_reachable = true;
          take_branch(0, 0);
        }

      }

    } else {
      // we cannot handle non-singleton interval intersections in comparison
      printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

  } else {
    // both rs1 and rs2 intervals are wrapped around
    printf("OUTPUT: < of two non-wrapped intervals are not supported for now at %x \n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void backtrack_sltu() {
  uint64_t vaddr;

  if (debug_symbolic) {
    printf("OUTPUT: backtracking sltu ");
    print_symbolic_memory(tc);
  }

  vaddr = *(vaddrs + tc);

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      *(reg_data_typ + vaddr) = *(data_types + tc);
      *(registers    + vaddr) = *(values     + tc);
      reg_mints[vaddr].los[0] = mints[tc].los[0];
      reg_mints[vaddr].ups[0] = mints[tc].ups[0];
      reg_mints_idx[vaddr]    = 1;
      reg_steps[vaddr]        = 1;
      reg_addrs_idx[rd]       = 0;

      set_correction(vaddr, 0, 0, 0, 0, 0);

      // restoring mrcc
      mrcc = *(tcs + tc);

      if (vaddr != REG_FP)
        if (vaddr != REG_SP) {
          // stop backtracking and try next case
          pc = pc + INSTRUCTIONSIZE;

          ic_sltu = ic_sltu + 1;
        }
    }
  } else
    store_virtual_memory(pt, vaddr, *(tcs + tc));

  efree();
}

void backtrack_sd() {
  if (debug_symbolic) {
    printf("OUTPUT: backtracking sd ");
    print_symbolic_memory(tc);
  }

  uint64_t idx;
  for (uint8_t i = 0; i < ld_froms_idx[tc]; i++) {
    idx = load_symbolic_memory(pt, ld_froms[tc].vaddrs[i]);
    sd_to_idxs[idx]--;
  }

  store_virtual_memory(pt, *(vaddrs + tc), *(tcs + tc));

  efree();
}

void backtrack_ecall() {
  if (debug_symbolic) {
    printf("OUTPUT: backtracking ecall ");
    print_symbolic_memory(tc);
  }

  if (*(vaddrs + tc) == 0) {
    // backtracking malloc
    if (get_program_break(current_context) == mints[tc].los[0] + mints[tc].ups[0])
      set_program_break(current_context, mints[tc].los[0]);
    else {
      printf("OUTPUT: malloc backtracking error at %x", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking read
    rc = rc + 1;

    // record value, lower and upper bound
    *(read_values + rc) = *(values + tc);

    *(read_los + rc) = mints[tc].los[0];
    *(read_ups + rc) = mints[tc].ups[0];

    store_virtual_memory(pt, *(vaddrs + tc), *(tcs + tc));
  }

  efree();
}

void backtrack_trace(uint64_t* context) {
  uint64_t savepc;

  if (debug_symbolic) {
    printf("OUTPUT: backtracking from exit code \n");
    // printf3((uint64_t*) "%s: backtracking %s from exit code %d\n", exe_name, get_name(context), (uint64_t*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH));
  }

  symbolic = 0;

  backtrack = 1;

  while (backtrack) {
    pc = *(pcs + tc);

    if (pc == 0) {
      // we have backtracked all code back to the data segment
      backtrack = 0;
    } else {
      savepc = pc;

      fetch();
      decode_execute();

      if (pc != savepc)
        // backtracking stopped by sltu
        backtrack = 0;
    }
  }

  symbolic = 1;

  set_pc(context, pc);
}


// -------------------------------- propagation --------------------------------

void propagate_mul(uint64_t step, uint64_t k) {
  bool cnd;
  for (uint8_t i = 0; i < mints_num_prop; i++) {
    cnd = mul_condition(lo_prop[i], up_prop[i], k);
    if (cnd == true) {
      lo_prop[i] = lo_prop[i] * k;
      up_prop[i] = up_prop[i] * k;
    } else {
      // potential of overflow
      // assert: reg_mints[rs2].los[0] * reg_steps[rs1] <= UINT64_MAX_T
      uint128_t lcm_ = lcm_128(TWO_TO_THE_POWER_OF_64, (uint128_t) k * step);
      uint128_t rhs  = (uint128_t) (lcm_ - (uint128_t) k * step) / k;
      uint128_t lhs  = (up_prop[i] - lo_prop[i]);
      if (lhs >= rhs) {
        uint64_t gcd_step_k = gcd_128( (uint128_t) k * step, TWO_TO_THE_POWER_OF_64);
        uint64_t lo_p       = (lo_prop[i] * k);
        lo_prop[i]          = lo_p - (lo_p / gcd_step_k) * gcd_step_k;
        up_prop[i]          = compute_upper_bound(lo_prop[i], gcd_step_k, UINT64_MAX_T);
      } else {
        printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }
  }
}

void propagate_divu(uint64_t step, uint64_t k, uint64_t step_rd) {
  // interval semantics of divu
  for (uint8_t i = 0; i < mints_num_prop; i++) {
    if (lo_prop[i] > up_prop[i]) {
      // rs1 constraint is wrapped: [lo, UINT64_MAX_T], [0, up]
      // lo/k == up/k (or) up/k + step_rd
      if (lo_prop[i]/k != up_prop[i]/k)
        if (lo_prop[i]/k > up_prop[i]/k + step_rd) {
          printf("OUTPUT: wrapped divison rsults two intervals at %x \n", pc);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

      uint64_t max = compute_upper_bound(lo_prop[i], step, UINT64_MAX_T);
      lo_prop[i] = (max + step) / k;
      up_prop[i] = max          / k;
    } else {
      lo_prop[i] = lo_prop[i] / k;
      up_prop[i] = up_prop[i] / k;
    }
  }
}

void propagate_remu(uint64_t step, uint64_t divisor) {
  // interval semantics of remu
  for (uint8_t i = 0; i < mints_num_prop; i++) {
    if (lo_prop[i] <= up_prop[i]) {
      // rs1 interval is not wrapped
      int rem_typ = remu_condition(lo_prop[i], up_prop[i], step, divisor);
      if (rem_typ == 0) {
        lo_prop[i] = lo_prop[i] % divisor;
        up_prop[i] = up_prop[i] % divisor;
        step_prop  = step;
      } else if (rem_typ == 1) {
        printf("OUTPUT: modulo results two intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (rem_typ == 2) {
        uint64_t gcd_step_k = gcd(step, divisor);
        lo_prop[i] = lo_prop[i]%divisor - ((lo_prop[i]%divisor) / gcd_step_k) * gcd_step_k;
        up_prop[i] = compute_upper_bound(lo_prop[i], gcd_step_k, divisor - 1);
        step_prop  = gcd_step_k;
      } else {
        printf("OUTPUT: modulo results many intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

    } else if (is_power_of_two(divisor)) {
      // rs1 interval is wrapped
      uint64_t gcd_step_k = gcd(step, divisor);
      uint64_t lcm        = (step * divisor) / gcd_step_k;

      if (up_prop[i] - lo_prop[i] < lcm - step) {
        printf("OUTPUT: wrapped modulo results many intervals at %x \n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      lo_prop[i] = lo_prop[i]%divisor - ((lo_prop[i]%divisor) / gcd_step_k) * gcd_step_k;
      up_prop[i] = compute_upper_bound(lo_prop[i], gcd_step_k, divisor - 1);
      step_prop  = gcd_step_k;
    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x \n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }
}

// --------------------------- conditional expression --------------------------

uint8_t check_conditional_type() {
  uint64_t saved_pc = pc;

  pc = pc - INSTRUCTIONSIZE;
  fetch();
  if (get_opcode(ir) == OP_OP && get_funct3(ir) == F3_XOR) {
    // !=
    pc = saved_pc;
    return DEQ;
  }

  pc = pc - INSTRUCTIONSIZE;
  fetch();
  if (get_opcode(ir) == OP_OP && get_funct3(ir) == F3_XOR) {
    // ==
    pc = saved_pc;
    return EQ;
  }

  pc = saved_pc + INSTRUCTIONSIZE;
  fetch();
  if (get_opcode(ir) == OP_IMM) {
    if (match_addi()) {
      uint64_t rd_ = get_rd(ir);
      pc = saved_pc + 2 * INSTRUCTIONSIZE;
      fetch();
      if (get_opcode(ir) == OP_OP) {
        if (match_sub(rd_)) {
          pc = saved_pc;
          return LGTE;
        }
      }
    }
  }

  pc = saved_pc;
  return LT;
}