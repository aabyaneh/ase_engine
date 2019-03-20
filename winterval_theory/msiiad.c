// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t MAX_TRACE_LENGTH = 1000000;

// trace
uint64_t  tc         = 0;             // trace counter
uint64_t* pcs        = (uint64_t*) 0; // trace of program counter values
uint64_t* tcs        = (uint64_t*) 0; // trace of trace counters to previous values
uint64_t* values     = (uint64_t*) 0; // trace of values
uint64_t* data_types = (uint64_t*) 0; // memory range or integer interval
uint64_t* los        = (uint64_t*) 0; // trace of lower bounds on values
uint64_t* ups        = (uint64_t*) 0; // trace of upper bounds on values
uint64_t* steps      = (uint64_t*) 0;
uint64_t* vaddrs     = (uint64_t*) 0; // trace of virtual addresses
uint64_t* ld_froms   = (uint64_t*) 0;
uint64_t* addsub_corrs    = (uint64_t*) 0;
uint64_t* muldivrem_corrs = (uint64_t*) 0;
uint64_t* corr_validitys  = (uint64_t*) 0;
bool*     hasmns          = (bool*) 0;

// read history
uint64_t  rc = 0; // read counter
uint64_t* read_values = (uint64_t*) 0;
uint64_t* read_los    = (uint64_t*) 0;
uint64_t* read_ups    = (uint64_t*) 0;

// registers
uint64_t* reg_los      = (uint64_t*) 0; // lower bound on register value
uint64_t* reg_ups      = (uint64_t*) 0; // upper bound on register value
uint64_t* reg_steps    = (uint64_t*) 0; // step on register value
uint8_t*  reg_data_typ = (uint8_t*) 0; // memory range or integer interval
uint8_t   VALUE_T      = 0;
uint8_t   POINTER_T    = 1;
// register constraints on memory
uint8_t*  reg_symb_typ = (uint8_t*) 0; // register has constraint
uint8_t   CONCRETE_T   = 0;
uint8_t   SYMBOLIC_CONCRETE_T = 1;
uint8_t   SYMBOLIC_T   = 2;
uint64_t* reg_vaddr = (uint64_t*) 0; // vaddr of constrained memory
bool*     reg_hasmn = (bool*) 0; // constraint has minuend
// corrections
uint64_t* reg_addsub_corr    = (uint64_t*) 0;
uint64_t* reg_muldivrem_corr = (uint64_t*) 0;
uint64_t* reg_corr_validity  = (uint64_t*) 0;
uint64_t  MUL_T  = 3;
uint64_t  DIVU_T = 4;
uint64_t  REMU_T = 5;

uint64_t current_rs1_tc = 0;
uint64_t current_rs2_tc = 0;

// trace counter of most recent constraint

uint64_t mrcc = 0;

// ------------------------- INITIALIZATION ------------------------

void init_symbolic_engine() {
  pcs        = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  tcs        = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  values     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  data_types = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  los        = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  ups        = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  steps      = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  vaddrs     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  addsub_corrs    = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  muldivrem_corrs = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  corr_validitys  = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  hasmns          = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);

  read_values = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  read_los    = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  read_ups    = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);

  reg_data_typ = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_los      = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_ups      = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_steps    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);

  reg_symb_typ = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_vaddr    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_hasmn    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_addsub_corr    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_muldivrem_corr = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_corr_validity  = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
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

bool is_power_of_two(uint64_t v) {
  return v && (!(v & (v - 1)));
}

bool check_incompleteness(uint64_t gcd_steps) {
  uint64_t i_max;

  if (*(reg_steps + rs1) < *(reg_steps + rs2)) {
    if (*(reg_steps + rs1) == gcd_steps) {
      i_max = (*(reg_ups + rs1) - *(reg_los + rs1)) / *(reg_steps + rs1);
      if (i_max < *(reg_steps + rs2)/gcd_steps - 1)
        return 1;
    } else
      return 1;
  } else if (*(reg_steps + rs1) > *(reg_steps + rs2)) {
    if (*(reg_steps + rs2) == gcd_steps) {
      i_max = (*(reg_ups + rs2) - *(reg_los + rs2)) / *(reg_steps + rs2);
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
  c2 = UINT64_MAX - (up2 - lo2);

  if (c1 <= c2)
    return 1;
  else
    return 0;
}

uint64_t mul_condition(uint64_t lo, uint64_t up, uint64_t k) {
  uint64_t c1;
  uint64_t c2;

  if (k == 0)
    return 0;

  c1 = up - lo;
  c2 = UINT64_MAX / k;

  if (c1 <= c2)
    return 0;

  return 1;
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
    return lo + ((value - lo) / step) * step;
}

////////////////////////////////////////////////////////////////////////////////
//                                operations
////////////////////////////////////////////////////////////////////////////////

void constrain_lui() {
  if (rd != REG_ZR) {
    reg_data_typ[rd] = VALUE_T;

    // interval semantics of lui
    reg_los[rd]   = imm << 12;
    reg_ups[rd]   = imm << 12;
    reg_steps[rd] = 1;

    // rd has no constraint
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);
  }
}

void constrain_addi() {
  if (rd == REG_ZR)
    return;

  if (reg_data_typ[rs1] == POINTER_T) {
    reg_data_typ[rd] = reg_data_typ[rs1];

    reg_los[rd]   = reg_los[rs1];
    reg_ups[rd]   = reg_ups[rs1];
    reg_steps[rd] = reg_steps[rs1];

    // rd has no constraint if rs1 is memory range
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);

    return;
  }

  reg_data_typ[rd] = VALUE_T;

  // interval semantics of addi
  reg_los[rd] = reg_los[rs1] + imm;
  reg_ups[rd] = reg_ups[rs1] + imm;

  if (reg_symb_typ[rs1] == SYMBOLIC_T) {
      // rd inherits rs1 constraint
      set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
      set_correction(rd, reg_addsub_corr[rs1] + imm, reg_muldivrem_corr[rs1],
        (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);

  } else {
    // rd has no constraint if rs1 has none
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);
  }
}

bool constrain_add_pointer() {
  if (reg_data_typ[rs1] == POINTER_T) {
    if (reg_data_typ[rs2] == POINTER_T) {
      // adding two pointers is undefined
      printf("OUTPUT: undefined addition of two pointers at %x\n", pc);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_data_typ[rd] = reg_data_typ[rs1];
    reg_los[rd]      = reg_los[rs1];
    reg_ups[rd]      = reg_ups[rs1];
    reg_steps[rd]    = 1;

    // rd has no constraint if rs1 is memory range
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);

    return 1;
  } else if (reg_data_typ[rs2] == POINTER_T) {
    reg_data_typ[rd] = reg_data_typ[rs2];
    reg_los[rd]      = reg_los[rs2];
    reg_ups[rd]      = reg_ups[rs2];
    reg_steps[rd]    = 1;

    // rd has no constraint if rs2 is memory range
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);

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
    bool cnd = add_sub_condition(*(reg_los + rs1), *(reg_ups + rs1), *(reg_los + rs2), *(reg_ups + rs2));
    if (cnd == true) {
      add_lo = reg_los[rs1] + reg_los[rs2];
      add_up = reg_ups[rs1] + reg_ups[rs2];
    }

    if (reg_symb_typ[rs1] == SYMBOLIC_T) {
      if (reg_symb_typ[rs2] == SYMBOLIC_T) {
        // we cannot keep track of more than one constraint for add but
        // need to warn about their earlier presence if used in comparisons
        set_constraint(rd, SYMBOLIC_T, 0, 0);
        set_correction(rd, 0, 0, 10);

        // interval semantics of add
        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("%s\n", " steps in addition are not consistent");
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        if (cnd == false) {
          // TODO: make sure
          uint64_t rhs = (lcm(TWO_TO_THE_POWER_OF_32, gcd_steps) - gcd_steps);
          uint64_t lhs = (reg_ups[rs1] - reg_los[rs1]) + (reg_ups[rs2] - reg_los[rs2]);
          if (lhs >= rhs) {
            uint64_t gcd_step_k = gcd(gcd_steps, TWO_TO_THE_POWER_OF_32);
            uint64_t lo = (reg_los[rs1] + reg_los[rs2]) % TWO_TO_THE_POWER_OF_32;
            add_lo    = lo - (lo / gcd_step_k) * gcd_step_k;
            add_up    = compute_upper_bound(add_lo, gcd_step_k, TWO_TO_THE_POWER_OF_32 - 1);
            gcd_steps = gcd_step_k;
          } else {
            printf("OUTPUT: phantom canot reason about overflowed add %x \n", pc);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        }

        reg_los[rd]   = add_lo;
        reg_ups[rd]   = add_up;
        reg_steps[rd] = gcd_steps;

      } else {
        // rd inherits rs1 constraint since rs2 has none
        set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
        set_correction(rd, reg_addsub_corr[rs1] + reg_los[rs2], reg_muldivrem_corr[rs1],
          (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);

        reg_los[rd]   = add_lo;
        reg_ups[rd]   = add_up;
        reg_steps[rd] = reg_steps[rs1];
      }
    } else if (reg_symb_typ[rs2] == SYMBOLIC_T) {
      // rd inherits rs2 constraint since rs1 has none
      set_constraint(rd, reg_symb_typ[rs2], reg_vaddr[rs2], 0);
      set_correction(rd, reg_addsub_corr[rs2] + reg_los[rs1], reg_muldivrem_corr[rs2],
        (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);

      reg_los[rd]   = add_lo;
      reg_ups[rd]   = add_up;
      reg_steps[rd] = reg_steps[rs2];
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_constraint(rd, 0, 0, 0);
      set_correction(rd, 0, 0, 0);

      reg_los[rd]   = add_lo;
      reg_ups[rd]   = add_up;
      reg_steps[rd] = 1;
    }
  }
}

bool constrain_sub_pointer() {
  if (reg_data_typ[rs1] == POINTER_T) {
    if (reg_data_typ[rs2] == POINTER_T) {
      if (reg_los[rs1] == reg_los[rs2])
        if (reg_ups[rs1] == reg_ups[rs2]) {
          reg_data_typ[rd] = POINTER_T;
          reg_los[rd]      = registers[rd];
          reg_ups[rd]      = registers[rd];
          reg_steps[rd]    = 1;

          // rd has no constraint if rs1 and rs2 are memory range
          set_constraint(rd, 0, 0, 0);
          set_correction(rd, 0, 0, 0);

          return 1;
        }

      // subtracting incompatible pointers
      throw_exception(EXCEPTION_INVALIDADDRESS, 0);

      return 1;
    } else {
      reg_data_typ[rd] = reg_data_typ[rs1];
      reg_los[rd]      = reg_los[rs1];
      reg_ups[rd]      = reg_ups[rs1];
      reg_steps[rd]    = 1;

      // rd has no constraint if rs1 is memory range
      set_constraint(rd, 0, 0, 0);
      set_correction(rd, 0, 0, 0);

      return 1;
    }
  } else if (reg_data_typ[rs2] == POINTER_T) {
    reg_data_typ[rd] = reg_data_typ[rs2];
    reg_los[rd]      = reg_los[rs2];
    reg_ups[rd]      = reg_ups[rs2];
    reg_steps[rd]    = 1;

    // rd has no constraint if rs2 is memory range
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);

    return 1;
  }

  return 0;
}

void constrain_sub() {
  uint64_t sub_lo;
  uint64_t sub_up;

  if (rd != REG_ZR) {
    if (constrain_sub_pointer())
      return;

    reg_data_typ[rd] = VALUE_T;

    // interval semantics of sub
    bool cnd = add_sub_condition(reg_los[rs1], reg_ups[rs1], reg_los[rs2], reg_ups[rs2]);
    if (cnd == true) {
      sub_lo = reg_los[rs1] + reg_ups[rs2];
      sub_up = reg_ups[rs1] + reg_los[rs2];
    }

    if (reg_symb_typ[rs1] == SYMBOLIC_T) {
      if (reg_symb_typ[rs2] == SYMBOLIC_T) {
        // we cannot keep track of more than one constraint for sub but
        // need to warn about their earlier presence if used in comparisons
        set_constraint(rd, SYMBOLIC_T, 0, 0);
        set_correction(rd, 0, 0, 10);

        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("%s\n", " steps in subtraction are not consistent");
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        if (cnd == false) {
          printf("OUTPUT: phantom canot reason about overflowed sub %x \n", pc);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        reg_los[rd]   = sub_lo;
        reg_ups[rd]   = sub_up;
        reg_steps[rd] = gcd_steps;

      } else {
        // rd inherits rs1 constraint since rs2 has none
        set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
        set_correction(rd, reg_addsub_corr[rs1] - reg_los[rs2], reg_muldivrem_corr[rs1],
          (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);

        reg_los[rd]   = sub_lo;
        reg_ups[rd]   = sub_up;
        reg_steps[rd] = reg_steps[rs1];
      }
    } else if (reg_symb_typ[rs2] == SYMBOLIC_T) {
      if (*(reg_hasmn + rs2)) {
        // rs2 constraint has already minuend and can have another minuend
        set_constraint(rd, reg_symb_typ[rs2], reg_vaddr[rs2], 0);
        set_correction(rd, reg_los[rs1] - reg_addsub_corr[rs2], reg_muldivrem_corr[rs2],
          (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      } else {
        // rd inherits rs2 constraint since rs1 has none
        set_constraint(rd, reg_symb_typ[rs2], reg_vaddr[rs2], 1);
        set_correction(rd, reg_los[rs1] - reg_addsub_corr[rs2], reg_muldivrem_corr[rs2],
          (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      }

      reg_los[rd]   = sub_lo;
      reg_ups[rd]   = sub_up;
      reg_steps[rd] = reg_steps[rs2];
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_constraint(rd, 0, 0, 0);
      set_correction(rd, 0, 0, 0);

      reg_los[rd]   = add_lo;
      reg_ups[rd]   = add_up;
      reg_steps[rd] = 1;
    }
  }
}

void constrain_mul() {
  uint64_t mul_lo;
  uint64_t mul_up;

  if (rd != REG_ZR) {
    reg_data_typ[rd] = VALUE_T;

    // interval semantics of mul
    mul_lo = reg_los[rs1] * reg_los[rs2];
    mul_up = reg_ups[rs1] * reg_ups[rs2];

    if (reg_symb_typ[rs1] == SYMBOLIC_T) {
      if (reg_symb_typ[rs2] == SYMBOLIC_T) {
        // non-linear expressions are not supported
        printf("OUTPUT: detected non-linear expression in mul at %x \n", pc);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);

      } else if (reg_hasmn[rs1]) {
        // correction does not work anymore
        printf("correction does not work anymore at e.g. (1 - [.]) * 10 %x \n", pc);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
        set_correction(rd, reg_addsub_corr[rs1], reg_los[rs2], reg_corr_validity[rs1] + MUL_T);

        bool cnd = mul_condition(reg_los[rs1], reg_ups[rs1], reg_los[rs2]);
        if (cnd == true) {
          reg_los[rd]   = mul_lo;
          reg_ups[rd]   = mul_up;
          reg_steps[rd] = reg_steps[rs1] * reg_los[rs2];
        } else {
          // TODO: make sure
          uint64_t rhs = (lcm(TWO_TO_THE_POWER_OF_32, reg_los[rs2] * reg_steps[rs1]) - reg_los[rs2] * reg_steps[rs1]) / reg_los[rs2];
          if (reg_ups[rs1] - reg_los[rs1] >= rhs) {
            uint64_t gcd_step_k = gcd(reg_los[rs2] * reg_steps[rs1], TWO_TO_THE_POWER_OF_32);
            uint64_t lo   = (reg_los[rs1] * reg_los[rs2]) % TWO_TO_THE_POWER_OF_32;
            reg_los[rd]   = lo - (lo / gcd_step_k) * gcd_step_k;
            reg_ups[rd]   = compute_upper_bound(reg_los[rd], gcd_step_k, TWO_TO_THE_POWER_OF_32 - 1);
            reg_steps[rd] = gcd_step_k;
            reg_corr_validity[rs1] += REMU_T;
          } else {
            printf("OUTPUT: phantom canot reason about overflowed mul %x \n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        }
      }
    } else if (reg_symb_typ[rs2] == SYMBOLIC_T) {
      if (reg_hasmn[rs2]) {
        // correction does not work anymore
        printf("correction does not work anymore at e.g. 10 * (1 - [.]) %x \n", pc);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs2 constraint since rs1 has none
        // assert: rs1 interval is singleton
        set_constraint(rd, reg_symb_typ[rs2], reg_vaddr[rs2], 0);
        set_correction(rd, reg_addsub_corr[rs2], reg_los[rs1], reg_corr_validity[rs2] + MUL_T);

        bool cnd = mul_condition(reg_los[rs2], reg_ups[rs2], reg_los[rs1]);
        if (cnd == true) {
          reg_los[rd]   = mul_lo;
          reg_ups[rd]   = mul_up;
          reg_steps[rd] = reg_steps[rs2] * reg_los[rs1];
        } else {
          // TODO: make sure
          uint64_t rhs = (lcm(TWO_TO_THE_POWER_OF_32, reg_los[rs1] * reg_steps[rs2]) - reg_los[rs1] * reg_steps[rs2]) / reg_los[rs1];
          if (reg_ups[rs2] - reg_los[rs2] >= rhs) {
            uint64_t gcd_step_k = gcd(reg_los[rs1] * reg_steps[rs2], TWO_TO_THE_POWER_OF_32);
            uint64_t lo   = (reg_los[rs1] * reg_los[rs2]) % TWO_TO_THE_POWER_OF_32;
            reg_los[rd]   = lo - (lo / gcd_step_k) * gcd_step_k;
            reg_ups[rd]   = compute_upper_bound(reg_los[rd], gcd_step_k, TWO_TO_THE_POWER_OF_32 - 1);
            reg_steps[rd] = gcd_step_k;
            reg_corr_validity[rs2] += REMU_T;
          } else {
            printf("OUTPUT: phantom canot reason about overflowed mul %x \n", pc - entry_point);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        }
      }
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_constraint(rd, 0, 0, 0);
      set_correction(rd, 0, 0, 0);

      reg_los[rd]   = mul_lo;
      reg_ups[rd]   = mul_up;
      reg_steps[rd] = 1;
    }
  }
}

void constrain_divu() {
  uint64_t div_lo;
  uint64_t div_up;

  if (reg_los[rs2] != 0) {
    if (reg_ups[rs2] >= reg_los[rs2]) {
      // 0 is not in interval
      if (rd != REG_ZR) {
        reg_data_typ[rd] = VALUE_T;

        // interval semantics of divu
        div_lo = reg_los[rs1] / reg_ups[rs2];
        div_up = reg_ups[rs1] / reg_los[rs2];
        step   = reg_steps[rs1];

        if (reg_symb_typ[rs1] == SYMBOLIC_T) {
          if (reg_symb_typ[rs2] == SYMBOLIC_T) {
            // non-linear expressions are not supported
            printf("OUTPUT: detected non-linear expression in divu at %x", pc);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);

          } else if (reg_hasmn[rs1]) {
            // correction does not work anymore
            printf("correction does not work anymore at e.g. (1 - [.]) / 10 %x \n", pc);
            exit(EXITCODE_SYMBOLICEXECUTIONERROR);

          } else {
            // rd inherits rs1 constraint since rs2 has none
            // assert: rs2 interval is singleton
            set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
            set_correction(rd, reg_addsub_corr[rs1], reg_los[rs2], reg_corr_validity[rs1] + DIVU_T);

            // step computation
            if (reg_steps[rs1] < reg_los[rs2]) {
              if (reg_los[rs2] % reg_steps[rs1] != 0) {
                printf("OUTPUT: steps in divison are not consistent at %x\n", pc);
                exit(EXITCODE_SYMBOLICEXECUTIONERROR);
              }
              reg_steps[rd] = 1;
            } else {
              if (reg_steps[rs1] % reg_los[rs2] != 0) {
                printf("OUTPUT: steps in divison are not consistent at %x\n", pc);
                exit(EXITCODE_SYMBOLICEXECUTIONERROR);
              }
              reg_steps[rd] = reg_steps[rs1] / reg_los[rs2];
            }

            // interval semantics of divu
            if (*(reg_los + rs1) > *(reg_ups + rs1)) {
              // rs1 constraint is wrapped: [lo, UINT64_MAX], [0, up]
              max = compute_upper_bound(reg_los[rs1, step, UINT64_MAX);
              reg_los[rd] = (max + step) / reg_los[rs2];
              reg_ups[rd] = max          / reg_ups[rs2];

              // lo/k == up/k (or) up/k + step_rd
              if (div_los != div_ups)
                if (div_los > div_ups + reg_steps[rd]) {
                  printf("OUTPUT: wrapped divison rsults two intervals at %x \n", pc);
                  exit(EXITCODE_SYMBOLICEXECUTIONERROR);
                }
            } else {
              // rs1 constraint is not wrapped
              reg_los[rd] = div_lo;
              reg_ups[rd] = div_up;
            }

          }
        } else if (reg_symb_typ[rs2] == SYMBOLIC_T) {
          printf("OUTPUT: detected division of constant by interval at %x \n", pc);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);

        } else {
          // rd has no constraint if both rs1 and rs2 have no constraints
          set_constraint(rd, 0, 0, 0);
          set_correction(rd, 0, 0, 0);

          reg_los[rd]   = div_lo;
          reg_ups[rd]   = div_up;
          reg_steps[rd] = 1;
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

  if (reg_los[rs2] == 0)
    throwException(EXCEPTION_DIVISIONBYZERO, 0);

  if (reg_symb_typ[rs2] == SYMBOLIC_T) {
    // rs2 has constraint
    printf("OUTPUT: constrained memory location in right operand of remu at %x", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (rd == REG_ZR)
    return;

  reg_data_typ[rd] = VALUE_T;

  if (reg_symb_typ[rs1] == SYMBOLIC_T) {
    // interval semantics of remu
    divisor = reg_los[rs2];
    step    = reg_steps[rs1];

    if (reg_los[rs1] <= reg_ups[rs1]) {
      // rs1 interval is not wrapped
      int rem_typ = remu_condition(reg_los[rs1], reg_ups[rs1], step, divisor);
      if (rem_typ == 0) {
        rem_lo        = reg_los[rs1] % divisor;
        rem_up        = reg_ups[rs1] % divisor;
        reg_steps[rd] = step;
      } else if (rem_typ == 1) {
        printf("OUTPUT: modulo results two intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (rem_typ == 2) {
        uint64_t gcd_step_k = gcd(step, divisor);
        rem_lo        = reg_los[rs1]%divisor - ((reg_los[rs1]%divisor) / gcd_step_k) * gcd_step_k;
        rem_up        = compute_upper_bound(rem_lo, gcd_step_k, divisor - 1);
        reg_steps[rd] = gcd_step_k;
      } else {
        printf("OUTPUT: modulo results many intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
      set_correction(rd, reg_addsub_corr[rs1], reg_los[rs2], reg_corr_validity[rs1] + REMU_T);

    } else if (is_power_of_two(divisor)) {
      // rs1 interval is wrapped
      uint64_t gcd_step_k = gcd(step, divisor);
      uint64_t lcm        = (step * divisor) / gcd_step_k;

      if (reg_ups[rs1] - reg_los[rs1] < lcm - step) {
        printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      rem_lo        = reg_los[rs1]%divisor - ((reg_los[rs1]%divisor) / gcd_step_k) * gcd_step_k;
      rem_up        = compute_upper_bound(rem_lo, gcd_step_k, divisor - 1);
      reg_steps[rd] = gcd_step_k;

      set_constraint(rd, reg_symb_typ[rs1], reg_vaddr[rs1], 0);
      set_correction(rd, reg_addsub_corr[rs1], reg_los[rs2], reg_corr_validity[rs1] + REMU_T);

    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (reg_hasmn[rs1]) {
      // correction does not work anymore
      printf("correction does not work anymore at e.g. (1 - [.]) mod 10 %x \n", pc);
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_los[rd] = rem_lo;
    reg_ups[rd] = rem_up;
  } else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);

    reg_los[rd]   = reg_los[rs1] % reg_los[rs2];
    reg_ups[rd]   = reg_ups[rs1] % reg_ups[rs2];
    reg_steps[rd] = 1;
  }
}

void constrain_sltu() {
  if (rd != REG_ZR) {
    if (reg_symb_typ[rs1] != SYMBOLIC_T && reg_symb_typ[rs2] != SYMBOLIC_T) {
      // concrete semantics of sltu
      registers[rd] = (registers[rs1] < registers[rs2]) ? 1 : 0;

      reg_data_typ[rd] = VALUE_T;
      reg_los[rd]      = registers[rd];
      reg_ups[rd]      = registers[rd];
      reg_steps[rd]    = 1;

      set_constraint(rd, 0, 0, 0);
      set_correction(rd, 0, 0, 0);

      pc = pc + INSTRUCTIONSIZE;

      ic_sltu = ic_sltu + 1;
      return;
    }

    current_rs1_tc = load_virtual_memory(pt, reg_vaddr[rs1]);
    current_rs2_tc = load_virtual_memory(pt, reg_vaddr[rs2]);

    if (reg_data_typ[rs1] == POINTER_T)
      if (reg_data_typ[rs2] == POINTER_T)
        create_constraints(registers[rs1], registers[rs1], registers[rs2], registers[rs2], mrcc, 0);
      else
        create_constraints(registers[rs1], registers[rs1], reg_los[rs2], reg_ups[rs2], mrcc, 0);
    else if (reg_data_typ[rs2] == POINTER_T)
      create_constraints(reg_los[rs1], reg_ups[rs1], registers[rs2], registers[rs2], mrcc, 0);
    else
      create_constraints(reg_los[rs1], reg_ups[rs1], reg_los[rs2], reg_ups[rs2], mrcc, 0);
  }

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
}

void take_eqne_branch(bool b, bool how_many_more) {
  if (how_many_more) {
    uint64_t new_pc = b ? pc + INSTRUCTIONSIZE : pc + imm;

    // record frame and stack pointer
    store_register_memory(REG_FP, *(registers + REG_FP), new_pc);
    store_register_memory(REG_SP, *(registers + REG_SP), 0);
  } else {
    pc = b ? pc + INSTRUCTIONSIZE : pc + imm;
  }
}

void create_bne_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb) {
  bool     cannot_handle = false;
  bool     empty;
  // uint64_t lo1 = reg_los[rs1];
  // uint64_t up1 = reg_ups[rs1];
  // uint64_t lo2 = reg_los[rs2];
  // uint64_t up2 = reg_ups[rs2];

  if (rd == REG_ZR)
    return;

  if (lo1 <= up1) {
    // rs1 non-wrapped
    if (lo2 <= up2) {
      // rs2 non-wrapped
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        constrain_memory(rs1, 0, 0, trb, true);
        constrain_memory(rs2, 0, 0, trb, true);

        take_eqne_branch(false, 0);
      } else if (up2 < lo1) {
        // rs2 interval is less than or equal to rs1 interval
        constrain_memory(rs1, 0, 0, trb, true);
        constrain_memory(rs2, 0, 0, trb, true);

        take_eqne_branch(false, 0);
      } else if (lo2 == up2) {
        // rs2 interval is a singleton

        // construct constraint for false case 1
        if (lo2 != lo1) {
          // non empty
          constrain_memory(rs1, lo1, lo2 - 1, trb, false);
          constrain_memory(rs2, lo2, up2, trb, false);
          empty = false;
        } else {
          empty = true;
        }

        // construct constraint for false case 1
        if (lo2 != up1) {
          // non empty
          if (!empty)
            take_eqne_branch(false, 1);
          constrain_memory(rs1, lo2 + 1, up1, trb, false);
          constrain_memory(rs2, lo2, up2, trb, false);
        }

        // check emptiness of true case for rhs
        if ( (lo2 - lo1) % reg_steps[rs1]) {
          // rhs for true case is empty
          take_eqne_branch(false, 0);
        } else {
          // record frame and stack pointer
          store_register_memory(REG_FP, *(registers + REG_FP), pc + imm);
          store_register_memory(REG_SP, *(registers + REG_SP), 0);

          // construct constraint for true case
          constrain_memory(rs1, lo2, up2, trb, false);
          constrain_memory(rs2, lo2, up2, trb, false);
          take_eqne_branch(true, 0);
        }

      } else if (lo1 == up1) {
        // rs1 interval is a singleton

        // construct constraint for false case 1
        if (lo1 != lo2) { // otherwise rhs is empty
          constrain_memory(rs1, lo1, up1, trb, false);
          constrain_memory(rs2, lo2, lo1 - 1, trb, false);
          empty = false;
        } else {
          empty = true;
        }

        // construct constraint for false case 2
        if (lo1 != up2) {
          // non empty
          if (!empty)
            take_eqne_branch(false, 1);
          constrain_memory(rs1, lo1, up1, trb, false);
          constrain_memory(rs2, lo1 + 1, up2, trb, false);
          empty = false;
        } else {
          empty = true;
        }

        // check emptiness of true case for rhs
        if ( (lo1 - lo2) % reg_steps[rs2]) {
          // rhs for true case is empty
          take_eqne_branch(false, 0);
        } else {
          // record frame and stack pointer
          store_register_memory(REG_FP, *(registers + REG_FP), pc + imm);
          store_register_memory(REG_SP, *(registers + REG_SP), 0);

          // construct constraint for true case
          constrain_memory(rs1, lo1, up1, trb, false);
          constrain_memory(rs2, lo1, up1, trb, false);
          take_eqne_branch(true, 0);
        }

      } else {
        // we cannot handle
        cannot_handle == true;
      }
    } else {
      // rs2 wrapped
      if (up1 < lo2 && up2 < lo1) {
        constrain_memory(rs1, 0, 0, trb, true);
        constrain_memory(rs2, 0, 0, trb, true);

        take_eqne_branch(false, 0);
      } else if (lo1 == up1) {
        // construct constraint for false case 1
        if (lo1 != lo2) {
          // non empty
          constrain_memory(rs1, lo1, up1, trb, false);
          constrain_memory(rs2, lo2, lo1 - 1, trb, false);
          empty = false;
        } else {
          empty = true;
        }

        // construct constraint for false case 2
        if (lo1 != up2) {
          // non empty
          if (!empty)
            take_eqne_branch(false, 1);
          constrain_memory(rs1, lo1, up1, trb, false);
          constrain_memory(rs2, lo1 + 1, up2, trb, false);
          empty = false;
        } else {
          empty = true;
        }

        // check emptiness of true case for rhs
        if ( (lo1 - lo2) % reg_steps[rs2]) {
          // rhs for true case is empty
          take_eqne_branch(false, 0);
        } else {
          // record frame and stack pointer
          store_register_memory(REG_FP, *(registers + REG_FP), pc + imm);
          store_register_memory(REG_SP, *(registers + REG_SP), 0);

          // construct constraint for true case
          constrain_memory(rs1, lo1, up1, trb, false);
          constrain_memory(rs2, lo1, up1, trb, false);
          take_eqne_branch(true, 0);
        }

      } else {
        // we cannot handle
        cannot_handle == true;
      }
    }

  } else if (lo2 <= up2) {
    // rs1 wrapped, rs2 non-wrapped
    if (up2 < lo1 && up1 < lo2) {
      constrain_memory(rs1, 0, 0, trb, true);
      constrain_memory(rs2, 0, 0, trb, true);

      take_eqne_branch(false, 0);
    } else if (lo2 == up2) {
      // construct constraint for false case 1
      if (lo2 != lo1) {
        // non empty
        constrain_memory(rs1, lo1, lo2 - 1, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);
        empty = false;
      } else {
        empty = true;
      }

      // construct constraint for false case 1
      if (lo2 != up1) {
        // non empty
        if (!empty)
          take_eqne_branch(false, 1);
        constrain_memory(rs1, lo2 + 1, up1, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);
      }

      // check emptiness of true case for rhs
      if ( (lo2 - lo1) % reg_steps[rs1]) {
        // rhs for true case is empty
        take_eqne_branch(false, 0);
      } else {
        // record frame and stack pointer
        store_register_memory(REG_FP, *(registers + REG_FP), pc + imm);
        store_register_memory(REG_SP, *(registers + REG_SP), 0);

        // construct constraint for true case
        constrain_memory(rs1, lo2, up2, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);
        take_eqne_branch(true, 0);
      }
    } else {
      // we cannot handle
      cannot_handle == true;
    }

  } else {
    // rs1 wrapped, rs2 wrapped
    // we cannot handle: they have common vlaues and they canont be singleton
    cannot_handle == true;
  }

  if (cannot_handle) {
    uint64_t rs1_tc = load_virtual_memory(pt, reg_vaddr[rs1]);
    uint64_t rs2_tc = load_virtual_memory(pt, reg_vaddr[rs2]);

    if (steps[rs1_tc] > 1) {
      if (steps[rs2_tc] > 1) {
        uint64_t los_diff = (los[rs1_tc] >= los[rs2_tc]) ? (los[rs1_tc] - los[rs2_tc]) : (los[rs2_tc]- los[rs1_tc]);
        if ( los_diff % gcd(steps[rs1_tc], steps[rs2_tc]) != 0) {
          constrain_memory(rs1, 0, 0, trb, true);
          constrain_memory(rs2, 0, 0, trb, true);

          take_eqne_branch(false, 0);

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

void constrain_bne() {
  if (reg_symb_typ[rs1] != SYMBOLIC_T && reg_symb_typ[rs2] != SYMBOLIC_T) {
    // concrete semantics of beq
    pc = (registers[rs1] != registers[rs2]) ? pc + imm : pc + INSTRUCTIONSIZE;

    ic_bne = ic_bne + 1;

    return;
  }

  if (reg_data_typ[rs1] == POINTER_T)
    if (reg_data_typ[rs2] == POINTER_T) {
      // concrete semantics of beq
      pc = (registers[rs1] != registers[rs2]) ? pc + imm : pc + INSTRUCTIONSIZE;
    } else {
      create_bne_constraints(registers[rs1], registers[rs1], reg_los[rs2], reg_ups[rs2], mrcc);
    }
  else if (reg_data_typ[rs2] == POINTER_T)
    create_bne_constraints(reg_los[rs1], reg_ups[rs1], registers[rs2], registers[rs2], mrcc);
  else
    create_bne_constraints(reg_los[rs1], reg_ups[rs1], reg_los[rs2], reg_ups[rs2], mrcc);

  ic_bne = ic_bne + 1;
}

uint64_t constrain_ld() {
  uint64_t vaddr;
  uint64_t mrvc;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

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
        *(reg_los   + rd) = *(los    + mrvc);
        *(reg_ups   + rd) = *(ups    + mrvc);
        *(reg_steps + rd) = *(steps  + mrvc);

        // assert: vaddr == *(vaddrs + mrvc)

        if (is_symbolic_value(*(reg_data_typ + rd), *(reg_los + rd), *(reg_ups + rd))) {
          // vaddr is constrained by rd if value interval is not singleton
          set_constraint(rd, 1, vaddr, 0);
          set_correction(rd, 0, 0, 0);
        } else {
          set_constraint(rd, 0, 0, 0);
          set_correction(rd, 0, 0, 0);
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
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

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

      store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_typ[rs2], reg_los[rs2], reg_ups[rs2], reg_steps[rs2], reg_vaddr[rs2], reg_hasmn[rs2], reg_addsub_corr[rs2], reg_muldivrem_corr[rs2], reg_corr_validity[rs2], mrcc);

      // keep track of instruction address for profiling stores
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of stores in total
      ic_sd = ic_sd + 1;

      // and individually
      *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void constrain_jal_jalr() {
  if (rd != REG_ZR) {
    *(reg_los + rd) = *(registers + rd);
    *(reg_ups + rd) = *(registers + rd);
  }
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void print_symbolic_memory(uint64_t svc) {
  printf3((uint64_t*) "@%d{@%d@%x", (uint64_t*) svc, (uint64_t*) *(tcs + svc), (uint64_t*) *(pcs + svc));
  if (*(pcs + svc) >= entry_point)
    print_code_line_number_for_instruction(*(pcs + svc) - entry_point);
  if (*(vaddrs + svc) == 0) {
    printf3((uint64_t*) ";%x=%x=malloc(%d)}\n", (uint64_t*) *(values + svc), (uint64_t*) *(los + svc), (uint64_t*) *(ups + svc));
    return;
  } else if (*(vaddrs + svc) < NUMBEROFREGISTERS)
    printf2((uint64_t*) ";%s=%d", get_register_name(*(vaddrs + svc)), (uint64_t*) *(values + svc));
  else
    printf2((uint64_t*) ";%x=%d", (uint64_t*) *(vaddrs + svc), (uint64_t*) *(values + svc));
  if (*(data_types + svc))
    if (*(los + svc) == *(ups + svc))
      printf1((uint64_t*) "(%d)}\n", (uint64_t*) *(los + svc));
    else
      printf2((uint64_t*) "(%d,%d)}\n", (uint64_t*) *(los + svc), (uint64_t*) *(ups + svc));
  else if (*(los + svc) == *(ups + svc))
    printf1((uint64_t*) "[%d]}\n", (uint64_t*) *(los + svc));
  else
    printf2((uint64_t*) "[%d,%d]}\n", (uint64_t*) *(los + svc), (uint64_t*) *(ups + svc));
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
  if (*(reg_data_typ + reg)) {
    if (vaddr < *(reg_los + reg))
      // memory access below start address of mallocated block
      return 0;
    else if (vaddr - *(reg_los + reg) >= *(reg_ups + reg))
      // memory access above end address of mallocated block
      return 0;
    else
      return 1;
  } else if (*(reg_los + reg) == *(reg_ups + reg))
    return 1;
  else {
    printf2((uint64_t*) "%s: detected unsupported symbolic access of memory interval at %x", exe_name, (uint64_t*) pc);
    print_code_line_number_for_instruction(pc - entry_point);
    println();

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
    printf4((uint64_t*) "%s: detected most recent value counter %d at vaddr %x greater than current trace counter %d\n", exe_name, (uint64_t*) mrvc, (uint64_t*) vaddr, (uint64_t*) tc);

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

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint8_t data_type, uint64_t lo, uint64_t up, uint64_t step, uint64_t ld_from, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb) {
  uint64_t mrvc;

  if (vaddr == 0)
    // tracking program break and size for malloc
    mrvc = 0;
  else if (vaddr < NUMBEROFREGISTERS)
    // tracking a register value for sltu
    mrvc = mrcc;
  else {
    // assert: vaddr is valid and mapped
    mrvc = load_symbolic_memory(pt, vaddr);

    if (trb < mrvc)
      if (value == *(values + mrvc))
        if (data_type == *(data_types + mrvc))
          if (lo == *(los + mrvc))
            if (up == *(ups + mrvc))
              if (step == *(steps + mrvc))
                if (ld_from == ld_froms[mrvc])
                  if (addsub_corr == addsub_corrs[mrvc])
                    if (muldivrem_corr == muldivrem_corrs[mrvc])
                      if (corr_validity == corr_validitys[mrvc])
                        if (hasmn == hasmns[mrvc])
                          // prevent tracking identical updates
                          return;

  }

  if (trb < mrvc) {
    // current value at vaddr does not need to be tracked,
    // just overwrite it in the trace
    *(data_types + mrvc) = data_type;

    *(values + mrvc) = value;
    *(los    + mrvc) = lo;
    *(ups    + mrvc) = up;
    *(steps  + mrvc) = step;

    // assert: vaddr == *(vaddrs + mrvc)

    *(ld_froms        + mrvc) = ld_from;
    *(hasmns          + mrvc) = hasmn;
    *(addsub_corrs    + mrvc) = addsub_corr;
    *(muldivrem_corrs + mrvc) = muldivrem_corr;
    *(corr_validitys  + mrvc) = corr_validity;

    if (debug_symbolic) {
      printf1((uint64_t*) "%s: overwriting ", exe_name);
      print_symbolic_memory(mrvc);
    }
  } else if (is_trace_space_available()) {
    // current value at vaddr is from before most recent branch,
    // track that value by creating a new trace event
    ealloc();

    *(pcs + tc) = pc;
    *(tcs + tc) = mrvc;
    *(data_types + tc) = data_type;
    *(values + tc) = value;
    *(los    + tc) = lo;
    *(ups    + tc) = up;
    *(steps  + tc) = step;
    *(vaddrs + tc) = vaddr;

    *(ld_froms        + tc) = ld_from;
    *(hasmns          + tc) = hasmn;
    *(addsub_corrs    + tc) = addsub_corr;
    *(muldivrem_corrs + tc) = muldivrem_corr;
    *(corr_validitys  + tc) = corr_validity;

    if (vaddr < NUMBEROFREGISTERS) {
      if (vaddr > 0)
        // register tracking marks most recent constraint
        mrcc = tc;
    } else
      // assert: vaddr is valid and mapped
      store_virtual_memory(pt, vaddr, tc);

    if (debug_symbolic) {
      printf1((uint64_t*) "%s: storing ", exe_name);
      print_symbolic_memory(tc);
    }
  } else
    throw_exception(EXCEPTION_MAXTRACE, 0);
}

void store_constrained_memory(uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t step, uint64_t ld_from, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb) {
  uint64_t mrvc;

  /* we need to constrain freed memory to keep our ld chain alive */
  // if (vaddr >= get_program_break(current_context))
  //   if (vaddr < *(registers + REG_SP))
  //     // do not constrain free memory
  //     return;

  /* useless */
  // mrvc = load_virtual_memory(pt, vaddr);
  // if (mrvc < trb) {
  //   // we do not support potentially aliased constrained memory
  //   printf1((uint64_t*) "%s: detected potentially aliased constrained memory\n", exe_name);
  //
  //   exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  // }

  // always track constrained memory by using tc as most recent branch
  store_symbolic_memory(pt, vaddr, lo, VALUE_T, lo, up, step, ld_from, hasmn, addsub_corr, muldivrem_corr, corr_validity, tc);
}

void store_register_memory(uint64_t reg, uint64_t value, uint64_t next_pc) {
  // always track register memory by using tc as most recent branch
  store_symbolic_memory(pt, reg, value, 0, value, value, next_pc, tc);
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
void apply_correction(uint64_t lo, uint64_t up, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t lo_before_op, uint64_t mrvc, uint64_t trb) {
  lo = compute_lower_bound(los[mrvc], steps[mrvc], lo);
  up = compute_upper_bound(los[mrvc], steps[mrvc], up);

  // add, sub
  if (hasmn) {
    uint64_t tmp = addsub_corr - up;
    up  = addsub_corr - lo;
    lo = tmp;
  } else {
    lo = lo - addsub_corr;
    up = up - addsub_corr;
  }

  // mul, div, rem
  if (corr_validity == MUL_T) {
    // <9223372036854775808, 2^64 - 1, 1> * 2 = <0, 2^64 - 2, 2>
    // <9223372036854775809, 15372286728091293014, 1> * 3 = <9223372036854775811, 9223372036854775810, 3>
    lo = los[mrvc] + (lo - lo_before_op) / muldivrem_corr; // lo_op_before_cmp
    up = los[mrvc] + (up - lo_before_op) / muldivrem_corr; // lo_op_before_cmp

  } else if (corr_validity == DIVU_T) {
    uint64_t divisor = muldivrem_corr;

    if (los[mrvc] <= ups[mrvc]) {
      // non-wrapped
      lo = (lo == 0) ? los[mrvc] : lo * divisor;

      // if (lo * divisor >= los[mrvc])
      //   lo = compute_lower_bound(los[mrvc], steps[mrvc], lo * divisor);
      // else
      //   lo = los[mrvc];

      up = compute_upper_bound(los[mrvc], steps[mrvc], up * divisor + reverse_division_up(ups[mrvc], up, divisor));
    } else {
      // wrapped
      uint64_t lo1;
      uint64_t up1;
      uint64_t lo2;
      uint64_t up2;
      uint64_t max = compute_upper_bound(los[mrvc], steps[mrvc], UINT64_MAX);
      uint8_t  which_is_empty;

      lo = (lo == 0) ? (max + steps[mrvc]) : lo * divisor;
      up = compute_upper_bound(los[mrvc], steps[mrvc], up * divisor + reverse_division_up(max, up, divisor));

      which_is_empty = 0;
      if (lo <= ups[mrvc]) {
        lo_1 = lo;
        up_1 = (up < ups[mrvc]) ? up : ups[mrvc];
      } else {
        which_is_empty = 1;
      }

      if (up >= los[mrvc]) {
        lo_2 = (lo > los[mrvc]) ? lo : los[mrvc];
        up_2 = up;
      } else {
        which_is_empty = (which_is_empty == 1) ? 4 : 2;
      }

      if (which_is_empty == 4) {
        if (up_1 + steps[mrvc] >= lo_2) {
          lo = lo_1;
          up = up_2;
        } else {
          printf("OUTPUT: reverse of division results two intervals at %x\n", pc - entry_point);
          exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }
      }
    }

  } else if (corr_validity == REMU_T) {
    if (*(rem_typ + reg) == 1) {
      operator = *(rem + reg);
      lo = computeLowerBound(*(los + mrvc), *(steps + mrvc), (*(los + mrvc) / operator) * operator + lo);
      up = computeUpperBound(*(los + mrvc), *(steps + mrvc), (*(ups + mrvc) / operator) * operator + up);
    } else {
      printf("OUTPUT: detected an unsupported remu in a conditional expression at %x \n", );
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else if (corr_validity > 5) {
    printf("OUTPUT: detected an unsupported conditional expression at \n", pc - entry_point);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  //////////////////////////////////////////////////////////////////////////////
  store_constrained_memory(vaddrs[mrvc], lo, up, steps[mrvc], ld_froms[mrvc], hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], trb);
  if (ld_froms[mrvc]) {
    propagate_backwards(vaddrs[mrvc], los[mrvc]);
  }
  //////////////////////////////////////////////////////////////////////////////
}

// y = x op a;
// if (y)
// vaddr of y -> new y
// lo_before_op for y -> before new y
void propagate_backwards(uint64_t vaddr, uint64_t lo_before_op) {
  uint64_t mrvc_y;
  uint64_t mrvc_x;

  mrvc_y = load_symbolic_memory(pt, vaddr);
  mrvc_x = load_symbolic_memory(pt, ld_froms[mrvc_y]);
  apply_correction(los[mrvc_y], ups[mrvc_y], hasmns[mrvc_y], addsub_corrs[mrvc_y], muldivrem_corrs[mrvc_y], corr_validitys[mrvc_y], lo_before_op, mrvc_x, trb);
}

void constrain_memory(uint64_t reg, uint64_t lo, uint64_t up, uint64_t trb, bool only_reachable_branch) {
  uint64_t mrvc;

  if (reg_symb_typ[reg] == SYMBOLIC_T) {
    mrvc = (reg == rs1) ? current_rs1_tc : current_rs2_tc;

    if (only_reachable_branch == true) {
      lo = los[mrvc];
      up = ups[mrvc];
      store_constrained_memory(reg_vaddr[reg], lo, up, steps[mrvc], ld_froms[mrvc], hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], trb);
    } else {
      apply_correction(lo, up, reg_hasmn[reg], reg_addsub_corr[reg], reg_muldivrem_corr[reg], reg_corr_validity[reg], reg_los[reg], mrvc, trb);
    }

  }
}

void set_constraint(uint64_t reg, uint64_t hasco, uint64_t vaddr, uint64_t hasmn) {
  reg_symb_typ[reg] = hasco;
  reg_vaddr[reg] = vaddr;
  reg_hasmn[reg] = hasmn;
}

void take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0) {
    // record that we need to set rd to true
    store_register_memory(rd, b, 0);

    // record frame and stack pointer
    store_register_memory(REG_FP, *(registers + REG_FP), 0);
    store_register_memory(REG_SP, *(registers + REG_SP), 0);
  } else {
    *(registers + rd) = b;

    *(reg_data_typ + rd) = 0;

    *(reg_los + rd) = b;
    *(reg_ups + rd) = b;

    set_constraint(rd, 0, 0, 0);
    set_correction(rd, 0, 0, 0);
  }
}

void create_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb, uint64_t how_many_more) {
  if (lo1 <= up1) {
    // rs1 interval is not wrapped around
    if (lo2 <= up2) {
      // both rs1 and rs2 intervals are not wrapped around
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        constrain_memory(rs1, lo1, up1, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);

        take_branch(1, how_many_more);
      } else if (up2 <= lo1) {
        // rs2 interval is less than or equal to rs1 interval
        constrain_memory(rs1, lo1, up1, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);

        take_branch(0, how_many_more);
      } else if (lo2 == up2) {
        // rs2 interval is a singleton

        // construct constraint for false case
        constrain_memory(rs1, lo2, up1, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);

        // record that we need to set rd to false
        store_register_memory(rd, 0, 0);
        // record frame and stack pointer
        store_register_memory(REG_FP, *(registers + REG_FP), 0);
        store_register_memory(REG_SP, *(registers + REG_SP), 0);

        // construct constraint for true case
        constrain_memory(rs1, lo1, lo2 - 1, trb, false);
        constrain_memory(rs2, lo2, up2, trb, false);

        take_branch(1, how_many_more);
      } else if (lo1 == up1) {
        // rs1 interval is a singleton

        // construct constraint for false case
        constrain_memory(rs1, lo1, up1, trb, false);
        constrain_memory(rs2, lo2, lo1, trb, false);

        // record that we need to set rd to false
        store_register_memory(rd, 0, 0);
        // record frame and stack pointer
        store_register_memory(REG_FP, *(registers + REG_FP), 0);
        store_register_memory(REG_SP, *(registers + REG_SP), 0);

        // construct constraint for true case
        constrain_memory(rs1, lo1, up1, trb, false);
        constrain_memory(rs2, lo1 + 1, up2, trb, false);

        take_branch(1, how_many_more);
      } else {
        // be careful about case [10, 20] < [20, 30] where needs a relation

        // we cannot handle non-singleton interval intersections in comparison
        printf1((uint64_t*) "%s: detected non-singleton interval intersection\n", exe_name);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      // rs1 interval is not wrapped around but rs2 is

      // unwrap rs2 interval and use higher portion first
      create_constraints(lo1, up1, lo2, UINT64_MAX_T, trb, 1);

      // then use lower portion of rs2 interval
      create_constraints(lo1, up1, 0, up2, trb, 0);
    }
  } else if (lo2 <= up2) {
    // rs2 interval is not wrapped around but rs1 is

    // unwrap rs1 interval and use higher portion first
    create_constraints(lo1, UINT64_MAX_T, lo2, up2, trb, 1);

    // then use lower portion of rs1 interval
    create_constraints(0, up1, lo2, up2, trb, 0);
  } else {
    // both rs1 and rs2 intervals are wrapped around

    // unwrap rs1 and rs2 intervals and use higher portions
    create_constraints(lo1, UINT64_MAX_T, lo2, UINT64_MAX_T, trb, 3);

    // use higher portion of rs1 interval and lower portion of rs2 interval
    create_constraints(lo1, UINT64_MAX_T, 0, up2, trb, 2);

    // use lower portions of rs1 and rs2 intervals
    create_constraints(0, up1, 0, up2, trb, 1);

    // use lower portion of rs1 interval and higher portion of rs2 interval
    create_constraints(0, up1, lo2, UINT64_MAX_T, trb, 0);
  }
}

void backtrack_bne() {
  uint64_t vaddr;

  if (debug_symbolic) {
    printf("OUTPUT: backtracking bne \n");
    print_symbolic_memory(tc);
  }

  vaddr = *(vaddrs + tc);

  if (vaddr < NUMBEROFREGISTERS && vaddr > 0) {
    // the register is identified by vaddr
    registers[vaddr]    = values[tc];
    reg_data_typ[vaddr] = data_types[tc];
    reg_los[vaddr]      = values[tc];
    reg_ups[vaddr]      = values[tc];
    reg_steps[vaddr]    = 1;

    set_constraint(vaddr, 0, 0, 0);
    set_correction(vaddr, 0, 0, 0);

    // restoring mrcc
    mrcc = *(tcs + tc);

    if (vaddr == REG_FP) {
      // stop backtracking and try next case
      pc = steps[tc]; // next pc was stored in steps trace (due to less memory consumption)

      ic_bne = ic_bne + 1;
    }
  } else
    store_virtual_memory(pt, vaddr, *(tcs + tc));

  efree();
}

void backtrack_sltu() {
  uint64_t vaddr;

  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking sltu ", exe_name);
    print_symbolic_memory(tc);
  }

  vaddr = *(vaddrs + tc);

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      *(reg_data_typ + vaddr) = *(data_types + tc);
      *(registers    + vaddr) = *(values     + tc);
      *(reg_los      + vaddr) = *(los        + tc);
      *(reg_ups      + vaddr) = *(ups        + tc);
      *(reg_steps    + vaddr) = 1;

      set_constraint(vaddr, 0, 0, 0);
      set_correction(vaddr, 0, 0, 0);

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
    printf1((uint64_t*) "%s: backtracking sd ", exe_name);
    print_symbolic_memory(tc);
  }

  store_virtual_memory(pt, *(vaddrs + tc), *(tcs + tc));

  efree();
}

void backtrack_ecall() {
  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking ecall ", exe_name);
    print_symbolic_memory(tc);
  }

  if (*(vaddrs + tc) == 0) {
    // backtracking malloc
    if (get_program_break(current_context) == *(los + tc) + *(ups + tc))
      set_program_break(current_context, *(los + tc));
    else {
      printf1((uint64_t*) "%s: malloc backtracking error at ", exe_name);
      print_symbolic_memory(tc);
      printf4((uint64_t*) " with current program break %x unequal %x which is previous program break %x plus size %d\n",
        (uint64_t*) get_program_break(current_context),
        (uint64_t*) (*(los + tc) + *(ups + tc)),
        (uint64_t*) *(los + tc),
        (uint64_t*) *(ups + tc));

      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking read
    rc = rc + 1;

    // record value, lower and upper bound
    *(read_values + rc) = *(values + tc);

    *(read_los + rc) = *(los + tc);
    *(read_ups + rc) = *(ups + tc);

    store_virtual_memory(pt, *(vaddrs + tc), *(tcs + tc));
  }

  efree();
}

void backtrack_trace(uint64_t* context) {
  uint64_t savepc;

  if (debug_symbolic)
    printf3((uint64_t*) "%s: backtracking %s from exit code %d\n", exe_name, get_name(context), (uint64_t*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH));

  symbolic = 0;

  backtrack = 1;

  while (backtrack) {
    pc = *(pcs + tc);

    if (pc == 0)
      // we have backtracked all code back to the data segment
      backtrack = 0;
    else {
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