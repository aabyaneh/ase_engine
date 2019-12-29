/*
  This project contains part of the Selfie Project source code
  which is governed by a BSD license. For further information
  and LICENSE conditions see the following website:
  http://selfie.cs.uni-salzburg.at

  Furthermore this project uses the api of boolector SMT solver
  further information: boolector.github.io
*/

#include "sase.h"

// -----------------------------------------------------------------
// ---------------- Solver Aided Symbolic Execution ----------------
// -----------------------------------------------------------------

char           var_buffer[100];   // a buffer for automatic variable name generation
char           const_buffer[64];  // a buffer for loading integers of more than 32 bits
Btor*          btor;
BoolectorSort  bv_sort;
BoolectorSort  bv_sort_32;
BoolectorNode* zero_bv;
BoolectorNode* one_bv;
BoolectorNode* eight_bv;
BoolectorNode* meight_bv;
BoolectorNode* twelve_bv;

uint64_t       b             = 0; // counting total number of backtracking
uint64_t       SASE          = 8; // Solver Aided Symbolic Execution
uint8_t        CONCRETE_T    = 0; // concrete value type
uint8_t        SYMBOLIC_T    = 1; // symbolic value type
uint64_t       two_to_the_power_of_32;

// symbolic registers
BoolectorNode**   sase_regs;         // array of pointers to SMT expressions
uint8_t*          sase_regs_typ;     // CONCRETE_T or SYMBOLIC_T

// engine trace
uint64_t        sase_trace_size = 1000000;
uint64_t        sase_tc         = 0;    // trace counter
uint64_t*       sase_pcs;
BoolectorNode** sase_false_branchs;
uint64_t*       sase_read_trace_ptrs;   // pointers to read trace
uint64_t*       sase_program_brks;      // keep track of program_break
uint64_t*       sase_store_trace_ptrs;  // pointers to store trace
uint64_t*       sase_rds;
uint64_t        mrif            = 0;    // most recent conditional expression

// store trace
// uint64_t        tc;
// uint64_t*       tcs;
// uint64_t*       vaddrs;
// uint64_t*       values;
uint8_t*        is_symbolics;
BoolectorNode** symbolic_values;

// read trace
uint64_t*       concrete_reads;
BoolectorNode** constrained_reads;
uint64_t        read_tc         = 0;
uint64_t        read_tc_current = 0;
uint64_t        read_buffer     = 0;

// input trace
BoolectorNode** constrained_inputs;
uint64_t*       sase_input_trace_ptrs;
uint64_t        input_cnt         = 0;
uint64_t        input_cnt_current = 0;

uint64_t        number_of_queries = 0;

// ********************** engine functions ************************
uint64_t minus_eight = -8;

void init_sase() {
  btor        = boolector_new();
  bv_sort     = boolector_bitvec_sort(btor, 64);
  bv_sort_32  = boolector_bitvec_sort(btor, 32);
  zero_bv     = boolector_unsigned_int(btor, 0, bv_sort);
  one_bv      = boolector_unsigned_int(btor, 1, bv_sort);
  twelve_bv   = boolector_unsigned_int(btor, 12, bv_sort);
  eight_bv    = boolector_unsigned_int(btor, 8, bv_sort);
  meight_bv   = boolector_unsigned_int_64(minus_eight);

  boolector_set_opt(btor, BTOR_OPT_INCREMENTAL, 1);
  boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);

  two_to_the_power_of_32 = two_to_the_power_of(32);

  sase_regs             = (BoolectorNode**) malloc(sizeof(BoolectorNode*) * NUMBEROFREGISTERS);
  sase_regs_typ         = (uint8_t*)        malloc(sizeof(uint8_t)        * NUMBEROFREGISTERS);
  for (size_t i = 0; i < NUMBEROFREGISTERS; i++) {
    sase_regs_typ[i] = CONCRETE_T;
  }
  sase_regs[REG_ZR] = zero_bv;
  // sase_regs[REG_FP] = zero_bv;

  sase_pcs              = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  sase_read_trace_ptrs  = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  sase_program_brks     = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  sase_store_trace_ptrs = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  sase_rds              = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  sase_false_branchs    = (BoolectorNode**) malloc(sizeof(BoolectorNode*) * sase_trace_size);

  tcs                   = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  vaddrs                = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  values                = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  is_symbolics          = (uint8_t*)        malloc(sizeof(uint8_t)        * sase_trace_size);
  symbolic_values       = (BoolectorNode**) malloc(sizeof(BoolectorNode*) * sase_trace_size);

  concrete_reads        = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);
  constrained_reads     = (BoolectorNode**) malloc(sizeof(BoolectorNode*) * sase_trace_size);

  constrained_inputs    = (BoolectorNode**) malloc(sizeof(BoolectorNode*) * sase_trace_size);
  sase_input_trace_ptrs = (uint64_t*)       malloc(sizeof(uint64_t)       * sase_trace_size);

  // initialization
  tc               = 0;
  *tcs             = 0;
  *vaddrs          = 0;
  *values          = 0;
  *is_symbolics    = CONCRETE_T;
  *symbolic_values = zero_bv;

  *sase_pcs              = 0;
  *sase_false_branchs    = (BoolectorNode*) 0;
  *sase_read_trace_ptrs  = 0;
  *sase_program_brks     = 0;
  *sase_store_trace_ptrs = 0;
  *sase_rds              = 0;
  sase_tc++;
}

uint64_t sase_is_trace_space_available() {
  return tc + 1 < sase_trace_size;
}

BoolectorNode* boolector_unsigned_int_64(uint64_t value) {
  sprintf(const_buffer, "%llu", value);
  return boolector_constd(btor, bv_sort, const_buffer);
}

bool check_branch_satisfiability(BoolectorNode* assert) {
  bool result = false;
  boolector_push(btor, 1);
  boolector_assert(btor, assert);
  number_of_queries++;
  if (boolector_sat(btor) == BOOLECTOR_SAT) {
    result = true;
  }
  boolector_pop(btor, 1);

  return result;
}

void store_registers(uint64_t b) {
  if (tc + 3 >= sase_trace_size)
    throw_exception(EXCEPTION_MAXTRACE, 0);

  tc++;
  tcs[tc]             = 0;
  is_symbolics[tc]    = CONCRETE_T;
  values[tc]          = b;
  symbolic_values[tc] = (b == 0) ? zero_bv : one_bv;
  vaddrs[tc]          = rd;

  tc++;
  tcs[tc]             = 0;
  is_symbolics[tc]    = CONCRETE_T;
  values[tc]          = registers[REG_FP];
  symbolic_values[tc] = (BoolectorNode*) 0;
  vaddrs[tc]          = REG_FP;

  tc++;
  tcs[tc]             = 0;
  is_symbolics[tc]    = CONCRETE_T;
  values[tc]          = registers[REG_SP];
  symbolic_values[tc] = (BoolectorNode*) 0;
  vaddrs[tc]          = REG_SP;
}

void restore_registers() {
  registers[REG_SP]     = values[tc];
  sase_regs[REG_SP]     = symbolic_values[tc];
  sase_regs_typ[REG_SP] = CONCRETE_T;

  tc--;
  registers[REG_FP]     = values[tc];
  sase_regs[REG_FP]     = symbolic_values[tc];
  sase_regs_typ[REG_FP] = CONCRETE_T;

  tc--;
  registers[vaddrs[tc]]     = values[tc];
  sase_regs[vaddrs[tc]]     = symbolic_values[tc];
  sase_regs_typ[vaddrs[tc]] = CONCRETE_T;
}

uint64_t check_conditional_type_eq_or_deq() {
  uint64_t saved_pc = pc;
  uint64_t op_code;
  uint64_t funct_3;

  pc = saved_pc + INSTRUCTIONSIZE;
  fetch();
  op_code = get_opcode(ir);
  funct_3 = get_funct3(ir);
  if (op_code == OP_IMM && funct_3 == F3_ADDI) {
    pc = saved_pc;
    return 1; // EQ;
  } else if (op_code == OP_OP && funct_3 == F3_SLTU) {
    pc = saved_pc;
    return 2; // DEQ;
  } else {
    printf("OUTPUT: XOR instruction is incorrectly used at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  return 0;
}

// ********************** engine instructions ************************

void sase_lui() {
  if (rd != REG_ZR) {
    if (imm < two_to_the_power_of_32)
      sase_regs[rd] = boolector_sll(btor, boolector_unsigned_int(btor, imm, bv_sort), twelve_bv);
    else
      sase_regs[rd] = boolector_unsigned_int_64(imm << 12);

    sase_regs_typ[rd] = CONCRETE_T;
  }
}

void sase_addi() {
  if (rd != REG_ZR) {
    sase_regs_typ[rd] = sase_regs_typ[rs1];

    if (sase_regs_typ[rd] == CONCRETE_T && is_system_register(rs1)) {
      sase_regs[rd] = (BoolectorNode*) 0;
    } else {
      if (imm == 8) {
        sase_regs[rd] = boolector_add(btor, sase_regs[rs1], eight_bv);
      } else if (imm == 0) {
        sase_regs[rd] = sase_regs[rs1];
      } else if (imm == minus_eight) {
        sase_regs[rd] = boolector_add(btor, sase_regs[rs1], meight_bv);
      } else if (imm == 1) {
        sase_regs[rd] = boolector_add(btor, sase_regs[rs1], one_bv);
      } else {
        if (imm < two_to_the_power_of_32) {
          sase_regs[rd] = boolector_add(btor, sase_regs[rs1], boolector_unsigned_int(btor, imm, bv_sort));
        } else {
          sase_regs[rd] = boolector_add(btor, sase_regs[rs1], boolector_unsigned_int_64(imm));
        }
      }
    }
  }
}

void sase_add() {
  if (rd != REG_ZR) {
    sase_regs_typ[rd] = sase_regs_typ[rs1] | sase_regs_typ[rs2];

    if (sase_regs_typ[rd] == CONCRETE_T && is_system_register(rs1)) {
      sase_regs[rd] = (BoolectorNode*) 0;
    } else {
      sase_regs[rd] = boolector_add(btor, sase_regs[rs1], sase_regs[rs2]);
    }
  }
}

void sase_sub() {
  if (rd != REG_ZR) {
    sase_regs[rd] = boolector_sub(btor, sase_regs[rs1], sase_regs[rs2]);

    sase_regs_typ[rd] = sase_regs_typ[rs1] | sase_regs_typ[rs2];
  }
}

void sase_mul() {
  if (rd != REG_ZR) {
    sase_regs[rd] = boolector_mul(btor, sase_regs[rs1], sase_regs[rs2]);

    sase_regs_typ[rd] = sase_regs_typ[rs1] | sase_regs_typ[rs2];
  }
}

void sase_divu() {
  // check if divisor is zero?
  boolector_push(btor, 1);
  boolector_assert(btor, boolector_eq(btor, sase_regs[rs2], zero_bv));
  if (boolector_sat(btor) == BOOLECTOR_SAT) {
    printf("OUTPUT: SE division by zero! at pc %llx \n", pc - entry_point);
    printf("backtracking: %llu \n", b);
    boolector_print_model (btor, "smt2", stdout);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
  boolector_pop(btor, 1);

  // divu semantics
  if (rd != REG_ZR) {
    sase_regs[rd] = boolector_udiv(btor, sase_regs[rs1], sase_regs[rs2]);

    sase_regs_typ[rd] = sase_regs_typ[rs1] | sase_regs_typ[rs2];
  }
}

void sase_remu() {
  // check if divisor is zero?
  boolector_push(btor, 1);
  boolector_assert(btor, boolector_eq(btor, sase_regs[rs2], zero_bv));
  if (boolector_sat (btor) == BOOLECTOR_SAT) {
    printf("OUTPUT: SE division by zero! at pc %llx \n", pc - entry_point);
    printf("backtracking: %llu \n", b);
    boolector_print_model (btor, "smt2", stdout);
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
  boolector_pop(btor, 1);

  // remu semantics
  if (rd != REG_ZR) {
    sase_regs[rd] = boolector_urem(btor, sase_regs[rs1], sase_regs[rs2]);

    sase_regs_typ[rd] = sase_regs_typ[rs1] | sase_regs_typ[rs2];
  }
}

void sase_xor() {
  bool true_branch_reachable  = false;
  bool false_branch_reachable = false;
  BoolectorNode* true_branch_expr;

  ic_xor = ic_xor + 1;

  if (rd != REG_ZR) {
    // concrete semantics
    if (sase_regs_typ[rs1] == CONCRETE_T && sase_regs_typ[rs2] == CONCRETE_T) {
      if (registers[rs1] ^ registers[rs2]) {
        registers[rd] = 1;
        sase_regs[rd] = one_bv;
      } else {
        registers[rd] = 0;
        sase_regs[rd] = zero_bv;
      }

      sase_regs_typ[rd] = CONCRETE_T;
      pc = pc + INSTRUCTIONSIZE;
      return;
    }

    if (check_conditional_type_eq_or_deq() == 1) {
      sase_false_branchs[sase_tc] = boolector_ne(btor, sase_regs[rs1], sase_regs[rs2]);
      false_branch_reachable      = check_branch_satisfiability(sase_false_branchs[sase_tc]);

      true_branch_expr            = boolector_eq(btor, sase_regs[rs1], sase_regs[rs2]);
      true_branch_reachable       = check_branch_satisfiability(true_branch_expr);

      if (true_branch_reachable) {
        if (false_branch_reachable) {
          // save state on trace for later false evaluation
          sase_pcs[sase_tc]              = pc  + INSTRUCTIONSIZE;
          sase_program_brks[sase_tc]     = get_program_break(current_context);
          sase_read_trace_ptrs[sase_tc]  = read_tc_current;
          sase_input_trace_ptrs[sase_tc] = input_cnt_current;
          sase_store_trace_ptrs[sase_tc] = mrif;
          mrif = tc;
          store_registers(1); // after mrif =
          sase_tc++;

          // continue with true branch
          boolector_push(btor, 1);
          boolector_assert(btor, true_branch_expr);
          registers[rd]     = 0;
          sase_regs[rd]     = zero_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        } else {
          // continue with true branch
          registers[rd]     = 0;
          sase_regs[rd]     = zero_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        }
      } else if (false_branch_reachable) {
        // continue with false branch
        registers[rd]     = 1;
        sase_regs[rd]     = one_bv;
        sase_regs_typ[rd] = CONCRETE_T;
      } else {
        printf("%s\n", "unreachable branch both true and false!");
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

    } else {
      sase_false_branchs[sase_tc] = boolector_eq(btor, sase_regs[rs1], sase_regs[rs2]);
      false_branch_reachable      = check_branch_satisfiability(sase_false_branchs[sase_tc]);

      true_branch_expr            = boolector_ne(btor, sase_regs[rs1], sase_regs[rs2]);
      true_branch_reachable       = check_branch_satisfiability(true_branch_expr);

      if (true_branch_reachable) {
        if (false_branch_reachable) {
          // save state on trace for later false evaluation
          sase_pcs[sase_tc]              = pc  + INSTRUCTIONSIZE;
          sase_program_brks[sase_tc]     = get_program_break(current_context);
          sase_read_trace_ptrs[sase_tc]  = read_tc_current;
          sase_input_trace_ptrs[sase_tc] = input_cnt_current;
          sase_store_trace_ptrs[sase_tc] = mrif;
          mrif = tc;
          store_registers(0); // after mrif =
          sase_tc++;

          // continue with true branch
          boolector_push(btor, 1);
          boolector_assert(btor, true_branch_expr);
          registers[rd]     = 1;
          sase_regs[rd]     = one_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        } else {
          // continue with true branch
          registers[rd]     = 1;
          sase_regs[rd]     = one_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        }
      } else if (false_branch_reachable) {
        // continue with false branch
        registers[rd]     = 0;
        sase_regs[rd]     = zero_bv;
        sase_regs_typ[rd] = CONCRETE_T;
      } else {
        printf("%s\n", "unreachable branch both true and false!");
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    pc = pc + INSTRUCTIONSIZE;
  }
}

// uint64_t satisfiability_check = 0;
// uint64_t satisfiability_step  = 0;

void sase_sltu() {
  bool true_branch_reachable  = false;
  bool false_branch_reachable = false;
  BoolectorNode* true_branch_expr;

  ic_sltu = ic_sltu + 1;

  if (rd != REG_ZR) {
    // concrete semantics
    if (sase_regs_typ[rs1] == CONCRETE_T && sase_regs_typ[rs2] == CONCRETE_T) {
      if (registers[rs1] < registers[rs2]) {
        registers[rd] = 1;
        sase_regs[rd] = one_bv;
      } else {
        registers[rd] = 0;
        sase_regs[rd] = zero_bv;
      }

      sase_regs_typ[rd] = CONCRETE_T;
      pc = pc + INSTRUCTIONSIZE;
      return;
    }

    if (check_conditional_type_lte_or_gte_() == 2) {
      sase_false_branchs[sase_tc] = boolector_ult(btor, sase_regs[rs1], sase_regs[rs2]);
      false_branch_reachable      = check_branch_satisfiability(sase_false_branchs[sase_tc]);

      true_branch_expr            = boolector_ugte(btor, sase_regs[rs1], sase_regs[rs2]);
      true_branch_reachable       = check_branch_satisfiability(true_branch_expr);

      if (true_branch_reachable) {
        if (false_branch_reachable) {
          // save state on trace for later false evaluation
          sase_pcs[sase_tc]              = pc  + INSTRUCTIONSIZE;
          sase_program_brks[sase_tc]     = get_program_break(current_context);
          sase_read_trace_ptrs[sase_tc]  = read_tc_current;
          sase_input_trace_ptrs[sase_tc] = input_cnt_current;
          sase_store_trace_ptrs[sase_tc] = mrif;
          mrif = tc;
          store_registers(1); // after mrif =
          sase_tc++;

          // continue with true branch
          boolector_push(btor, 1);
          boolector_assert(btor, true_branch_expr);
          registers[rd]     = 0;
          sase_regs[rd]     = zero_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        } else {
          // continue with true branch
          registers[rd]     = 0;
          sase_regs[rd]     = zero_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        }
      } else if (false_branch_reachable) {
        // continue with false branch
        registers[rd]     = 1;
        sase_regs[rd]     = one_bv;
        sase_regs_typ[rd] = CONCRETE_T;
      } else {
        printf("%s\n", "unreachable branch both true and false!");
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

    } else {
      sase_false_branchs[sase_tc] = boolector_ugte(btor, sase_regs[rs1], sase_regs[rs2]);
      false_branch_reachable      = check_branch_satisfiability(sase_false_branchs[sase_tc]);

      true_branch_expr            = boolector_ult(btor, sase_regs[rs1], sase_regs[rs2]);
      true_branch_reachable       = check_branch_satisfiability(true_branch_expr);

      if (true_branch_reachable) {
        if (false_branch_reachable) {
          // save state on trace for later false evaluation
          sase_pcs[sase_tc]              = pc  + INSTRUCTIONSIZE;
          sase_program_brks[sase_tc]     = get_program_break(current_context);
          sase_read_trace_ptrs[sase_tc]  = read_tc_current;
          sase_input_trace_ptrs[sase_tc] = input_cnt_current;
          sase_store_trace_ptrs[sase_tc] = mrif;
          mrif = tc;
          store_registers(0); // after mrif =
          sase_tc++;

          // continue with true branch
          boolector_push(btor, 1);
          boolector_assert(btor, true_branch_expr);
          registers[rd]     = 1;
          sase_regs[rd]     = one_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        } else {
          // continue with true branch
          registers[rd]     = 1;
          sase_regs[rd]     = one_bv;
          sase_regs_typ[rd] = CONCRETE_T;
        }
      } else if (false_branch_reachable) {
        // continue with false branch
        registers[rd]     = 0;
        sase_regs[rd]     = zero_bv;
        sase_regs_typ[rd] = CONCRETE_T;
      } else {
        printf("%s\n", "unreachable branch both true and false!");
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    pc = pc + INSTRUCTIONSIZE;
  }
}

void sase_backtrack_trace() {
  sase_tc--;
  pc                = sase_pcs[sase_tc];
  read_tc_current   = sase_read_trace_ptrs[sase_tc];
  input_cnt_current = sase_input_trace_ptrs[sase_tc];
  set_program_break(current_context, sase_program_brks[sase_tc]);
  backtrack_branch_stores(); // before mrif =
  mrif = sase_store_trace_ptrs[sase_tc];

  // moved to phantom
  // boolector_pop(btor, 1);
  // boolector_assert(btor, sase_false_branchs[sase_tc]);
}

void sase_ld() {
  uint64_t mrv;
  uint64_t vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (rd != REG_ZR) {
        mrv = load_symbolic_memory(pt, vaddr);

        // if (mrv == 0)
        //   printf("OUTPUT: uninitialize memory address %llu at pc %x\n", vaddr, pc - entry_point);

        sase_regs_typ[rd] = *(is_symbolics    + mrv);
        sase_regs[rd]     = *(symbolic_values + mrv);
        registers[rd]     = *(values          + mrv);

        pc = pc + INSTRUCTIONSIZE;
        ic_ld = ic_ld + 1;
      }
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void sase_sd() {
  uint64_t vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_virtual_address_mapped(pt, vaddr)) {

      sase_store_memory(pt, vaddr, sase_regs_typ[rs2], *(registers + rs2), sase_regs[rs2]);

      pc = pc + INSTRUCTIONSIZE;
      ic_sd = ic_sd + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void sase_jal_jalr() {
  if (rd != REG_ZR) {
    // assert: *(registers + rd) < 2^32
    sase_regs[rd] = (BoolectorNode*) 0; // (registers[rd] < two_to_the_power_of_32) ? boolector_unsigned_int(btor, registers[rd], bv_sort) : boolector_unsigned_int_64(registers[rd]);

    sase_regs_typ[rd] = CONCRETE_T;
  }
}

void sase_store_memory(uint64_t* pt, uint64_t vaddr, uint8_t is_symbolic, uint64_t value, BoolectorNode* sym_value) {
  uint64_t mrv;

  mrv = load_symbolic_memory(pt, vaddr);

  if (mrv != 0)
    if (is_symbolic == *(is_symbolics + mrv))
      if (value == *(values + mrv))
        if (sym_value == *(symbolic_values + mrv))
          return;

  if (mrif < mrv && vaddr != read_buffer) {
    *(is_symbolics    + mrv) = is_symbolic;
    *(values          + mrv) = value;
    *(symbolic_values + mrv) = sym_value;
  } else if (sase_is_trace_space_available()) {
    tc++;

    *(tcs             + tc) = mrv;
    *(is_symbolics    + tc) = is_symbolic;
    *(values          + tc) = value;
    *(symbolic_values + tc) = sym_value;
    *(vaddrs          + tc) = vaddr;

    store_virtual_memory(pt, vaddr, tc);
  } else
    throw_exception(EXCEPTION_MAXTRACE, 0);
}

void backtrack_branch_stores() {
  while (mrif < tc) {
    if (vaddrs[tc] < NUMBEROFREGISTERS) {
      restore_registers();
    } else {
      store_virtual_memory(pt, vaddrs[tc], tcs[tc]);
    }
    tc--;
  }
}

// --------------------------- conditional expression --------------------------

bool match_addi_instruction_() {
  uint64_t rs1_;
  uint64_t rd_;
  uint64_t funct3_;
  uint64_t imm_;

  rs1_    = get_rs1(ir);
  rd_     = get_rd(ir);
  funct3_ = get_funct3(ir);
  imm_    = get_immediate_i_format(ir);

  if (funct3_ == F3_ADDI) {
    if (imm_ == 1)
      if (rs1_ == REG_ZR)
        if (rd_ != rd)
          return true;
  }

  return false;
}

bool match_sub_instruction_(uint64_t prev_instr_rd) {
  uint64_t rs1_;
  uint64_t rs2_;
  uint64_t rd_;
  uint64_t funct3_;
  uint64_t funct7_;

  funct7_ = get_funct7(ir);
  funct3_ = get_funct3(ir);
  rs1_    = get_rs1(ir);
  rs2_    = get_rs2(ir);
  rd_     = get_rd(ir);

  if (funct3_ == F3_ADD) {
    if (funct7_ == F7_SUB)
      if (rs1_ == prev_instr_rd)
        if (rs2_ == rd)
          if (rd_ == rs2_)
            return true;
  }

  return false;
}

uint64_t check_conditional_type_lte_or_gte_() {
  uint64_t saved_pc = pc;

  pc = saved_pc + INSTRUCTIONSIZE;
  fetch();
  if (get_opcode(ir) == OP_IMM && match_addi_instruction_()) {
    uint64_t rd_ = get_rd(ir);
    pc = saved_pc + 2 * INSTRUCTIONSIZE;
    fetch();
    if (get_opcode(ir) == OP_OP && match_sub_instruction_(rd_)) {
      pc = saved_pc;
      return 2;
    }
  }

  pc = saved_pc;
  return 1;
}