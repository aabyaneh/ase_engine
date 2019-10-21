#include "pse.h"

// -----------------------------------------------------------------
// ---------------- Solver Aided Symbolic Execution ----------------
// -----------------------------------------------------------------

uint64_t  b             = 0; // counting total number of backtracking
uint64_t  SASE          = 8; // Solver Aided Symbolic Execution
uint8_t   CONCRETE_T    = 0; // concrete value type
uint8_t   SYMBOLIC_T    = 1; // symbolic value type

// engine trace
uint64_t  sase_trace_size = 1000000;
uint64_t  sase_tc         = 0;    // trace counter
uint64_t* sase_pcs;
uint64_t* sase_read_trace_ptrs;   // pointers to read trace
uint64_t* sase_program_brks;      // keep track of program_break
uint64_t* sase_store_trace_ptrs;  // pointers to store trace
uint64_t* sase_rds;
uint64_t  mrif            = 0;    // most recent conditional expression

// store trace
// uint64_t  tc;
// uint64_t* tcs;
// uint64_t* vaddrs;
// uint64_t* values;
uint8_t*  is_symbolics;
uint64_t* symbolic_values;

// read trace
uint64_t* concrete_reads;
uint64_t* constrained_reads;
uint64_t  read_tc         = 1;
uint64_t  read_tc_current = 1;
uint64_t  read_buffer     = 0;

// input trace
uint64_t* constrained_inputs;
uint64_t* sase_input_trace_ptrs;
uint64_t  input_cnt         = 1;
uint64_t  input_cnt_current = 1;

uint64_t check_conditional_type_lte_or_gte_();
void generate_path_condition_();

// ---------------------------------------------
// --------------- pse (probabilistic symbolic execution)
// ---------------------------------------------

// struct node {
//   uint8_t  type;
//   uint64_t left_node;
//   uint64_t right_node;
// };

uint8_t* pse_regs_typ;  // CONCRETE_T or SYMBOLIC_T
double   current_path_probability = 1;
double   threshold                = 0.00000000000000000001;
std::vector<double> false_branches_reachability;


bool pse_sat(bool is_branch_sat_check) {
  // --------------
  // generate query and write in output
  // --------------
  generate_path_condition_();
  path_condition_string.pop_back();
  std::ofstream output_query;
  output_query.open("query.txt", std::ofstream::trunc);
  output_query << ":Variables:\n\n";
  for (size_t i = 0; i < pse_variables_per_path.size(); i++) {
    output_query << pse_variables_per_path[i] << "\n";
  }
  output_query << "\n:Constraints:\n\n";
  output_query << path_condition_string << "\n";
  output_query.close();

  // --------------
  // run qCoral
  // --------------
  char buffer[128];
  std::string command = "cd /Users/arsa/Desktop/tools/qcoral_modified/; ./run_qcoral.sh --mcIterativeImprovement --mcTargetVariance 1E-10 --mcMaxSamples 1 --mcInitialPartitionBudget 1000000 /minterval/query.txt";
  std::string result = "";
  FILE* pipe = popen(command.c_str(), "r");
  if (!pipe) {
    printf("OUTPUT: popen failed!\n");
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
  while (!feof(pipe)) {
    if (fgets(buffer, 128, pipe) != NULL)
      result += buffer;
  }
  pclose(pipe);

  // --------------
  // process output
  // --------------
  size_t found = result.rfind("[qCORAL:results]");
  if (found == std::string::npos) {
    printf("OUTPUT: no [qCORAL:results] found!\n");
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
  std::string time_str, variance_str, mean_str;
  double time, variance, mean;
  found = result.rfind("time"); found = found + 5;
  while (result[found] != ',') {
    time_str.push_back(result[found]);
    found++;
  }
  time = std::stod(time_str);

  found = result.rfind("variance"); found = found + 9;
  while (result[found] != ',') {
    variance_str.push_back(result[found]);
    found++;
  }
  variance = std::stod(variance_str);

  found = result.rfind("mean"); found = found + 5;
  while (result[found] != ',') {
    mean_str.push_back(result[found]);
    found++;
  }
  mean = std::stod(mean_str);
  std::cout << mean << '\n';

  // --------------
  // apply branch probabilities
  // --------------
  if (variance <= 0.00001) {
    if (mean > 1)
      mean = 1;

    if (mean < threshold) {
      if (is_branch_sat_check) {
        false_branches_reachability.push_back(current_path_probability);
        current_path_probability = 0;
      }
      return false;
    } else if (1 - mean < threshold) {
      if (is_branch_sat_check) {
        false_branches_reachability.push_back(0);
        current_path_probability = 1;
      }
      return true;
    } else {
      if (is_branch_sat_check) {
        if (mean > current_path_probability)
          mean = current_path_probability;
        double false_branch_conditional_prob = 1 - (mean / current_path_probability);
        false_branches_reachability.push_back(false_branch_conditional_prob * current_path_probability);
        std::cout << (false_branch_conditional_prob * current_path_probability) << ", ";
        std::cout << false_branch_conditional_prob << " " << current_path_probability << '\n';
        current_path_probability = mean;
      }
      return true;
    }
  } else {
    printf("OUTPUT: variance accuracy!\n");
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

// ********************** engine functions ************************

void init_sase() {
  MAX_NODE_TRACE_LENGTH = 2 * sase_trace_size;
  pse_ast_nodes        = (struct node*) malloc(MAX_NODE_TRACE_LENGTH * sizeof(struct node*));
  reg_pse_ast          = (uint64_t*)    malloc(NUMBEROFREGISTERS     * sizeof(uint64_t));
  pse_regs_typ         = (uint8_t*)     malloc(sizeof(uint8_t)       * NUMBEROFREGISTERS);
  zero_node            = pse_operation(CONST, 0, 0);
  one_node             = pse_operation(CONST, 0, 1);
  reg_pse_ast[REG_ZR]  = zero_node;
  reg_pse_ast[REG_FP]  = zero_node;
  false_branches.reserve(sase_trace_size);
  path_condition.reserve(sase_trace_size);
  path_condition_string.reserve(sase_trace_size);
  traversed_path_condition_elements.reserve(sase_trace_size);

  for (size_t i = 0; i < NUMBEROFREGISTERS; i++) {
    pse_regs_typ[i] = CONCRETE_T;
  }
  reg_pse_ast[REG_ZR] = zero_node;
  reg_pse_ast[REG_FP] = zero_node;

  sase_pcs              = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  sase_read_trace_ptrs  = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  sase_program_brks     = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  sase_store_trace_ptrs = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  sase_rds              = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);

  tcs                   = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  vaddrs                = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  values                = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  is_symbolics          = (uint8_t*)  malloc(sizeof(uint8_t)  * sase_trace_size);
  symbolic_values       = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);

  concrete_reads        = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  constrained_reads     = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);

  constrained_inputs    = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);
  sase_input_trace_ptrs = (uint64_t*) malloc(sizeof(uint64_t) * sase_trace_size);

  // initialization
  tc               = 0;
  *tcs             = 0;
  *vaddrs          = 0;
  *values          = 0;
  *is_symbolics    = CONCRETE_T;
  *symbolic_values = zero_node;
}

uint64_t sase_is_trace_space_available() {
  return tc + 1 < sase_trace_size;
}

void store_registers_fp_sp_rd() {
  if (tc + 2 >= sase_trace_size)
    throw_exception(EXCEPTION_MAXTRACE, 0);

  tc++;
  *(tcs             + tc) = 0;
  *(is_symbolics    + tc) = 0;
  *(values          + tc) = registers[REG_FP];
  *(symbolic_values + tc) = reg_pse_ast[REG_FP];
  *(vaddrs + tc)          = 1 - registers[rd];

  tc++;
  *(tcs             + tc) = 0;
  *(is_symbolics    + tc) = 0;
  *(values          + tc) = registers[REG_SP];
  *(symbolic_values + tc) = reg_pse_ast[REG_SP];
  *(vaddrs + tc)          = rd;
}

void restore_registers_fp_sp_rd(uint64_t tr_cnt, uint64_t rd_reg) {
  registers[REG_SP]    = values[tr_cnt];
  reg_pse_ast[REG_SP]  = symbolic_values[tr_cnt];
  pse_regs_typ[REG_SP] = CONCRETE_T;
  tr_cnt--;
  tc--;
  registers[REG_FP]    = values[tr_cnt];
  reg_pse_ast[REG_FP]  = symbolic_values[tr_cnt];
  pse_regs_typ[REG_FP] = CONCRETE_T;

  registers[rd_reg]     = vaddrs[tc];
  reg_pse_ast[rd_reg]   = (registers[rd_reg] == 1) ? one_node : zero_node;
  pse_regs_typ[rd_reg]  = CONCRETE_T;
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
    pse_regs_typ[rd] = CONCRETE_T;

    reg_pse_ast[rd]  = pse_operation(CONST, 0, imm << 12);
  }
}

void sase_addi() {
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = pse_regs_typ[rs1];

    if (pse_regs_typ[rd]) {
      reg_pse_ast[rd] = pse_operation(ADDI, reg_pse_ast[rs1] , pse_operation(CONST, 0, imm));
    } else {
      reg_pse_ast[rd] = pse_operation(CONST, 0, registers[rd]);
    }
  }
}

void sase_add() {
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = pse_regs_typ[rs1] | pse_regs_typ[rs2];

    if (pse_regs_typ[rd]) {
      reg_pse_ast[rd] = pse_operation(ADD, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
    } else {
      reg_pse_ast[rd] = pse_operation(CONST, 0, registers[rd]);
    }
  }
}

void sase_sub() {
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = pse_regs_typ[rs1] | pse_regs_typ[rs2];

    if (pse_regs_typ[rd]) {
      reg_pse_ast[rd] = pse_operation(SUB, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
    } else {
      reg_pse_ast[rd] = pse_operation(CONST, 0, registers[rd]);
    }
  }
}

void sase_mul() {
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = pse_regs_typ[rs1] | pse_regs_typ[rs2];

    if (pse_regs_typ[rd]) {
      reg_pse_ast[rd] = pse_operation(MUL, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
    } else {
      reg_pse_ast[rd] = pse_operation(CONST, 0, registers[rd]);
    }
  }
}

void sase_divu() {
  // divu semantics
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = pse_regs_typ[rs1] | pse_regs_typ[rs2];

    if (pse_regs_typ[rd]) {
      // check if divisor is zero?
      path_condition.push_back(pse_operation(IEQ, reg_pse_ast[rs2], zero_node));
      if (pse_sat(false) == true) {
        printf("OUTPUT: SE division by zero! at pc %llx \n", pc - entry_point);
        printf("backtracking: %llu \n", b);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
      path_condition.pop_back();
      traversed_path_condition_elements.pop_back();
      tree_tc--;

      reg_pse_ast[rd] = pse_operation(DIVU, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
    } else {
      reg_pse_ast[rd] = pse_operation(CONST, 0, registers[rd]);
    }
  }
}

void sase_remu() {
  // remu semantics
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = pse_regs_typ[rs1] | pse_regs_typ[rs2];

    if (pse_regs_typ[rd]) {
      // check if divisor is zero?
      path_condition.push_back(pse_operation(IEQ, reg_pse_ast[rs2], zero_node));
      if (pse_sat(false) == true) {
        printf("OUTPUT: SE division by zero! at pc %llx \n", pc - entry_point);
        printf("backtracking: %llu \n", b);
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
      path_condition.pop_back();
      traversed_path_condition_elements.pop_back();
      tree_tc--;

      reg_pse_ast[rd] = pse_operation(REMU, reg_pse_ast[rs1], reg_pse_ast[rs2]);
    } else {
      reg_pse_ast[rd] = pse_operation(CONST, 0, registers[rd]);
    }
  }
}

void sase_xor() {
  ic_xor = ic_xor + 1;

  if (rd != REG_ZR) {
    // concrete semantics
    if (pse_regs_typ[rs1] == CONCRETE_T && pse_regs_typ[rs2] == CONCRETE_T) {
      if (registers[rs1] ^ registers[rs2]) {
        registers[rd]   = 1;
        reg_pse_ast[rd] = one_node;
      } else {
        registers[rd]   = 0;
        reg_pse_ast[rd] = zero_node;
      }

      pse_regs_typ[rd] = CONCRETE_T;
      pc = pc + INSTRUCTIONSIZE;
      return;
    }

    if (check_conditional_type_eq_or_deq() == 1) {
      false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));

      registers[rd] = 0;
    } else {
      false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));

      registers[rd] = 1;
    }

    sase_pcs[sase_tc] = pc + INSTRUCTIONSIZE;
    pc                = pc + INSTRUCTIONSIZE;

    // symbolic semantics
    sase_program_brks[sase_tc]     = get_program_break(current_context);
    sase_read_trace_ptrs[sase_tc]  = read_tc_current;
    sase_input_trace_ptrs[sase_tc] = input_cnt_current;
    sase_store_trace_ptrs[sase_tc] = mrif;
    mrif = tc;
    store_registers_fp_sp_rd(); // after mrif =
    sase_tc++;

    if (pse_sat(true) == true) {
      reg_pse_ast[rd]  = (registers[rd] == 1) ? one_node : zero_node;
      pse_regs_typ[rd] = CONCRETE_T;
    } else {
      // printf("%s\n", "unreachable branch true!");
      sase_backtrack_sltu(1);
    }
  }
}

void sase_sltu() {
  uint8_t  is_branch;
  uint64_t op;
  uint64_t saved_pc;

  ic_sltu = ic_sltu + 1;

  if (rd != REG_ZR) {
    // concrete semantics
    if (pse_regs_typ[rs1] == CONCRETE_T && pse_regs_typ[rs2] == CONCRETE_T) {
      registers[rd]    = (registers[rs1] < registers[rs2]) ? 1 : 0;
      reg_pse_ast[rd]  = (registers[rd] == 0) ? zero_node : one_node;
      pse_regs_typ[rd] = CONCRETE_T;

      pc = pc + INSTRUCTIONSIZE;
      return;
    }

    if (check_conditional_type_lte_or_gte_() == 2) {
      false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));

      registers[rd] = 0;
    } else {
      false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));

      registers[rd] = 1;
    }

    sase_pcs[sase_tc] = pc + INSTRUCTIONSIZE;
    pc                = pc + INSTRUCTIONSIZE;

    // symbolic semantics
    sase_program_brks[sase_tc]     = get_program_break(current_context);
    sase_read_trace_ptrs[sase_tc]  = read_tc_current;
    sase_input_trace_ptrs[sase_tc] = input_cnt_current;
    sase_store_trace_ptrs[sase_tc] = mrif;
    mrif = tc;
    store_registers_fp_sp_rd(); // after mrif =
    sase_tc++;

    if (pse_sat(true) == true) {
      reg_pse_ast[rd]  = (registers[rd] == 1) ? one_node : zero_node;
      pse_regs_typ[rd] = CONCRETE_T;
    } else {
      // printf("%s\n", "unreachable branch true!");
      sase_backtrack_sltu(1);
    }

  }
}

void sase_backtrack_sltu(int is_true_branch_unreachable) {
  if (sase_tc == 0) {
    // printf("pc: %llx, read_tc: %llu, arg: %d\n", pc - entry_point, read_tc, is_true_branch_unreachable);
    pc = 0;
    return;
  }

  sase_tc--;
  pc                = sase_pcs[sase_tc];
  read_tc_current   = sase_read_trace_ptrs[sase_tc];
  input_cnt_current = sase_input_trace_ptrs[sase_tc];
  set_program_break(current_context, sase_program_brks[sase_tc]);
  backtrack_branch_stores(); // before mrif =
  mrif = sase_store_trace_ptrs[sase_tc];

  while (false_branches.back() < path_condition.back()) {
    path_condition.pop_back();
    if (traversed_path_condition_elements.size() > path_condition.size()) traversed_path_condition_elements.pop_back();
  }
  tree_tc = false_branches.back();
  path_condition.push_back(false_branches.back());
  false_branches.pop_back();

  double false_branch_prob = false_branches_reachability.back();
  false_branches_reachability.pop_back();

  if (false_branch_prob < threshold) {
    if (is_true_branch_unreachable) {
      printf("%s\n", "unreachable branch both true and false!");
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    } else {
      // printf("%s %llu\n", "unreachable branch false!", pc);
      sase_backtrack_sltu(0);
    }
  } else {
    // reachable
    current_path_probability = false_branch_prob;
  }
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

        pse_regs_typ[rd]  = *(is_symbolics    + mrv);
        reg_pse_ast[rd]   = *(symbolic_values + mrv);
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

      sase_store_memory(pt, vaddr, pse_regs_typ[rs2], registers[rs2], reg_pse_ast[rs2]);

      pc = pc + INSTRUCTIONSIZE;
      ic_sd = ic_sd + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void sase_jal_jalr() {
  if (rd != REG_ZR) {
    pse_regs_typ[rd] = CONCRETE_T;
  }
}

void sase_store_memory(uint64_t* pt, uint64_t vaddr, uint8_t is_symbolic, uint64_t value, uint64_t sym_value) {
  uint64_t mrv;

  mrv = load_symbolic_memory(pt, vaddr);

  if (mrv != 0)
    if (is_symbolic == is_symbolics[mrv])
      if (value == values[mrv])
        if (sym_value == symbolic_values[mrv])
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
      restore_registers_fp_sp_rd(tc, vaddrs[tc]);
    } else {
      if (symbolic_values[tc] && tree_tc > symbolic_values[tc]) tree_tc = symbolic_values[tc];
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

// ------------------------------ path condition -------------------------------

void decode_operation_(uint64_t node_tc) {
  switch (pse_ast_nodes[node_tc].type) {
    case 2:
      path_condition_string += "ADD(";
      break;
    case 3:
      path_condition_string += "ADD(";
      break;
    case 4:
      path_condition_string += "SUB(";
      break;
    case 5:
      path_condition_string += "MUL(";
      break;
    case 6:
      path_condition_string += "DIV(";
      break;
    case 7:
      path_condition_string += "REM(";
      break;
    case 8:
      path_condition_string += "ILT(";
      break;
    case 9:
      path_condition_string += "IGE(";
      break;
    case 10:
      path_condition_string += "IEQ(";
      break;
    case 11:
      path_condition_string += "INE(";
      break;
  }
}

void decode_var_(uint64_t node_tc) {
  path_condition_string = path_condition_string + "IVAR(ID_" + std::to_string(pse_ast_nodes[node_tc].right_node) + ")";
}

void decode_const_(uint64_t node_tc) {
  path_condition_string = path_condition_string + "ICONST(" + std::to_string(pse_ast_nodes[node_tc].right_node) + ")";
}

bool node_decoder_(uint64_t node_tc) {
  switch (pse_ast_nodes[node_tc].type) {
    case 0:
      decode_const_(node_tc);
      return true;
    case 1:
      decode_var_(node_tc);
      return true;
    default:
      decode_operation_(node_tc);
      return false;
  }
}

void path_condition_traverse_(uint64_t node_tc) {
  if (node_decoder_(node_tc))
    return;

  path_condition_traverse_(pse_ast_nodes[node_tc].left_node);
  path_condition_string += ",";
  path_condition_traverse_(pse_ast_nodes[node_tc].right_node);
  path_condition_string += ")";
}

void generate_path_condition_() {
  path_condition_string.clear();
  for (size_t i = 0; i < path_condition.size(); i++) {
    if (traversed_path_condition_elements.size() <= i) {
      // not yet traversed
      size_t end = path_condition_string.size();

      path_condition_traverse_(path_condition[i]); // node_tc
      path_condition_string += ";";

      traversed_path_condition_elements.push_back("");
      traversed_path_condition_elements[i].append(path_condition_string, end, path_condition_string.size() - end);
    } else {
      // already traversed
      path_condition_string += traversed_path_condition_elements[i];
    }
  }
}