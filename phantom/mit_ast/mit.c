#include "mit.h"

typedef unsigned __int128 uint128_t;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t MIT                  = 9;        // symbolic execution with modular interval theory as backend
uint64_t MAX_TRACE_LENGTH     = 5000000;
uint64_t MAX_NUM_OF_INTERVALS = 2001;
uint64_t MAX_NUM_OF_OP_VADDRS = 100;

uint128_t UINT64_MAX_VALUE    = 18446744073709551615U;
uint128_t TWO_TO_THE_POWER_OF_64;

// ---------------------------------------------
// --------------- the memory trace
// ---------------------------------------------

uint64_t  tc              = 0;             // trace counter
uint64_t* pcs             = (uint64_t*) 0; // trace of program counter values
uint64_t* tcs             = (uint64_t*) 0; // trace of trace counters to previous values
uint64_t* vaddrs          = (uint64_t*) 0; // trace of virtual addresses
uint64_t* values          = (uint64_t*) 0; // trace of values
uint32_t* data_types      = (uint32_t*) 0; // memory range (or) value interval
uint64_t* asts            = (uint64_t*) 0;
uint64_t* mr_sds          = (uint64_t*) 0; // the tc of most recent store to a memory address

uint32_t  VALUE_T         = 0;
uint32_t  POINTER_T       = 1;
uint32_t  INPUT_T         = 2;

// ---------------------------------------------
// --------------- read trace
// ---------------------------------------------

uint64_t  rc          = 0;              // read counter
uint64_t* read_values = (uint64_t*) 0;
uint64_t* read_los    = (uint64_t*) 0;
uint64_t* read_ups    = (uint64_t*) 0;

// ---------------------------------------------
// --------------- registers
// ---------------------------------------------

std::vector<std::vector<uint64_t> > reg_mintervals_los(NUMBEROFREGISTERS);
std::vector<std::vector<uint64_t> > reg_mintervals_ups(NUMBEROFREGISTERS);
uint32_t* reg_mintervals_cnts = (uint32_t*) 0;
uint64_t* reg_steps           = (uint64_t*) 0; // incrementing step of the register's value interval
uint32_t* reg_data_type       = (uint32_t*) 0; // memory range or value integer interval
uint32_t* reg_symb_type       = (uint32_t*) 0; // CONCRETE (or) SYMBOLIC
uint64_t* reg_asts;
uint32_t  CONCRETE            = 0; // must be zero look is_symbolic_value()
uint32_t  SYMBOLIC            = 2;

std::vector<std::vector<uint64_t> > reg_vaddrs(NUMBEROFREGISTERS); // virtual addresses of expression operands
uint32_t* reg_vaddrs_cnts     = (uint32_t*) 0;

// optimization technique
// corrections -- constant folding
uint8_t*  reg_hasmn;
uint64_t* reg_addsub_corr;
uint8_t*  reg_corr_validity;

// ---------------------------------------------
// --------------- branch evaluation
// ---------------------------------------------

std::vector<uint64_t>  zero_v (1, 0);
std::vector<uint64_t>  one_v  (1, 1);
std::vector<uint64_t>  value_v(1);

std::vector<uint64_t> true_branch_rs1_minterval_los (MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> true_branch_rs1_minterval_ups (MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> false_branch_rs1_minterval_los(MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> false_branch_rs1_minterval_ups(MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> true_branch_rs2_minterval_los (MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> true_branch_rs2_minterval_ups (MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> false_branch_rs2_minterval_los(MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> false_branch_rs2_minterval_ups(MAX_NUM_OF_INTERVALS);
uint32_t true_branch_rs1_minterval_cnt   = 0;
uint32_t true_branch_rs2_minterval_cnt   = 0;
uint32_t false_branch_rs1_minterval_cnt  = 0;
uint32_t false_branch_rs2_minterval_cnt  = 0;

uint64_t tc_before_branch_evaluation_rs1 = 0;
uint64_t tc_before_branch_evaluation_rs2 = 0;

uint64_t mrcc = 0;  // trace counter of most recent constraint
uint64_t most_recent_if_on_ast_trace = 0;

// ==, !=, <, <=, >= detection
uint32_t  detected_conditional = 0;
uint32_t  LT   = 1;
uint32_t  LGTE = 2;
uint32_t  EQ   = 4;
uint32_t  DEQ  = 5;

// assertion
bool is_only_one_branch_reachable = false;

// ---------------------------------------------
// --------------- symbolic inputs management
// ---------------------------------------------

std::vector<uint64_t> input_table;

// ---------------------------------------------
// --------------- testing
// ---------------------------------------------

bool IS_TEST_MODE = false;
std::ofstream output_results;

// ---------------------------------------------
// --------------- AST node
// ---------------------------------------------

// in this implmentation we use abstract syntax tree (AST) to represent expressions

struct node {
  uint8_t  type;
  uint64_t left_node;
  uint64_t right_node;
};

uint64_t      ast_trace_cnt = 0;
struct node*  ast_nodes;
uint64_t      zero_node;
uint64_t      one_node;
const uint8_t CONST = 0, VAR = 1, ADDI = 2, ADD = 3, SUB = 4, MUL = 5, DIVU = 6, REMU = 7, ILT = 8, IGTE = 9, IEQ = 10, INEQ = 11;
uint64_t      MAX_NODE_TRACE_LENGTH = 5 * MAX_TRACE_LENGTH;

std::vector<std::vector<uint64_t> > mintervals_los;
std::vector<std::vector<uint64_t> > mintervals_ups;
uint64_t* steps = (uint64_t*) 0;                      // incrementing step of the value intervals
std::vector<std::vector<uint64_t> > store_trace_ptrs; // points to records on memory trace which store this node at vaddr
uint64_t*                           involved_sym_inputs_cnts;
std::vector<std::vector<uint64_t> > involved_sym_inputs_ast_tcs;

// temporary data-structure to pass values targeting propagations
std::vector<uint64_t> propagated_minterval_lo(MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> propagated_minterval_up(MAX_NUM_OF_INTERVALS);

// ------------------------- INITIALIZATION ------------------------

void init_symbolic_engine() {
  pcs                  = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  tcs                  = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  vaddrs               = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  values               = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  data_types           = (uint32_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint32_t));
  asts                 = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  mr_sds               = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));

  read_values          = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  read_los             = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  read_ups             = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));

  reg_data_type        = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_symb_type        = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_steps            = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_mintervals_cnts  = (uint32_t*) malloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_vaddrs_cnts      = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_asts             = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_hasmn            = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t));
  reg_addsub_corr      = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_corr_validity    = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t ));

  steps                    = (uint64_t*)    malloc(MAX_NODE_TRACE_LENGTH * sizeof(uint64_t));
  ast_nodes                = (struct node*) malloc(MAX_NODE_TRACE_LENGTH * sizeof(struct node*));
  involved_sym_inputs_cnts = (uint64_t*)    malloc(MAX_NODE_TRACE_LENGTH * sizeof(uint64_t));

  mintervals_los.resize(MAX_NODE_TRACE_LENGTH);
  mintervals_ups.resize(MAX_NODE_TRACE_LENGTH);
  store_trace_ptrs.resize(MAX_NODE_TRACE_LENGTH);
  involved_sym_inputs_ast_tcs.resize(MAX_NODE_TRACE_LENGTH);

  zero_node            = add_ast_node(CONST, 0, 0, 1, zero_v, zero_v, 1, 0, zero_v);
  one_node             = add_ast_node(CONST, 0, 0, 1, one_v , one_v , 1, 0, zero_v);
  reg_asts[REG_ZR]     = zero_node;
  reg_asts[REG_FP]     = zero_node;

  for (size_t i = 0; i < NUMBEROFREGISTERS; i++) {
    reg_steps[i]           = 1;
    reg_mintervals_cnts[i] = 1;

    reg_mintervals_los[i].resize(MAX_NUM_OF_INTERVALS);
    reg_mintervals_ups[i].resize(MAX_NUM_OF_INTERVALS);

    reg_vaddrs[i].resize(MAX_NUM_OF_OP_VADDRS);
  }

  pcs[0]             = 0;
  tcs[0]             = 0;
  vaddrs[0]          = 0;
  values[0]          = 0;
  data_types[0]      = 0;
  asts[0]            = 0;
  mr_sds[0]          = 0;

  mintervals_los[0].push_back(0);
  mintervals_ups[0].push_back(0);
  steps[0]                    = 0;
  involved_sym_inputs_cnts[0] = 0;

  input_table.reserve(1000);

  TWO_TO_THE_POWER_OF_64 = UINT64_MAX_VALUE + 1U;

  if (IS_TEST_MODE) {
    std::string test_output = reinterpret_cast<const char*>(binary_name);
    test_output += ".result";
    output_results.open(test_output, std::ofstream::trunc);
  }
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

  return gcd_128(n2 % n1, n1);
}

uint128_t lcm_128(uint128_t n1, uint128_t n2) {
  return (n1 / gcd_128(n1, n2)) * n2;
}

bool is_power_of_two(uint64_t v) {
  return v && (!(v & (v - 1)));
}

bool check_incompleteness(uint64_t gcd_steps) {
  uint64_t i_max;

  if (reg_steps[rs1] == reg_steps[rs2])
    return 0;
  else if (reg_steps[rs1] < reg_steps[rs2]) {
    if (reg_steps[rs1] == gcd_steps) {
      for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
        i_max = (reg_mintervals_ups[rs1][i] - reg_mintervals_los[rs1][i]) / reg_steps[rs1];
        if (i_max < reg_steps[rs2]/gcd_steps - 1)
          return 1;
      }
    } else
      return 1;
  } else {
    if (reg_steps[rs2] == gcd_steps) {
      for (size_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        i_max = (reg_mintervals_ups[rs2][i] - reg_mintervals_los[rs2][i]) / reg_steps[rs2];
        if (i_max < reg_steps[rs1]/gcd_steps - 1)
          return 1;
      }
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
//                                corrections
////////////////////////////////////////////////////////////////////////////////

void set_correction(uint64_t reg, uint8_t hasmn, uint64_t addsub_corr, uint8_t corr_validity) {
  reg_hasmn[reg]          = hasmn;
  reg_addsub_corr[reg]    = addsub_corr;
  reg_corr_validity[reg]  = corr_validity;
}

void create_ast_node_entry_for_accumulated_corr(uint64_t sym_reg) {
  value_v[0] = reg_addsub_corr[sym_reg];
  uint64_t crt_ptr = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v);
  if (reg_hasmn[sym_reg]) {
    reg_asts[sym_reg] = add_ast_node(SUB, crt_ptr, reg_asts[sym_reg], reg_mintervals_cnts[sym_reg], reg_mintervals_los[sym_reg], reg_mintervals_ups[sym_reg], reg_steps[sym_reg], reg_vaddrs_cnts[sym_reg], reg_vaddrs[sym_reg]);
  } else {
    reg_asts[sym_reg] = add_ast_node(ADD, crt_ptr, reg_asts[sym_reg], reg_mintervals_cnts[sym_reg], reg_mintervals_los[sym_reg], reg_mintervals_ups[sym_reg], reg_steps[sym_reg], reg_vaddrs_cnts[sym_reg], reg_vaddrs[sym_reg]);
  }
}

void create_crt_operand_ast_node_entry(uint64_t crt_reg) {
  value_v[0]        = reg_mintervals_los[crt_reg][0];
  reg_asts[crt_reg] = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v);
}

////////////////////////////////////////////////////////////////////////////////
//                                operations
////////////////////////////////////////////////////////////////////////////////

void constrain_lui() {
  if (rd != REG_ZR) {
    // interval semantics of lui
    reg_data_type[rd]         = VALUE_T;
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = imm << 12;
    reg_mintervals_ups[rd][0] = imm << 12;
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);
  }
}

void constrain_addi() {
  uint64_t crt_ptr;

  if (rd == REG_ZR)
    return;

  if (reg_data_type[rs1] == POINTER_T) {
    reg_data_type[rd]         = reg_data_type[rs1];
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);

    return;
  }

  reg_data_type[rd] = VALUE_T;

  if (reg_symb_type[rs1] == SYMBOLIC) {
    // rd inherits rs1 constraint
    reg_symb_type[rd] = SYMBOLIC;

    for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
      reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] + imm;
      reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] + imm;
    }
    reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
    reg_steps[rd]           = reg_steps[rs1];
    set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

    if (reg_corr_validity[rs1] == 0) {
      set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] + imm, 0);
      reg_asts[rd] = reg_asts[rs1];
    } else {
      set_correction(rd, 0, 0, 1);
      value_v[0] = imm; crt_ptr = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v);
      reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], crt_ptr, reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);
    }

  } else {
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] + imm;
    reg_mintervals_ups[rd][0] = reg_mintervals_los[rd][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);
  }
}

bool constrain_add_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      // adding two pointers is undefined
      printf("OUTPUT: undefined addition of two pointers at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_data_type[rd]         = reg_data_type[rs1];
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);

    return 1;
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]         = reg_data_type[rs2];
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

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

    reg_data_type[rd] = VALUE_T;

    // interval semantics of add
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        reg_symb_type[rd]    = SYMBOLIC;
        uint32_t rd_addr_idx = reg_vaddrs_cnts[rs1] + reg_vaddrs_cnts[rs2];
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);
        set_vaddrs(rd, reg_vaddrs[rs2], reg_vaddrs_cnts[rs1], rd_addr_idx);

        if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
          create_ast_node_entry_for_accumulated_corr(rs1);
        }
        if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
          create_ast_node_entry_for_accumulated_corr(rs2);
        }
        set_correction(rd, 0, 0, 1);

        // interval semantics of add
        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("OUTPUT: steps in addition are not consistent at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        bool cnd;
        std::vector<uint64_t> mul_lo_rd;
        std::vector<uint64_t> mul_up_rd;
        for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          for (size_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
            cnd = add_sub_condition(reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][j], reg_mintervals_ups[rs2][j]);
            if (cnd == false) {
              handle_add_cnd_failure(mul_lo_rd, mul_up_rd, i, j);
            } else {
              mul_lo_rd.push_back(reg_mintervals_los[rs1][i] + reg_mintervals_los[rs2][j]);
              mul_up_rd.push_back(reg_mintervals_ups[rs1][i] + reg_mintervals_ups[rs2][j]);
            }
          }
        }

        if (mul_lo_rd.size() > 1)
          merge_intervals(mul_lo_rd, mul_up_rd, mul_lo_rd.size(), gcd_steps);

        if (mul_lo_rd.size() > MAX_NUM_OF_INTERVALS) {
          printf("OUTPUT: MAX_NUM_OF_INTERVALS in addition of two symbolics at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        for (size_t i = 0; i < mul_lo_rd.size(); i++) {
          reg_mintervals_los[rd][i] = mul_lo_rd[i];
          reg_mintervals_ups[rd][i] = mul_up_rd[i];
        }
        reg_mintervals_cnts[rd] = mul_lo_rd.size();
        reg_steps[rd]           = gcd_steps;

        reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        uint64_t addend = reg_mintervals_los[rs2][0];
        reg_symb_type[rd] = SYMBOLIC;
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

        for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] + reg_mintervals_los[rs2][0];
          reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] + reg_mintervals_ups[rs2][0];
        }
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
        reg_steps[rd]           = reg_steps[rs1];

        if (reg_corr_validity[rs1] == 0) {
          set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] + addend, 0);
          reg_asts[rd] = reg_asts[rs1];
        } else {
          set_correction(rd, 0, 0, 1);
          reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);
        }
      }

    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      uint64_t addend = reg_mintervals_los[rs1][0];
      reg_symb_type[rd] = SYMBOLIC;
      set_vaddrs(rd, reg_vaddrs[rs2], 0, reg_vaddrs_cnts[rs2]);

      for (uint32_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][0] + reg_mintervals_los[rs2][i];
        reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][0] + reg_mintervals_ups[rs2][i];
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
      reg_steps[rd]           = reg_steps[rs2];

      if (reg_corr_validity[rs2] == 0) {
        set_correction(rd, reg_hasmn[rs2], reg_addsub_corr[rs2] + addend, 0);
        reg_asts[rd] = reg_asts[rs2];
      } else {
        set_correction(rd, 0, 0, 1);
        reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);
      }

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]         = CONCRETE;
      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] + reg_mintervals_los[rs2][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_los[rd][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
      reg_asts[rd]              = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

bool constrain_sub_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      if (reg_mintervals_los[rs1][0] == reg_mintervals_los[rs2][0])
        if (reg_mintervals_ups[rs1][0] == reg_mintervals_ups[rs2][0]) {
          reg_data_type[rd]         = POINTER_T;
          reg_symb_type[rd]         = CONCRETE;
          reg_mintervals_los[rd][0] = registers[rd];
          reg_mintervals_ups[rd][0] = registers[rd];
          reg_mintervals_cnts[rd]   = 1;
          reg_steps[rd]             = 1;
          reg_vaddrs_cnts[rd]       = 0;
          reg_asts[rd]              = 0;

          set_correction(rd, 0, 0, 0);

          return 1;
        }

      // subtracting incompatible pointers
      printf("sub invalid address\n");
      throw_exception(EXCEPTION_INVALIDADDRESS, 0);

      return 1;
    } else {
      reg_data_type[rd]         = reg_data_type[rs1];
      reg_symb_type[rd]         = CONCRETE;
      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
      reg_asts[rd]              = 0;

      set_correction(rd, 0, 0, 0);

      return 1;
    }
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]         = reg_data_type[rs2];
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);

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

    reg_data_type[rd] = VALUE_T;

    // interval semantics of sub
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        reg_symb_type[rd] = SYMBOLIC;
        uint32_t rd_addr_idx = reg_vaddrs_cnts[rs1] + reg_vaddrs_cnts[rs2];
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);
        set_vaddrs(rd, reg_vaddrs[rs2], reg_vaddrs_cnts[rs1], rd_addr_idx);

        if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
          create_ast_node_entry_for_accumulated_corr(rs1);
        }
        if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
          create_ast_node_entry_for_accumulated_corr(rs2);
        }
        set_correction(rd, 0, 0, 1);

        if (reg_mintervals_cnts[rs1] > 1 || reg_mintervals_cnts[rs2] > 1) {
          printf("OUTPUT: unsupported mintervals in sub at %x \n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("OUTPUT: steps in subtraction are not consistent \n");
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        bool cnd = add_sub_condition(reg_mintervals_los[rs1][0], reg_mintervals_ups[rs1][0], reg_mintervals_los[rs2][0], reg_mintervals_ups[rs2][0]);
        if (cnd == false) {
          printf("OUTPUT: cannot reason about overflowed sub %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        sub_lo = reg_mintervals_los[rs2][0];
        sub_up = reg_mintervals_ups[rs2][0];
        reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] - sub_up;
        reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0] - sub_lo;
        reg_mintervals_cnts[rd]   = 1;
        reg_steps[rd]             = gcd_steps;
        reg_asts[rd]              = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        uint64_t subend = reg_mintervals_los[rs2][0];
        reg_symb_type[rd] = SYMBOLIC;
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

        sub_lo = reg_mintervals_los[rs2][0];
        sub_up = reg_mintervals_ups[rs2][0];
        for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] - sub_up;
          reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] - sub_lo;
        }
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
        reg_steps[rd]           = reg_steps[rs1];

        if (reg_corr_validity[rs1] == 0) {
          set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] - subend, 0);
          reg_asts[rd] = reg_asts[rs1];
        } else {
          set_correction(rd, 0, 0, 1);
          reg_asts[rd] = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);
        }
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      uint64_t subend = reg_mintervals_los[rs1][0];
      reg_symb_type[rd] = SYMBOLIC;
      set_vaddrs(rd, reg_vaddrs[rs2], 0, reg_vaddrs_cnts[rs2]);

      sub_lo = reg_mintervals_los[rs1][0];
      sub_up = reg_mintervals_ups[rs1][0];
      for (uint32_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        sub_tmp                   = sub_lo - reg_mintervals_ups[rs2][i];
        reg_mintervals_ups[rd][i] = sub_up - reg_mintervals_los[rs2][i];
        reg_mintervals_los[rd][i] = sub_tmp;
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
      reg_steps[rd]           = reg_steps[rs2];

      if (reg_corr_validity[rs2] == 0) {
        if (reg_hasmn[rs2]) {
          // rs2 constraint has already minuend and can have another minuend
          set_correction(rd, 0, subend - reg_addsub_corr[rs2], 0);
        } else {
          // rd inherits rs2 constraint since rs1 has none
          set_correction(rd, 1, subend - reg_addsub_corr[rs2], 0);
        }
        reg_asts[rd] = reg_asts[rs2];
      } else {
        set_correction(rd, 0, 0, 1);
        reg_asts[rd] = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);
      }

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]         = CONCRETE;
      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] - reg_mintervals_ups[rs2][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_los[rd][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
      reg_asts[rd]              = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void constrain_mul() {
  uint64_t mul_lo;
  uint64_t mul_up;
  uint64_t multiplier;
  bool     cnd;

  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;

    // interval semantics of mul
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        printf("OUTPUT: detected non-linear expression in mul at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
          create_ast_node_entry_for_accumulated_corr(rs1);
          // now reg_asts[rs1] is updated
        }
        if (reg_asts[rs2] == 0) {
          create_crt_operand_ast_node_entry(rs2);
        }
        set_correction(rd, 0, 0, 1);

        reg_symb_type[rd] = SYMBOLIC;
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

        multiplier = reg_mintervals_los[rs2][0];

        bool cnd;
        std::vector<uint64_t> mul_lo_rd;
        std::vector<uint64_t> mul_up_rd;
        for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          cnd = mul_condition(reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][0]);
          if (cnd == true) {
            mul_lo_rd.push_back(reg_mintervals_los[rs1][i] * reg_mintervals_los[rs2][0]);
            mul_up_rd.push_back(reg_mintervals_ups[rs1][i] * reg_mintervals_ups[rs2][0]);
          } else {
            printf("OUTPUT: cnd failure in mul at %x\n", pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
            // handle_mul_cnd_failure(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_steps[rs1], reg_mintervals_los[rs2][0]);
            // reg_corr_validity[rd] = MUL_T_FALSE;
          }
        }

        for (size_t i = 0; i < mul_lo_rd.size(); i++) {
          reg_mintervals_los[rd][i] = mul_lo_rd[i];
          reg_mintervals_ups[rd][i] = mul_up_rd[i];
        }
        reg_mintervals_cnts[rd] = mul_lo_rd.size();
        reg_steps[rd]           = reg_steps[rs1] * multiplier;
        reg_asts[rd]            = add_ast_node(MUL, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);
      }

    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton

      if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
        create_ast_node_entry_for_accumulated_corr(rs2);
        // now reg_asts[rs2] is updated
      }
      if (reg_asts[rs1] == 0) {
        create_crt_operand_ast_node_entry(rs1);
      }
      set_correction(rd, 0, 0, 1);

      reg_symb_type[rd] = SYMBOLIC;
      set_vaddrs(rd, reg_vaddrs[rs2], 0, reg_vaddrs_cnts[rs2]);

      multiplier = reg_mintervals_los[rs1][0];

      bool cnd;
      std::vector<uint64_t> mul_lo_rd;
      std::vector<uint64_t> mul_up_rd;
      for (size_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        cnd = mul_condition(reg_mintervals_los[rs2][i], reg_mintervals_ups[rs2][i], reg_mintervals_los[rs1][0]);
        if (cnd == true) {
          mul_lo_rd.push_back(reg_mintervals_los[rs2][i] * reg_mintervals_los[rs1][0]);
          mul_up_rd.push_back(reg_mintervals_ups[rs2][i] * reg_mintervals_ups[rs1][0]);
        } else {
          printf("OUTPUT: cnd failure in mul at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
          // handle_mul_cnd_failure(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs2][i], reg_mintervals_ups[rs2][i], reg_steps[rs2], reg_mintervals_los[rs1][0]);
          // reg_corr_validity[rd] = MUL_T_FALSE;
        }
      }

      for (size_t i = 0; i < mul_lo_rd.size(); i++) {
        reg_mintervals_los[rd][i] = mul_lo_rd[i];
        reg_mintervals_ups[rd][i] = mul_up_rd[i];
      }
      reg_mintervals_cnts[rd] = mul_lo_rd.size();
      reg_steps[rd]           = reg_steps[rs2] * multiplier;
      reg_asts[rd]            = add_ast_node(MUL, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]         = CONCRETE;
      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] * reg_mintervals_los[rs2][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0] * reg_mintervals_ups[rs2][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
      reg_asts[rd]              = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void constrain_divu() {
  uint64_t div_lo;
  uint64_t div_up;
  uint64_t step;

  if (reg_mintervals_los[rs2][0] != 0) {
    if (reg_mintervals_ups[rs2][0] >= reg_mintervals_los[rs2][0]) {
      // 0 is not in interval
      if (rd != REG_ZR) {
        reg_data_type[rd] = VALUE_T;

        if (reg_mintervals_cnts[rs1] > 1 || reg_mintervals_cnts[rs2] > 1) {
          printf("OUTPUT: unsupported mintervals in divu at %x \n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        // interval semantics of divu
        div_lo = reg_mintervals_los[rs1][0] / reg_mintervals_ups[rs2][0];
        div_up = reg_mintervals_ups[rs1][0] / reg_mintervals_los[rs2][0];
        step   = reg_steps[rs1];

        if (reg_symb_type[rs1] == SYMBOLIC) {
          if (reg_symb_type[rs2] == SYMBOLIC) {
            // non-linear expressions are not supported
            printf("OUTPUT: detected non-linear expression in divu at %x\n", pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

          } else {
            // rd inherits rs1 constraint since rs2 has none
            // assert: rs2 interval is singleton

            if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
              create_ast_node_entry_for_accumulated_corr(rs1);
              // now reg_asts[rs1] is updated
            }
            if (reg_asts[rs2] == 0) {
              create_crt_operand_ast_node_entry(rs2);
            }
            set_correction(rd, 0, 0, 1);

            reg_symb_type[rd] = SYMBOLIC;
            set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

            // step computation
            if (reg_steps[rs1] < reg_mintervals_los[rs2][0]) {
              if (reg_mintervals_los[rs2][0] % reg_steps[rs1] != 0) {
                printf("OUTPUT: steps in divison are not consistent at %x\n", pc - entry_point);
                exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
              }
              reg_steps[rd] = 1;
            } else {
              if (reg_steps[rs1] % reg_mintervals_los[rs2][0] != 0) {
                printf("OUTPUT: steps in divison are not consistent at %x\n", pc - entry_point);
                exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
              }
              reg_steps[rd] = reg_steps[rs1] / reg_mintervals_los[rs2][0];
            }

            // interval semantics of divu
            if (reg_mintervals_los[rs1][0] > reg_mintervals_ups[rs1][0]) {
              // rs1 constraint is wrapped: [lo, UINT64_MAX_T], [0, up]
              uint64_t max = compute_upper_bound(reg_mintervals_los[rs1][0], step, UINT64_MAX_T);
              reg_mintervals_los[rd][0] = (max + step) / reg_mintervals_los[rs2][0];
              reg_mintervals_los[rd][0] = max          / reg_mintervals_ups[rs2][0];

              // lo/k == up/k (or) up/k + step_rd
              if (div_lo != div_up)
                if (div_lo > div_up + reg_steps[rd]) {
                  printf("OUTPUT: wrapped divison rsults two intervals at %x\n", pc - entry_point);
                  exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
                }
            } else {
              // rs1 constraint is not wrapped
              reg_mintervals_los[rd][0] = div_lo;
              reg_mintervals_ups[rd][0] = div_up;
            }

            reg_mintervals_cnts[rd] = 1;
          }

          reg_asts[rd] = add_ast_node(DIVU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);

        } else if (reg_symb_type[rs2] == SYMBOLIC) {
          printf("OUTPUT: detected division of constant by interval at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

        } else {
          // rd has no constraint if both rs1 and rs2 have no constraints
          reg_symb_type[rd]         = CONCRETE;
          reg_mintervals_los[rd][0] = div_lo;
          reg_mintervals_ups[rd][0] = div_up;
          reg_mintervals_cnts[rd]   = 1;
          reg_steps[rd]             = 1;
          reg_vaddrs_cnts[rd]       = 0;
          reg_asts[rd]              = 0;

          set_correction(rd, 0, 0, 0);
        }
      }
    } else
      throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

void constrain_remu() {
  uint64_t rem_lo;
  uint64_t rem_up;
  uint64_t divisor;
  uint64_t step;

  if (reg_mintervals_los[rs2][0] == 0)
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);

  if (reg_symb_type[rs2] == SYMBOLIC) {
    // rs2 has constraint
    printf("OUTPUT: constrained memory location in right operand of remu at %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (rd == REG_ZR)
    return;

  if (reg_mintervals_cnts[rs1] > 1 || reg_mintervals_cnts[rs2] > 1) {
    printf("OUTPUT: unsupported minterval 5 %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  reg_data_type[rd] = VALUE_T;

  if (reg_symb_type[rs1] == SYMBOLIC) {
    // interval semantics of remu
    divisor = reg_mintervals_los[rs2][0];
    step    = reg_steps[rs1];

    if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
      create_ast_node_entry_for_accumulated_corr(rs1);
      // now reg_asts[rs1] is updated
    }
    if (reg_asts[rs2] == 0) {
      create_crt_operand_ast_node_entry(rs2);
    }
    set_correction(rd, 0, 0, 1);

    if (reg_mintervals_los[rs1][0] <= reg_mintervals_ups[rs1][0]) {
      // rs1 interval is not wrapped
      int rem_typ = remu_condition(reg_mintervals_los[rs1][0], reg_mintervals_ups[rs1][0], step, divisor);
      if (rem_typ == 0) {
        rem_lo        = reg_mintervals_los[rs1][0] % divisor;
        rem_up        = reg_mintervals_ups[rs1][0] % divisor;
        reg_steps[rd] = step;
      } else if (rem_typ == 1) {
        printf("OUTPUT: modulo results two intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (rem_typ == 2) {
        uint64_t gcd_step_k = gcd(step, divisor);
        rem_lo        = reg_mintervals_los[rs1][0]%divisor - ((reg_mintervals_los[rs1][0]%divisor) / gcd_step_k) * gcd_step_k;
        rem_up        = compute_upper_bound(rem_lo, gcd_step_k, divisor - 1);
        reg_steps[rd] = gcd_step_k;
      } else {
        printf("OUTPUT: modulo results many intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      reg_symb_type[rd] = SYMBOLIC;
      set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

    } else if (is_power_of_two(divisor)) {
      // rs1 interval is wrapped
      uint64_t gcd_step_k = gcd(step, divisor);
      uint64_t lcm        = (step * divisor) / gcd_step_k;

      if (reg_mintervals_ups[rs1][0] - reg_mintervals_los[rs1][0] < lcm - step) {
        printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      rem_lo        = reg_mintervals_los[rs1][0]%divisor - ((reg_mintervals_los[rs1][0]%divisor) / gcd_step_k) * gcd_step_k;
      rem_up        = compute_upper_bound(rem_lo, gcd_step_k, divisor - 1);
      reg_steps[rd] = gcd_step_k;

      reg_symb_type[rd] = SYMBOLIC;
      set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_mintervals_los[rd][0] = rem_lo;
    reg_mintervals_ups[rd][0] = rem_up;
    reg_mintervals_cnts[rd]   = 1;

    reg_asts[rd] = add_ast_node(REMU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_vaddrs_cnts[rd], reg_vaddrs[rd]);

  } else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] % reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0] % reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);
  }
}

void constrain_sltu() {
  if (rd != REG_ZR) {
    if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
      // concrete semantics of sltu
      registers[rd] = (registers[rs1] < registers[rs2]) ? 1 : 0;

      reg_data_type[rd]         = VALUE_T;
      reg_symb_type[rd]         = CONCRETE;
      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
      reg_asts[rd]              = (registers[rd] == 0) ? zero_node : one_node;

      is_only_one_branch_reachable = true;

      pc = pc + INSTRUCTIONSIZE;
      ic_sltu = ic_sltu + 1;

      return;
    }

    is_only_one_branch_reachable = false;

    if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
      create_ast_node_entry_for_accumulated_corr(rs1);
      // now reg_asts[rs1] is updated
    } else if (reg_asts[rs1] == 0 && reg_symb_type[rs1] == CONCRETE) {
      create_crt_operand_ast_node_entry(rs1);
    }
    if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
      create_ast_node_entry_for_accumulated_corr(rs2);
      // now reg_asts[rs1] is updated
    } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == CONCRETE) {
      create_crt_operand_ast_node_entry(rs2);
    }

    if (reg_data_type[rs1] == POINTER_T) {
      if (reg_data_type[rs2] != POINTER_T) {
        create_mconstraints_lptr(registers[rs1], registers[rs1], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], mrcc);
      }
    } else if (reg_data_type[rs2] == POINTER_T) {
      create_mconstraints_rptr(reg_mintervals_los[rs1], reg_mintervals_ups[rs1], registers[rs2], registers[rs2], mrcc);
    } else {
      create_mconstraints(reg_mintervals_los[rs1], reg_mintervals_ups[rs1], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], mrcc);
    }
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_sltu = ic_sltu + 1;
}

void constrain_xor() {
  if (rd == REG_ZR)
    return;

  if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
    // concrete semantics of xor
    registers[rd] = registers[rs1] ^ registers[rs2];

    reg_data_type[rd]         = VALUE_T;
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = registers[rd];
    reg_mintervals_ups[rd][0] = registers[rd];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = (registers[rd] == 0) ? zero_node : one_node;

    is_only_one_branch_reachable = true;

    pc = pc + INSTRUCTIONSIZE;
    ic_xor = ic_xor + 1;

    return;
  }

  is_only_one_branch_reachable = false;

  if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
    create_ast_node_entry_for_accumulated_corr(rs1);
    // now reg_asts[rs1] is updated
  } else if (reg_asts[rs1] == 0 && reg_symb_type[rs1] == CONCRETE) {
    create_crt_operand_ast_node_entry(rs1);
  }
  if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
    create_ast_node_entry_for_accumulated_corr(rs2);
    // now reg_asts[rs1] is updated
  } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == CONCRETE) {
    create_crt_operand_ast_node_entry(rs2);
  }

  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] != POINTER_T) {
      create_xor_mconstraints_lptr(registers[rs1], registers[rs1], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], mrcc);
    }
  } else if (reg_data_type[rs2] == POINTER_T)
    create_xor_mconstraints_rptr(reg_mintervals_los[rs1], reg_mintervals_ups[rs1], registers[rs2], registers[rs2], mrcc);
  else
    create_xor_mconstraints(reg_mintervals_los[rs1], reg_mintervals_ups[rs1], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], mrcc);

  pc = pc + INSTRUCTIONSIZE;
  ic_xor = ic_xor + 1;

}

uint64_t check_whether_represents_most_recent_constraint(uint64_t mrvc) {
  uint64_t ast_tc = asts[mrvc];
  uint64_t most_recent_input;
  uint64_t input_ast_tc;
  bool     is_updated = true;

  for (size_t i = 0; i < involved_sym_inputs_cnts[ast_tc]; i++) {
    input_ast_tc = involved_sym_inputs_ast_tcs[ast_tc][i];
    most_recent_input = input_table[ast_nodes[input_ast_tc].right_node];
    if (most_recent_input > input_ast_tc) {
      is_updated = false;
      break;
    }
  }

  if (is_updated == false) {
    recompute_expression(ast_tc);
    return load_symbolic_memory(pt, vaddrs[mrvc]);
  } else
    return mrvc;
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

        mrvc = check_whether_represents_most_recent_constraint(mrvc);

        reg_asts[rd] = asts[mrvc];

        // it is important because we have prevousely freed stack addresses on the trace
        if (vaddr >= get_program_break(current_context))
          if (vaddr < registers[REG_SP]) {
            // free memory
            printf("%llu, %llu, %llu\n", get_program_break(current_context), registers[REG_SP], mrvc);
            printf("OUTPUT: loading an uninitialized memory %llu at %x\n", vaddr, pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
          }

        // interval semantics of ld
        reg_data_type[rd]       = data_types[mrvc];
        registers[rd]           = values[mrvc];
        reg_mintervals_cnts[rd] = mintervals_los[reg_asts[rd]].size();
        if (reg_mintervals_cnts[rd] == 0) printf("OUTPUT: reg_mintervals_cnts is zero\n");
        for (uint32_t i = 0; i < reg_mintervals_cnts[rd]; i++) {
          reg_mintervals_los[rd][i] = mintervals_los[reg_asts[rd]][i];
          reg_mintervals_ups[rd][i] = mintervals_ups[reg_asts[rd]][i];
        }
        reg_steps[rd]           = steps[reg_asts[rd]];

        // assert: vaddr == *(vaddrs + mrvc)

        if (is_symbolic_value(reg_data_type[rd], reg_mintervals_cnts[rd], reg_mintervals_los[rd][0], reg_mintervals_ups[rd][0])) {
          // vaddr is constrained by rd if value interval is not singleton
          reg_symb_type[rd]   = SYMBOLIC;
          reg_vaddrs_cnts[rd] = involved_sym_inputs_cnts[reg_asts[rd]];
          for (size_t i = 0; i < reg_vaddrs_cnts[rd]; i++) {
            reg_vaddrs[rd][i] = involved_sym_inputs_ast_tcs[reg_asts[rd]][i];
          }
        } else {
          reg_symb_type[rd]   = CONCRETE;
          reg_vaddrs_cnts[rd] = 0;
        }

        set_correction(rd, 0, 0, 0);
      }

      // keep track of instruction address for profiling loads
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of loads in total
      ic_ld = ic_ld + 1;

      // and individually
      loads_per_instruction[a] = loads_per_instruction[a] + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    printf("load invalid address\n");
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

uint64_t constrain_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = registers[rs1] + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // interval semantics of sd
      if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
        create_ast_node_entry_for_accumulated_corr(rs2);
        // now reg_asts[rs2] is updated
        set_correction(rs2, 0, 0, 1);
      }

      if (reg_asts[rs2] == 0) {
        if (reg_symb_type[rs2] == CONCRETE) {
          reg_asts[rs2] = add_ast_node(CONST, 0, 0, 1, reg_mintervals_los[rs2], reg_mintervals_ups[rs2], 1, 0, zero_v);
        } else {
          printf("OUTPUT: detected symbolic value with reg_asts = 0 at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }
      }
      store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_type[rs2], reg_asts[rs2], mrcc, 1);

      // keep track of instruction address for profiling stores
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of stores in total
      ic_sd = ic_sd + 1;

      // and individually
      stores_per_instruction[a] = stores_per_instruction[a] + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    printf("store invalid address at %x\n", pc-entry_point);
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

void constrain_jal_jalr() {
  if (rd != REG_ZR) {
    reg_data_type[rd]         = VALUE_T;
    reg_symb_type[rd]         = CONCRETE;
    reg_mintervals_los[rd][0] = registers[rd];
    reg_mintervals_ups[rd][0] = registers[rd];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = 0;

    set_correction(rd, 0, 0, 0);
  }
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void print_symbolic_memory(uint64_t svc) {

}

uint8_t is_symbolic_value(uint64_t type, uint32_t mints_num, uint64_t lo, uint64_t up) {
  if (type == POINTER_T)
    // memory range
    return CONCRETE;
  else if (mints_num > 1)
    return SYMBOLIC;
  else if (lo == up)
    // singleton interval
    return CONCRETE;
  else
    // non-singleton interval
    return SYMBOLIC;
}

uint64_t is_safe_address(uint64_t vaddr, uint64_t reg) {
  if (reg_data_type[reg] == POINTER_T) {
    if (vaddr < reg_mintervals_los[reg][0])
      // memory access below start address of mallocated block
      return 0;
    else if (vaddr - reg_mintervals_los[reg][0] >= reg_mintervals_ups[reg][0])
      // memory access above end address of mallocated block
      return 0;
    else
      return 1;
  } else if (reg_mintervals_los[reg][0] == reg_mintervals_ups[reg][0])
    return 1;
  else {
    printf("%llu: %llu, %llu, %llu, %llu, %llu, %llu\n", reg, reg_data_type[reg], vaddr, reg_mintervals_los[reg][0], reg_mintervals_ups[reg][0], registers[REG_SP], ast_trace_cnt);
    printf("OUTPUT: detected unsupported symbolic access of memory interval at %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
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
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t is_trace_space_available() {
  return tc + 1 < MAX_TRACE_LENGTH;
}

uint64_t get_current_tc() {
  return tc;
}

void ealloc() {
  tc = tc + 1;
}

void efree() {
  // assert: tc > 0
  tc = tc - 1;
}

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint32_t data_type, uint64_t ast_ptr, uint64_t trb, uint64_t is_store) {
  uint64_t mrvc;

  if (vaddr == 0)
    // tracking program break and size for malloc
    mrvc = 0;
  else if (vaddr < NUMBEROFREGISTERS) {
    // tracking a register value for sltu
    mrvc    = mrcc;
  } else if (vaddr == NUMBEROFREGISTERS) {
    if (is_trace_space_available()) {
      ealloc();

      pcs[tc]        = pc;
      tcs[tc]        = 0;
      data_types[tc] = data_type;
      values[tc]     = value;
      vaddrs[tc]     = vaddr;
      asts[tc]       = ast_ptr;
      mr_sds[tc]     = tc;
    } else {
      throw_exception(EXCEPTION_MAXTRACE, 0);
    }
    return;
  } else {
    // assert: vaddr is valid and mapped
    mrvc = load_symbolic_memory(pt, vaddr);

    if (trb < mrvc) {
      if (ast_nodes[ast_ptr].type == CONST) {
        if (ast_nodes[asts[mrvc]].type == CONST) {
          // overwrite

          pcs[mrvc]        = pc;
          data_types[mrvc] = data_type;
          values[mrvc]     = value;
          asts[mrvc]       = ast_ptr;

          if (ast_ptr)  { store_trace_ptrs[ast_ptr].push_back(mrvc); }
          if (is_store) { mr_sds[mrvc]   = mrvc; }

          return;
        }
      }
    }
  }

  if (is_trace_space_available()) {
    ealloc();

    pcs[tc]        = pc;
    tcs[tc]        = mrvc;
    data_types[tc] = data_type;
    values[tc]     = value;
    vaddrs[tc]     = vaddr;
    asts[tc]       = ast_ptr;

    if (ast_ptr) store_trace_ptrs[ast_ptr].push_back(tc);

    if (is_store) {
      mr_sds[tc] = tc;
    } else {
      mr_sds[tc] = mr_sds[mrvc];
    }

    if (vaddr < NUMBEROFREGISTERS) {
      if (vaddr > 0) {
        // register tracking marks most recent constraint
        mrcc     = tc;
        asts[tc] = most_recent_if_on_ast_trace;
        most_recent_if_on_ast_trace = ast_trace_cnt;
      }
    } else
      // assert: vaddr is valid and mapped
      store_virtual_memory(pt, vaddr, tc);
  } else {
    throw_exception(EXCEPTION_MAXTRACE, 0);
  }
}

void store_register_memory(uint64_t reg, std::vector<uint64_t>& value) {
  // always track register memory by using tc as most recent branch
  store_symbolic_memory(pt, reg, value[0], VALUE_T, 0, tc, 1);
}

uint64_t reverse_division_up(uint64_t ups_mrvc, uint64_t up, uint64_t codiv) {
  if (ups_mrvc < up * codiv + (codiv - 1))
    return ups_mrvc - up * codiv;
  else
    return codiv - 1;
}

uint64_t add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, uint32_t mints_num, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t step, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs) {
  ast_trace_cnt++;

  if (ast_trace_cnt > MAX_NODE_TRACE_LENGTH) {
    printf("OUTPUT: MAX_NODE_TRACE_LENGTH reached %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (mints_num > MAX_NUM_OF_INTERVALS) {
    printf("OUTPUT: maximum number of possible intervals is reached at %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  ast_nodes[ast_trace_cnt].type       = typ;
  ast_nodes[ast_trace_cnt].left_node  = left_node;
  ast_nodes[ast_trace_cnt].right_node = right_node;
  store_trace_ptrs[ast_trace_cnt].clear();


  mintervals_los[ast_trace_cnt].clear();
  mintervals_ups[ast_trace_cnt].clear();
  for (size_t i = 0; i < mints_num; i++) {
    mintervals_los[ast_trace_cnt].push_back(lo[i]);
    mintervals_ups[ast_trace_cnt].push_back(up[i]);
  }
  steps[ast_trace_cnt]       = step;

  if (typ == VAR) {
    involved_sym_inputs_cnts[ast_trace_cnt] = 1;
    involved_sym_inputs_ast_tcs[ast_trace_cnt].clear();
    involved_sym_inputs_ast_tcs[ast_trace_cnt].push_back(ast_trace_cnt);
  } else {
    involved_sym_inputs_cnts[ast_trace_cnt] = sym_input_num;
    involved_sym_inputs_ast_tcs[ast_trace_cnt].clear();
    for (size_t i = 0; i < sym_input_num; i++) {
      involved_sym_inputs_ast_tcs[ast_trace_cnt].push_back(sym_input_ast_tcs[i]);
    }
  }

  return ast_trace_cnt;
}

uint8_t LEFT  = 10;
uint8_t RIGHT = 20;
uint64_t sym_operand_ast_tc = 0;
uint64_t crt_operand_ast_tc = 0;
uint8_t detect_sym_operand(uint64_t ast_tc) {
  uint8_t left_typ = is_symbolic_value(VALUE_T, mintervals_los[ast_nodes[ast_tc].left_node].size(), mintervals_los[ast_nodes[ast_tc].left_node][0], mintervals_ups[ast_nodes[ast_tc].left_node][0]);
  uint8_t right_typ = is_symbolic_value(VALUE_T, mintervals_los[ast_nodes[ast_tc].right_node].size(), mintervals_los[ast_nodes[ast_tc].right_node][0], mintervals_ups[ast_nodes[ast_tc].right_node][0]);

  if (left_typ == SYMBOLIC && right_typ == CONCRETE) {
    sym_operand_ast_tc = ast_nodes[ast_tc].left_node;
    crt_operand_ast_tc = ast_nodes[ast_tc].right_node;
    return LEFT;
  } else if (left_typ == CONCRETE && right_typ == SYMBOLIC) {
    sym_operand_ast_tc = ast_nodes[ast_tc].right_node;
    crt_operand_ast_tc = ast_nodes[ast_tc].left_node;
    return RIGHT;
  } else {
    printf("%llu %llu %llu %llu\n", mintervals_los[ast_nodes[ast_tc].right_node][0], mintervals_ups[ast_nodes[ast_tc].right_node][0], right_typ, ast_tc);
    printf("%llu %llu %llu %llu\n", mintervals_los[ast_nodes[ast_tc].left_node][0], mintervals_ups[ast_nodes[ast_tc].left_node][0], left_typ, ast_trace_cnt);
    printf("OUTPUT: backward propagation of symbolics at %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void store_input_record(uint64_t ast_ptr, uint64_t prev_input_record) {
  store_symbolic_memory(pt, NUMBEROFREGISTERS, prev_input_record, INPUT_T, ast_ptr, tc, 0);
}

uint64_t stored_to_tc;
uint64_t mr_stored_to_tc;
uint64_t backward_analysis_ast(uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num) {
  std::vector<uint64_t> saved_lo;
  std::vector<uint64_t> saved_up;
  std::vector<uint32_t> idxs;
  uint8_t left_or_right_is_sym;
  uint64_t ast_ptr;
  bool is_assigned = false;
  uint64_t prev_input;

  uint32_t j;
  // bool is_found;
  for (size_t i = 0; i < mints_num; i++) {
    // is_found = false;
    // we have several intervals; we need to detect which lo_before_op was for which [lo, up] interval.
    for (j = 0; j < mintervals_los[ast_tc].size(); j++) {
      if (mintervals_ups[ast_tc][j] - mintervals_los[ast_tc][j] >= lo[i] - mintervals_los[ast_tc][j]) {
        // is_found = true;
        break;
      }
    }
    // assert: is_found == true
    // if (is_found == false) {
    //   printf("OUTPUT: lo_before_op not found at %x\n", pc - entry_point);
    //   exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    // }

    idxs.push_back(j);
    propagated_minterval_lo[i] = compute_lower_bound(mintervals_los[ast_tc][j], steps[ast_tc], lo[i]);
    propagated_minterval_up[i] = compute_upper_bound(mintervals_los[ast_tc][j], steps[ast_tc], up[i]);
  }

  if (ast_nodes[ast_tc].type == VAR) {
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[ast_tc].right_node, mints_num, propagated_minterval_lo, propagated_minterval_up, steps[ast_tc], 0, zero_v);

    prev_input = input_table.at(ast_nodes[ast_tc].right_node);
    input_table.at(ast_nodes[ast_tc].right_node) = ast_ptr;

    for (size_t i = 0; i < store_trace_ptrs[ast_tc].size(); i++) {
      stored_to_tc    = store_trace_ptrs[ast_tc][i];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= store_trace_ptrs[ast_tc][i]) {
        store_symbolic_memory(pt, vaddrs[store_trace_ptrs[ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, prev_input);
    }

    return ast_ptr;
  }

  left_or_right_is_sym = detect_sym_operand(ast_tc);

  for (size_t i = 0; i < mints_num; i++) {
    saved_lo.push_back(propagated_minterval_lo[i]);
    saved_up.push_back(propagated_minterval_up[i]);
  }

  switch (ast_nodes[ast_tc].type) {
    case ADD: {
      for (size_t i = 0; i < mints_num; i++) {
        propagated_minterval_lo[i] = propagated_minterval_lo[i] - mintervals_los[crt_operand_ast_tc][0];
        propagated_minterval_up[i] = propagated_minterval_up[i] - mintervals_los[crt_operand_ast_tc][0];
      }
      break;
    }
    case SUB: {
      if (left_or_right_is_sym == RIGHT) {
        // minuend
        uint64_t tmp;
        for (size_t i = 0; i < mints_num; i++) {
          tmp = mintervals_los[crt_operand_ast_tc][0] - propagated_minterval_up[i];
          propagated_minterval_up[i] = mintervals_los[crt_operand_ast_tc][0] - propagated_minterval_lo[i];
          propagated_minterval_lo[i] = tmp;
        }
      } else {
        for (size_t i = 0; i < mints_num; i++) {
          propagated_minterval_lo[i] = propagated_minterval_lo[i] + mintervals_los[crt_operand_ast_tc][0];
          propagated_minterval_up[i] = propagated_minterval_up[i] + mintervals_los[crt_operand_ast_tc][0];
        }
      }
      break;
    }
    case MUL: {
      // <9223372036854775808, 2^64 - 1, 1> * 2 = <0, 2^64 - 2, 2>
      // <9223372036854775809, 15372286728091293014, 1> * 3 = <9223372036854775811, 9223372036854775810, 3>
      for (size_t i = 0; i < mints_num; i++) {
        propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][idxs[i]] + (propagated_minterval_lo[i] - mintervals_los[ast_tc][idxs[i]]) / mintervals_los[crt_operand_ast_tc][0];
        propagated_minterval_up[i] = mintervals_los[sym_operand_ast_tc][idxs[i]] + (propagated_minterval_up[i] - mintervals_los[ast_tc][idxs[i]]) / mintervals_los[crt_operand_ast_tc][0];
      }
      break;
    }
    case DIVU: {
      if (mints_num > 1) {
        printf("OUTPUT: backward propagation of minterval needed at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      uint64_t divisor = mintervals_los[crt_operand_ast_tc][0];

      if (mintervals_los[sym_operand_ast_tc][0] <= mintervals_ups[sym_operand_ast_tc][0]) {
        // non-wrapped
        if (propagated_minterval_lo[0] * divisor > mintervals_los[sym_operand_ast_tc][0])
          propagated_minterval_lo[0] = compute_lower_bound(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_lo[0] * divisor);
        else
          propagated_minterval_lo[0] = mintervals_los[sym_operand_ast_tc][0];

        propagated_minterval_up[0] = compute_upper_bound(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_up[0] * divisor + reverse_division_up(mintervals_ups[sym_operand_ast_tc][0], propagated_minterval_up[0], divisor));
      } else {
        // wrapped
        uint64_t lo_1;
        uint64_t up_1;
        uint64_t lo_2;
        uint64_t up_2;
        uint64_t max = compute_upper_bound(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], UINT64_MAX_T);
        uint64_t min = (max + steps[sym_operand_ast_tc]);
        uint32_t  which_is_empty;

        if (propagated_minterval_lo[0] * divisor > min)
          propagated_minterval_lo[0] = compute_lower_bound(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_lo[0] * divisor);
        else
          propagated_minterval_lo[0] = min;

        propagated_minterval_up[0] = compute_upper_bound(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_up[0] * divisor + reverse_division_up(max, propagated_minterval_up[0], divisor));

        // intersection of [propagated_minterval_lo, propagated_minterval_up] with original interval
        which_is_empty = 0;
        if (propagated_minterval_lo[0] <= mintervals_ups[sym_operand_ast_tc][0]) {
          lo_1 = propagated_minterval_lo[0];
          up_1 = (propagated_minterval_up[0] < mintervals_ups[sym_operand_ast_tc][0]) ? propagated_minterval_up[0] : mintervals_ups[sym_operand_ast_tc][0];
        } else {
          which_is_empty = 1;
        }

        if (propagated_minterval_up[0] >= mintervals_los[sym_operand_ast_tc][0]) {
          lo_2 = (propagated_minterval_lo[0] > mintervals_los[sym_operand_ast_tc][0]) ? propagated_minterval_lo[0] : mintervals_los[sym_operand_ast_tc][0];
          up_2 = propagated_minterval_up[0];
        } else {
          which_is_empty = (which_is_empty == 1) ? 4 : 2;
        }

        if (which_is_empty == 0) {
          if (up_1 + steps[sym_operand_ast_tc] >= lo_2) {
            propagated_minterval_lo[0] = lo_1;
            propagated_minterval_up[0] = up_2;
          } else {
            printf("OUTPUT: reverse of division results two intervals at %x\n", pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        } else if (which_is_empty == 1) {
          propagated_minterval_lo[0] = lo_2;
          propagated_minterval_up[0] = up_2;
        } else if (which_is_empty == 2) {
          propagated_minterval_lo[0] = lo_1;
          propagated_minterval_up[0] = up_1;
        } else if (which_is_empty == 4) {
          printf("OUTPUT: reverse of division results empty intervals at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

      }
      break;
    }
    case REMU: {
      printf("OUTPUT: detected an unsupported remu in a conditional expression at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
    default: {
      printf("OUTPUT: reverse of division results empty intervals at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
  }

  uint64_t sym_operand_ptr = backward_analysis_ast(sym_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, mints_num);

  if (left_or_right_is_sym == LEFT)
    ast_ptr = add_ast_node(ast_nodes[ast_tc].type, sym_operand_ptr, ast_nodes[ast_tc].right_node, mints_num, saved_lo, saved_up, steps[ast_tc], involved_sym_inputs_cnts[sym_operand_ptr], involved_sym_inputs_ast_tcs[sym_operand_ptr]);
  else
    ast_ptr = add_ast_node(ast_nodes[ast_tc].type, ast_nodes[ast_tc].left_node, sym_operand_ptr, mints_num, saved_lo, saved_up, steps[ast_tc], involved_sym_inputs_cnts[sym_operand_ptr], involved_sym_inputs_ast_tcs[sym_operand_ptr]);

  for (size_t i = 0; i < store_trace_ptrs[ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= store_trace_ptrs[ast_tc][i]) {
      store_symbolic_memory(pt, vaddrs[store_trace_ptrs[ast_tc][i]], saved_lo[0], VALUE_T, ast_ptr, tc, 0);
      is_assigned = true;
    }
  }

  return ast_ptr;
}

void constrain_memory(uint64_t reg, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t trb, bool only_reachable_branch) {
  uint64_t mrvc;

  if (reg_symb_type[reg] == SYMBOLIC) {
    if (only_reachable_branch == false) {
      backward_analysis_ast(reg_asts[reg], lo, up, mints_num);
    }
  }
}

void set_vaddrs(uint64_t reg, std::vector<uint64_t>& vaddrs, uint32_t start_idx, uint32_t vaddr_num) {
  reg_vaddrs_cnts[reg] = vaddr_num;
  for (uint32_t i = 0; i < vaddr_num; i++) {
    reg_vaddrs[reg][start_idx++] = vaddrs[i];
  }
}

void take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0) {
    // record that we need to set rd to true
    value_v[0] = b;
    store_register_memory(rd, value_v);

    // record frame and stack pointer
    value_v[0] = registers[REG_FP];
    store_register_memory(REG_FP, value_v);
    value_v[0] = registers[REG_SP];
    store_register_memory(REG_SP, value_v);
  } else {
    reg_data_type[rd]         = VALUE_T;
    reg_symb_type[rd]         = CONCRETE;
    registers[rd]             = b;
    reg_mintervals_los[rd][0] = b;
    reg_mintervals_ups[rd][0] = b;
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
    reg_asts[rd]              = (b == 0) ? zero_node : one_node;

    set_correction(rd, 0, 0, 0);
  }
}

bool create_true_false_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  bool cannot_handle = false;

  if (lo1 <= up1) {
    // rs1 interval is not wrapped around
    if (lo2 <= up2) {
      // both rs1 and rs2 intervals are not wrapped around
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else if (up2 <= lo1) {
        // rs2 interval is less than or equal to rs1 interval
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
        false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
        false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;

      } else if (lo2 == up2) {
        // rs2 interval is a singleton
        // a case where lo1 = up1 shouldn't be reach here
        // false case
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo2;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
        false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
        false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;

        // true case
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = lo2 - 1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else if (lo1 == up1) {
        // rs1 interval is a singleton
        // false case
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
        false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
        false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = lo1;

        // true case
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo1 + 1; // never overflow
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else {
        // be careful about case [10, 20] < [20, 30] where needs a relation
        // we cannot handle non-singleton interval intersections in comparison
        cannot_handle = true;
      }
    } else {
      // rs1 interval is not wrapped around but rs2 is
      if (up1 < lo2 && up2 <= lo1) {
        // false
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
        false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = 0;
        false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;

        // true
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = UINT64_MAX_T;

      } else if (lo1 == up1) {
        uint64_t lo_p;
        uint64_t up_p;

        if (lo1 >= lo2) { // upper part
          false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
          false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
          // non-empty false case 1
          false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
          false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = lo1;
          // non-empty false case 2
          false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = 0;
          false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;

          // true case
          if (lo1 != UINT64_MAX_T) {
            lo_p = compute_lower_bound(lo2, reg_steps[rs1], lo1 + 1);
            up_p = compute_upper_bound(lo1, reg_steps[rs1], UINT64_MAX_T);
            if (lo_p <= up_p) {
              true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
              true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
              true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo_p;
              true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up_p;
            }
          }

        } else { // lower part
          // false case
          lo_p = compute_lower_bound(lo2, reg_steps[rs1], 0);
          up_p = compute_upper_bound(lo1, reg_steps[rs1], lo1);
          if (lo_p <= up_p) {
            false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
            false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
            false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo_p;
            false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up_p;
          }

          true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
          true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
          // non-empty true case 1
          true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo1 + 1;
          true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
          // non-empty true case 2
          true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
          true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = UINT64_MAX_T;
        }

      } else {
        // we cannot handle non-singleton interval intersections in comparison
        cannot_handle = true;
      }
    }
  } else if (lo2 <= up2) {
    // rs2 interval is not wrapped around but rs1 is
    if (up1 < lo2 && up2 <= lo1) {
      // false case
      false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
      false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = UINT64_MAX_T;
      false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
      false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;

      // true case
      true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = 0;
      true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
      true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
      true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
    } else if (lo2 == up2) {
      // construct constraint for true case
      uint64_t lo_p;
      uint64_t up_p;

      if (lo2 > lo1) { // upper part
        // false case
        lo_p = compute_lower_bound(lo1, reg_steps[rs1], lo2);
        up_p = compute_upper_bound(lo1, reg_steps[rs1], UINT64_MAX_T);
        if (lo_p <= up_p) {
          false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo_p;
          false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up_p;
          false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
          false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;
        }

        // non-empty true 1
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = lo2 - 1; // never lo2 = 0
        // non-empty true 2
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = 0;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;

        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else {
        // non-empty false case 1
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo2;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
        // non-empty false case 2
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = UINT64_MAX_T;

        false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
        false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;

        // true case
        if (lo2 != 0) {
          lo_p = compute_lower_bound(lo1, reg_steps[rs1], 0);
          up_p = compute_upper_bound(lo1, reg_steps[rs1], lo2 - 1);
          if (lo_p <= up_p) {
            true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo_p;
            true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up_p;
            true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
            true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
          }
        }
      }

    } else {
      // we cannot handle non-singleton interval intersections in comparison
      cannot_handle = true;
    }

  } else {
    // both rs1 and rs2 intervals are wrapped around
    printf("OUTPUT: < of two non-wrapped intervals are not supported for now at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  return cannot_handle;
}

void create_mconstraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo1;
  uint64_t up1;
  uint64_t lo2;
  uint64_t up2;

  true_branch_rs1_minterval_cnt  = 0;
  true_branch_rs2_minterval_cnt  = 0;
  false_branch_rs1_minterval_cnt = 0;
  false_branch_rs2_minterval_cnt = 0;

  for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
    lo1 = lo1_p[i];
    up1 = up1_p[i];
    for (uint32_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
      lo2 = lo2_p[j];
      up2 = up2_p[j];
      cannot_handle = create_true_false_constraints(lo1, up1, lo2, up2);
    }
  }

  if (cannot_handle) {
    // detected non-singleton interval intersection
    printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_lte_or_gte() == LGTE) {
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 1);
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 0);
      }
    } else {
      constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

}

void create_mconstraints_lptr(uint64_t lo1, uint64_t up1, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo2;
  uint64_t up2;

  true_branch_rs1_minterval_cnt  = 0;
  true_branch_rs2_minterval_cnt  = 0;
  false_branch_rs1_minterval_cnt = 0;
  false_branch_rs2_minterval_cnt = 0;

  for (uint32_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
    lo2 = lo2_p[j];
    up2 = up2_p[j];
    cannot_handle = create_true_false_constraints(lo1, up1, lo2, up2);
  }

  if (cannot_handle) {
    // detected non-singleton interval intersection
    printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_lte_or_gte() == LGTE) {
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 1);
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 0);
      }
    } else {
      constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void create_mconstraints_rptr(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, uint64_t lo2, uint64_t up2, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo1;
  uint64_t up1;

  true_branch_rs1_minterval_cnt  = 0;
  true_branch_rs2_minterval_cnt  = 0;
  false_branch_rs1_minterval_cnt = 0;
  false_branch_rs2_minterval_cnt = 0;

  for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
    lo1 = lo1_p[i];
    up1 = up1_p[i];
    cannot_handle = create_true_false_constraints(lo1, up1, lo2, up2);
  }

  if (cannot_handle) {
    // detected non-singleton interval intersection
    printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_lte_or_gte() == LGTE) {
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 1);
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 0);
      }
    } else {
      constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

bool create_xor_true_false_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  bool cannot_handle = false;

  if (lo1 <= up1) {
    // rs1 non-wrapped
    if (lo2 <= up2) {
      // rs2 non-wrapped
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else if (up2 < lo1) {
        // rs2 interval is strictly less than rs1 interval
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else if (lo2 == up2) {
        // rs2 interval is a singleton
        /* one of the true cases are definitly happens since rs1 at least has two values. */
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
        // true case 1
        if (lo2 != lo1) {
          // non empty
          true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
          true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = lo2 - 1;
        }
        // true case 2
        if (lo2 != up1) {
          // non empty
          true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo2 + 1;
          true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        }

        // check emptiness of false case
        if ((lo2 - lo1) % reg_steps[rs1] == 0) {
          false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo2;
          false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up2;
          false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
          false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;
        }

      } else if (lo1 == up1) {
        // rs1 interval is a singleton
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        // true case 1
        if (lo1 != lo2) {
          true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
          true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = lo1 - 1;
        }
        // true case 2
        if (lo1 != up2) {
          // non empty
          true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo1 + 1;
          true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
        }

        // check emptiness of false case
        if ( (lo1 - lo2) % reg_steps[rs2] == 0) {
          false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
          false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
          false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo1;
          false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up1;
        }

      } else {
        // we cannot handle
        cannot_handle = true;
      }
    } else {
      // rs2 wrapped
      if (up1 < lo2 && up2 < lo1) {
        // true case
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
        true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

      } else if (lo1 == up1) {
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
        // true case 1
        if (lo1 != lo2) {
          // non empty
          true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
          true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = lo1 - 1;
        }
        // true case 2
        if (lo1 != up2) {
          // non empty
          true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo1 + 1;
          true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
        }

        // check emptiness of false case
        if ((lo1 - lo2) % reg_steps[rs2] == 0) {
          false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo1;
          false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up1;
          false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo1;
          false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up1;
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
      true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
      true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
      true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
      true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;

    } else if (lo2 == up2) {
      true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo2;
      true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up2;
      // true case 1
      if (lo2 != lo1) {
        // non empty
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = lo2 - 1;
      }
      // true case 2
      if (lo2 != up1) {
        // non empty
        true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo2 + 1;
        true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
      }

      // check emptiness of false case
      if ((lo2 - lo1) % reg_steps[rs1] == 0) {
        false_branch_rs1_minterval_los[false_branch_rs1_minterval_cnt]   = lo2;
        false_branch_rs1_minterval_ups[false_branch_rs1_minterval_cnt++] = up2;
        false_branch_rs2_minterval_los[false_branch_rs2_minterval_cnt]   = lo2;
        false_branch_rs2_minterval_ups[false_branch_rs2_minterval_cnt++] = up2;
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
void create_xor_mconstraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo1;
  uint64_t up1;
  uint64_t lo2;
  uint64_t up2;

  true_branch_rs1_minterval_cnt  = 0;
  true_branch_rs2_minterval_cnt  = 0;
  false_branch_rs1_minterval_cnt = 0;
  false_branch_rs2_minterval_cnt = 0;

  for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
    lo1 = lo1_p[i];
    up1 = up1_p[i];
    for (uint32_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
      lo2 = lo2_p[j];
      up2 = up2_p[j];
      cannot_handle = create_xor_true_false_constraints(lo1, up1, lo2, up2);
    }
  }

  if (cannot_handle) {
    // detected non-singleton interval intersection
    printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_equality_or_disequality() == EQ) {
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 1);
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 0);
      }
    } else {
      constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void create_xor_mconstraints_lptr(uint64_t lo1, uint64_t up1, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo2;
  uint64_t up2;

  true_branch_rs1_minterval_cnt  = 0;
  true_branch_rs2_minterval_cnt  = 0;
  false_branch_rs1_minterval_cnt = 0;
  false_branch_rs2_minterval_cnt = 0;

  for (uint32_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
    lo2 = lo2_p[j];
    up2 = up2_p[j];
    cannot_handle = create_xor_true_false_constraints(lo1, up1, lo2, up2);
  }

  if (cannot_handle) {
    // detected non-singleton interval intersection
    printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_equality_or_disequality() == EQ) {
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 1);
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 0);
      }
    } else {
      constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void create_xor_mconstraints_rptr(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, uint64_t lo2, uint64_t up2, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t lo1;
  uint64_t up1;

  true_branch_rs1_minterval_cnt  = 0;
  true_branch_rs2_minterval_cnt  = 0;
  false_branch_rs1_minterval_cnt = 0;
  false_branch_rs2_minterval_cnt = 0;

  for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
    lo1 = lo1_p[i];
    up1 = up1_p[i];
    cannot_handle = create_xor_true_false_constraints(lo1, up1, lo2, up2);
  }

  if (cannot_handle) {
    // detected non-singleton interval intersection
    printf("OUTPUT: detected non-singleton interval intersection at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_equality_or_disequality() == EQ) {
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 1);
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 0);
      }
    } else {
      constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      is_only_one_branch_reachable = true;
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    is_only_one_branch_reachable = true;
    take_branch(0, 0);
  } else {
    printf("OUTPUT: both branches unreachable!!! %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void backtrack_sltu() {
  uint64_t vaddr;

  vaddr = vaddrs[tc];

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      reg_data_type[vaddr]         = data_types[tc];
      reg_symb_type[vaddr]         = CONCRETE;
      registers[vaddr]             = values[tc];
      reg_mintervals_los[vaddr][0] = values[tc];
      reg_mintervals_ups[vaddr][0] = values[tc];
      reg_mintervals_cnts[vaddr]   = 1;
      reg_steps[vaddr]             = 1;
      reg_vaddrs_cnts[vaddr]       = 0;
      reg_asts[vaddr]              = 0;

      set_correction(vaddr, 0, 0, 0);

      // restoring mrcc
      mrcc = tcs[tc];

      if (vaddr != REG_FP) {
        if (vaddr != REG_SP) {
          // stop backtracking and try next case
          pc = pc + INSTRUCTIONSIZE;
          ic_sltu = ic_sltu + 1;

          reg_asts[vaddr] = (registers[vaddr] == 0) ? zero_node : one_node;
        }
      } else {
        if (ast_trace_cnt > most_recent_if_on_ast_trace) {
          ast_trace_cnt = most_recent_if_on_ast_trace;
        }
        most_recent_if_on_ast_trace = asts[tc];
      }
    }
  } else if (vaddr == NUMBEROFREGISTERS) {
    input_table.at(ast_nodes[asts[tc]].right_node) = values[tc];
  } else {
    if (ast_nodes[asts[tc]].type == VAR) {
      if (store_trace_ptrs[asts[tc]].size() > 1) {
        store_trace_ptrs[asts[tc]].pop_back();
      } else if (store_trace_ptrs[asts[tc]].size() == 1) {
        input_table.at(ast_nodes[asts[tc]].right_node) = asts[tcs[tc]];
        store_trace_ptrs[asts[tc]].pop_back();
      } else {
        printf("OUTPUT: sltu backtracking error at %x", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      if (store_trace_ptrs[asts[tc]].size() > 1) {
        store_trace_ptrs[asts[tc]].pop_back();
      } else if (store_trace_ptrs[asts[tc]].size() == 1) {
        store_trace_ptrs[asts[tc]].pop_back();
      } else {
        printf("OUTPUT: sltu backtracking error at %x", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    store_virtual_memory(pt, vaddr, tcs[tc]);
  }

  efree();
}

void backtrack_sd() {
  if (ast_nodes[asts[tc]].type == VAR) {
    if (store_trace_ptrs[asts[tc]].size() > 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else if (store_trace_ptrs[asts[tc]].size() == 1) {
      input_table.pop_back();
      symbolic_input_cnt = input_table.size();
      printf("OUT: *** input %llu undone \n", symbolic_input_cnt); // never happens in backtrack_sd
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      printf("OUTPUT: sd backtracking error at %x", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    if (store_trace_ptrs[asts[tc]].size() > 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else if (store_trace_ptrs[asts[tc]].size() == 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      printf("OUTPUT: sd backtracking error at %x", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }

  store_virtual_memory(pt, vaddrs[tc], tcs[tc]);

  efree();
}

void backtrack_ld() {
  // same as backtrack_sltu because it happens as a consequence of sltu
  if (ast_nodes[asts[tc]].type == VAR) {
    if (store_trace_ptrs[asts[tc]].size() > 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else if (store_trace_ptrs[asts[tc]].size() == 1) {
      input_table.at(ast_nodes[asts[tc]].right_node) = asts[tcs[tc]];
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      printf("OUTPUT: ld backtracking error at %x", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    if (store_trace_ptrs[asts[tc]].size() > 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else if (store_trace_ptrs[asts[tc]].size() == 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      printf("OUTPUT: ld backtracking error at %x", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }

  store_virtual_memory(pt, vaddrs[tc], tcs[tc]);

  efree();
}

void backtrack_ecall() {
  if (vaddrs[tc] == 0) {
    // backtracking malloc
    if (get_program_break(current_context) == mintervals_los[asts[tc]][0] + mintervals_ups[asts[tc]][0])
      set_program_break(current_context, mintervals_los[asts[tc]][0]);
    else {
      printf("OUTPUT: malloc backtracking error at %x", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking input
    input_table.pop_back();
    symbolic_input_cnt = input_table.size();
    printf("\nOUT: *** input %llu undone \n", symbolic_input_cnt);
    store_trace_ptrs[asts[tc]].pop_back();

    store_virtual_memory(pt, vaddrs[tc], tcs[tc]);

    // // backtracking read
    // rc = rc + 1;
    //
    // // record value, lower and upper bound
    // read_values[rc] = values[tc];
    // read_los[rc]    = mintervals_los[asts[tc]][0];
    // read_ups[rc]    = mintervals_ups[asts[tc]][0];
    //
    // store_virtual_memory(pt, vaddrs[tc], tcs[tc]);
  }

  efree();
}

void backtrack_trace(uint64_t* context) {
  uint64_t savepc;

  backtrack = 1;

  while (backtrack) {
    pc = pcs[tc];

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

  set_pc(context, pc);
}

// -------------------------- auxiliary functions ------------------------------
// auxiliary functions to deal with addition and
// multiplication when the conditions are failed
// -----------------------------------------------------------------------------

struct interval {
  uint64_t lo;
  uint64_t up;
};

bool compare_interval(interval i1, interval i2) {
  return (i1.lo > i2.lo);
}

bool are_step_intervals_overlapped(uint64_t lo1, uint64_t lo2, uint64_t step) {
  return ((lo1 - lo2) % step == 0) ? true : false;
}

void merge_intervals(std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t size, uint64_t step) {
  struct interval mint[size];

  for (size_t i = 0; i < size; i++) {
    mint[i].lo = lo[i];
    mint[i].up = up[i];
  }

  std::sort(mint, mint + size, compare_interval);

  size_t index = 1;
  bool is_overlapped;
  for (size_t i = 1; i < size; i++) {
    is_overlapped = false;
    for (size_t j = 0; j < index; j++) {
      if (mint[j].lo <= mint[i].up && are_step_intervals_overlapped(mint[j].lo, mint[i].lo, step)) {
        mint[j].lo = mint[i].lo;
        mint[j].up = std::max(mint[j].up, mint[i].up);
        is_overlapped = true;
      }
    }

    if (is_overlapped == false) {
      mint[index++] = mint[i];
    }
  }

  lo.clear();
  up.clear();
  for (size_t i = 0; i < index; i++) {
    lo.push_back(mint[i].lo);
    up.push_back(mint[i].up);
  }
}

void add_cnd_failure_rinterval(std::vector<uint64_t>& lo_res, std::vector<uint64_t>& up_res, uint128_t lo_1, uint128_t up_1, uint128_t lo_2, uint128_t up_2) {
  uint128_t lo = lo_1 + lo_2;
  uint128_t up = up_1 + up_2;
  uint64_t  gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
  if (lo <= UINT64_MAX_T) {
    // interval 1
    lo_res.push_back((uint64_t) lo);
    if (up <= UINT64_MAX_T) {
      // interval 1
      up_res.push_back((uint64_t) up);
    } else {
      uint64_t max = compute_upper_bound(lo, gcd_steps, UINT64_MAX_T); // safe cast
      if (lo - (max + gcd_steps) % gcd_steps == 0) {
        // mean both sub-interval can be represented as one wrapped.
        up_res.push_back((uint64_t) up % TWO_TO_THE_POWER_OF_64);
      } else {
        // interval 1
        up_res.push_back(max);
        // interval 2
        lo_res.push_back(max + gcd_steps);
        up_res.push_back((uint64_t) up % TWO_TO_THE_POWER_OF_64);
      }
    }
  } else {
    // one interval
    lo_res.push_back((uint64_t) lo % TWO_TO_THE_POWER_OF_64);
    up_res.push_back((uint64_t) up % TWO_TO_THE_POWER_OF_64);
  }
}

void handle_add_cnd_failure(std::vector<uint64_t>& mul_lo_rd, std::vector<uint64_t>& mul_up_rd, uint64_t i, uint64_t j) {
  uint64_t max_rs1;
  uint64_t max_rs2;
  if (reg_mintervals_los[rs1][i] > reg_mintervals_ups[rs1][i]) {
    // wrapped
    max_rs1 = compute_upper_bound(reg_mintervals_los[rs1][i], reg_steps[rs1], UINT64_MAX_T);
    if (reg_mintervals_los[rs2][j] > reg_mintervals_ups[rs2][j]) {
      // wrapped
      max_rs2 = compute_upper_bound(reg_mintervals_los[rs2][j], reg_steps[rs2], UINT64_MAX_T);
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], max_rs1, reg_mintervals_los[rs2][j], max_rs2);
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], max_rs1, max_rs2 + reg_steps[rs2], reg_mintervals_ups[rs2][j]);
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, max_rs1 + reg_steps[rs1], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][j], max_rs2);
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, max_rs1 + reg_steps[rs1], reg_mintervals_ups[rs1][i], max_rs2 + reg_steps[rs2], reg_mintervals_ups[rs2][j]);
    } else {
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], max_rs1, reg_mintervals_los[rs2][j], reg_mintervals_ups[rs2][j]);
      printf("--\n");
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, max_rs1 + reg_steps[rs1], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][j], reg_mintervals_ups[rs2][j]);
    }
  } else {
    if (reg_mintervals_los[rs2][j] > reg_mintervals_ups[rs2][j]) {
      // wrapped
      max_rs2 = compute_upper_bound(reg_mintervals_los[rs2][j], reg_steps[rs2], UINT64_MAX_T);
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][j], max_rs2);
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], max_rs2 + reg_steps[rs2], reg_mintervals_ups[rs2][j]);
    } else {
      add_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][j], reg_mintervals_ups[rs2][j]);
    }
  }
}

void mul_cnd_failure_rinterval(std::vector<uint64_t>& lo_res, std::vector<uint64_t>& up_res, uint128_t lo_1, uint128_t up_1, uint128_t k, uint64_t step) {
  uint128_t lo = lo_1 * k;
  uint128_t up = up_1 * k;
  step         = step * k;
  if (lo <= UINT64_MAX_T) {
    // interval 1
    lo_res.push_back((uint64_t) lo);
    if (up <= UINT64_MAX_T) {
      // interval 1
      up_res.push_back((uint64_t) up);
    } else {
      uint64_t max = compute_upper_bound(lo, step, UINT64_MAX_T); // safe cast
      if (lo - (max + step) % step == 0) {
        // mean both sub-interval can be represented as one wrapped.
        up_res.push_back((uint64_t) up % TWO_TO_THE_POWER_OF_64);
      } else {
        // interval 1
        up_res.push_back(max); // cast is safe
        // interval 2
        lo_res.push_back(max + step);
        up_res.push_back((uint64_t) up % TWO_TO_THE_POWER_OF_64);
      }
    }
  } else {
    // one interval
    lo_res.push_back((uint64_t) lo % TWO_TO_THE_POWER_OF_64);
    up_res.push_back((uint64_t) up % TWO_TO_THE_POWER_OF_64);
  }
}

void handle_mul_cnd_failure(std::vector<uint64_t>& mul_lo_rd, std::vector<uint64_t>& mul_up_rd, uint64_t lo, uint64_t up, uint64_t step, uint64_t k) {
  uint64_t max_reg;
  if (lo > up) {
    // wrapped
    max_reg = compute_upper_bound(lo, step, UINT64_MAX_T);
    mul_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, lo, max_reg, k, step);
    mul_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, max_reg + step, up, k, step);
  } else {
    mul_cnd_failure_rinterval(mul_lo_rd, mul_up_rd, lo, up, k, step);
  }
}

// -------------------------------- propagation --------------------------------

uint64_t compute_add(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc) {
  uint64_t addend;
  bool is_assigned = false;

  if (detect_sym_operand(old_ast_tc) == LEFT) {
    crt_operand_ast_tc = right_operand_ast_tc;
    sym_operand_ast_tc = left_operand_ast_tc;
    addend = mintervals_los[crt_operand_ast_tc][0];
  } else {
    crt_operand_ast_tc = left_operand_ast_tc;
    sym_operand_ast_tc = right_operand_ast_tc;
    addend = mintervals_los[crt_operand_ast_tc][0];
  }

  for (uint32_t i = 0; i < mintervals_los[sym_operand_ast_tc].size(); i++) {
    propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][i] + addend;
    propagated_minterval_up[i] = mintervals_ups[sym_operand_ast_tc][i] + addend;
  }

  uint64_t ast_ptr = add_ast_node(ADD, sym_operand_ast_tc, crt_operand_ast_tc, mintervals_los[sym_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= store_trace_ptrs[old_ast_tc][i]) {
      store_symbolic_memory(pt, vaddrs[store_trace_ptrs[old_ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
      is_assigned = true;
    }
  }

  return ast_ptr;
}

uint64_t compute_sub(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc) {
  uint64_t sub_lo;
  uint64_t sub_up;
  uint64_t sub_tmp;
  bool is_assigned = false;

  if (is_symbolic_value(VALUE_T, mintervals_los[left_operand_ast_tc].size(), mintervals_los[left_operand_ast_tc][0], mintervals_ups[left_operand_ast_tc][0])) {
    sub_lo = mintervals_los[right_operand_ast_tc][0];
    sub_up = mintervals_ups[right_operand_ast_tc][0];
    for (uint32_t i = 0; i < mintervals_los[left_operand_ast_tc].size(); i++) {
      propagated_minterval_lo[i] = mintervals_los[left_operand_ast_tc][i] - sub_up;
      propagated_minterval_up[i] = mintervals_ups[left_operand_ast_tc][i] - sub_lo;
    }

    uint64_t ast_ptr = add_ast_node(SUB, left_operand_ast_tc, right_operand_ast_tc, mintervals_los[left_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_ast_tcs[left_operand_ast_tc]);

    for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
      stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= store_trace_ptrs[old_ast_tc][i]) {
        store_symbolic_memory(pt, vaddrs[store_trace_ptrs[old_ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
        is_assigned = true;
      }
    }

    return ast_ptr;
  } else {
    sub_lo = mintervals_los[left_operand_ast_tc][0];
    sub_up = mintervals_ups[left_operand_ast_tc][0];
    for (uint32_t i = 0; i < mintervals_los[right_operand_ast_tc].size(); i++) {
      sub_tmp                    = sub_lo - mintervals_ups[right_operand_ast_tc][i];
      propagated_minterval_up[i] = sub_up - mintervals_los[right_operand_ast_tc][i];
      propagated_minterval_lo[i] = sub_tmp;
    }

    uint64_t ast_ptr = add_ast_node(SUB, left_operand_ast_tc, right_operand_ast_tc, mintervals_los[right_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc]);

    for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
      stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= store_trace_ptrs[old_ast_tc][i]) {
        store_symbolic_memory(pt, vaddrs[store_trace_ptrs[old_ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
        is_assigned = true;
      }
    }

    return ast_ptr;
  }
}

uint64_t compute_mul(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc) {
  bool cnd;
  uint64_t multiplier;
  bool is_assigned = false;

  if (detect_sym_operand(old_ast_tc) == LEFT) {
    crt_operand_ast_tc = right_operand_ast_tc;
    sym_operand_ast_tc = left_operand_ast_tc;
    multiplier = mintervals_los[crt_operand_ast_tc][0];
  } else {
    crt_operand_ast_tc = left_operand_ast_tc;
    sym_operand_ast_tc = right_operand_ast_tc;
    multiplier = mintervals_los[crt_operand_ast_tc][0];
  }

  for (size_t i = 0; i < mintervals_los[sym_operand_ast_tc].size(); i++) {
    cnd = mul_condition(mintervals_los[sym_operand_ast_tc][i], mintervals_ups[sym_operand_ast_tc][i], multiplier);
    if (cnd == true) {
      propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][i] * multiplier;
      propagated_minterval_up[i] = mintervals_ups[sym_operand_ast_tc][i] * multiplier;
    } else {
      printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }

  uint64_t ast_ptr = add_ast_node(MUL, sym_operand_ast_tc, crt_operand_ast_tc, mintervals_los[sym_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= store_trace_ptrs[old_ast_tc][i]) {
      store_symbolic_memory(pt, vaddrs[store_trace_ptrs[old_ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
      is_assigned = true;
    }
  }

  return ast_ptr;
}

uint64_t compute_divu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc) {
  uint64_t divisor = mintervals_los[right_operand_ast_tc][0];
  bool is_assigned = false;

  if (mintervals_los[left_operand_ast_tc].size() > 1) {
    printf("OUTPUT: unsupported minterval divu %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  // interval semantics of divu
  for (uint32_t i = 0; i < mintervals_los[left_operand_ast_tc].size(); i++) {
    if (mintervals_los[left_operand_ast_tc][i] > mintervals_ups[left_operand_ast_tc][i]) {
      // rs1 constraint is wrapped: [lo, UINT64_MAX_T], [0, up]
      // lo/divisor == up/divisor (or) up/divisor + step_rd
      if (mintervals_los[left_operand_ast_tc][i]/divisor != mintervals_ups[left_operand_ast_tc][i]/divisor)
        if (mintervals_los[left_operand_ast_tc][i]/divisor > mintervals_ups[left_operand_ast_tc][i]/divisor + steps[old_ast_tc]) {
          printf("OUTPUT: wrapped divison results two intervals at %x \n", pc);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

      uint64_t max = compute_upper_bound(mintervals_los[left_operand_ast_tc][i], steps[left_operand_ast_tc], UINT64_MAX_T);
      propagated_minterval_lo[i] = (max + steps[left_operand_ast_tc]) / divisor;
      propagated_minterval_up[i] = max / divisor;
    } else {
      propagated_minterval_lo[i] = mintervals_los[left_operand_ast_tc][i] / divisor;
      propagated_minterval_up[i] = mintervals_ups[left_operand_ast_tc][i] / divisor;
    }
  }

  uint64_t ast_ptr = add_ast_node(DIVU, left_operand_ast_tc, right_operand_ast_tc, mintervals_los[left_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_ast_tcs[left_operand_ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= store_trace_ptrs[old_ast_tc][i]) {
      store_symbolic_memory(pt, vaddrs[store_trace_ptrs[old_ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
      is_assigned = true;
    }
  }

  return ast_ptr;
}

uint64_t compute_remu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc) {
  uint64_t divisor;
  uint64_t step;
  bool is_assigned = false;

  if (mintervals_los[left_operand_ast_tc].size() > 1) {
    printf("OUTPUT: unsupported minterval 5 %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  divisor = mintervals_los[right_operand_ast_tc][0];
  step    = steps[left_operand_ast_tc];

  for (uint32_t i = 0; i < mintervals_los[left_operand_ast_tc].size(); i++) {
    if (mintervals_los[left_operand_ast_tc][i] <= mintervals_ups[left_operand_ast_tc][i]) {
      // rs1 interval is not wrapped
      int rem_typ = remu_condition(mintervals_los[left_operand_ast_tc][i], mintervals_ups[left_operand_ast_tc][i], step, divisor);
      if (rem_typ == 0) {
        propagated_minterval_lo[i] = mintervals_los[left_operand_ast_tc][i] % divisor;
        propagated_minterval_up[i] = mintervals_ups[left_operand_ast_tc][i] % divisor;
      } else if (rem_typ == 1) {
        printf("OUTPUT: modulo results two intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (rem_typ == 2) {
        uint64_t gcd_step_k = gcd(step, divisor);
        propagated_minterval_lo[i] = mintervals_los[left_operand_ast_tc][i]%divisor - ((mintervals_los[left_operand_ast_tc][i]%divisor) / gcd_step_k) * gcd_step_k;
        propagated_minterval_up[i] = compute_upper_bound(mintervals_los[left_operand_ast_tc][i], gcd_step_k, divisor - 1);
        step  = gcd_step_k;
      } else {
        printf("OUTPUT: modulo results many intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

    } else if (is_power_of_two(divisor)) {
      // rs1 interval is wrapped
      uint64_t gcd_step_k = gcd(step, divisor);
      uint64_t lcm        = (step * divisor) / gcd_step_k;

      if (mintervals_ups[left_operand_ast_tc][i] - mintervals_los[left_operand_ast_tc][i] < lcm - step) {
        printf("OUTPUT: wrapped modulo results many intervals at %x \n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      propagated_minterval_lo[i] = mintervals_los[left_operand_ast_tc][i]%divisor - ((mintervals_los[left_operand_ast_tc][i]%divisor) / gcd_step_k) * gcd_step_k;
      propagated_minterval_up[i] = compute_upper_bound(mintervals_los[left_operand_ast_tc][i], gcd_step_k, divisor - 1);
      step  = gcd_step_k;
    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x \n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }

  uint64_t ast_ptr = add_ast_node(REMU, left_operand_ast_tc, right_operand_ast_tc, mintervals_los[left_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, step, involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_ast_tcs[left_operand_ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= store_trace_ptrs[old_ast_tc][i]) {
      store_symbolic_memory(pt, vaddrs[store_trace_ptrs[old_ast_tc][i]], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0);
      is_assigned = true;
    }
  }

  return ast_ptr;
}

uint64_t recompute_operation(uint8_t op, uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc) {
  switch (op) {
    case ADD:
      return compute_add(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc);
    case SUB:
      return compute_sub(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc);
    case MUL:
      return compute_mul(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc);
    case DIVU:
      return compute_divu(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc);
    case REMU:
      return compute_remu(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc);
  }
}

uint64_t recompute_expression(uint64_t ast_tc) {
  uint64_t left_operand_ast_tc;
  uint64_t right_operand_ast_tc;
  uint64_t ast_ptr;

  if (ast_nodes[ast_tc].type == VAR)
    return input_table[ast_nodes[ast_tc].right_node];

  if (detect_sym_operand(ast_tc) == LEFT) {
    left_operand_ast_tc  = recompute_expression(ast_nodes[ast_tc].left_node);
    right_operand_ast_tc = ast_nodes[ast_tc].right_node;
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc);
  } else {
    right_operand_ast_tc = recompute_expression(ast_nodes[ast_tc].right_node);
    left_operand_ast_tc  = ast_nodes[ast_tc].left_node;
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc);
  }
}

// --------------------------- conditional expression --------------------------

bool match_addi_instruction() {
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

bool match_sub_instruction(uint64_t prev_instr_rd) {
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

uint64_t check_conditional_type_equality_or_disequality() {
  uint64_t saved_pc = pc;
  uint64_t op_code;
  uint64_t funct_3;

  pc = saved_pc + INSTRUCTIONSIZE;
  fetch();
  op_code = get_opcode(ir);
  funct_3 = get_funct3(ir);
  if (op_code == OP_IMM && funct_3 == F3_ADDI) {
    pc = saved_pc;
    return EQ;
  } else if (op_code == OP_OP && funct_3 == F3_SLTU) {
    pc = saved_pc;
    return DEQ;
  } else {
    printf("OUTPUT: XOR instruction is incorrectly used at %x \n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  return 0;
}

uint64_t check_conditional_type_lte_or_gte() {
  uint64_t saved_pc = pc;

  pc = saved_pc + INSTRUCTIONSIZE;
  fetch();
  if (get_opcode(ir) == OP_IMM && match_addi_instruction()) {
    uint64_t rd_ = get_rd(ir);
    pc = saved_pc + 2 * INSTRUCTIONSIZE;
    fetch();
    if (get_opcode(ir) == OP_OP && match_sub_instruction(rd_)) {
      pc = saved_pc;
      return LGTE;
    }
  }

  pc = saved_pc;
  return LT;
}