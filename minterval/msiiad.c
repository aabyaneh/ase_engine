#include "msiiad.h"

typedef unsigned __int128 uint128_t;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t MSIIAD               = 9;
uint64_t MAX_TRACE_LENGTH     = 10000000;
uint64_t MAX_SD_TO_NUM        = 2001;
uint64_t MAX_NUM_OF_INTERVALS = 2001;
uint64_t MAX_NUM_OF_OP_VADDRS = 100;
uint64_t TWO_TO_THE_POWER_OF_32;

uint128_t UINT64_MAX_VALUE    = 18446744073709551615U;
uint128_t TWO_TO_THE_POWER_OF_64;

// ---------------------------------------------
// --------------- the trace
// ---------------------------------------------

uint64_t  tc              = 0;             // trace counter
uint64_t* pcs             = (uint64_t*) 0; // trace of program counter values
uint64_t* tcs             = (uint64_t*) 0; // trace of trace counters to previous values
uint64_t* vaddrs          = (uint64_t*) 0; // trace of virtual addresses

// ---------------------------------------------
// --------------- propagation trace
// ---------------------------------------------

uint64_t* mr_sds          = (uint64_t*) 0; // the tc of most recent store to a memory address

// propagation from right to left
std::vector<std::vector<uint64_t> > forward_propagated_to_tcs(MAX_TRACE_LENGTH);

// propagation from left to right (chain)
std::vector<std::vector<uint64_t> > ld_from_tcs(MAX_TRACE_LENGTH);

// temporary data-structure to pass values targeting propagations
std::vector<uint64_t> propagated_minterval_lo(MAX_NUM_OF_INTERVALS);
std::vector<uint64_t> propagated_minterval_up(MAX_NUM_OF_INTERVALS);
uint32_t propagated_minterval_cnt = 0;
uint64_t propagated_minterval_step;

// ---------------------------------------------
// --------------- read trace
// ---------------------------------------------

uint64_t  rc          = 0;              // read counter
uint64_t* read_values = (uint64_t*) 0;
uint64_t* read_los    = (uint64_t*) 0;
uint64_t* read_ups    = (uint64_t*) 0;

// ---------------------------------------------
// --------------- memory trace
// ---------------------------------------------

uint32_t  VALUE_T         = 0;
uint32_t  POINTER_T       = 1;
uint32_t  INPUT_T         = 2;

uint64_t* values          = (uint64_t*) 0; // trace of values
uint64_t* data_types      = (uint64_t*) 0; // memory range (or) value integer interval
uint64_t* steps           = (uint64_t*) 0; // incrementing step of the value intervals
uint64_t* addsub_corrs    = (uint64_t*) 0; // corrections
uint64_t* muldivrem_corrs = (uint64_t*) 0; // corrections
uint64_t* corr_validitys  = (uint64_t*) 0; // corrections
bool*     hasmns          = (bool*) 0;     // corrections

std::vector<std::vector<uint64_t> > mintervals_los(MAX_TRACE_LENGTH);
std::vector<std::vector<uint64_t> > mintervals_ups(MAX_TRACE_LENGTH);

// ---------------------------------------------
// --------------- registers
// ---------------------------------------------

std::vector<std::vector<uint64_t> > reg_mintervals_los(NUMBEROFREGISTERS);
std::vector<std::vector<uint64_t> > reg_mintervals_ups(NUMBEROFREGISTERS);
uint32_t* reg_mintervals_cnts = (uint32_t*) 0;
uint64_t* reg_steps           = (uint64_t*) 0; // incrementing step of the register's value interval
uint32_t* reg_data_type       = (uint32_t*) 0; // memory range or value integer interval
uint32_t* reg_symb_type       = (uint32_t*) 0; // CONCRETE (or) SYMBOLIC
uint32_t  CONCRETE            = 0;
uint32_t  SYMBOLIC            = 2;
bool*     reg_hasmn           = (bool*) 0;     // has minuend?
uint64_t* reg_addsub_corr     = (uint64_t*) 0; // correction
uint64_t* reg_muldivrem_corr  = (uint64_t*) 0; // correction
uint64_t* reg_corr_validity   = (uint64_t*) 0; // correction
uint64_t  MUL_T               = 3;             // correction
uint64_t  DIVU_T              = 4;             // correction
uint64_t  REMU_T              = 5;             // correction
uint64_t  MUL_T_FALSE         = 11;            // correction

std::vector<std::vector<uint64_t> > reg_vaddrs(NUMBEROFREGISTERS); // virtual addresses of expression operands
uint32_t* reg_vaddrs_cnts     = (uint32_t*) 0;

// ---------------------------------------------
// --------------- branch evaluation
// ---------------------------------------------

std::vector<uint64_t>  zero_v (1, 0);
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

uint64_t* is_inputs              = (uint64_t*) 0;
std::vector<uint64_t> input_table;

// ---------------------------------------------
// --------------- testing
// ---------------------------------------------

bool IS_TEST_MODE = false;
std::ofstream output_results;

// ---------------------------------------------
// --------------- pse (probabilistic symbolic execution)
// ---------------------------------------------

struct node {
  uint8_t  type;
  uint64_t left_node;
  uint64_t right_node;
};

uint8_t      CONST = 0, VAR = 1, ADDI = 2, ADD = 3, SUB = 4, MUL = 5, DIVU = 6, REMU = 7, ILT = 8, IGTE = 9, IEQ = 10, INEQ = 11;
uint64_t     MAX_NODE_TRACE_LENGTH = 2 * MAX_TRACE_LENGTH;
uint64_t     tree_tc = 0;
struct node* pse_ast_nodes;
uint64_t*    pse_asts;
uint64_t*    reg_pse_ast;
uint64_t     zero_node;
uint64_t     one_node;
std::vector<std::string> pse_variables_per_path;
std::vector<std::string> pse_variables_per_multi_path;
std::vector<uint64_t>    path_condition;
std::vector<uint64_t>    false_branches;
std::vector<std::string> traversed_path_condition_elements;
std::string              path_condition_string;

uint64_t pse_operation(uint8_t typ, uint64_t left_node, uint64_t right_node) {
  tree_tc++;

  if (tree_tc > MAX_NODE_TRACE_LENGTH) {
    printf("OUTPUT: MAX_NODE_TRACE_LENGTH reached %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  pse_ast_nodes[tree_tc].type       = typ;
  pse_ast_nodes[tree_tc].left_node  = left_node;
  pse_ast_nodes[tree_tc].right_node = right_node;

  return tree_tc;
}

// -------- engine parameters
// PSE = true means probabilistic symbolic execution is enabled
bool PSE = true;
// PSE_WRITE = true means write the queries in output
bool PSE_WRITE = false;
// PER_PATH = false means generate pse variables targeting disjunction of all paths
// PER_PATH = true  means generate pse variables targeting one under analysis path
bool PER_PATH = false;
// -------- modes management
// mode == 1 means complete theory of intervals
// mode != 1 means approximated theory of intervals + pse
uint8_t  MODE = 1;
uint64_t tc_before_changing_mode = 0;

void upgrade_mode(std::string message) {
  if (MODE == 1) {
    printf("OUTPUT: %s at %x\n", pc - entry_point);
    tc_before_changing_mode = tc;
    MODE = 2;
  }
}

void downgrade_mode() {
  MODE = 1;
}

// ------------------------- INITIALIZATION ------------------------

void init_symbolic_engine() {
  pcs                  = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  tcs                  = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  values               = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  data_types           = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  steps                = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  vaddrs               = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  addsub_corrs         = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  muldivrem_corrs      = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  corr_validitys       = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  hasmns               = (bool*)     malloc(MAX_TRACE_LENGTH  * sizeof(bool));
  mr_sds               = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));

  read_values          = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  read_los             = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  read_ups             = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));

  is_inputs            = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));

  reg_data_type        = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_steps            = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_symb_type        = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_hasmn            = (bool*)     zalloc(NUMBEROFREGISTERS * sizeof(bool));
  reg_addsub_corr      = (uint64_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_muldivrem_corr   = (uint64_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_corr_validity    = (uint64_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_vaddrs_cnts      = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_mintervals_cnts  = (uint32_t*) malloc(NUMBEROFREGISTERS * sizeof(uint32_t));

  if (PSE) {
    pse_ast_nodes        = (struct node*) malloc(MAX_NODE_TRACE_LENGTH  * sizeof(struct node*));
    pse_asts             = (uint64_t*)    malloc(MAX_TRACE_LENGTH       * sizeof(uint64_t));
    reg_pse_ast          = (uint64_t*)    malloc(NUMBEROFREGISTERS      * sizeof(uint64_t));
    zero_node            = pse_operation(CONST, 0, 0);
    one_node             = pse_operation(CONST, 0, 1);
    reg_pse_ast[REG_ZR]  = zero_node;
    reg_pse_ast[REG_FP]  = zero_node;
    pse_asts[0]          = zero_node;
    false_branches.reserve(MAX_TRACE_LENGTH);
    path_condition.reserve(MAX_TRACE_LENGTH);
    path_condition_string.reserve(MAX_TRACE_LENGTH);
  }

  for (size_t i = 0; i < NUMBEROFREGISTERS; i++) {
    reg_steps[i]           = 1;
    reg_mintervals_cnts[i] = 1;

    reg_mintervals_los[i].resize(MAX_NUM_OF_INTERVALS);
    reg_mintervals_ups[i].resize(MAX_NUM_OF_INTERVALS);

    reg_vaddrs[i].resize(MAX_NUM_OF_OP_VADDRS);
  }

  pcs[0]             = 0;
  tcs[0]             = 0;
  values[0]          = 0;
  data_types[0]      = 0;
  steps[0]           = 0;
  vaddrs[0]          = 0;
  addsub_corrs[0]    = 0;
  muldivrem_corrs[0] = 0;
  corr_validitys[0]  = 0;
  hasmns[0]          = 0;
  mr_sds[0]          = 0;
  is_inputs[0]       = 0;

  mintervals_los[0].push_back(0);
  mintervals_ups[0].push_back(0);

  TWO_TO_THE_POWER_OF_32 = two_to_the_power_of(32);
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
//                                operations
////////////////////////////////////////////////////////////////////////////////

void constrain_lui() {
  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;

    // interval semantics of lui
    reg_mintervals_los[rd][0] = imm << 12;
    reg_mintervals_ups[rd][0] = imm << 12;
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

    // rd has no constraint
    set_correction(rd, 0, 0, 0, 0, 0);

    if (PSE) reg_pse_ast[rd] = pse_operation(CONST, 0, imm << 12);
  }
}

void constrain_addi() {
  if (rd == REG_ZR)
    return;

  if (reg_data_type[rs1] == POINTER_T) {
    reg_data_type[rd]         = reg_data_type[rs1];
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

    // rd has no constraint if rs1 is memory range
    set_correction(rd, 0, 0, 0, 0, 0);

    return;
  }

  reg_data_type[rd] = VALUE_T;

  // interval semantics of addi
  if (reg_symb_type[rs1] == SYMBOLIC) {
      // rd inherits rs1 constraint
      set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1] + imm, reg_muldivrem_corr[rs1],
        (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);
      set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

      reg_steps[rd] = reg_steps[rs1];
      for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
        reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] + imm;
        reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] + imm;
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];

  } else {
    // rd has no constraint if rs1 has none
    set_correction(rd, 0, 0, 0, 0, 0);

    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] + imm;
    reg_mintervals_ups[rd][0] = reg_mintervals_los[rd][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
  }

  if (PSE) reg_pse_ast[rd] = pse_operation(ADDI, reg_pse_ast[rs1] , pse_operation(CONST, 0, imm));
}

bool constrain_add_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      // adding two pointers is undefined
      printf("OUTPUT: undefined addition of two pointers at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_data_type[rd]         = reg_data_type[rs1];
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

    // rd has no constraint if rs1 is memory range
    set_correction(rd, 0, 0, 0, 0, 0);

    return 1;
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]         = reg_data_type[rs2];
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

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

    reg_data_type[rd] = VALUE_T;

    // interval semantics of add
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // we cannot keep track of more than one constraint for add but
        // need to warn about their earlier presence if used in comparisons
        set_correction(rd, SYMBOLIC, 0, 0, 0, 10);
        uint32_t rd_addr_idx = reg_vaddrs_cnts[rs1] + reg_vaddrs_cnts[rs2];
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);
        set_vaddrs(rd, reg_vaddrs[rs2], reg_vaddrs_cnts[rs1], rd_addr_idx);

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

      } else {
        // rd inherits rs1 constraint since rs2 has none
        set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1] + reg_mintervals_los[rs2][0], reg_muldivrem_corr[rs1],
          (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

        reg_steps[rd] = reg_steps[rs1];
        for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] + reg_mintervals_los[rs2][0];
          reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] + reg_mintervals_ups[rs2][0];
        }
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      set_correction(rd, reg_symb_type[rs2], 0, reg_addsub_corr[rs2] + reg_mintervals_los[rs1][0], reg_muldivrem_corr[rs2],
        (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      set_vaddrs(rd, reg_vaddrs[rs2], 0, reg_vaddrs_cnts[rs2]);

      reg_steps[rd] = reg_steps[rs2];
      for (uint32_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][0] + reg_mintervals_los[rs2][i];
        reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][0] + reg_mintervals_ups[rs2][i];
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_correction(rd, 0, 0, 0, 0, 0);

      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] + reg_mintervals_los[rs2][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_los[rd][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
    }

    if (PSE) reg_pse_ast[rd] = pse_operation(ADD, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
  }
}

bool constrain_sub_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      if (reg_mintervals_los[rs1][0] == reg_mintervals_los[rs2][0])
        if (reg_mintervals_ups[rs1][0] == reg_mintervals_ups[rs2][0]) {
          reg_data_type[rd] = POINTER_T;
          reg_mintervals_los[rd][0] = registers[rd];
          reg_mintervals_ups[rd][0] = registers[rd];
          reg_mintervals_cnts[rd]   = 1;
          reg_steps[rd]             = 1;
          reg_vaddrs_cnts[rd]       = 0;

          // rd has no constraint if rs1 and rs2 are memory range
          set_correction(rd, 0, 0, 0, 0, 0);

          return 1;
        }

      // subtracting incompatible pointers
      throw_exception(EXCEPTION_INVALIDADDRESS, 0);

      return 1;
    } else {
      reg_data_type[rd] = reg_data_type[rs1];
      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;

      // rd has no constraint if rs1 is memory range
      set_correction(rd, 0, 0, 0, 0, 0);

      return 1;
    }
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd] = reg_data_type[rs2];
    reg_mintervals_los[rd][0] = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

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

    reg_data_type[rd] = VALUE_T;

    // interval semantics of sub
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // we cannot keep track of more than one constraint for sub but
        // need to warn about their earlier presence if used in comparisons
        set_correction(rd, SYMBOLIC, 0, 0, 0, 10);
        uint32_t rd_addr_idx = reg_vaddrs_cnts[rs1] + reg_vaddrs_cnts[rs2];
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);
        set_vaddrs(rd, reg_vaddrs[rs2], reg_vaddrs_cnts[rs1], rd_addr_idx);

        if (reg_mintervals_cnts[rs1] > 1 || reg_mintervals_cnts[rs2] > 1) {
          printf("OUTPUT: unsupported minterval 2 %x \n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        uint64_t gcd_steps = gcd(reg_steps[rs1], reg_steps[rs2]);
        if (check_incompleteness(gcd_steps) == true) {
          printf("%s\n", " steps in subtraction are not consistent");
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

      } else {
        // rd inherits rs1 constraint since rs2 has none
        set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1] - reg_mintervals_los[rs2][0], reg_muldivrem_corr[rs1],
          (reg_corr_validity[rs1] == 0) ? MUL_T : reg_corr_validity[rs1]);
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

        reg_steps[rd] = reg_steps[rs1];
        sub_lo = reg_mintervals_los[rs2][0];
        sub_up = reg_mintervals_ups[rs2][0];
        for (uint32_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] - sub_up;
          reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] - sub_lo;
        }
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      if (reg_hasmn[rs2]) {
        // rs2 constraint has already minuend and can have another minuend
        set_correction(rd, reg_symb_type[rs2], 0, reg_mintervals_los[rs1][0] - reg_addsub_corr[rs2], reg_muldivrem_corr[rs2],
          (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      } else {
        // rd inherits rs2 constraint since rs1 has none
        set_correction(rd, reg_symb_type[rs2], 1, reg_mintervals_los[rs1][0] - reg_addsub_corr[rs2], reg_muldivrem_corr[rs2],
          (reg_corr_validity[rs2] == 0) ? MUL_T : reg_corr_validity[rs2]);
      }

      set_vaddrs(rd, reg_vaddrs[rs2], 0, reg_vaddrs_cnts[rs2]);

      reg_steps[rd] = reg_steps[rs2];
      sub_lo = reg_mintervals_los[rs1][0];
      sub_up = reg_mintervals_ups[rs1][0];
      for (uint32_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        sub_tmp                   = sub_lo - reg_mintervals_ups[rs2][i];
        reg_mintervals_ups[rd][i] = sub_up - reg_mintervals_los[rs2][i];
        reg_mintervals_los[rd][i] = sub_tmp;
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_correction(rd, 0, 0, 0, 0, 0);

      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] - reg_mintervals_ups[rs2][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_los[rd][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;
    }

    if (PSE) reg_pse_ast[rd] = pse_operation(SUB, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
  }
}

void constrain_mul() {
  uint64_t mul_lo;
  uint64_t mul_up;
  bool     cnd;

  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;

    // interval semantics of mul
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        printf("OUTPUT: detected non-linear expression in mul at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else if (reg_hasmn[rs1]) {
        // correction does not work anymore
        printf("OUTPUT: correction does not work anymore e.g. (1 - [.]) * 10 at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1], reg_mintervals_los[rs2][0], reg_corr_validity[rs1] + MUL_T);
        set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

        bool cnd;
        std::vector<uint64_t> mul_lo_rd;
        std::vector<uint64_t> mul_up_rd;
        for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          cnd = mul_condition(reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_mintervals_los[rs2][0]);
          if (cnd == true) {
            mul_lo_rd.push_back(reg_mintervals_los[rs1][i] * reg_mintervals_los[rs2][0]);
            mul_up_rd.push_back(reg_mintervals_ups[rs1][i] * reg_mintervals_ups[rs2][0]);
          } else {
            handle_mul_cnd_failure(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], reg_steps[rs1], reg_mintervals_los[rs2][0]);
            reg_corr_validity[rd] = MUL_T_FALSE;
          }
        }

        reg_steps[rd] = reg_steps[rs1] * reg_mintervals_los[rs2][0];
        for (size_t i = 0; i < mul_lo_rd.size(); i++) {
          reg_mintervals_los[rd][i] = mul_lo_rd[i];
          reg_mintervals_ups[rd][i] = mul_up_rd[i];
        }
        reg_mintervals_cnts[rd] = mul_lo_rd.size();

      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      if (reg_hasmn[rs2]) {
        // correction does not work anymore
        printf("OUTPUT: correction does not work anymore e.g. 10 * (1 - [.]) at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs2 constraint since rs1 has none
        // assert: rs1 interval is singleton
        set_correction(rd, reg_symb_type[rs2], 0, reg_addsub_corr[rs2], reg_mintervals_los[rs1][0], reg_corr_validity[rs2] + MUL_T);
        set_vaddrs(rd, reg_vaddrs[rs2], 0, reg_vaddrs_cnts[rs2]);

        bool cnd;
        std::vector<uint64_t> mul_lo_rd;
        std::vector<uint64_t> mul_up_rd;
        for (size_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
          cnd = mul_condition(reg_mintervals_los[rs2][i], reg_mintervals_ups[rs2][i], reg_mintervals_los[rs1][0]);
          if (cnd == true) {
            mul_lo_rd.push_back(reg_mintervals_los[rs2][i] * reg_mintervals_los[rs1][0]);
            mul_up_rd.push_back(reg_mintervals_ups[rs2][i] * reg_mintervals_ups[rs1][0]);
          } else {
            handle_mul_cnd_failure(mul_lo_rd, mul_up_rd, reg_mintervals_los[rs2][i], reg_mintervals_ups[rs2][i], reg_steps[rs2], reg_mintervals_los[rs1][0]);
            reg_corr_validity[rd] = MUL_T_FALSE;
          }
        }

        reg_steps[rd] = reg_steps[rs2] * reg_mintervals_los[rs1][0];
        for (size_t i = 0; i < mul_lo_rd.size(); i++) {
          reg_mintervals_los[rd][i] = mul_lo_rd[i];
          reg_mintervals_ups[rd][i] = mul_up_rd[i];
        }
        reg_mintervals_cnts[rd] = mul_lo_rd.size();

      }
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      set_correction(rd, 0, 0, 0, 0, 0);

      reg_steps[rd]             = 1;
      reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] * reg_mintervals_los[rs2][0];
      reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0] * reg_mintervals_ups[rs2][0];
      reg_mintervals_cnts[rd]   = 1;
      reg_vaddrs_cnts[rd]       = 0;
    }

    if (PSE) reg_pse_ast[rd] = pse_operation(MUL, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
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
          printf("OUTPUT: unsupported minterval 4 %x \n", pc - entry_point);
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

          } else if (reg_hasmn[rs1]) {
            // correction does not work anymore
            printf("OUTPUT: correction does not work anymore e.g. (1 - [.]) / 10 at %x\n", pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

          } else {
            // rd inherits rs1 constraint since rs2 has none
            // assert: rs2 interval is singleton
            set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1], reg_mintervals_los[rs2][0], reg_corr_validity[rs1] + DIVU_T);
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
        } else if (reg_symb_type[rs2] == SYMBOLIC) {
          printf("OUTPUT: detected division of constant by interval at %x\n", pc - entry_point);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

        } else {
          // rd has no constraint if both rs1 and rs2 have no constraints
          set_correction(rd, 0, 0, 0, 0, 0);

          reg_mintervals_los[rd][0] = div_lo;
          reg_mintervals_ups[rd][0] = div_up;
          reg_mintervals_cnts[rd]   = 1;
          reg_steps[rd]             = 1;
          reg_vaddrs_cnts[rd]       = 0;
        }

        if (PSE) reg_pse_ast[rd] = pse_operation(DIVU, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
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

      set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1], reg_mintervals_los[rs2][0], reg_corr_validity[rs1] + REMU_T);
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

      set_correction(rd, reg_symb_type[rs1], 0, reg_addsub_corr[rs1], reg_mintervals_los[rs2][0], reg_corr_validity[rs1] + REMU_T);
      set_vaddrs(rd, reg_vaddrs[rs1], 0, reg_vaddrs_cnts[rs1]);

    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (reg_hasmn[rs1]) {
      // correction does not work anymore
      printf("OUTPUT: correction does not work anymore e.g. (1 - [.]) mod 10 at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_mintervals_los[rd][0] = rem_lo;
    reg_mintervals_ups[rd][0] = rem_up;
    reg_mintervals_cnts[rd]   = 1;
  } else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    set_correction(rd, 0, 0, 0, 0, 0);

    reg_mintervals_los[rd][0] = reg_mintervals_los[rs1][0] % reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0] = reg_mintervals_ups[rs1][0] % reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;
  }

  if (PSE) reg_pse_ast[rd] = pse_operation(REMU, reg_pse_ast[rs1] , reg_pse_ast[rs2]);
}

void constrain_sltu() {
  if (rd != REG_ZR) {
    if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
      // concrete semantics of sltu
      registers[rd] = (registers[rs1] < registers[rs2]) ? 1 : 0;

      is_only_one_branch_reachable = true;

      reg_data_type[rd]     = VALUE_T;
      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_vaddrs_cnts[rd]       = 0;

      set_correction(rd, 0, 0, 0, 0, 0);

      if (PSE) reg_pse_ast[rd] = (registers[rd] == 0) ? zero_node : one_node;

      pc = pc + INSTRUCTIONSIZE;
      ic_sltu = ic_sltu + 1;

      return;
    }

    is_only_one_branch_reachable = false;

    if (reg_symb_type[rs1])
      tc_before_branch_evaluation_rs1 = load_symbolic_memory(pt, reg_vaddrs[rs1][0]);

    if (reg_symb_type[rs2])
      tc_before_branch_evaluation_rs2 = load_symbolic_memory(pt, reg_vaddrs[rs2][0]);

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

    reg_mintervals_los[rd][0] = registers[rd];
    reg_mintervals_ups[rd][0] = registers[rd];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

    is_only_one_branch_reachable = true;
    set_correction(rd, 0, 0, 0, 0, 0);

    if (PSE) reg_pse_ast[rd] = (registers[rd] == 0) ? zero_node : one_node;

    pc = pc + INSTRUCTIONSIZE;
    ic_xor = ic_xor + 1;

    return;
  }

  is_only_one_branch_reachable = false;

  if (reg_symb_type[rs1])
    tc_before_branch_evaluation_rs1 = load_symbolic_memory(pt, reg_vaddrs[rs1][0]);

  if (reg_symb_type[rs2])
    tc_before_branch_evaluation_rs2 = load_symbolic_memory(pt, reg_vaddrs[rs2][0]);

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
          if (vaddr < registers[REG_SP]) {
            // free memory
            printf("OUTPUT: loading an uninitialized memory %x\n", pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
          }

        // interval semantics of ld
        reg_data_type[rd] = data_types[mrvc];

        registers[rd]     = values[mrvc];
        reg_steps[rd]     = steps[mrvc];
        reg_mintervals_cnts[rd] = mintervals_los[mrvc].size();
        if (reg_mintervals_cnts[rd] == 0) {
          printf("OUTPUT: reg_mintervals_cnts is zero\n");
        }
        for (uint32_t i = 0; i < reg_mintervals_cnts[rd]; i++) {
          reg_mintervals_los[rd][i] = mintervals_los[mrvc][i];
          reg_mintervals_ups[rd][i] = mintervals_ups[mrvc][i];
        }

        // assert: vaddr == *(vaddrs + mrvc)

        if (is_symbolic_value(reg_data_type[rd], mintervals_los[mrvc].size(), reg_mintervals_los[rd][0], reg_mintervals_ups[rd][0])) {
          // vaddr is constrained by rd if value interval is not singleton
          set_correction(rd, SYMBOLIC, 0, 0, 0, 0);
          reg_vaddrs_cnts[rd] = 1;
          reg_vaddrs[rd][0]   = vaddr;
        } else {
          set_correction(rd, CONCRETE, 0, 0, 0, 0);
          reg_vaddrs_cnts[rd] = 0;
        }
      }

      if (PSE) reg_pse_ast[rd] = pse_asts[mrvc];

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
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

void retrieve_ld_from_tcs(std::vector<uint64_t>& vaddrs, uint32_t vaddrs_size) {
  for (size_t i = 0; i < vaddrs_size; i++) {
    vaddrs[i] = load_symbolic_memory(pt, vaddrs[i]);
  }
}

uint64_t constrain_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = registers[rs1] + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // interval semantics of sd
      retrieve_ld_from_tcs(reg_vaddrs[rs2], reg_vaddrs_cnts[rs2]);

      uint64_t pse_ast = (PSE) ? reg_pse_ast[rs2] : 0;

      if (reg_symb_type[rs2] == SYMBOLIC && reg_vaddrs_cnts[rs2] == 0) { // means it is an x = input();
        store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_type[rs2], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], reg_mintervals_cnts[rs2], reg_steps[rs2], reg_vaddrs[rs2], reg_vaddrs_cnts[rs2], reg_hasmn[rs2], reg_addsub_corr[rs2], reg_muldivrem_corr[rs2], reg_corr_validity[rs2], mrcc, 0, symbolic_input_cnt-1, pse_ast); // doesn't matter symbolic_input_cnt-1 or anything greater than 0
      } else
        store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_type[rs2], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], reg_mintervals_cnts[rs2], reg_steps[rs2], reg_vaddrs[rs2], reg_vaddrs_cnts[rs2], reg_hasmn[rs2], reg_addsub_corr[rs2], reg_muldivrem_corr[rs2], reg_corr_validity[rs2], mrcc, 0, 0, pse_ast);

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
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

void constrain_jal_jalr() {
  if (rd != REG_ZR) {
    reg_mintervals_los[rd][0] = registers[rd];
    reg_mintervals_ups[rd][0] = registers[rd];
    reg_mintervals_cnts[rd]   = 1;
    reg_steps[rd]             = 1;
    reg_vaddrs_cnts[rd]       = 0;

    set_correction(rd, 0, 0, 0, 0, 0);
  }
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void print_symbolic_memory(uint64_t svc) {

}

bool is_symbolic_value(uint64_t type, uint32_t mints_num, uint64_t lo, uint64_t up) {
  if (type)
    // memory range
    return 0;
  else if (mints_num > 1)
    return 1;
  else if (lo == up)
    // singleton interval
    return 0;
  else
    // non-singleton interval
    return 1;
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

bool is_pure_concrete_value(uint32_t data_type, uint32_t mints_num, uint64_t lo, uint64_t up, uint32_t ld_from_num, uint64_t is_input) {
  if (is_symbolic_value(data_type, mints_num, lo, up))
    return false;

  if (ld_from_num == 0 && is_input == 0)
    return true;

  return false;
}

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint32_t data_type, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t step, std::vector<uint64_t>& ld_from_tc, uint32_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb, uint64_t to_tc, uint64_t is_input, uint64_t pse_ast_ptr) {
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

    bool is_this_value_concrete = is_pure_concrete_value(data_type, mints_num, lo[0], up[0], ld_from_num, is_input);
    bool is_prev_value_concrete = is_pure_concrete_value(data_types[mrvc], mintervals_los[mrvc].size(), mintervals_los[mrvc][0], mintervals_ups[mrvc][0], ld_from_tcs[mrvc].size(), is_inputs[mrvc]);

    if (is_this_value_concrete && is_prev_value_concrete && trb < mrvc) {
      // overwrite
      if (mints_num > MAX_NUM_OF_INTERVALS) {
        printf("OUTPUT: maximum number of possible intervals is reached at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      data_types[mrvc]      = data_type;
      values[mrvc]          = value;
      steps[mrvc]           = step;

      mintervals_los[mrvc].clear();
      mintervals_ups[mrvc].clear();
      for (uint32_t i = 0; i < mints_num; i++) {
        mintervals_los[mrvc].push_back(lo[i]);
        mintervals_ups[mrvc].push_back(up[i]);
      }

      if (PSE) pse_asts[mrvc] = pse_ast_ptr;

      return;
    }
  }

  if (is_trace_space_available()) {
    if (mints_num > MAX_NUM_OF_INTERVALS) {
      printf("OUTPUT: maximum number of possible intervals is reached at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (ld_from_num > MAX_NUM_OF_OP_VADDRS) {
      printf("OUTPUT: maximum number of possible vaddrs is reached at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    ealloc();

    pcs[tc]             = pc;
    tcs[tc]             = mrvc;
    data_types[tc]      = data_type;
    values[tc]          = value;
    steps[tc]           = step;
    vaddrs[tc]          = vaddr;
    hasmns[tc]          = hasmn;
    addsub_corrs[tc]    = addsub_corr;
    muldivrem_corrs[tc] = muldivrem_corr;
    corr_validitys[tc]  = corr_validity;

    // keep track of symbolic inputs
    if (is_input && to_tc == 0) { // when sd
      input_table.push_back(tc);
      is_inputs[tc] = input_table.size();
    } else if (is_input) {        // when sltu
      input_table.at(is_input - 1) = tc;
      is_inputs[tc] = is_input;
    } else {
      is_inputs[tc] = is_input;
    }

    mintervals_los[tc].clear();
    mintervals_ups[tc].clear();
    for (uint32_t i = 0; i < mints_num; i++) {
      mintervals_los[tc].push_back(lo[i]);
      mintervals_ups[tc].push_back(up[i]);
    }

    if (to_tc == 0) { // means SD instruction
      ld_from_tcs[tc].clear();
      if (ld_from_num != 0 && reg_symb_type[rs2] == SYMBOLIC) {
        // updating relations between memory locations, both ways
        for (uint32_t i = 0; i < ld_from_num; i++) {
          idx = ld_from_tc[i];
          ld_from_tcs[tc].push_back(idx);
          if (forward_propagated_to_tcs[idx].size() < MAX_SD_TO_NUM) {
            forward_propagated_to_tcs[idx].push_back(tc);
          } else {
            printf("OUTPUT: maximum number of possible sd_to is reached at %x\n", pc - entry_point);
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        }
      }
      forward_propagated_to_tcs[tc].clear();
      mr_sds[tc]            = tc;
      if (PSE) pse_asts[tc] = pse_ast_ptr;
    } else {
      forward_propagated_to_tcs[tc] = forward_propagated_to_tcs[to_tc];
      mr_sds[tc]                    = mr_sds[mrvc];
      if (PSE) pse_asts[tc]         = pse_asts[mrvc];

      // copying relations with other memory locations
      ld_from_tcs[tc].clear();
      for (uint32_t i = 0; i < ld_from_num; i++) {
        ld_from_tcs[tc].push_back(ld_from_tcs[mrvc][i]);
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
  } else {
    printf("OUTPUT: storing\n");
    throw_exception(EXCEPTION_MAXTRACE, 0);
  }
}

// store temporarily an updated symbolic variable on trace without updating the memory and tc++; just for passing args
void store_temp_constrained_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint32_t data_type, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t step, std::vector<uint64_t>& ld_from_tc, uint32_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb, uint64_t to_tc) {
  uint64_t mrvc;
  uint64_t idx;

  if (is_trace_space_available()) {
    if (mints_num > MAX_NUM_OF_INTERVALS) {
      printf("OUTPUT: maximum number of possible intervals is reached at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (ld_from_num > MAX_NUM_OF_OP_VADDRS) {
      printf("OUTPUT: maximum number of possible vaddrs is reached at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    ealloc();

    pcs[tc]             = pc;
    tcs[tc]             = to_tc;
    data_types[tc]      = data_type;
    values[tc]          = value;
    steps[tc]           = step;
    vaddrs[tc]          = vaddr;
    hasmns[tc]          = hasmn;
    addsub_corrs[tc]    = addsub_corr;
    muldivrem_corrs[tc] = muldivrem_corr;
    corr_validitys[tc]  = corr_validity;

    is_inputs[tc]       = 0;

    mintervals_los[tc].clear();
    mintervals_ups[tc].clear();
    for (uint32_t i = 0; i < mints_num; i++) {
      mintervals_los[tc].push_back(lo[i]);
      mintervals_ups[tc].push_back(up[i]);
    }

    ld_from_tcs[tc].clear();
    for (uint32_t i = 0; i < ld_from_num; i++) {
      ld_from_tcs[tc].push_back(ld_from_tcs[to_tc][i]);
    }

    if (PSE) pse_asts[tc] = 0;

    // no trace update
    efree();

    // no memory update

  } else
    throw_exception(EXCEPTION_MAXTRACE, 0);
}

// store an updated symbolic input on trace without updating the memory; new data type of 3
void store_input_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint32_t data_type, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t step, std::vector<uint64_t>& ld_from_tc, uint32_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb, uint64_t to_tc, uint64_t is_input) {
  uint64_t mrvc;
  uint64_t idx;

  if (is_trace_space_available()) {
    if (mints_num > MAX_NUM_OF_INTERVALS) {
      printf("OUTPUT: maximum number of possible intervals is reached at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (ld_from_num > MAX_NUM_OF_OP_VADDRS) {
      printf("OUTPUT: maximum number of possible vaddrs is reached at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    ealloc();

    pcs[tc]             = pc;
    tcs[tc]             = input_table.at(is_input - 1);
    data_types[tc]      = INPUT_T;
    values[tc]          = value;
    steps[tc]           = step;
    vaddrs[tc]          = vaddr;
    hasmns[tc]          = hasmn;
    addsub_corrs[tc]    = addsub_corr;
    muldivrem_corrs[tc] = muldivrem_corr;
    corr_validitys[tc]  = corr_validity;

    is_inputs[tc]       = is_input;
    input_table.at(is_input - 1) = tc;

    mintervals_los[tc].clear();
    mintervals_ups[tc].clear();
    for (uint32_t i = 0; i < mints_num; i++) {
      mintervals_los[tc].push_back(lo[i]);
      mintervals_ups[tc].push_back(up[i]);
    }

    ld_from_tcs[tc].clear();
    for (uint32_t i = 0; i < ld_from_num; i++) {
      ld_from_tcs[tc].push_back(ld_from_tcs[to_tc][i]);
    }

    if (PSE) pse_asts[tc] = 0;

    // no memory update

  } else
    throw_exception(EXCEPTION_MAXTRACE, 0);
}

void store_constrained_memory(uint64_t vaddr, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t step, std::vector<uint64_t>& ld_from_tc, uint32_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t to_tc, uint64_t is_input) {
  uint64_t mrvc;

  // always track constrained memory by using tc as most recent branch
  store_symbolic_memory(pt, vaddr, lo[0], VALUE_T, lo, up, mints_num, step, ld_from_tc, ld_from_num, hasmn, addsub_corr, muldivrem_corr, corr_validity, tc, to_tc, is_input, 0);
}

void store_register_memory(uint64_t reg, std::vector<uint64_t>& value) {
  // always track register memory by using tc as most recent branch
  store_symbolic_memory(pt, reg, value[0], VALUE_T, value, value, 1, 1, zero_v, 0, 0, 0, 0, 0, tc, 0, 0, 0);
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
void apply_correction(std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, std::vector<uint64_t>& lo_before_op, std::vector<uint64_t>& up_before_op, uint64_t step, uint64_t mrvc, bool should_be_stored_or_not) {
  bool is_lo_p_up_p_used = false;
  std::vector<uint64_t> lo_p;
  std::vector<uint64_t> up_p;
  std::vector<uint32_t> idxs;
  // uint64_t lo_p[mints_num];
  // uint64_t up_p[mints_num];
  // uint32_t idxs[mints_num];

  uint32_t j;
  // bool is_found;
  for (uint32_t i = 0; i < mints_num; i++) {
    // is_found = false;
    for (j = 0; j < mintervals_los[mrvc].size(); j++) {
      if (up_before_op[j] - lo_before_op[j] >= lo[i] - lo_before_op[j]) {
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
    propagated_minterval_lo[i] = compute_lower_bound(lo_before_op[j], step, lo[i]);
    propagated_minterval_up[i] = compute_upper_bound(lo_before_op[j], step, up[i]);
  }

  // add, sub
  if (hasmn) {
    uint64_t tmp;
    for (uint32_t i = 0; i < mints_num; i++) {
      tmp        = addsub_corr - propagated_minterval_up[i];
      propagated_minterval_up[i] = addsub_corr - propagated_minterval_lo[i];
      propagated_minterval_lo[i] = tmp;
    }
  } else {
    for (uint32_t i = 0; i < mints_num; i++) {
      propagated_minterval_lo[i] = propagated_minterval_lo[i] - addsub_corr;
      propagated_minterval_up[i] = propagated_minterval_up[i] - addsub_corr;
    }
  }

  // mul, div, rem
  if (corr_validity == MUL_T && muldivrem_corr != 0) { // muldivrem_corr == 0 when (x + 1)
    // <9223372036854775808, 2^64 - 1, 1> * 2 = <0, 2^64 - 2, 2>
    // <9223372036854775809, 15372286728091293014, 1> * 3 = <9223372036854775811, 9223372036854775810, 3>
    for (uint32_t i = 0; i < mints_num; i++) {
      propagated_minterval_lo[i] = mintervals_los[mrvc][idxs[i]] + (propagated_minterval_lo[i] - lo_before_op[idxs[i]]) / muldivrem_corr; // lo_op_before_cmp
      propagated_minterval_up[i] = mintervals_los[mrvc][idxs[i]] + (propagated_minterval_up[i] - lo_before_op[idxs[i]]) / muldivrem_corr; // lo_op_before_cmp
    }

  } else if (corr_validity == DIVU_T) {
    if (mints_num > 1) {
      printf("OUTPUT: backward propagation of minterval needed at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    uint64_t divisor = muldivrem_corr;

    if (mintervals_los[mrvc][0] <= mintervals_ups[mrvc][0]) {
      // non-wrapped
      if (propagated_minterval_lo[0] * divisor > mintervals_los[mrvc][0])
        propagated_minterval_lo[0] = compute_lower_bound(mintervals_los[mrvc][0], steps[mrvc], propagated_minterval_lo[0] * divisor);
      else
        propagated_minterval_lo[0] = mintervals_los[mrvc][0];

      propagated_minterval_up[0] = compute_upper_bound(mintervals_los[mrvc][0], steps[mrvc], propagated_minterval_up[0] * divisor + reverse_division_up(mintervals_ups[mrvc][0], propagated_minterval_up[0], divisor));
    } else {
      // wrapped
      uint64_t lo_1;
      uint64_t up_1;
      uint64_t lo_2;
      uint64_t up_2;
      uint64_t max = compute_upper_bound(mintervals_los[mrvc][0], steps[mrvc], UINT64_MAX_T);
      uint64_t min = (max + steps[mrvc]);
      uint32_t  which_is_empty;

      if (propagated_minterval_lo[0] * divisor > min)
        propagated_minterval_lo[0] = compute_lower_bound(mintervals_los[mrvc][0], steps[mrvc], propagated_minterval_lo[0] * divisor);
      else
        propagated_minterval_lo[0] = min;

      propagated_minterval_up[0] = compute_upper_bound(mintervals_los[mrvc][0], steps[mrvc], propagated_minterval_up[0] * divisor + reverse_division_up(max, propagated_minterval_up[0], divisor));

      // intersection of [propagated_minterval_lo, propagated_minterval_up] with original interval
      which_is_empty = 0;
      if (propagated_minterval_lo[0] <= mintervals_ups[mrvc][0]) {
        lo_1 = propagated_minterval_lo[0];
        up_1 = (propagated_minterval_up[0] < mintervals_ups[mrvc][0]) ? propagated_minterval_up[0] : mintervals_ups[mrvc][0];
      } else {
        which_is_empty = 1;
      }

      if (propagated_minterval_up[0] >= mintervals_los[mrvc][0]) {
        lo_2 = (propagated_minterval_lo[0] > mintervals_los[mrvc][0]) ? propagated_minterval_lo[0] : mintervals_los[mrvc][0];
        up_2 = propagated_minterval_up[0];
      } else {
        which_is_empty = (which_is_empty == 1) ? 4 : 2;
      }

      if (which_is_empty == 0) {
        if (up_1 + steps[mrvc] >= lo_2) {
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

  } else if (corr_validity == REMU_T) {
    printf("OUTPUT: detected an unsupported remu in a conditional expression at %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  } else if (corr_validity > 5) {
    printf("OUTPUT: detected an unsupported conditional expression at %x\n", pc - entry_point);
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  //////////////////////////////////////////////////////////////////////////////
  if (should_be_stored_or_not == true) {
    store_constrained_memory(vaddrs[mrvc], propagated_minterval_lo, propagated_minterval_up, mints_num, steps[mrvc], ld_from_tcs[mrvc], ld_from_tcs[mrvc].size(), hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], mrvc, is_inputs[mrvc]);
  } else {
    // if memory addr is recently updated by a new variable, but we need to propagate constraints through its previouse value
    // carefull about: x = input(); y = x; x = input(); if(y);
    if (is_inputs[mrvc]) {
      // at (tc + 1) with ealloc()
      store_input_memory(pt, vaddrs[mrvc], propagated_minterval_lo[0], VALUE_T, propagated_minterval_lo, propagated_minterval_up, mints_num, steps[mrvc], ld_from_tcs[mrvc], ld_from_tcs[mrvc].size(), hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], tc, mrvc, is_inputs[mrvc]);
    } else {
      // at (tc + 1) but without ealloc()
      store_temp_constrained_memory(pt, vaddrs[mrvc], propagated_minterval_lo[0], VALUE_T, propagated_minterval_lo, propagated_minterval_up, mints_num, steps[mrvc], ld_from_tcs[mrvc], ld_from_tcs[mrvc].size(), hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], tc, mrvc);
    }
  }

  // assert: (ld_from_tcs[mrvc].size() > 1) never reach here
  if (ld_from_tcs[mrvc].size()) {
    for (uint32_t i = 0; i < mints_num; i++) {
      lo_p.push_back(propagated_minterval_lo[i]);
      up_p.push_back(propagated_minterval_up[i]);
    }
    is_lo_p_up_p_used = true;

    if (should_be_stored_or_not == true)
      propagate_backwards(load_symbolic_memory(pt, vaddrs[mrvc]), mintervals_los[mrvc], mintervals_ups[mrvc]);
    else
      propagate_backwards(tc + 1, mintervals_los[mrvc], mintervals_ups[mrvc]); // see above

  }

  if (forward_propagated_to_tcs[mrvc].size()) {
    if (is_lo_p_up_p_used) {
      for (uint32_t i = 0; i < mints_num; i++) {
        propagated_minterval_lo[i] = lo_p[i];
        propagated_minterval_up[i] = up_p[i];
      }
    }
    propagate_backwards_rhs(propagated_minterval_lo, propagated_minterval_up, mints_num, mrvc);
  }
  //////////////////////////////////////////////////////////////////////////////
}

void propagate_backwards_rhs(std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t mrvc) {
  uint64_t stored_to_tc;
  uint64_t mr_stored_to_tc;
  uint64_t tmp;
  std::vector<uint64_t> lo_p;
  std::vector<uint64_t> up_p;
  // uint64_t lo_p[mints_num];
  // uint64_t up_p[mints_num];

  for (uint32_t j = 0; j < mints_num; j++) {
    lo_p.push_back(lo[j]);
    up_p.push_back(up[j]);
  }

  propagated_minterval_cnt = mints_num;
  for (int i = 0; i < forward_propagated_to_tcs[mrvc].size(); i++) {
    stored_to_tc = forward_propagated_to_tcs[mrvc].at(i);
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];

    // carefull about: x = input(); y = x; z = y; y = input(); if(x);

    for (uint32_t j = 0; j < mints_num; j++) {
      propagated_minterval_lo[j] = lo_p[j];
      propagated_minterval_up[j] = up_p[j];
    }
    propagated_minterval_step = steps[stored_to_tc];
    if (corr_validitys[stored_to_tc] == MUL_T && muldivrem_corrs[stored_to_tc] != 0) {
      // mul
      propagate_mul(steps[mrvc], muldivrem_corrs[stored_to_tc]);
    } else if (corr_validitys[stored_to_tc] == DIVU_T) {
      // divu
      propagate_divu(steps[mrvc], muldivrem_corrs[stored_to_tc], propagated_minterval_step);
    } else if (corr_validitys[stored_to_tc] == REMU_T) {
      // remu
      propagate_remu(steps[mrvc], muldivrem_corrs[stored_to_tc]);
    } else if (corr_validitys[stored_to_tc] > REMU_T) {
      printf("OUTPUT: unsupported backward propagation %llu at %x\n", corr_validitys[stored_to_tc], pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    if (hasmns[stored_to_tc]) {
      // addsub_corrs[stored_to_tc] -
      for (uint32_t j = 0; j < mints_num; j++) {
        tmp        = addsub_corrs[stored_to_tc] - propagated_minterval_up[j];
        propagated_minterval_up[j] = addsub_corrs[stored_to_tc] - propagated_minterval_lo[j];
        propagated_minterval_lo[j] = tmp;
      }
    } else {
      // + addsub_corrs[stored_to_tc]
      for (uint32_t j = 0; j < mints_num; j++) {
        propagated_minterval_lo[j] = propagated_minterval_lo[j] + addsub_corrs[stored_to_tc];
        propagated_minterval_up[j] = propagated_minterval_up[j] + addsub_corrs[stored_to_tc];
      }
    }

    if (mr_stored_to_tc == stored_to_tc) {
      store_constrained_memory(vaddrs[stored_to_tc], propagated_minterval_lo, propagated_minterval_up, mints_num, propagated_minterval_step, ld_from_tcs[stored_to_tc], ld_from_tcs[stored_to_tc].size(), hasmns[stored_to_tc], addsub_corrs[stored_to_tc], muldivrem_corrs[stored_to_tc], corr_validitys[stored_to_tc], stored_to_tc, is_inputs[stored_to_tc]);
    } else if (mr_stored_to_tc < stored_to_tc) {
      printf("OUTPUT: mr_stored_to_tc < stored_to_tc at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
    // else if mr_stored_to_tc > stored_to_tc => means it is overwritten

    if (forward_propagated_to_tcs[stored_to_tc].size()) {
      propagate_backwards_rhs(propagated_minterval_lo, propagated_minterval_up, mints_num, stored_to_tc);
    }
  }
}

// y = x op a;
// if (y)
// vaddr of y -> new y
// lo_before_op for y -> before new y
void propagate_backwards(uint64_t mrvc_y, std::vector<uint64_t>& lo_before_op, std::vector<uint64_t>& up_before_op) {
  uint64_t mrvc_x;

  mrvc_x = load_symbolic_memory(pt, vaddrs[ld_from_tcs[mrvc_y][0]]);
  if (mr_sds[mrvc_x] > ld_from_tcs[mrvc_y][0]) {
    // means x is overwritten
    mrvc_x = ld_from_tcs[mrvc_y][0];
    apply_correction(mintervals_los[mrvc_y], mintervals_ups[mrvc_y], mintervals_los[mrvc_y].size(), hasmns[mrvc_y], addsub_corrs[mrvc_y], muldivrem_corrs[mrvc_y], corr_validitys[mrvc_y], lo_before_op, up_before_op, steps[mrvc_y], mrvc_x, false);
  } else {
    mrvc_x = ld_from_tcs[mrvc_y][0];
    apply_correction(mintervals_los[mrvc_y], mintervals_ups[mrvc_y], mintervals_los[mrvc_y].size(), hasmns[mrvc_y], addsub_corrs[mrvc_y], muldivrem_corrs[mrvc_y], corr_validitys[mrvc_y], lo_before_op, up_before_op, steps[mrvc_y], mrvc_x, true);
  }
}

void constrain_memory(uint64_t reg, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t trb, bool only_reachable_branch) {
  uint64_t mrvc;

  if (reg_symb_type[reg] == SYMBOLIC && assert_zone == false) {
    if (only_reachable_branch == true) {
      // for (uint32_t i = 0; i < reg_vaddrs_cnts[reg]; i++) {
      //   mrvc = load_symbolic_memory(pt, reg_vaddrs[reg][i]);
      //   lo = mintervals_los[mrvc];
      //   up = mintervals_ups[mrvc];
      //   store_constrained_memory(reg_vaddrs[reg][i], lo, up, mintervals_los[mrvc].size(), steps[mrvc], ld_from_tcs[mrvc], ld_from_tcs[mrvc].size(), hasmns[mrvc], addsub_corrs[mrvc], muldivrem_corrs[mrvc], corr_validitys[mrvc], mrvc, is_inputs[mrvc]);
      // }
    } else {
      mrvc = (reg == rs1) ? tc_before_branch_evaluation_rs1 : tc_before_branch_evaluation_rs2;
      apply_correction(lo, up, mints_num, reg_hasmn[reg], reg_addsub_corr[reg], reg_muldivrem_corr[reg], reg_corr_validity[reg], reg_mintervals_los[reg], reg_mintervals_ups[reg], reg_steps[reg], mrvc, true);
    }

  }
}

void set_vaddrs(uint64_t reg, std::vector<uint64_t>& vaddrs, uint32_t start_idx, uint32_t vaddr_num) {
  reg_vaddrs_cnts[reg] = vaddr_num;
  for (uint32_t i = 0; i < vaddr_num; i++) {
    reg_vaddrs[reg][start_idx++] = vaddrs[i];
  }
}

void set_correction(uint64_t reg, uint32_t hasco, uint32_t hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity) {
  reg_symb_type[reg]      = hasco;
  reg_hasmn[reg]          = hasmn;
  reg_addsub_corr[reg]    = addsub_corr;
  reg_muldivrem_corr[reg] = muldivrem_corr;
  reg_corr_validity[reg]  = corr_validity;
}

void take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0 && assert_zone == false) {
    // record that we need to set rd to true
    value_v[0] = b;
    store_register_memory(rd, value_v);

    // record frame and stack pointer
    value_v[0] = registers[REG_FP];
    store_register_memory(REG_FP, value_v);
    value_v[0] = registers[REG_SP];
    store_register_memory(REG_SP, value_v);
  } else {
    reg_data_type[rd] = VALUE_T;
    registers[rd]     = b;
    reg_steps[rd]     = 1;
    reg_mintervals_los[rd][0] = b;
    reg_mintervals_ups[rd][0] = b;
    reg_mintervals_cnts[rd]   = 1;
    reg_vaddrs_cnts[rd]       = 0;

    set_correction(rd, 0, 0, 0, 0, 0);

    if (PSE) reg_pse_ast[rd] = (b == 0) ? zero_node : one_node;
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
    upgrade_mode("detected non-singleton interval intersection");

    if (check_conditional_type_lte_or_gte() == LGTE) {
      false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      take_branch(1, 1);
      take_branch(0, 0);
    } else {
      false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      take_branch(0, 1);
      take_branch(1, 0);
    }
    return;
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_lte_or_gte() == LGTE) {
        if (PSE) {
          false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
          path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        }
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        if (PSE) {
          false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
          path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        }
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
    upgrade_mode("detected non-singleton interval intersection");

    if (check_conditional_type_lte_or_gte() == LGTE) {
      false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      take_branch(1, 1);
      take_branch(0, 0);
    } else {
      false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      take_branch(0, 1);
      take_branch(1, 0);
    }
    return;
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_lte_or_gte() == LGTE) {
        if (PSE) {
          false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
          path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        }
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        if (PSE) {
          false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
          path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        }
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
    upgrade_mode("detected non-singleton interval intersection");

    if (check_conditional_type_lte_or_gte() == LGTE) {
      false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      take_branch(1, 1);
      take_branch(0, 0);
    } else {
      false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
      path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
      take_branch(0, 1);
      take_branch(1, 0);
    }
    return;
  }

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_lte_or_gte() == LGTE) {
        if (PSE) {
          false_branches.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
          path_condition.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        }
        constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        take_branch(1, 1);
        constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        if (PSE) {
          false_branches.push_back(pse_operation(IGTE, reg_pse_ast[rs1], reg_pse_ast[rs2]));
          path_condition.push_back(pse_operation(ILT , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        }
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
    if (reg_mintervals_cnts[rs1] == 1 && reg_mintervals_cnts[rs2] == 1) {
      if (steps[tc_before_branch_evaluation_rs1] > 1) {
        if (steps[tc_before_branch_evaluation_rs2] > 1) {
          uint64_t los_diff = (mintervals_los[tc_before_branch_evaluation_rs1][0] >= mintervals_los[tc_before_branch_evaluation_rs2][0]) ? (mintervals_los[tc_before_branch_evaluation_rs1][0] - mintervals_los[tc_before_branch_evaluation_rs2][0]) : (mintervals_los[tc_before_branch_evaluation_rs2][0] - mintervals_los[tc_before_branch_evaluation_rs1][0]);
          if ( los_diff % gcd(steps[tc_before_branch_evaluation_rs1], steps[tc_before_branch_evaluation_rs2]) != 0) {
            constrain_memory(rs1, zero_v, zero_v, 0, trb, true);
            constrain_memory(rs2, zero_v, zero_v, 0, trb, true);

            is_only_one_branch_reachable = true;
            take_branch(1, 0);

            cannot_handle = false;
          }
        }
      }
    }

    if (cannot_handle) {
      // detected non-singleton interval intersection
      upgrade_mode("detected non-singleton interval intersection");

      if (check_conditional_type_equality_or_disequality() == EQ) {
        false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        take_branch(1, 1);
        take_branch(0, 0);
      } else {
        false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        take_branch(0, 1);
        take_branch(1, 0);
      }
      return;
    }

  } else {
    if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
      true_reachable  = true;
    if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
      false_reachable = true;

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_equality_or_disequality() == EQ) {
          if (PSE) {
            false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
            path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
          }
          constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
          constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
          take_branch(1, 1);
          constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
          constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
          take_branch(0, 0);
        } else {
          if (PSE) {
            false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
            path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
          }
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
    if (reg_mintervals_cnts[rs1] == 1 && reg_mintervals_cnts[rs2] == 1) {
      if (steps[tc_before_branch_evaluation_rs1] > 1) {
        if (steps[tc_before_branch_evaluation_rs2] > 1) {
          uint64_t los_diff = (mintervals_los[tc_before_branch_evaluation_rs1][0] >= mintervals_los[tc_before_branch_evaluation_rs2][0]) ? (mintervals_los[tc_before_branch_evaluation_rs1][0] - mintervals_los[tc_before_branch_evaluation_rs2][0]) : (mintervals_los[tc_before_branch_evaluation_rs2][0] - mintervals_los[tc_before_branch_evaluation_rs1][0]);
          if ( los_diff % gcd(steps[tc_before_branch_evaluation_rs1], steps[tc_before_branch_evaluation_rs2]) != 0) {
            constrain_memory(rs1, zero_v, zero_v, 0, trb, true);
            constrain_memory(rs2, zero_v, zero_v, 0, trb, true);

            is_only_one_branch_reachable = true;
            take_branch(1, 0);

            cannot_handle = false;
          }
        }
      }
    }

    if (cannot_handle) {
      // detected non-singleton interval intersection
      upgrade_mode("detected non-singleton interval intersection");

      if (check_conditional_type_equality_or_disequality() == EQ) {
        false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        take_branch(1, 1);
        take_branch(0, 0);
      } else {
        false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        take_branch(0, 1);
        take_branch(1, 0);
      }
      return;
    }

  } else {
    if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
      true_reachable  = true;
    if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
      false_reachable = true;

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_equality_or_disequality() == EQ) {
          if (PSE) {
            false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
            path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
          }
          constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
          constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
          take_branch(1, 1);
          constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
          constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
          take_branch(0, 0);
        } else {
          if (PSE) {
            false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
            path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
          }
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
    if (reg_mintervals_cnts[rs1] == 1 && reg_mintervals_cnts[rs2] == 1) {
      if (steps[tc_before_branch_evaluation_rs1] > 1) {
        if (steps[tc_before_branch_evaluation_rs2] > 1) {
          uint64_t los_diff = (mintervals_los[tc_before_branch_evaluation_rs1][0] >= mintervals_los[tc_before_branch_evaluation_rs2][0]) ? (mintervals_los[tc_before_branch_evaluation_rs1][0] - mintervals_los[tc_before_branch_evaluation_rs2][0]) : (mintervals_los[tc_before_branch_evaluation_rs2][0] - mintervals_los[tc_before_branch_evaluation_rs1][0]);
          if ( los_diff % gcd(steps[tc_before_branch_evaluation_rs1], steps[tc_before_branch_evaluation_rs2]) != 0) {
            constrain_memory(rs1, zero_v, zero_v, 0, trb, true);
            constrain_memory(rs2, zero_v, zero_v, 0, trb, true);

            is_only_one_branch_reachable = true;
            take_branch(1, 0);

            cannot_handle = false;
          }
        }
      }
    }

    if (cannot_handle) {
      // detected non-singleton interval intersection
      upgrade_mode("detected non-singleton interval intersection");

      if (check_conditional_type_equality_or_disequality() == EQ) {
        false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        take_branch(1, 1);
        take_branch(0, 0);
      } else {
        false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
        path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
        take_branch(0, 1);
        take_branch(1, 0);
      }
      return;
    }

  } else {
    if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
      true_reachable  = true;
    if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
      false_reachable = true;

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_equality_or_disequality() == EQ) {
          if (PSE) {
            false_branches.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
            path_condition.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
          }
          constrain_memory(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
          constrain_memory(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
          take_branch(1, 1);
          constrain_memory(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
          constrain_memory(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
          take_branch(0, 0);
        } else {
          if (PSE) {
            false_branches.push_back(pse_operation(IEQ , reg_pse_ast[rs1], reg_pse_ast[rs2]));
            path_condition.push_back(pse_operation(INEQ, reg_pse_ast[rs1], reg_pse_ast[rs2]));
          }
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

}

void backtrack_sltu() {
  uint64_t vaddr;

  if (debug_symbolic) {
    printf("OUTPUT: backtracking sltu ");
    print_symbolic_memory(tc);
  }

  vaddr = vaddrs[tc];

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      reg_data_type[vaddr]         = data_types[tc];
      registers[vaddr]             = values[tc];
      reg_mintervals_los[vaddr][0] = mintervals_los[tc][0];
      reg_mintervals_ups[vaddr][0] = mintervals_ups[tc][0];
      reg_mintervals_cnts[vaddr]   = 1;
      reg_steps[vaddr]             = 1;
      reg_vaddrs_cnts[rd]          = 0;

      set_correction(vaddr, 0, 0, 0, 0, 0);

      // restoring mrcc
      mrcc = tcs[tc];

      if (vaddr != REG_FP)
        if (vaddr != REG_SP) {
          // stop backtracking and try next case
          pc = pc + INSTRUCTIONSIZE;
          ic_sltu = ic_sltu + 1;

          if (PSE) {
            reg_pse_ast[vaddr] = (registers[vaddr] == 0) ? zero_node : one_node;
            while (false_branches.back() < path_condition.back()) {
              path_condition.pop_back();
              // traversed_path_condition_element.pop_back();
            }
            tree_tc = false_branches.back();
            path_condition.push_back(false_branches.back());
            // traversed_path_condition_element.push_back("");
            false_branches.pop_back();
          }

        }
    }
  } else {
    if (is_inputs[tc] && data_types[tc] == INPUT_T) {
      // undo the input record on trace; there was no memory update
      input_table.at(is_inputs[tc] - 1) = tcs[tc];
      efree();
      return;
    } else if (is_inputs[tc]) {
      // undo x = input(); if(x);
      input_table.at(is_inputs[tc] - 1) = tcs[tc];
    }

    store_virtual_memory(pt, vaddr, tcs[tc]);
  }

  efree();
}

void backtrack_sd() {
  if (debug_symbolic) {
    printf("OUTPUT: backtracking sd ");
    print_symbolic_memory(tc);
  }

  // if x = input(); pop the already inserted is_inputs[tc] on input table
  if (is_inputs[tc]) {
    symbolic_input_cnt = input_table.size();
    input_table.pop_back();

    if (PSE) pse_variables_per_path.pop_back();
  }

  uint64_t idx;
  for (uint32_t i = 0; i < ld_from_tcs[tc].size(); i++) {
    idx = ld_from_tcs[tc][i];
    forward_propagated_to_tcs[idx].pop_back();
  }

  if (PSE && pse_asts[tc] && tree_tc > pse_asts[tc]) tree_tc = pse_asts[tc];

  store_virtual_memory(pt, vaddrs[tc], tcs[tc]);

  efree();
}

void backtrack_ecall() {
  if (debug_symbolic) {
    printf("OUTPUT: backtracking ecall ");
    print_symbolic_memory(tc);
  }

  if (vaddrs[tc] == 0) {
    // backtracking malloc
    if (get_program_break(current_context) == mintervals_los[tc][0] + mintervals_ups[tc][0])
      set_program_break(current_context, mintervals_los[tc][0]);
    else {
      printf("OUTPUT: malloc backtracking error at %x", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking read
    rc = rc + 1;

    // record value, lower and upper bound
    read_values[rc] = values[tc];
    read_los[rc]    = mintervals_los[tc][0];
    read_ups[rc]    = mintervals_ups[tc][0];

    store_virtual_memory(pt, vaddrs[tc], tcs[tc]);
  }

  efree();
}

void backtrack_trace(uint64_t* context) {
  uint64_t savepc;

  if (debug_symbolic) {
    printf("OUTPUT: backtracking from exit code \n");
  }

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

void propagate_mul(uint64_t step, uint64_t k) {
  // important assert:
  // corr_validity > REMU_T never reach here e.g. when MUL_T_FALSE
  bool cnd;
  for (size_t i = 0; i < propagated_minterval_cnt; i++) {
    cnd = mul_condition(propagated_minterval_lo[i], propagated_minterval_up[i], k);
    if (cnd == true) {
      propagated_minterval_lo[i] = propagated_minterval_lo[i] * k;
      propagated_minterval_up[i] = propagated_minterval_up[i] * k;
    } else {
      printf("OUTPUT: cannot reason about overflowed mul at %x\n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }
}

void propagate_divu(uint64_t step, uint64_t k, uint64_t step_rd) {
  // interval semantics of divu
  for (uint32_t i = 0; i < propagated_minterval_cnt; i++) {
    if (propagated_minterval_lo[i] > propagated_minterval_up[i]) {
      // rs1 constraint is wrapped: [lo, UINT64_MAX_T], [0, up]
      // lo/k == up/k (or) up/k + step_rd
      if (propagated_minterval_lo[i]/k != propagated_minterval_up[i]/k)
        if (propagated_minterval_lo[i]/k > propagated_minterval_up[i]/k + step_rd) {
          printf("OUTPUT: wrapped divison rsults two intervals at %x \n", pc);
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

      uint64_t max = compute_upper_bound(propagated_minterval_lo[i], step, UINT64_MAX_T);
      propagated_minterval_lo[i] = (max + step) / k;
      propagated_minterval_up[i] = max          / k;
    } else {
      propagated_minterval_lo[i] = propagated_minterval_lo[i] / k;
      propagated_minterval_up[i] = propagated_minterval_up[i] / k;
    }
  }
}

void propagate_remu(uint64_t step, uint64_t divisor) {
  // interval semantics of remu
  for (uint32_t i = 0; i < propagated_minterval_cnt; i++) {
    if (propagated_minterval_lo[i] <= propagated_minterval_up[i]) {
      // rs1 interval is not wrapped
      int rem_typ = remu_condition(propagated_minterval_lo[i], propagated_minterval_up[i], step, divisor);
      if (rem_typ == 0) {
        propagated_minterval_lo[i] = propagated_minterval_lo[i] % divisor;
        propagated_minterval_up[i] = propagated_minterval_up[i] % divisor;
        propagated_minterval_step  = step;
      } else if (rem_typ == 1) {
        printf("OUTPUT: modulo results two intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (rem_typ == 2) {
        uint64_t gcd_step_k = gcd(step, divisor);
        propagated_minterval_lo[i] = propagated_minterval_lo[i]%divisor - ((propagated_minterval_lo[i]%divisor) / gcd_step_k) * gcd_step_k;
        propagated_minterval_up[i] = compute_upper_bound(propagated_minterval_lo[i], gcd_step_k, divisor - 1);
        propagated_minterval_step  = gcd_step_k;
      } else {
        printf("OUTPUT: modulo results many intervals at %x\n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

    } else if (is_power_of_two(divisor)) {
      // rs1 interval is wrapped
      uint64_t gcd_step_k = gcd(step, divisor);
      uint64_t lcm        = (step * divisor) / gcd_step_k;

      if (propagated_minterval_up[i] - propagated_minterval_lo[i] < lcm - step) {
        printf("OUTPUT: wrapped modulo results many intervals at %x \n", pc - entry_point);
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      propagated_minterval_lo[i] = propagated_minterval_lo[i]%divisor - ((propagated_minterval_lo[i]%divisor) / gcd_step_k) * gcd_step_k;
      propagated_minterval_up[i] = compute_upper_bound(propagated_minterval_lo[i], gcd_step_k, divisor - 1);
      propagated_minterval_step  = gcd_step_k;
    } else {
      printf("OUTPUT: wrapped modulo results many intervals at %x \n", pc - entry_point);
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
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

// ------------------------------ path condition -------------------------------

void decode_operation(uint64_t node_tc) {
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

void decode_var(uint64_t node_tc) {
  path_condition_string = (PER_PATH) ? path_condition_string + "IVAR(ID_" + std::to_string(pse_ast_nodes[node_tc].right_node) + ")"
                                     : path_condition_string + "IVAR(ID_" + std::to_string(pse_ast_nodes[node_tc].left_node ) + ")";
}

void decode_const(uint64_t node_tc) {
  path_condition_string = path_condition_string + "ICONST(" + std::to_string(pse_ast_nodes[node_tc].right_node) + ")";
}

bool node_decoder(uint64_t node_tc) {
  switch (pse_ast_nodes[node_tc].type) {
    case 0:
      decode_const(node_tc);
      return true;
    case 1:
      decode_var(node_tc);
      return true;
    default:
      decode_operation(node_tc);
      return false;
  }
}

void path_condition_traverse(uint64_t node_tc) {
  if (node_decoder(node_tc))
    return;

  path_condition_traverse(pse_ast_nodes[node_tc].left_node);
  path_condition_string += ",";
  path_condition_traverse(pse_ast_nodes[node_tc].right_node);
  path_condition_string += ")";
}

void generate_path_condition() {
  path_condition_string.clear();
  for (size_t i = 0; i < path_condition.size(); i++) {
    path_condition_traverse(path_condition[i]); // node_tc
    path_condition_string += ";";
  }
}