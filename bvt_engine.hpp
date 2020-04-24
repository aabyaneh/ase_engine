#include "engine.hpp"

class bvt_engine : public engine {
  public:
    // extra syscalls
    uint64_t SYSCALL_SYMPOLIC_INPUT = 42;
    uint64_t SYSCALL_PRINTSV        = 43;
    uint64_t symbolic_input_cnt     = 0;
    // extra exeptions
    uint64_t EXCEPTION_MAXTRACE     = 7;
    // backtracking
    uint64_t backtrack              = 0;

    // -------------------------
    // BVT decision procedure
    // -------------------------

    enum abstraction_layer : uint8_t {
      BVT = 2, ABVT = 3 // bit vector theory, approximate bit vector theory
    };

    // -------------------------
    // the trace data structure
    // -------------------------

    uint64_t MAX_NUM_OF_INTERVALS       = 1;
    uint64_t MAX_NUM_OF_INVOLVED_INPUTS = 100;
    uint64_t MAX_TRACE_LENGTH           = 10000000;
    uint64_t MAX_AST_NODES_TRACE_LENGTH = 5 * MAX_TRACE_LENGTH;
    uint64_t AST_NODES_TRACE_LENGTH     = MAX_AST_NODES_TRACE_LENGTH / 2;
    uint64_t MEMORY_ALLOCATION_STEP_AST_NODES_TRACE = 10000000;

    // -------------------------
    // memory trace
    // -------------------------
    uint64_t  tc = 0;        // trace counter
    uint64_t* pcs;           // trace of program counter values
    uint64_t* tcs;           // trace of trace counters to previous values
    uint64_t* vaddrs;        // trace of virtual addresses
    uint64_t* values;        // trace of values
    uint8_t*  data_types;    // VALUE_T, POINTER_T, INPUT_T
    uint64_t* asts;          // trace of pointers to the AST nodes
    uint64_t* mr_sds;        // trace of most recent stores to memory addresses
    BoolectorNode** bvt_false_branches; // trace of pointers to boolector expressions for keeping track of false branch expressions

    enum data_type : uint8_t {
      VALUE_T = 0, POINTER_T = 1, INPUT_T = 2
    };

    // -------------------------
    // read trace
    // -------------------------
    uint64_t  rc = 0;        // read counter
    uint64_t* read_values;
    uint64_t* read_los;
    uint64_t* read_ups;

    // -------------------------
    // registers
    // -------------------------
    uint8_t*                            reg_data_type;
    uint8_t*                            reg_symb_type;     // CONCRETE, SYMBOLIC
    std::vector<std::vector<uint64_t> > reg_mintervals_los;
    std::vector<std::vector<uint64_t> > reg_mintervals_ups;
    // uint32_t*                        reg_mintervals_cnts; // always contains one witness
    std::vector<std::vector<uint64_t> > reg_involved_inputs;
    uint32_t*                           reg_involved_inputs_cnts;
    uint64_t*                           reg_asts;
    BoolectorNode**                     reg_bvts;          // array of pointers to SMT expressions
    uint8_t*                            reg_hasmn;         // corrections -> constant folding
    uint64_t*                           reg_addsub_corr;   // corrections -> constant folding
    uint8_t*                            reg_corr_validity; // corrections -> constant folding

    enum symbolic_type : uint8_t {
      CONCRETE = 0, SYMBOLIC = 2  // CONCRETE must be zero look is_symbolic_value()
    };

    // -------------------------
    // ASTs (Abstract Syntax Tree)
    // -------------------------
    enum ast_node_type {
      CONST = 0, VAR = 1, ADDI = 2, ADD = 3, SUB = 4, MUL = 5, DIVU = 6, REMU = 7, ILT = 8, IGTE = 9, IEQ = 10, INEQ = 11
    };

    struct node {
      uint8_t  type;
      uint64_t left_node;
      uint64_t right_node;
    };

    uint64_t ast_trace_cnt = 0;
    struct node*                        ast_nodes;
    std::vector<std::vector<uint64_t> > mintervals_los;
    std::vector<std::vector<uint64_t> > mintervals_ups;
    std::vector<std::vector<uint64_t> > store_trace_ptrs;
    std::vector<std::vector<uint64_t> > involved_sym_inputs_ast_tcs;
    uint64_t*                           involved_sym_inputs_cnts;
    BoolectorNode**                     smt_exprs;
    uint8_t*                            symb_types;

    uint64_t zero_node;
    uint64_t one_node;
    uint64_t queries_reasoned_by_bvt = 0; // number of queries handled by bvt
    uint64_t paths = 0;

    // detection of symbolic operand in an expression
    enum symbolic_operands_in_an_expression : uint8_t {
      LEFT = 10, RIGHT = 20, BOTH = 30
    };
    uint64_t sym_operand_ast_tc = 0;
    uint64_t crt_operand_ast_tc = 0;

    std::vector<uint64_t> merged_array;
    bool vector_contains_element(std::vector<uint64_t>& vector, uint64_t element);
    void merge_arrays(std::vector<uint64_t>& vector_1, std::vector<uint64_t>& vector_2, size_t vector_1_size, size_t vector_2_size);

    // -------------------------
    // branch evaluation
    // -------------------------
    std::vector<uint64_t>  zero_v;
    std::vector<uint64_t>  one_v;
    std::vector<uint64_t>  value_v;

    uint64_t mrcc = 0;  // trace counter of most recent constraint

    // temporary data-structure to pass values targeting propagations
    std::vector<uint64_t> propagated_minterval_lo;
    std::vector<uint64_t> propagated_minterval_up;

    std::vector<uint64_t> involved_inputs_in_current_conditional_expression_rs1_operand;
    std::vector<uint64_t> involved_inputs_in_current_conditional_expression_rs2_operand;

    // ==, !=, <, <=, >= detection
    enum conditional_type : uint8_t {
      LT = 1, LGTE = 2, EQ = 4, DEQ = 5
    };

    // -------------------------
    // symbolic inputs management
    // -------------------------
    std::vector<uint64_t> input_table;
    std::vector<uint64_t> input_table_store_trace_ptr;
    std::vector<uint64_t> input_table_ast_tcs_before_branch_evaluation;
    uint64_t total_number_of_generated_witnesses_for_all_paths = 0;
    uint64_t max_number_of_generated_witnesses_among_all_paths = 0;
    void     witness_profile();

    // -------------------------
    // SMT solver instance
    // -------------------------
    char            var_buffer[100];   // a buffer for automatic variable name generation
    char            const_buffer[64];  // a buffer for loading integers of more than 32 bits
    Btor*           btor;
    BoolectorSort   bv_sort;
    BoolectorNode*  zero_bv;
    BoolectorNode*  one_bv;
    uint64_t        TWO_TO_THE_POWER_OF_32;

    // smt's witness
    std::vector<const char*> true_input_assignments;
    std::vector<const char*> false_input_assignments;

    BoolectorNode*         boolector_null = (BoolectorNode*) 0;
    uint64_t               most_recent_if_on_ast_trace = 0;

    // -------------------------
    // testing
    // -------------------------
    bool IS_TEST_MODE = false;
    std::ofstream output_results;

    // ---------------------------
    // run-time functions
    // ---------------------------
    virtual void     init_engine(uint64_t peek_argument);
    virtual uint64_t run_engine(uint64_t* to_context);
    void     init_interpreter();
    void     up_load_binary(uint64_t* context);
    void     map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data);
    void     set_SP(uint64_t* context);
    uint64_t handle_system_call(uint64_t* context);
    uint64_t handle_exception(uint64_t* context);
    uint64_t handle_max_trace(uint64_t* context);
    uint64_t down_load_string(uint64_t* table, uint64_t vstring, uint64_t* s);
    BoolectorNode* boolector_unsigned_int_64(uint64_t value);
    void     implement_exit(uint64_t* context);
    void     implement_read(uint64_t* context);
    void     implement_write(uint64_t* context);
    void     implement_open(uint64_t* context);
    void     implement_brk(uint64_t* context);
    void     implement_printsv(uint64_t* context);
    void     implement_symbolic_input(uint64_t* context);

    // ---------------------------
    // constant folding
    // ---------------------------
    void set_correction(uint64_t reg, uint8_t hasmn, uint64_t addsub_corr, uint8_t corr_validity);
    void create_ast_node_entry_for_accumulated_corr(uint64_t sym_reg);
    void create_ast_node_entry_for_concrete_operand(uint64_t crt_reg);
    void evaluate_correction(uint64_t reg);

    // ---------------------------
    // symbolic instructions
    // ---------------------------
    uint64_t check_memory_vaddr_whether_represents_most_recent_constraint(uint64_t mrvc);
    uint8_t  is_symbolic_value(uint8_t type, uint32_t mints_num, uint64_t lo, uint64_t up, uint8_t theory_type);
    uint64_t is_safe_address(uint64_t vaddr, uint64_t reg);

    bool apply_add_pointer();
    bool apply_sub_pointer();
    void apply_lui();
    void apply_addi();
    void apply_add();
    void apply_sub();
    void apply_mul();
    void apply_divu();
    void apply_remu();
    void apply_sltu();
    void apply_xor();
    void apply_jal();
    void apply_jalr();
    void apply_ecall();
    uint64_t apply_ld();
    uint64_t apply_sd();

    void backtrack_sltu();
    void backtrack_sd();
    void backtrack_ld();
    void backtrack_ecall();
    void backtrack_trace(uint64_t* context);

    // ---------------------------
    // memory trace managment
    // ---------------------------
    uint64_t is_trace_space_available();
    uint64_t get_current_tc();
    void     ealloc();
    void     efree();
    uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);
    void     store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint8_t data_type, uint64_t ast_ptr, uint64_t trb, uint64_t is_store, uint8_t symbolic_type);
    void     store_register_memory(uint64_t reg, std::vector<uint64_t>& value);
    void     store_input_record(uint64_t ast_ptr, uint64_t prev_input_record, uint8_t theory_type);

    // ---------------------------
    // reasoning/decision core
    // ---------------------------
    virtual uint64_t add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs, BoolectorNode* smt_expr, uint8_t symbolic_type);
    uint8_t  detect_symbolic_operand(uint64_t ast_tc);
    void     set_involved_inputs(uint64_t reg, std::vector<uint64_t>& involved_inputs, size_t vaddr_num);
    void     set_involved_inputs_two_symbolic_operands();
    void     take_branch(uint64_t b, uint64_t how_many_more);
    virtual  void create_sltu_constraints();
    void     create_xor_constraints();
    bool     check_sat_true_branch_bvt(BoolectorNode* assert);
    bool     check_sat_false_branch_bvt(BoolectorNode* assert);
    void     dump_involving_input_variables_true_branch_bvt();
    void     dump_involving_input_variables_false_branch_bvt();
    void     dump_all_input_variables_on_trace_true_branch_bvt();
    void     dump_all_input_variables_on_trace_false_branch_bvt();
    bool     match_addi_instruction();
    bool     match_sub_instruction(uint64_t prev_instr_rd);
    uint8_t  check_conditional_type_whether_is_equality_or_disequality();
    uint8_t  check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq();
    void           check_operands_smt_expressions();
    BoolectorNode* create_smt_expression(uint64_t ast_tc);
    BoolectorNode* boolector_op(uint8_t op, uint64_t ast_tc);

    // ---------------------------
    // on-demand propagation
    // ---------------------------
    uint64_t compute_add(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands);
    uint64_t compute_sub(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands);
    uint64_t compute_mul(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands);
    uint64_t compute_divu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands);
    uint64_t compute_remu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands);
    uint64_t recompute_operation(uint8_t op, uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands);
    uint64_t update_current_constraint_on_ast_expression(uint64_t ast_tc);
};