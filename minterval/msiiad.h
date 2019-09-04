#include <stdint.h>
#include <iostream>
#include <fcntl.h>
#include <unistd.h>
#include <vector>

// ------ shared variables and procedures between source files -----

extern uint64_t rs1;
extern uint64_t rs2;
extern uint64_t rd;
extern uint64_t imm;
extern uint64_t pc;
extern uint64_t ir;
extern uint64_t REG_ZR;
extern uint64_t REG_FP;
extern uint64_t REG_SP;
extern uint64_t NUMBEROFREGISTERS;
extern uint64_t OP_BRANCH;
extern uint64_t INSTRUCTIONSIZE;
extern uint64_t EXCEPTION_PAGEFAULT;
extern uint64_t EXCEPTION_INVALIDADDRESS;
extern uint64_t EXITCODE_SYMBOLICEXECUTIONERROR;
extern uint64_t F3_ADD;
extern uint64_t F3_XOR;
extern uint64_t F7_SUB;
extern uint64_t OP_IMM;
extern uint64_t OP_OP;
extern uint64_t F3_ADDI;
extern uint64_t F3_SLTU;
extern uint64_t REGISTERSIZE;
extern uint64_t SIZEOFUINT64;
extern uint64_t NUMBEROFREGISTERS;
extern uint64_t UINT64_MAX_T;
extern uint64_t EXCEPTION_DIVISIONBYZERO;
extern uint64_t EXCEPTION_MAXTRACE;

extern uint64_t* pt;
extern uint64_t* current_context;
extern uint64_t* registers;
extern uint64_t* loads_per_instruction;
extern uint64_t* stores_per_instruction;

extern uint64_t entry_point;
extern bool     assert_zone;

extern uint64_t ic_addi;
extern uint64_t ic_sub;
extern uint64_t ic_sltu;
extern uint64_t ic_ld;
extern uint64_t ic_sd;
extern uint64_t ic_xor;

uint64_t* zalloc(uint64_t size);
uint64_t is_valid_virtual_address(uint64_t vaddr);
uint64_t get_page_of_virtual_address(uint64_t vaddr);
uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr);
uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr);
void     store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);
uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);
void     throw_exception(uint64_t exception, uint64_t faulting_page);
uint64_t get_program_break(uint64_t* context);
void     set_program_break(uint64_t* context, uint64_t brk);
void     fetch();
void     decode_execute();
uint64_t load_instruction(uint64_t baddr);
uint64_t get_opcode(uint64_t instruction);
uint64_t get_funct7(uint64_t instruction);
uint64_t get_funct3(uint64_t instruction);
uint64_t get_rd(uint64_t instruction);
uint64_t get_rs1(uint64_t instruction);
uint64_t get_rs2(uint64_t instruction);
uint64_t get_immediate_i_format(uint64_t instruction);
uint64_t two_to_the_power_of(uint64_t p);
uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b);
void     set_pc(uint64_t* context, uint64_t pc);

// ---------------------------- SYMBOLIC----------------------------

extern uint64_t MSIIAD;
extern uint64_t MAX_TRACE_LENGTH;
extern uint64_t debug_symbolic;
extern uint64_t symbolic;
extern uint64_t backtrack;
extern bool     is_only_one_branch_reachable;
extern bool     assert_zone;

extern uint64_t  rc;
extern uint64_t* read_values;
extern uint64_t* read_los;
extern uint64_t* read_ups;

extern uint64_t* reg_steps;
extern uint32_t* reg_data_type;
extern uint32_t  VALUE_T;
extern uint32_t  POINTER_T;
extern uint32_t* reg_symb_type;
extern uint32_t  CONCRETE;
extern uint32_t  SYMBOLIC;
extern bool*     reg_hasmn;
extern uint64_t* reg_addsub_corr;
extern uint64_t* reg_muldivrem_corr;
extern uint64_t* reg_corr_validity;
extern uint32_t* reg_mintervals_cnts;
extern uint32_t* reg_vaddrs_cnts;
extern std::vector<std::vector<uint64_t> > reg_vaddrs;

extern uint64_t* values;
extern uint64_t* data_types;
extern uint64_t* steps;
extern uint32_t* mintervals_cnts;
extern std::vector<std::vector<uint64_t> > mintervals_los;
extern std::vector<std::vector<uint64_t> > mintervals_ups;
extern std::vector<std::vector<uint64_t> > reg_mintervals_los;
extern std::vector<std::vector<uint64_t> > reg_mintervals_ups;
extern std::vector<std::vector<uint64_t> > ld_from_tcs;

extern std::vector<uint64_t>  zero_v;

extern uint64_t mrcc;

extern uint64_t symbolic_input_cnt;

extern std::vector<uint64_t> input_table;

// ------------------------ INSTRUCTIONS -----------------------

void constrain_lui();
void constrain_addi();
void constrain_add();
void constrain_sub();
void constrain_mul();
void constrain_divu();
void constrain_remu();
void constrain_sltu();
void constrain_xor();
void constrain_jal_jalr();
uint64_t constrain_ld();
uint64_t constrain_sd();

void backtrack_sltu();
void backtrack_sd();
void backtrack_ecall();
void backtrack_trace(uint64_t* context);

void init_symbolic_engine();
void print_symbolic_memory(uint64_t svc);
bool is_symbolic_value(uint64_t type, uint32_t mints_num, uint64_t lo, uint64_t up);
uint64_t is_safe_address(uint64_t vaddr, uint64_t reg);
uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);
uint64_t is_trace_space_available();

void ealloc();
void efree();

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint32_t data_type, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t step, std::vector<uint64_t>& ld_from, uint32_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb, uint64_t to_tc, uint64_t is_input);
void store_constrained_memory(uint64_t vaddr, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t step, std::vector<uint64_t>& ld_from, uint32_t ld_from_num, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t to_tc, uint64_t is_input);
void store_register_memory(uint64_t reg, uint64_t* value);

void constrain_memory(uint64_t reg, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t trb, bool only_reachable_branch);
void propagate_backwards(uint64_t vaddr, std::vector<uint64_t>& lo_before_op, std::vector<uint64_t>& up_before_op);
void propagate_mul(uint64_t step, uint64_t k);
void propagate_divu(uint64_t step, uint64_t k, uint64_t step_rd);
void propagate_remu(uint64_t step, uint64_t divisor);
void propagate_backwards_rhs(std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t mrvc);

void set_vaddrs(uint64_t reg, std::vector<uint64_t>& vaddrs, uint32_t start_idx, uint32_t vaddr_num);
void set_correction(uint64_t reg, uint32_t hasco, uint32_t hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity);

void take_branch(uint64_t b, uint64_t how_many_more);
void create_mconstraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
void create_mconstraints_rptr(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, uint64_t lo2, uint64_t up2, uint64_t trb);
void create_mconstraints_lptr(uint64_t lo1, uint64_t up1, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
void create_xor_mconstraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
void create_xor_mconstraints_rptr(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, uint64_t lo2, uint64_t up2, uint64_t trb);
void create_xor_mconstraints_lptr(uint64_t lo1, uint64_t up1, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);

uint64_t compute_upper_bound(uint64_t lo, uint64_t step, uint64_t value);