#include "stdint.h"
#include "stdbool.h"

// -----------------------------------------------------------------
// variables and procedures which will be defined in selfie.c
// and are needed in sase engine
// -----------------------------------------------------------------

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

extern uint64_t entry_point;

extern uint64_t* loads_per_instruction;
extern uint64_t* stores_per_instruction;

extern uint64_t ic_addi;
extern uint64_t ic_sub;
extern uint64_t ic_sltu;
extern uint64_t ic_ld;
extern uint64_t ic_sd;
extern uint64_t ic_xor;

extern uint64_t* pt;
extern uint64_t* current_context;
extern uint64_t* registers;

uint64_t* zalloc(uint64_t size);
uint64_t is_valid_virtual_address(uint64_t vaddr);
uint64_t get_page_of_virtual_address(uint64_t vaddr);
uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr);
void     store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);
uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);
void     throw_exception(uint64_t exception, uint64_t faulting_page);
uint64_t get_program_break(uint64_t* context);
void     set_program_break(uint64_t* context, uint64_t brk);
void     fetch();
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

// ---------------------------- SYMBOLIC----------------------------
extern uint64_t MSIIAD;

extern uint64_t debug_symbolic;
extern uint64_t symbolic;
extern uint64_t backtrack;

extern uint64_t rc;
extern uint64_t* read_values;
extern uint64_t* read_los;
extern uint64_t* read_ups;

extern uint64_t* reg_los;
extern uint64_t* reg_ups;
extern uint64_t* reg_steps;
extern uint8_t*  reg_data_typ;

extern uint64_t* values;
extern uint64_t* data_types;
extern uint64_t* los;
extern uint64_t* ups;

extern uint64_t mrcc;

// -----------------------------------------------------------------
// ----------------------- BUILTIN PROCEDURES ----------------------
// -----------------------------------------------------------------

void      exit(uint64_t code);
uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t  write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);
void*     malloc(uint64_t size);

// ------------------------ INSTRUCTIONS -----------------------

void constrain_lui();
void constrain_addi();
void constrain_add();
void constrain_sub();
void constrain_mul();
void constrain_divu();
void constrain_remu();
void constrain_sltu();
void constrain_jal_jalr();
uint64_t constrain_ld();
uint64_t constrain_sd();

void constrain_xor();
void do_xor();

void backtrack_sltu();
void backtrack_sd();
void backtrack_ecall();

void backtrack_trace(uint64_t* context);

void init_symbolic_engine();

void print_symbolic_memory(uint64_t svc);

uint64_t is_symbolic_value(uint64_t type, uint64_t lo, uint64_t up);
uint64_t is_safe_address(uint64_t vaddr, uint64_t reg);
uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);

uint64_t is_trace_space_available();

void ealloc();
void efree();

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint8_t data_type, uint64_t lo, uint64_t up, uint64_t step, uint64_t ld_from, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity, uint64_t trb);

void store_constrained_memory(uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t step, uint64_t ld_from, bool hasmn, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity);
void store_register_memory(uint64_t reg, uint64_t value);

void constrain_memory(uint64_t reg, uint64_t lo, uint64_t up, uint64_t trb, bool only_reachable_branch);
void propagate_backwards(uint64_t vaddr, uint64_t lo_before_op);

void set_constraint(uint64_t reg, uint64_t hasco, uint64_t vaddr, uint64_t hasmn);
void set_correction(uint64_t reg, uint64_t addsub_corr, uint64_t muldivrem_corr, uint64_t corr_validity);

void take_branch(uint64_t b, uint64_t how_many_more);
void create_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb);
