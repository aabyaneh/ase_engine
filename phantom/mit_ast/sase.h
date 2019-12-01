#include <iostream>
#include "boolector/boolector.h"

#include <fcntl.h>
#include <unistd.h>

#define RED   "\x1B[31m"
#define GREEN "\033[32m"
#define RESET "\x1B[0m"

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
extern uint64_t EXCEPTION_MAXTRACE;
extern uint64_t EXCEPTION_PAGEFAULT;
extern uint64_t EXCEPTION_INVALIDADDRESS;
extern uint64_t EXCEPTION_UNREACH_EXPLORE;
extern uint64_t EXITCODE_SYMBOLICEXECUTIONERROR;
extern uint64_t F3_ADD;
extern uint64_t F7_SUB;
extern uint64_t OP_IMM;
extern uint64_t OP_OP;
extern uint64_t F3_ADDI;
extern uint64_t F3_SLTU;

extern uint64_t entry_point;
extern uint64_t ic_addi;
extern uint64_t ic_sub;
extern uint64_t ic_xor;
extern uint64_t ic_sltu;
extern uint64_t ic_ld;
extern uint64_t ic_sd;

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
uint64_t is_system_register(uint64_t reg);

// -----------------------------------------------------------------
// ---------------- Solver Aided Symbolic Execution ----------------
// -----------------------------------------------------------------

extern char              var_buffer[100]; // a buffer for automatic variable name generation
extern Btor*             btor;
extern BoolectorSort     bv_sort;
extern BoolectorNode*    zero_bv;
extern BoolectorNode*    one_bv;
extern BoolectorNode*    eight_bv;
extern BoolectorNode*    meight_bv;
extern BoolectorNode*    twelve_bv;
extern uint64_t          b;
extern uint64_t          SASE;
extern uint8_t           CONCRETE_T;
extern uint8_t           SYMBOLIC_T;
extern uint64_t          two_to_the_power_of_32;

// symbolic registers
extern BoolectorNode**   sase_regs;
extern uint8_t*          sase_regs_typ;

// engine trace
extern uint64_t          sase_trace_size;
extern uint64_t          sase_tc;
extern uint64_t*         sase_pcs;
extern BoolectorNode**   sase_false_branchs;
extern uint64_t*         sase_read_trace_ptrs;
extern uint64_t*         sase_program_brks;
extern uint64_t*         sase_store_trace_ptrs;
extern uint64_t*         sase_rds;
extern uint64_t          mrif;

// store trace
extern uint64_t          tc;
extern uint64_t*         tcs;
extern uint64_t*         vaddrs;
extern uint64_t*         values;
extern uint8_t*          is_symbolics;
extern BoolectorNode**   symbolic_values;

// read trace
extern uint64_t*         concrete_reads;
extern BoolectorNode**   constrained_reads;
extern uint64_t          read_tc;
extern uint64_t          read_tc_current;
extern uint64_t          read_buffer;

// input trace
extern uint64_t          input_cnt;
extern uint64_t          input_cnt_current;
extern BoolectorNode**   constrained_inputs;

extern uint64_t          number_of_queries;

// ********************** engine functions ************************

BoolectorNode* boolector_unsigned_int_64(uint64_t value);
uint8_t match_sub(uint64_t prev_instr_rd);
uint8_t match_addi();
uint8_t check_next_1_instrs();
uint8_t check_next_3_instrs();
uint8_t check_conditional_type_lte_or_gte_();

void init_sase();
void sase_lui();
void sase_addi();
void sase_add();
void sase_sub();
void sase_mul();
void sase_divu();
void sase_remu();
void sase_xor();
void sase_sltu();
void sase_ld();
void sase_sd();
void sase_jal_jalr();
void sase_store_memory(uint64_t* pt, uint64_t vaddr, uint8_t is_symbolic, uint64_t value, BoolectorNode* sym_value);
void sase_backtrack_trace();
void backtrack_branch_stores();
void sase_backtrack_sltu(int is_true_branch_unreachable);