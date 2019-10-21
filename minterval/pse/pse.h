#include <stdint.h>
#include <iostream>
#include <fcntl.h>
#include <unistd.h>
#include <vector>
#include <string>
#include <fstream>
#include <iomanip>
#include <algorithm>
#include<iterator>
#include <sys/time.h>

#define RED   "\x1B[31m"
#define GREEN "\033[32m"
#define RESET "\x1B[0m"

// ---------------------------- PSE ----------------------------

struct node {
  uint8_t  type;
  uint64_t left_node;
  uint64_t right_node;
};

extern uint8_t      CONST, VAR, ADDI, ADD, SUB, MUL, DIVU, REMU, ILT, IGTE, IEQ, INEQ;
extern uint64_t     MAX_NODE_TRACE_LENGTH;
extern uint64_t     tree_tc;
extern struct node* pse_ast_nodes;
extern uint64_t*    pse_asts;
extern uint64_t*    reg_pse_ast;
extern uint64_t     zero_node;
extern uint64_t     one_node;
extern std::vector<std::string> pse_variables_per_path;
extern std::vector<std::string> pse_variables_per_multi_path;
extern std::vector<uint64_t>    path_condition;
extern std::vector<uint64_t>    false_branches;
extern std::vector<std::string> traversed_path_condition_elements;
extern std::string              path_condition_string;

uint64_t pse_operation(uint8_t typ, uint64_t left_node, uint64_t right_node);

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

// -----------------------------------------------------------------
// ---------------- Solver Aided Symbolic Execution ----------------
// -----------------------------------------------------------------

extern uint64_t  b;
extern uint64_t  SASE;
extern uint8_t   CONCRETE_T;
extern uint8_t   SYMBOLIC_T;

// symbolic registers
extern uint64_t* reg_pse_ast;
extern uint8_t*  pse_regs_typ;

// engine trace
extern uint64_t  sase_trace_size;
extern uint64_t  sase_tc;
extern uint64_t* sase_pcs;
extern uint64_t* sase_read_trace_ptrs;
extern uint64_t* sase_program_brks;
extern uint64_t* sase_store_trace_ptrs;
extern uint64_t* sase_rds;
extern uint64_t  mrif;

// store trace
extern uint64_t  tc;
extern uint64_t* tcs;
extern uint64_t* vaddrs;
extern uint64_t* values;
extern uint8_t*  is_symbolics;
extern uint64_t* symbolic_values;

// read trace
// TODO

// input trace
extern uint64_t  input_cnt;
extern uint64_t  input_cnt_current;

// ********************** engine functions ************************

void store_registers_fp_sp_rd();
void restore_registers_fp_sp_rd(uint64_t tr_cnt, uint64_t rd_reg);

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
void sase_backtrack_sltu(int is_true_branch_unreachable);
void sase_ld();
void sase_sd();
void sase_jal_jalr();
void sase_store_memory(uint64_t* pt, uint64_t vaddr, uint8_t is_symbolic, uint64_t value, uint64_t sym_value);
void backtrack_branch_stores();
void sase_backtrack_sltu(int is_true_branch_unreachable);