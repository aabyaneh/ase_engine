/*
  This project uses parts of the *Selfie Project* source code
  which is governed by a BSD license. For further information
  and LICENSE conditions see the following website:
  selfie.cs.uni-salzburg.at
*/

#ifndef FILE_ENGINE_INCLUDED
#define FILE_ENGINE_INCLUDED

#include <cstdint>
#include <iostream>
#include <fcntl.h>
#include <unistd.h>
#include <vector>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <algorithm>
#include <iterator>
#include "boolector.h"

#define RED     "\x1B[31m"
#define GREEN   "\033[32m"
#define BLUE    "\033[34m"
#define YELLOW  "\033[33m"
#define CYAN    "\x1B[36m"
#define MAGENTA "\x1B[35m"
#define RESET   "\x1B[0m"

// typedef unsigned long long uint64_t;

class engine {
  public:
    uint64_t CPUBITWIDTH         = 64;
    uint64_t SIZEOFUINT64        = 8; // must be the same as REGISTERSIZE
    uint64_t SIZEOFUINT64STAR    = 8; // must be the same as REGISTERSIZE
    uint64_t MAX_FILENAME_LENGTH = 128;
    uint64_t INT64_MAX_T;             // maximum numerical value of a signed 64-bit integer
    uint64_t INT64_MIN_T;             // minimum numerical value of a signed 64-bit integer
    uint64_t UINT64_MAX_T;            // maximum numerical value of an unsigned 64-bit integer
    uint64_t CHAR_BACKSPACE      = 8; // ASCII code 8  = backspace

    uint64_t* character_buffer; // buffer for reading and writing characters
    uint64_t* integer_buffer;   // buffer for printing integers
    uint64_t* filename_buffer;  // buffer for opening files
    uint64_t* binary_buffer;    // buffer for binary I/O
    uint64_t* power_of_two_table;

    uint64_t number_of_written_characters = 0;
    uint64_t output_fd = 1;     // 1 is file descriptor of standard output

    bool     IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT = false;

    // -----------------------------------------------------------------
    // ----------------------- LIBRARY PROCEDURES ----------------------
    // -----------------------------------------------------------------

    void init_library();
    void reset_library();

    uint64_t  two_to_the_power_of(uint64_t p);
    uint64_t  left_shift(uint64_t n, uint64_t b);
    uint64_t  right_shift(uint64_t n, uint64_t b);
    uint64_t  get_bits(uint64_t n, uint64_t i, uint64_t b);
    uint64_t  get_low_word(uint64_t n);
    uint64_t  get_high_word(uint64_t n);
    uint64_t  abs(uint64_t n);
    uint64_t  signed_less_than(uint64_t a, uint64_t b);
    uint64_t  signed_division(uint64_t a, uint64_t b);
    uint64_t  is_signed_integer(uint64_t n, uint64_t b);
    uint64_t  sign_extend(uint64_t n, uint64_t b);
    uint64_t  sign_shrink(uint64_t n, uint64_t b);
    uint64_t  load_character(uint64_t* s, uint64_t i);
    uint64_t* store_character(uint64_t* s, uint64_t i, uint64_t c);
    uint64_t  string_length(uint64_t* s);
    void      string_reverse(uint64_t* s);
    uint64_t* itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a);
    void      put_character(uint64_t c);
    void      print(uint64_t* s);
    void      print_integer(uint64_t n);
    void      unprint_integer(uint64_t n);
    uint64_t  round_up(uint64_t n, uint64_t m);
    uint64_t* smalloc(uint64_t size);
    uint64_t* zalloc(uint64_t size);

    // -----------------------------------------------------------------
    // ---------------------------- REGISTER ---------------------------
    // -----------------------------------------------------------------

    uint64_t NUMBEROFREGISTERS   = 32;
    uint64_t NUMBEROFTEMPORARIES = 7;

    uint64_t REG_ZR  = 0;
    uint64_t REG_RA  = 1;
    uint64_t REG_SP  = 2;
    uint64_t REG_GP  = 3;
    uint64_t REG_TP  = 4;
    uint64_t REG_T0  = 5;
    uint64_t REG_T1  = 6;
    uint64_t REG_T2  = 7;
    uint64_t REG_FP  = 8;
    uint64_t REG_S1  = 9;
    uint64_t REG_A0  = 10;
    uint64_t REG_A1  = 11;
    uint64_t REG_A2  = 12;
    uint64_t REG_A3  = 13;
    uint64_t REG_A4  = 14;
    uint64_t REG_A5  = 15;
    uint64_t REG_A6  = 16;
    uint64_t REG_A7  = 17;
    uint64_t REG_S2  = 18;
    uint64_t REG_S3  = 19;
    uint64_t REG_S4  = 20;
    uint64_t REG_S5  = 21;
    uint64_t REG_S6  = 22;
    uint64_t REG_S7  = 23;
    uint64_t REG_S8  = 24;
    uint64_t REG_S9  = 25;
    uint64_t REG_S10 = 26;
    uint64_t REG_S11 = 27;
    uint64_t REG_T3  = 28;
    uint64_t REG_T4  = 29;
    uint64_t REG_T5  = 30;
    uint64_t REG_T6  = 31;

    // -----------------------------------------------------------------
    // ------------------------ ENCODER/DECODER ------------------------
    // -----------------------------------------------------------------

    // opcodes
    uint64_t OP_LD     = 3;   // 0000011, I format (LD)
    uint64_t OP_IMM    = 19;  // 0010011, I format (ADDI, NOP)
    uint64_t OP_SD     = 35;  // 0100011, S format (SD)
    uint64_t OP_OP     = 51;  // 0110011, R format (ADD, SUB, MUL, DIVU, REMU, SLTU)
    uint64_t OP_LUI    = 55;  // 0110111, U format (LUI)
    uint64_t OP_BRANCH = 99;  // 1100011, B format (BEQ)
    uint64_t OP_JALR   = 103; // 1100111, I format (JALR)
    uint64_t OP_JAL    = 111; // 1101111, J format (JAL)
    uint64_t OP_SYSTEM = 115; // 1110011, I format (ECALL)

    // f3-codes
    uint64_t F3_NOP   = 0; // 000
    uint64_t F3_ADDI  = 0; // 000
    uint64_t F3_ADD   = 0; // 000
    uint64_t F3_SUB   = 0; // 000
    uint64_t F3_MUL   = 0; // 000
    uint64_t F3_XOR   = 4; // 100
    uint64_t F3_DIVU  = 5; // 101
    uint64_t F3_REMU  = 7; // 111
    uint64_t F3_SLTU  = 3; // 011
    uint64_t F3_LD    = 3; // 011
    uint64_t F3_SD    = 3; // 011
    uint64_t F3_BEQ   = 0; // 000
    uint64_t F3_JALR  = 0; // 000
    uint64_t F3_ECALL = 0; // 000

    // f7-codes
    uint64_t F7_ADD  = 0;  // 0000000
    uint64_t F7_MUL  = 1;  // 0000001
    uint64_t F7_SUB  = 32; // 0100000
    uint64_t F7_DIVU = 1;  // 0000001
    uint64_t F7_REMU = 1;  // 0000001
    uint64_t F7_SLTU = 0;  // 0000000
    uint64_t F7_XOR  = 0;  // 0000000

    // f12-codes (immediates)
    uint64_t F12_ECALL = 0; // 000000000000

    uint64_t opcode = 0;
    uint64_t rs1    = 0;
    uint64_t rs2    = 0;
    uint64_t rd     = 0;
    uint64_t imm    = 0;
    uint64_t funct3 = 0;
    uint64_t funct7 = 0;

    uint64_t encode_r_format(uint64_t funct7, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode);
    uint64_t get_funct7(uint64_t instruction);
    uint64_t get_rs2(uint64_t instruction);
    uint64_t get_rs1(uint64_t instruction);
    uint64_t get_funct3(uint64_t instruction);
    uint64_t get_rd(uint64_t instruction);
    uint64_t get_opcode(uint64_t instruction);
    void     decode_r_format();

    uint64_t encode_i_format(uint64_t immediate, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode);
    uint64_t get_immediate_i_format(uint64_t instruction);
    void     decode_i_format();

    uint64_t encode_s_format(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode);
    uint64_t get_immediate_s_format(uint64_t instruction);
    void     decode_s_format();

    uint64_t encode_b_format(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode);
    uint64_t get_immediate_b_format(uint64_t instruction);
    void     decode_b_format();

    uint64_t encode_j_format(uint64_t immediate, uint64_t rd, uint64_t opcode);
    uint64_t get_immediate_j_format(uint64_t instruction);
    void     decode_j_format();

    uint64_t encode_u_format(uint64_t immediate, uint64_t rd, uint64_t opcode);
    uint64_t get_immediate_u_format(uint64_t instruction);
    void     decode_u_format();

    // -----------------------------------------------------------------
    // ---------------------------- BINARY -----------------------------
    // -----------------------------------------------------------------

    uint64_t MAX_BINARY_LENGTH = 262144; // 256KB = MAX_CODE_LENGTH + MAX_DATA_LENGTH
    uint64_t MAX_CODE_LENGTH   = 245760; // 240KB
    uint64_t MAX_DATA_LENGTH   = 16384;  // 16KB
    uint64_t ELF_HEADER_LEN    = 120;    // = 64 + 56 bytes (file + program header)
    uint64_t ELF_ENTRY_POINT   = 65536;  // = 0x10000 (address of beginning of code); according to RISC-V pk

    // instruction counters
    uint64_t ic_lui   = 0;
    uint64_t ic_addi  = 0;
    uint64_t ic_add   = 0;
    uint64_t ic_sub   = 0;
    uint64_t ic_mul   = 0;
    uint64_t ic_divu  = 0;
    uint64_t ic_remu  = 0;
    uint64_t ic_xor   = 0;
    uint64_t ic_sltu  = 0;
    uint64_t ic_ld    = 0;
    uint64_t ic_sd    = 0;
    uint64_t ic_beq   = 0;
    uint64_t ic_jal   = 0;
    uint64_t ic_jalr  = 0;
    uint64_t ic_ecall = 0;

    char*     exe_name         = (char*) 0;
    uint64_t* binary           = (uint64_t*) 0; // binary of code and data segments
    uint64_t  binary_length    = 0;             // length of binary in bytes including data segment
    char*     binary_name      = (char*) 0;     // file name of binary
    uint64_t  code_length      = 0;             // length of code segment in binary in bytes
    uint64_t  entry_point      = 0;             // beginning of code segment in virtual address space
    uint64_t* code_line_number = (uint64_t*) 0; // code line number per emitted instruction
    uint64_t* data_line_number = (uint64_t*) 0; // data line number per emitted data
    uint64_t* ELF_header       = (uint64_t*) 0;

    void      reset_instruction_counters();
    uint64_t  get_total_number_of_instructions();
    void      print_instruction_counter(uint64_t total, uint64_t counter, char* mnemonics);
    void      print_instruction_counters();
    uint64_t  load_instruction(uint64_t baddr);
    void      store_instruction(uint64_t baddr, uint64_t instruction);
    uint64_t  load_data(uint64_t baddr);
    void      store_data(uint64_t baddr, uint64_t data);
    uint64_t* create_elf_header(uint64_t binary_length);
    uint64_t  validate_elf_header(uint64_t* header);
    uint64_t* touch(uint64_t* memory, uint64_t length);
    void      selfie_load(char* string);

    // -----------------------------------------------------------------
    // --------------------------- SYSCALLS ----------------------------
    // -----------------------------------------------------------------

    uint64_t SYSCALL_EXIT  = 93;
    uint64_t SYSCALL_READ  = 63;
    uint64_t SYSCALL_WRITE = 64;
    uint64_t SYSCALL_OPEN  = 1024;
    uint64_t SYSCALL_BRK   = 214;

    virtual uint64_t down_load_string(uint64_t* table, uint64_t vstring, uint64_t* s);
    virtual void implement_exit(uint64_t* context);
    virtual void implement_read(uint64_t* context);
    virtual void implement_write(uint64_t* context);
    virtual void implement_open(uint64_t* context);
    virtual void implement_brk(uint64_t* context);

    // -----------------------------------------------------------------
    // ---------------------------- MEMORY -----------------------------
    // -----------------------------------------------------------------

    uint64_t MEGABYTE          = 1048576;    // 1MB
    uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory
    uint64_t WORDSIZE          = 4;          // in bytes
    uint64_t WORDSIZEINBITS    = 32;
    uint64_t INSTRUCTIONSIZE   = 4;          // must be the same as WORDSIZE
    uint64_t REGISTERSIZE      = 8;          // must be twice of WORDSIZE
    uint64_t PAGESIZE          = 4096;       // we use standard 4KB pages
    uint64_t page_frame_memory = 0;          // size of memory for frames

    void      init_memory(uint64_t megabytes);
    uint64_t  load_physical_memory(uint64_t* paddr);
    void      store_physical_memory(uint64_t* paddr, uint64_t data);
    uint64_t  frame_for_page(uint64_t* table, uint64_t page);
    uint64_t  get_frame_for_page(uint64_t* table, uint64_t page);
    uint64_t  is_page_mapped(uint64_t* table, uint64_t page);
    uint64_t  is_valid_virtual_address(uint64_t vaddr);
    uint64_t  get_page_of_virtual_address(uint64_t vaddr);
    uint64_t  is_virtual_address_mapped(uint64_t* table, uint64_t vaddr);
    uint64_t* tlb(uint64_t* table, uint64_t vaddr);
    uint64_t  load_virtual_memory(uint64_t* table, uint64_t vaddr);
    void      store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);

    // -----------------------------------------------------------------
    // ------------------------- INSTRUCTIONS --------------------------
    // -----------------------------------------------------------------

    void do_lui();
    void do_addi();
    void do_add();
    void do_sub();
    void do_mul();
    void do_divu();
    void do_remu();
    void do_sltu();
    void do_xor();
    void do_jal();
    void do_jalr();
    void do_beq();
    void do_ecall();
    uint64_t do_ld();
    uint64_t do_sd();

    virtual void apply_lui();
    virtual void apply_addi();
    virtual void apply_add();
    virtual void apply_sub();
    virtual void apply_mul();
    virtual void apply_divu();
    virtual void apply_remu();
    virtual void apply_sltu();
    virtual void apply_xor();
    virtual void apply_jal();
    virtual void apply_jalr();
    virtual void apply_beq();
    virtual void apply_ecall();
    virtual uint64_t apply_ld();
    virtual uint64_t apply_sd();

    // -----------------------------------------------------------------
    // -------------------------- INTERPRETER --------------------------
    // -----------------------------------------------------------------

    uint64_t EXCEPTION_NOEXCEPTION        = 0;
    uint64_t EXCEPTION_PAGEFAULT          = 1;
    uint64_t EXCEPTION_SYSCALL            = 2;
    uint64_t EXCEPTION_TIMER              = 3;
    uint64_t EXCEPTION_INVALIDADDRESS     = 4;
    uint64_t EXCEPTION_DIVISIONBYZERO     = 5;
    uint64_t EXCEPTION_UNKNOWNINSTRUCTION = 6;
    uint64_t* EXCEPTIONS;    // strings representing exceptions
    uint64_t  TIMEROFF  = 0;
    uint64_t  execute   = 0; // flag for executing code
    uint64_t  pc = 0;        // program counter
    uint64_t  ir = 0;        // instruction register
    uint64_t* registers = (uint64_t*) 0; // general-purpose registers
    uint64_t* pt        = (uint64_t*) 0; // page table
    uint64_t  timer = 0;     // counter for timer interrupt
    uint64_t  trap  = 0;     // flag for creating a trap

    // profiling
    uint64_t  calls               = 0;                // total number of executed procedure calls
    uint64_t* calls_per_procedure = (uint64_t*) 0;    // number of executed calls of each procedure
    uint64_t  iterations          = 0;                // total number of executed loop iterations
    uint64_t* iterations_per_loop = (uint64_t*) 0;    // number of executed iterations of each loop
    uint64_t* loads_per_instruction  = (uint64_t*) 0; // number of executed loads per load instruction
    uint64_t* stores_per_instruction = (uint64_t*) 0; // number of executed stores per store instruction

    virtual void init_interpreter();
    void      reset_interpreter();
    void      print_exception(uint64_t exception, uint64_t faulting_page);
    void      throw_exception(uint64_t exception, uint64_t faulting_page);
    void      fetch();
    void      decode_execute();
    void      interrupt();
    uint64_t* run_until_exception();
    void      print_profile();

    // -----------------------------------------------------------------
    // ---------------------------- CONTEXTS ---------------------------
    // -----------------------------------------------------------------

    uint64_t* allocate_context(uint64_t* parent, uint64_t* vctxt, uint64_t* in);
    void      free_context(uint64_t* context);
    uint64_t* delete_context(uint64_t* context, uint64_t* from);

    // context struct:
    // +----+----------------+
    // |  0 | next context    | pointer to next context
    // |  1 | prev context    | pointer to previous context
    // |  2 | program counter | program counter
    // |  3 | regs            | pointer to general purpose registers
    // |  4 | page table      | pointer to page table
    // |  5 | lo page         | lowest low unmapped page
    // |  6 | me page         | highest low unmapped page
    // |  7 | hi page         | highest high unmapped page
    // |  8 | original break  | original end of data segment
    // |  9 | program break   | end of data segment
    // | 10 | exception       | exception ID
    // | 11 | faulting page   | faulting page
    // | 12 | exit code       | exit code
    // | 13 | parent          | context that created this context
    // | 14 | virtual context | virtual context address
    // | 15 | name            | binary name loaded into context
    // +----+-----------------+

    uint64_t next_context(uint64_t* context)    { return (uint64_t) context; }
    uint64_t prev_context(uint64_t* context)    { return (uint64_t) (context + 1); }
    uint64_t program_counter(uint64_t* context) { return (uint64_t) (context + 2); }
    uint64_t regs(uint64_t* context)            { return (uint64_t) (context + 3); }
    uint64_t page_table(uint64_t* context)      { return (uint64_t) (context + 4); }
    uint64_t lo_page(uint64_t* context)         { return (uint64_t) (context + 5); }
    uint64_t me_page(uint64_t* context)         { return (uint64_t) (context + 6); }
    uint64_t hi_page(uint64_t* context)         { return (uint64_t) (context + 7); }
    uint64_t original_break(uint64_t* context)  { return (uint64_t) (context + 8); }
    uint64_t program_break(uint64_t* context)   { return (uint64_t) (context + 9); }
    uint64_t exception(uint64_t* context)       { return (uint64_t) (context + 10); }
    uint64_t faulting_page(uint64_t* context)   { return (uint64_t) (context + 11); }
    uint64_t exit_code(uint64_t* context)       { return (uint64_t) (context + 12); }
    uint64_t parent(uint64_t* context)          { return (uint64_t) (context + 13); }
    uint64_t virtual_context(uint64_t* context) { return (uint64_t) (context + 14); }
    uint64_t name(uint64_t* context)            { return (uint64_t) (context + 15); }

    uint64_t* get_next_context(uint64_t* context)    { return (uint64_t*) *context; }
    uint64_t* get_prev_context(uint64_t* context)    { return (uint64_t*) *(context + 1); }
    uint64_t  get_pc(uint64_t* context)              { return             *(context + 2); }
    uint64_t* get_regs(uint64_t* context)            { return (uint64_t*) *(context + 3); }
    uint64_t* get_pt(uint64_t* context)              { return (uint64_t*) *(context + 4); }
    uint64_t  get_lo_page(uint64_t* context)         { return             *(context + 5); }
    uint64_t  get_me_page(uint64_t* context)         { return             *(context + 6); }
    uint64_t  get_hi_page(uint64_t* context)         { return             *(context + 7); }
    uint64_t  get_original_break(uint64_t* context)  { return             *(context + 8); }
    uint64_t  get_program_break(uint64_t* context)   { return             *(context + 9); }
    uint64_t  get_exception(uint64_t* context)       { return             *(context + 10); }
    uint64_t  get_faulting_page(uint64_t* context)   { return             *(context + 11); }
    uint64_t  get_exit_code(uint64_t* context)       { return             *(context + 12); }
    uint64_t* get_parent(uint64_t* context)          { return (uint64_t*) *(context + 13); }
    uint64_t* get_virtual_context(uint64_t* context) { return (uint64_t*) *(context + 14); }
    char*     get_name(uint64_t* context)            { return (char*)     *(context + 15); }

    void set_next_context(uint64_t* context, uint64_t* next)     { *context        = (uint64_t) next; }
    void set_prev_context(uint64_t* context, uint64_t* prev)     { *(context + 1)  = (uint64_t) prev; }
    void set_pc(uint64_t* context, uint64_t pc)                  { *(context + 2)  = pc; }
    void set_regs(uint64_t* context, uint64_t* regs)             { *(context + 3)  = (uint64_t) regs; }
    void set_pt(uint64_t* context, uint64_t* pt)                 { *(context + 4)  = (uint64_t) pt; }
    void set_lo_page(uint64_t* context, uint64_t lo_page)        { *(context + 5)  = lo_page; }
    void set_me_page(uint64_t* context, uint64_t me_page)        { *(context + 6)  = me_page; }
    void set_hi_page(uint64_t* context, uint64_t hi_page)        { *(context + 7)  = hi_page; }
    void set_original_break(uint64_t* context, uint64_t brk)     { *(context + 8)  = brk; }
    void set_program_break(uint64_t* context, uint64_t brk)      { *(context + 9)  = brk; }
    void set_exception(uint64_t* context, uint64_t exception)    { *(context + 10) = exception; }
    void set_faulting_page(uint64_t* context, uint64_t page)     { *(context + 11) = page; }
    void set_exit_code(uint64_t* context, uint64_t code)         { *(context + 12) = code; }
    void set_parent(uint64_t* context, uint64_t* parent)         { *(context + 13) = (uint64_t) parent; }
    void set_virtual_context(uint64_t* context, uint64_t* vctxt) { *(context + 14) = (uint64_t) vctxt; }
    void set_name(uint64_t* context, char* name)                 { *(context + 15) = (uint64_t) name; }

    // -----------------------------------------------------------------
    // -------------------------- MICROKERNEL --------------------------
    // -----------------------------------------------------------------

    void reset_microkernel();
    uint64_t* create_context(uint64_t* parent, uint64_t* vctxt);
    void map_page(uint64_t* context, uint64_t page, uint64_t frame);

    uint64_t* current_context = (uint64_t*) 0; // context currently running
    uint64_t* used_contexts   = (uint64_t*) 0; // doubly-linked list of used contexts
    uint64_t* free_contexts   = (uint64_t*) 0; // singly-linked list of free contexts

    // -----------------------------------------------------------------
    // ---------------------------- KERNEL -----------------------------
    // -----------------------------------------------------------------

    uint64_t* MY_CONTEXT = (uint64_t*) 0;

    uint64_t DONOTEXIT = 0;
    uint64_t EXIT      = 1;

    uint64_t EXITCODE_NOERROR                = 0;
    uint64_t EXITCODE_BADARGUMENTS           = 1;
    uint64_t EXITCODE_IOERROR                = 2;
    uint64_t EXITCODE_SCANNERERROR           = 3;
    uint64_t EXITCODE_PARSERERROR            = 4;
    uint64_t EXITCODE_COMPILERERROR          = 5;
    uint64_t EXITCODE_OUTOFVIRTUALMEMORY     = 6;
    uint64_t EXITCODE_OUTOFPHYSICALMEMORY    = 7;
    uint64_t EXITCODE_DIVISIONBYZERO         = 8;
    uint64_t EXITCODE_UNKNOWNINSTRUCTION     = 9;
    uint64_t EXITCODE_UNKNOWNSYSCALL         = 10;
    uint64_t EXITCODE_MULTIPLEEXCEPTIONERROR = 11;
    uint64_t EXITCODE_SYMBOLICEXECUTIONERROR = 12;
    uint64_t EXITCODE_OUTOFTRACEMEMORY       = 13;
    uint64_t EXITCODE_UNCAUGHTEXCEPTION      = 14;

    uint64_t SYSCALL_BITWIDTH = 32; // integer bit width for system calls

    uint64_t next_page_frame             = 0;
    uint64_t allocated_page_frame_memory = 0;
    uint64_t free_page_frame_memory      = 0;

    uint64_t  pavailable();
    uint64_t  pexcess();
    uint64_t  pused();
    uint64_t* palloc();
    void      pfree(uint64_t* frame);
    virtual   void      up_load_binary(uint64_t* context);
    uint64_t  handle_page_fault(uint64_t* context);
    uint64_t  handle_division_by_zero(uint64_t* context);
    uint64_t  handle_timer(uint64_t* context);
    virtual   uint64_t  handle_system_call(uint64_t* context);
    virtual   uint64_t  handle_exception(uint64_t* context);
    virtual   void      map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data);
    virtual   void      set_SP(uint64_t* context);
    virtual   void      init_engine(uint64_t peek_argument);
    virtual   uint64_t  run_engine(uint64_t* to_context);

};

#endif /* FILE_ENGINE_INCLUDED */