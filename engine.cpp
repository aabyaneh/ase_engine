/*
  This project uses parts of the *Selfie Project* source code
  which is governed by a BSD license. For further information
  and LICENSE conditions see the following website:
  selfie.cs.uni-salzburg.at
*/

#include "engine.hpp"

// ----------------------------- INITIALIZATION --------------------------------

void engine::init_library() {
  uint64_t i;

  // powers of two table with CPUBITWIDTH entries for 2^0 to 2^(CPUBITWIDTH - 1)
  power_of_two_table = smalloc(CPUBITWIDTH * SIZEOFUINT64);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < CPUBITWIDTH) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }

  // compute 64-bit unsigned integer range using signed integer arithmetic
  UINT64_MAX_T = -1;

  // compute 64-bit signed integer range using unsigned integer arithmetic
  INT64_MAX_T = two_to_the_power_of(CPUBITWIDTH - 1) - 1;
  INT64_MIN_T = INT64_MAX_T + 1;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = smalloc(SIZEOFUINT64);
  *character_buffer = 0;

  // accommodate at least CPUBITWIDTH numbers for itoa, no mapping needed
  integer_buffer = smalloc(CPUBITWIDTH + 1);

  // does not need to be mapped
  filename_buffer = smalloc(MAX_FILENAME_LENGTH);

  // allocate and touch to make sure memory is mapped for read calls
  binary_buffer  = smalloc(SIZEOFUINT64);
  *binary_buffer = 0;
}

void engine::reset_library() {
  number_of_written_characters = 0;
}

// -----------------------------------------------------------------------------
// ---------------------------------- MEMORY -----------------------------------
// -----------------------------------------------------------------------------

void engine::init_memory(uint64_t megabytes) {
  if (megabytes > 4096)
    megabytes = 4096;

  page_frame_memory = megabytes * MEGABYTE;
}

// -----------------------------------------------------------------------------
// -------------------------------- INTERPRETER --------------------------------
// -----------------------------------------------------------------------------

void engine::init_interpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_UNKNOWNINSTRUCTION + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)     = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
}

void engine::reset_interpreter() {
  pc = 0;
  ir = 0;

  registers = (uint64_t*) 0;

  pt = (uint64_t*) 0;

  trap = 0;

  timer = TIMEROFF;

  if (execute) {
    reset_instruction_counters();

    calls               = 0;
    calls_per_procedure = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);

    iterations          = 0;
    iterations_per_loop = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);

    loads_per_instruction  = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);
    stores_per_instruction = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);
  }
}

// -----------------------------------------------------------------------------
// ------------------------------ MICROKERNEL ----------------------------------
// -----------------------------------------------------------------------------

void engine::reset_microkernel() {
  current_context = (uint64_t*) 0;

  while (used_contexts != (uint64_t*) 0)
    used_contexts = delete_context(used_contexts, used_contexts);
}

// -----------------------------------------------------------------------------
// ---------------------------- LIBRARY PROCEDURES -----------------------------
// -----------------------------------------------------------------------------

uint64_t engine::two_to_the_power_of(uint64_t p) {
  // assert: 0 <= p < CPUBITWIDTH
  return *(power_of_two_table + p);
}

uint64_t engine::left_shift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n << b;
}

uint64_t engine::right_shift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n >> b;
}

uint64_t engine::get_bits(uint64_t n, uint64_t i, uint64_t b) {
  // assert: 0 < b <= i + b < CPUBITWIDTH
  if (i == 0)
    return n % two_to_the_power_of(b);
  else
    // shift to-be-loaded bits all the way to the left
    // to reset all bits to the left of them, then
    // shift to-be-loaded bits all the way to the right and return
    return right_shift(left_shift(n, CPUBITWIDTH - (i + b)), CPUBITWIDTH - b);
}

uint64_t engine::get_low_word(uint64_t n) {
  return get_bits(n, 0, WORDSIZEINBITS);
}

uint64_t engine::get_high_word(uint64_t n) {
  return get_bits(n, WORDSIZEINBITS, WORDSIZEINBITS);
}

uint64_t engine::abs(uint64_t n) {
  if (signed_less_than(n, 0))
    return -n;
  else
    return n;
}

uint64_t engine::signed_less_than(uint64_t a, uint64_t b) {
  // INT64_MIN <= n <= INT64_MAX iff
  // INT64_MIN + INT64_MIN <= n + INT64_MIN <= INT64_MAX + INT64_MIN iff
  // -2^64 <= n + INT64_MIN <= 2^64 - 1 (sign-extended to 65 bits) iff
  // 0 <= n + INT64_MIN <= UINT64_MAX
  return a + INT64_MIN_T < b + INT64_MIN_T;
}

uint64_t engine::signed_division(uint64_t a, uint64_t b) {
  // assert: b != 0
  // assert: a == INT64_MIN -> b != -1
  if (a == INT64_MIN_T)
    if (b == INT64_MIN_T)
      return 1;
    else if (signed_less_than(b, 0))
      return INT64_MIN_T / abs(b);
    else
      return -(INT64_MIN_T / b);
  else if (b == INT64_MIN_T)
    return 0;
  else if (signed_less_than(a, 0))
    if (signed_less_than(b, 0))
      return abs(a) / abs(b);
    else
      return -(abs(a) / b);
  else if (signed_less_than(b, 0))
    return -(a / abs(b));
  else
    return a / b;
}

uint64_t engine::is_signed_integer(uint64_t n, uint64_t b) {
  // assert: 0 < b <= CPUBITWIDTH
  if (n < two_to_the_power_of(b - 1))
    // assert: 0 <= n < 2^(b - 1)
    return 1;
  else if (n >= -two_to_the_power_of(b - 1))
    // assert: -2^(b - 1) <= n < 2^64
    return 1;
  else
    return 0;
}

uint64_t engine::sign_extend(uint64_t n, uint64_t b) {
  // assert: 0 <= n <= 2^b
  // assert: 0 < b < CPUBITWIDTH
  if (n < two_to_the_power_of(b - 1))
    return n;
  else
    return n - two_to_the_power_of(b);
}

uint64_t engine::sign_shrink(uint64_t n, uint64_t b) {
  // assert: -2^(b - 1) <= n < 2^(b - 1)
  // assert: 0 < b < CPUBITWIDTH
  return get_bits(n, 0, b);
}

uint64_t engine::load_character(uint64_t* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the double word where
  // the to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // return i-th 8-bit character in s
  return get_bits(*(s + a), (i % SIZEOFUINT64) * 8, 8);
}

uint64_t* engine::store_character(uint64_t* s, uint64_t i, uint64_t c) {
  // assert: i >= 0, 0 <= c < 2^8 (all characters are 8-bit)
  uint64_t a;

  // a is the index of the double word where
  // the with c to-be-overwritten i-th character in s is
  a = i / SIZEOFUINT64;

  // subtract the to-be-overwritten character to reset its bits in s
  // then add c to set its bits at the i-th position in s
  *(s + a) = (*(s + a) - left_shift(load_character(s, i), (i % SIZEOFUINT64) * 8)) + left_shift(c, (i % SIZEOFUINT64) * 8);

  return s;
}

uint64_t engine::string_length(uint64_t* s) {
  uint64_t i;

  i = 0;

  while (load_character(s, i) != 0)
    i = i + 1;

  return i;
}

void engine::string_reverse(uint64_t* s) {
  uint64_t i;
  uint64_t j;
  uint64_t tmp;

  i = 0;
  j = string_length(s) - 1;

  while (i < j) {
    tmp = load_character(s, i);

    store_character(s, i, load_character(s, j));
    store_character(s, j, tmp);

    i = i + 1;
    j = j - 1;
  }
}

uint64_t* engine::itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a) {
  // assert: b in {2,4,8,10,16}

  uint64_t i;
  uint64_t sign;

  // the conversion of the integer n to an ASCII string in s with
  // base b and alignment a begins with the leftmost digit in s
  i = 0;

  // for now assuming n is positive
  sign = 0;

  if (n == 0) {
    store_character(s, 0, '0');

    i = 1;
  } else if (signed_less_than(n, 0)) {
    if (b == 10) {
      // n is represented as two's complement
      // convert n to a positive number but remember the sign
      n = -n;

      sign = 1;
    }
  }

  while (n != 0) {
    if (n % b > 9)
      // the ASCII code of hexadecimal digits larger than 9
      // is offset by the ASCII code of 'A' (which is 65)
      store_character(s, i, n % b - 10 + 'A');
    else
      // the ASCII code of digits less than or equal to 9
      // is offset by the ASCII code of '0' (which is 48)
      store_character(s, i, n % b + '0');

    // convert n by dividing n with base b
    n = n / b;

    i = i + 1;
  }

  if (b == 10) {
    if (sign) {
      store_character(s, i, '-'); // negative decimal numbers start with -

      i = i + 1;
    }

    while (i < a) {
      store_character(s, i, ' '); // align with spaces

      i = i + 1;
    }
  } else {
    while (i < a) {
      store_character(s, i, '0'); // align with 0s

      i = i + 1;
    }

    if (b == 8) {
      store_character(s, i, '0'); // octal numbers start with 00
      store_character(s, i + 1, '0');

      i = i + 2;
    } else if (b == 16) {
      store_character(s, i, 'x'); // hexadecimal numbers start with 0x
      store_character(s, i + 1, '0');

      i = i + 2;
    }
  }

  store_character(s, i, 0); // null-terminated string

  // our numeral system is positional hindu-arabic, that is,
  // the weight of digits increases right to left, which means
  // that we need to reverse the string we computed above
  string_reverse(s);

  return s;
}

void engine::put_character(uint64_t c) {
  *character_buffer = c;

  // assert: character_buffer is mapped

  // try to write 1 character from character_buffer
  // into file with output_fd file descriptor
  if (write(output_fd, character_buffer, 1) == 1) {
    if (output_fd != 1)
      // count number of characters written to a file,
      // not the console which has file descriptor 1
      number_of_written_characters = number_of_written_characters + 1;
  } else {
    // write failed
    if (output_fd != 1) {
      // failed write was not to the console which has file descriptor 1
      // to report the error we may thus still write to the console
      output_fd = 1;

      std::cout << exe_name << ": could not write character to output file\n";
    }

    exit((int) EXITCODE_IOERROR);
  }
}

void engine::print(uint64_t* s) {
  uint64_t i;

  if (s == (uint64_t*) 0)
    print((uint64_t*) "NULL");
  else {
    i = 0;

    while (load_character(s, i) != 0) {
      put_character(load_character(s, i));

      i = i + 1;
    }
  }
}

void engine::print_integer(uint64_t n) {
  print(itoa(n, integer_buffer, 10, 0));
}

void engine::unprint_integer(uint64_t n) {
  n = string_length(itoa(n, integer_buffer, 10, 0));

  while (n > 0) {
    put_character(CHAR_BACKSPACE);

    n = n - 1;
  }
}

uint64_t engine::round_up(uint64_t n, uint64_t m) {
  if (n % m == 0)
    return n;
  else
    return n - n % m + m;
}

uint64_t* engine::smalloc(uint64_t size) {
  // this procedure ensures a defined program exit,
  // if no memory can be allocated
  uint64_t* memory;

  memory = (uint64_t*) malloc(size);

  if (size == 0)
    // any address including null
    return memory;
  else if ((uint64_t) memory == 0) {
    std::cout << exe_name << ": malloc out of memory\n";

    exit((int) EXITCODE_OUTOFVIRTUALMEMORY);
  }

  return memory;
}

uint64_t* engine::zalloc(uint64_t size) {
  // this procedure is only executed at boot level zero
  // zalloc allocates size bytes rounded up to word size
  // and then zeroes that memory, similar to calloc, but
  // called zalloc to avoid redeclaring calloc
  uint64_t* memory;
  uint64_t  i;

  size = round_up(size, REGISTERSIZE);

  memory = smalloc(size);

  size = size / REGISTERSIZE;

  i = 0;

  while (i < size) {
    // erase memory by setting it to 0
    *(memory + i) = 0;

    i = i + 1;
  }

  return memory;
}

// -----------------------------------------------------------------------------
// ------------------------------ ENCODER/DECODER ------------------------------
// -----------------------------------------------------------------------------

// RISC-V R Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |      funct7      | rs2 | rs1 |funct3|       rd        |opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t engine::get_funct7(uint64_t instruction) {
  return get_bits(instruction, 25, 7);
}

uint64_t engine::get_rs2(uint64_t instruction) {
  return get_bits(instruction, 20, 5);
}

uint64_t engine::get_rs1(uint64_t instruction) {
  return get_bits(instruction, 15, 5);
}

uint64_t engine::engine::get_funct3(uint64_t instruction) {
  return get_bits(instruction, 12, 3);
}

uint64_t engine::get_rd(uint64_t instruction) {
  return get_bits(instruction, 7, 5);
}

uint64_t engine::get_opcode(uint64_t instruction) {
  return get_bits(instruction, 0, 7);
}

void engine::decode_r_format() {
  funct7 = get_funct7(ir);
  rs2    = get_rs2(ir);
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = get_rd(ir);
  imm    = 0;
}

// RISC-V I Format
// ----------------------------------------------------------------
// |           12           |  5  |  3   |        5        |  7   |
// +------------------------+-----+------+-----------------+------+
// |    immediate[11:0]     | rs1 |funct3|       rd        |opcode|
// +------------------------+-----+------+-----------------+------+
// |31                    20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t engine::get_immediate_i_format(uint64_t instruction) {
  return sign_extend(get_bits(instruction, 20, 12), 12);
}

void engine::decode_i_format() {
  funct7 = 0;
  rs2    = 0;
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = get_rd(ir);
  imm    = get_immediate_i_format(ir);
}

// RISC-V S Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |    imm1[11:5]    | rs2 | rs1 |funct3|    imm2[4:0]    |opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t engine::get_immediate_s_format(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;

  imm1 = get_bits(instruction, 25, 7);
  imm2 = get_bits(instruction,  7, 5);

  return sign_extend(left_shift(imm1, 5) + imm2, 12);
}

void engine::decode_s_format() {
  funct7 = 0;
  rs2    = get_rs2(ir);
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = 0;
  imm    = get_immediate_s_format(ir);
}

// RISC-V B Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |imm1[12]imm2[10:5]| rs2 | rs1 |funct3|imm3[4:1]imm4[11]|opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t engine::get_immediate_b_format(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  imm1 = get_bits(instruction, 31, 1);
  imm2 = get_bits(instruction, 25, 6);
  imm3 = get_bits(instruction,  8, 4);
  imm4 = get_bits(instruction,  7, 1);

  // reassemble immediate and add trailing zero
  return sign_extend(left_shift(left_shift(left_shift(left_shift(imm1, 1) + imm4, 6) + imm2, 4) + imm3, 1), 13);
}

void engine::decode_b_format() {
  funct7 = 0;
  rs2    = get_rs2(ir);
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = 0;
  imm    = get_immediate_b_format(ir);
}

// RISC-V J Format
// ----------------------------------------------------------------
// |                  20                 |        5        |  7   |
// +-------------------------------------+-----------------+------+
// |imm1[20]imm2[10:1]imm3[11]imm4[19:12]|       rd        |opcode|
// +-------------------------------------+-----------------+------+
// |31                                 12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t engine::get_immediate_j_format(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  imm1 = get_bits(instruction, 31,  1);
  imm2 = get_bits(instruction, 21, 10);
  imm3 = get_bits(instruction, 20,  1);
  imm4 = get_bits(instruction, 12,  8);

  // reassemble immediate and add trailing zero
  return sign_extend(left_shift(left_shift(left_shift(left_shift(imm1, 8) + imm4, 1) + imm3, 10) + imm2, 1), 21);
}

void engine::decode_j_format() {
  funct7 = 0;
  rs2    = 0;
  rs1    = 0;
  funct3 = 0;
  rd     = get_rd(ir);
  imm    = get_immediate_j_format(ir);
}

// RISC-V U Format
// ----------------------------------------------------------------
// |                  20                 |        5        |  7   |
// +-------------------------------------+-----------------+------+
// |           immediate[19:0]           |       rd        |opcode|
// +-------------------------------------+-----------------+------+
// |31                                 12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t engine::get_immediate_u_format(uint64_t instruction) {
  return sign_extend(get_bits(instruction, 12, 20), 20);
}

void engine::decode_u_format() {
  funct7 = 0;
  rs2    = 0;
  rs1    = 0;
  funct3 = 0;
  rd     = get_rd(ir);
  imm    = get_immediate_u_format(ir);
}

// -----------------------------------------------------------------------------
// --------------------------------- BINARY ------------------------------------
// -----------------------------------------------------------------------------

void engine::reset_instruction_counters() {
  ic_lui   = 0;
  ic_addi  = 0;
  ic_add   = 0;
  ic_sub   = 0;
  ic_mul   = 0;
  ic_divu  = 0;
  ic_remu  = 0;
  ic_xor   = 0;
  ic_sltu  = 0;
  ic_ld    = 0;
  ic_sd    = 0;
  ic_beq   = 0;
  ic_jal   = 0;
  ic_jalr  = 0;
  ic_ecall = 0;
}

uint64_t engine::get_total_number_of_instructions() {
  return ic_lui + ic_addi + ic_add + ic_sub + ic_mul + ic_divu + ic_remu + ic_xor + ic_sltu + ic_ld + ic_sd + ic_beq + ic_jal + ic_jalr + ic_ecall;
}

void engine::print_instruction_counter(uint64_t total, uint64_t counter, char* mnemonics) {
  std::cout << mnemonics << ": " << counter;
}

void engine::print_instruction_counters() {
  uint64_t ic;

  ic = get_total_number_of_instructions();

  std::cout << exe_name << ": init:    ";
  print_instruction_counter(ic, ic_lui, "lui");
  std::cout << ", ";
  print_instruction_counter(ic, ic_addi, "addi");
  std::cout << '\n';

  std::cout << exe_name << ": memory:  ";
  print_instruction_counter(ic, ic_ld, "ld");
  std::cout << ", ";
  print_instruction_counter(ic, ic_sd, "sd");
  std::cout << '\n';

  std::cout << exe_name << ": compute: ";
  print_instruction_counter(ic, ic_add, "add");
  std::cout << ", ";
  print_instruction_counter(ic, ic_sub, "sub");
  std::cout << ", ";
  print_instruction_counter(ic, ic_mul, "mul");
  std::cout << ", ";
  print_instruction_counter(ic, ic_divu, "divu");
  std::cout << ", ";
  print_instruction_counter(ic, ic_remu, "remu");
  std::cout << ", ";
  print_instruction_counter(ic, ic_xor, "xor");
  std::cout << '\n';

  std::cout << exe_name << ": control: ";
  print_instruction_counter(ic, ic_sltu, "sltu");
  std::cout << ", ";
  print_instruction_counter(ic, ic_beq, "beq");
  std::cout << ", ";
  print_instruction_counter(ic, ic_jal, "jal");
  std::cout << ", ";
  print_instruction_counter(ic, ic_jalr, "jalr");
  std::cout << ", ";
  print_instruction_counter(ic, ic_ecall, "ecall");
  std::cout << '\n';
}

uint64_t engine::load_instruction(uint64_t baddr) {
  if (baddr % REGISTERSIZE == 0)
    return get_low_word(*(binary + baddr / REGISTERSIZE));
  else
    return get_high_word(*(binary + baddr / REGISTERSIZE));
}

uint64_t engine::load_data(uint64_t baddr) {
  return *(binary + baddr / REGISTERSIZE);
}

uint64_t* engine::create_elf_header(uint64_t binary_length) {
  uint64_t* header;

  // store all numbers necessary to create a minimal and valid
  // ELF64 header including the program header
  header = smalloc(ELF_HEADER_LEN);

  // RISC-U ELF64 file header:
  *(header + 0) = 127                               // magic number part 0 is 0x7F
                + left_shift((uint64_t) 'E', 8)     // magic number part 1
                + left_shift((uint64_t) 'L', 16)    // magic number part 2
                + left_shift((uint64_t) 'F', 24)    // magic number part 3
                + left_shift(2, 32)                 // file class is ELFCLASS64
                + left_shift(1, 40)                 // object file data structures endianess is ELFDATA2LSB
                + left_shift(1, 48);                // version of the object file format
  *(header + 1) = 0;                                // ABI version and start of padding bytes
  *(header + 2) = 2                                 // object file type is ET_EXEC
                + left_shift(243, 16)               // target architecture is RV64
                + left_shift(1, 32);                // version of the object file format
  *(header + 3) = ELF_ENTRY_POINT;                  // entry point address
  *(header + 4) = 8 * SIZEOFUINT64;                 // program header offset
  *(header + 5) = 0;                                // section header offset
  *(header + 6) = left_shift(8 * SIZEOFUINT64, 32)  // elf header size
                + left_shift(7 * SIZEOFUINT64, 48); // size of program header entry
  *(header + 7) = 1;                                // number of program header entries

  // RISC-U ELF64 program header table:
  *(header + 8)  = 1                              // type of segment is LOAD
                 + left_shift(7, 32);             // segment attributes is RWX
  *(header + 9)  = ELF_HEADER_LEN + SIZEOFUINT64; // segment offset in file
  *(header + 10) = ELF_ENTRY_POINT;               // virtual address in memory
  *(header + 11) = 0;                             // physical address (reserved)
  *(header + 12) = binary_length;                 // size of segment in file
  *(header + 13) = binary_length;                 // size of segment in memory
  *(header + 14) = PAGESIZE;                      // alignment of segment

  return header;
}

uint64_t engine::validate_elf_header(uint64_t* header) {
  uint64_t  new_entry_point;
  uint64_t  new_binary_length;
  uint64_t  position;
  uint64_t* valid_header;

  new_entry_point   = *(header + 10);
  new_binary_length = *(header + 12);

  if (new_binary_length != *(header + 13))
    // segment size in file is not the same as segment size in memory
    return 0;

  if (new_entry_point > VIRTUALMEMORYSIZE - PAGESIZE - new_binary_length)
    // binary does not fit into virtual address space
    return 0;

  valid_header = create_elf_header(new_binary_length);

  position = 0;

  while (position < ELF_HEADER_LEN / SIZEOFUINT64) {
    if (*(header + position) != *(valid_header + position))
      return 0;

    position = position + 1;
  }

  entry_point   = new_entry_point;
  binary_length = new_binary_length;

  return 1;
}

uint64_t* engine::touch(uint64_t* memory, uint64_t length) {
  uint64_t* m;
  uint64_t n;

  m = memory;

  if (length > 0)
    // touch memory at beginning
    n = *m;

  while (length > PAGESIZE) {
    length = length - PAGESIZE;

    m = m + PAGESIZE / REGISTERSIZE;

    // touch every following page
    n = *m;
  }

  if (length > 0) {
    m = m + (length - 1) / REGISTERSIZE;

    // touch at end
    n = *m;
  }

  // avoids unused warning for n
  n = 0; n = n + 1;

  return memory;
}

void engine::selfie_load(char* string) {
  uint64_t fd;
  uint64_t number_of_read_bytes;

  binary_name = string;

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  fd = sign_extend((uint64_t) open(binary_name, (int) O_RDONLY, (mode_t) 0), SYSCALL_BITWIDTH);

  if (signed_less_than(fd, 0)) {
    std::cout << exe_name << ": could not open input file " << binary_name << '\n';
    exit((int) EXITCODE_IOERROR);
  }

  // make sure binary is mapped for reading into it
  binary = touch(smalloc(MAX_BINARY_LENGTH), MAX_BINARY_LENGTH);

  binary_length = 0;
  code_length   = 0;
  entry_point   = 0;

  // no source line numbers in binaries
  code_line_number = (uint64_t*) 0;
  data_line_number = (uint64_t*) 0;

  // make sure ELF_header is mapped for reading into it
  ELF_header = touch(smalloc(ELF_HEADER_LEN), ELF_HEADER_LEN);

  // read ELF_header first
  number_of_read_bytes = read(fd, ELF_header, ELF_HEADER_LEN);

  if (number_of_read_bytes == ELF_HEADER_LEN) {
    if (validate_elf_header(ELF_header)) {
      // now read code length
      number_of_read_bytes = read(fd, binary_buffer, SIZEOFUINT64);

      if (number_of_read_bytes == SIZEOFUINT64) {
        code_length = *binary_buffer;

        if (binary_length <= MAX_BINARY_LENGTH) {
          // now read binary including global variables and strings
          number_of_read_bytes = sign_extend(read(fd, binary, binary_length), SYSCALL_BITWIDTH);

          if (signed_less_than(0, number_of_read_bytes)) {
            // check if we are really at EOF
            if (read(fd, binary_buffer, SIZEOFUINT64) == 0) {
              std::cout << exe_name << ": "
                << (int64_t) (ELF_HEADER_LEN + SIZEOFUINT64 + binary_length)
                << " bytes with "
                << (int64_t) (code_length / INSTRUCTIONSIZE)
                << " instructions and "
                << (int64_t) (binary_length - code_length)
                << " bytes of data loaded from "
                << binary_name << '\n';

              return;
            }
          }
        }
      }
    }
  }

  std::cout << exe_name << ": failed to load code from input file " << binary_name << '\n';
  exit((int) EXITCODE_IOERROR);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

uint64_t engine::load_physical_memory(uint64_t* paddr) {
  return *paddr;
}

void engine::store_physical_memory(uint64_t* paddr, uint64_t data) {
  *paddr = data;
}

uint64_t engine::frame_for_page(uint64_t* table, uint64_t page) {
  return (uint64_t) (table + page);
}

uint64_t engine::get_frame_for_page(uint64_t* table, uint64_t page) {
  return *(table + page);
}

uint64_t engine::is_page_mapped(uint64_t* table, uint64_t page) {
  if (get_frame_for_page(table, page) != 0)
    return 1;
  else
    return 0;
}

uint64_t engine::is_valid_virtual_address(uint64_t vaddr) {
  if (vaddr < VIRTUALMEMORYSIZE)
    // memory must be word-addressed for lack of byte-sized data type
    if (vaddr % REGISTERSIZE == 0)
      return 1;

  return 0;
}

uint64_t engine::get_page_of_virtual_address(uint64_t vaddr) {
  return vaddr / PAGESIZE;
}

uint64_t engine::is_virtual_address_mapped(uint64_t* table, uint64_t vaddr) {
  // assert: is_valid_virtual_address(vaddr) == 1

  return is_page_mapped(table, get_page_of_virtual_address(vaddr));
}

uint64_t* engine::tlb(uint64_t* table, uint64_t vaddr) {
  uint64_t page;
  uint64_t frame;
  uint64_t paddr;

  // assert: is_valid_virtual_address(vaddr) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  page = get_page_of_virtual_address(vaddr);

  frame = get_frame_for_page(table, page);

  // map virtual address to physical address
  paddr = vaddr - page * PAGESIZE + frame;

  return (uint64_t*) paddr;
}

uint64_t engine::load_virtual_memory(uint64_t* table, uint64_t vaddr) {
  // assert: is_valid_virtual_address(vaddr) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  return load_physical_memory(tlb(table, vaddr));
}

void engine::store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data) {
  // assert: is_valid_virtual_address(vaddr) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  store_physical_memory(tlb(table, vaddr), data);
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void engine::print_exception(uint64_t exception, uint64_t faulting_page) {
  std::cout << reinterpret_cast<char*>(*(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    std::cout << " at " << (uint64_t*) faulting_page;
}

void engine::throw_exception(uint64_t exception, uint64_t faulting_page) {
  if (get_exception(current_context) != EXCEPTION_NOEXCEPTION)
    if (get_exception(current_context) != exception) {
      std::cout << exe_name << ": context " << (uint64_t*) current_context << " throws ";
      print_exception(exception, faulting_page);
      std::cout << " exception in presence of ";
      print_exception(get_exception(current_context), get_faulting_page(current_context));
      std::cout << " exception\n";

      exit((int) EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  set_exception(current_context, exception);
  set_faulting_page(current_context, faulting_page);

  trap = 1;
}

void engine::fetch() {
  // assert: is_valid_virtual_address(pc) == 1
  // assert: is_virtual_address_mapped(pt, pc) == 1

  if (pc % REGISTERSIZE == 0)
    ir = get_low_word(load_virtual_memory(pt, pc));
  else
    ir = get_high_word(load_virtual_memory(pt, pc - INSTRUCTIONSIZE));
}

void engine::decode_execute() {
  opcode = get_opcode(ir);

  if (opcode == OP_IMM) {
    decode_i_format();
    if (funct3 == F3_ADDI) {
      apply_addi();
      return;
    }

  } else if (opcode == OP_LD) {
    decode_i_format();
    if (funct3 == F3_LD) {
      apply_ld();
      return;
    }

  } else if (opcode == OP_SD) {
    decode_s_format();
    if (funct3 == F3_SD) {
      apply_sd();
      return;
    }

  } else if (opcode == OP_OP) { // could be ADD, SUB, MUL, DIVU, REMU, SLTU
    decode_r_format();
    if (funct3 == F3_ADD) { // = F3_SUB = F3_MUL
      if (funct7 == F7_ADD) {
        apply_add();
        return;

      } else if (funct7 == F7_SUB) {
        apply_sub();
        return;
      } else if (funct7 == F7_MUL) {
        apply_mul();
        return;
      }

    } else if (funct3 == F3_DIVU) {
      if (funct7 == F7_DIVU) {
        apply_divu();
        return;
      }

    } else if (funct3 == F3_REMU) {
      if (funct7 == F7_REMU) {
        apply_remu();
        return;
      }

    } else if (funct3 == F3_SLTU) {
      if (funct7 == F7_SLTU) {
        apply_sltu();
        return;
      }

    } else if (funct3 == F3_XOR) {
      if (funct7 == F7_XOR) {
        apply_xor();
        return;
      }
    }

  } else if (opcode == OP_BRANCH) {
    decode_b_format();
    if (funct3 == F3_BEQ) {
      apply_beq();
      return;
    }

  } else if (opcode == OP_JAL) {
    decode_j_format();
    apply_jal();
    return;

  } else if (opcode == OP_JALR) {
    decode_i_format();
    if (funct3 == F3_JALR) {
      apply_jalr();
      return;
    }

  } else if (opcode == OP_LUI) {
    decode_u_format();
    apply_lui();
    return;

  } else if (opcode == OP_SYSTEM) {
    decode_i_format();
    if (funct3 == F3_ECALL) {
      apply_ecall();
      return;
    }
  }

  if (execute)
    throw_exception(EXCEPTION_UNKNOWNINSTRUCTION, 0);
  else {
    //report the error on the console
    output_fd = 1;

    std::cout << exe_name << ": unknown instruction with " << std::hex << (int64_t) opcode << "opcode detected" << std::dec << std::endl;

    exit((int) EXITCODE_UNKNOWNINSTRUCTION);
  }
}

void engine::interrupt() {
  if (timer != TIMEROFF) {
    timer = timer - 1;

    if (timer == 0) {
      if (get_exception(current_context) == EXCEPTION_NOEXCEPTION)
        // only throw exception if no other is pending
        // TODO: handle multiple pending exceptions
        throw_exception(EXCEPTION_TIMER, 0);
      else
        // trigger timer in the next interrupt cycle
        timer = 1;
    }
  }
}

uint64_t* engine::run_until_exception() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode_execute();
    interrupt();
  }

  trap = 0;

  return current_context;
}

void engine::print_profile() {
  std::cout << exe_name << ": summary: " <<
    (int64_t) get_total_number_of_instructions() << " executed instructions and " <<
    std::fixed << std::setprecision(2) << (double) pused() / MEGABYTE << "MB(" <<
    ((double) pused() / page_frame_memory) * 100 << "%) mapped memory\n";

  if (get_total_number_of_instructions() > 0) {
    print_instruction_counters();
  }
}

// -----------------------------------------------------------------------------
// ---------------------------------- CONTEXTS ---------------------------------
// -----------------------------------------------------------------------------

uint64_t* engine::allocate_context(uint64_t* parent, uint64_t* vctxt, uint64_t* in) {
  uint64_t* context;

  if (free_contexts == (uint64_t*) 0)
    context = smalloc(7 * SIZEOFUINT64STAR + 9 * SIZEOFUINT64);
  else {
    context = free_contexts;

    free_contexts = get_next_context(free_contexts);
  }

  set_next_context(context, in);
  set_prev_context(context, (uint64_t*) 0);

  if (in != (uint64_t*) 0)
    set_prev_context(in, context);

  set_pc(context, 0);

  // allocate zeroed memory for general purpose registers
  // TODO: reuse memory
  set_regs(context, zalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  set_pt(context, zalloc(VIRTUALMEMORYSIZE / PAGESIZE * REGISTERSIZE));

  // determine range of recently mapped pages
  set_lo_page(context, 0);
  set_me_page(context, 0);
  set_hi_page(context, get_page_of_virtual_address(VIRTUALMEMORYSIZE - REGISTERSIZE));

  set_exception(context, EXCEPTION_NOEXCEPTION);
  set_faulting_page(context, 0);

  set_exit_code(context, EXITCODE_NOERROR);

  set_parent(context, parent);
  set_virtual_context(context, vctxt);

  set_name(context, (char*) 0);

  return context;
}

void engine::free_context(uint64_t* context) {
  set_next_context(context, free_contexts);

  free_contexts = context;
}

uint64_t* engine::delete_context(uint64_t* context, uint64_t* from) {
  if (get_next_context(context) != (uint64_t*) 0)
    set_prev_context(get_next_context(context), get_prev_context(context));

  if (get_prev_context(context) != (uint64_t*) 0) {
    set_next_context(get_prev_context(context), get_next_context(context));
    set_prev_context(context, (uint64_t*) 0);
  } else
    from = get_next_context(context);

  free_context(context);

  return from;
}

// -----------------------------------------------------------------------------
// ------------------------------ MICROKERNEL ----------------------------------
// -----------------------------------------------------------------------------

uint64_t* engine::create_context(uint64_t* parent, uint64_t* vctxt) {
  // TODO: check if context already exists
  used_contexts = allocate_context(parent, vctxt, used_contexts);

  if (current_context == (uint64_t*) 0)
    current_context = used_contexts;

  return used_contexts;
}

void engine::map_page(uint64_t* context, uint64_t page, uint64_t frame) {
  uint64_t* table;

  table = get_pt(context);

  // assert: 0 <= page < VIRTUALMEMORYSIZE / PAGESIZE

  *(table + page) = frame;

  if (page <= get_page_of_virtual_address(get_program_break(context) - REGISTERSIZE)) {
    // exploit spatial locality in page table caching
    if (page < get_lo_page(context))
      set_lo_page(context, page);
    else if (page > get_me_page(context))
      set_me_page(context, page);
  }
}

// -----------------------------------------------------------------------------
// ------------------------------- KERNEL --------------------------------------
// -----------------------------------------------------------------------------

uint64_t engine::pavailable() {
  if (free_page_frame_memory > 0)
    return 1;
  else if (allocated_page_frame_memory + MEGABYTE <= page_frame_memory)
    return 1;
  else
    return 0;
}

uint64_t engine::pexcess() {
  if (pavailable())
    return 1;
  else if (allocated_page_frame_memory + MEGABYTE <= 2 * page_frame_memory)
    // tolerate twice as much memory mapped on demand than physically available
    return 1;
  else
    return 0;
}

uint64_t engine::pused() {
  return allocated_page_frame_memory - free_page_frame_memory;
}

uint64_t* engine::palloc() {
  uint64_t block;
  uint64_t frame;

  // assert: page_frame_memory is equal to or a multiple of MEGABYTE
  // assert: PAGESIZE is a factor of MEGABYTE strictly less than MEGABYTE

  if (free_page_frame_memory == 0) {
    if (pexcess()) {
      free_page_frame_memory = MEGABYTE;

      // on boot level zero allocate zeroed memory
      block = (uint64_t) zalloc(free_page_frame_memory);

      allocated_page_frame_memory = allocated_page_frame_memory + free_page_frame_memory;

      // page frames must be page-aligned to work as page table index
      next_page_frame = round_up(block, PAGESIZE);

      if (next_page_frame > block)
        // losing one page frame to fragmentation
        free_page_frame_memory = free_page_frame_memory - PAGESIZE;
    } else {
      std::cout << exe_name << ": palloc out of physical memory\n";

      exit((int) EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  frame = next_page_frame;

  next_page_frame = next_page_frame + PAGESIZE;

  free_page_frame_memory = free_page_frame_memory - PAGESIZE;

  // strictly, touching is only necessary on boot levels higher than zero
  return touch((uint64_t*) frame, PAGESIZE);
}

void engine::pfree(uint64_t* frame) {
  // TODO: implement free list of page frames
}

void engine::up_load_binary(uint64_t* context) {
  uint64_t baddr;

  // assert: entry_point is multiple of PAGESIZE and REGISTERSIZE

  set_pc(context, entry_point);
  set_lo_page(context, get_page_of_virtual_address(entry_point));
  set_me_page(context, get_page_of_virtual_address(entry_point));
  set_original_break(context, entry_point + binary_length);
  set_program_break(context, get_original_break(context));

  baddr = 0;

  while (baddr < binary_length) {
    map_and_store(context, entry_point + baddr, load_data(baddr));

    baddr = baddr + REGISTERSIZE;
  }

  set_name(context, binary_name);
}

uint64_t engine::handle_page_fault(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  // TODO: use this table to unmap and reuse frames
  map_page(context, get_faulting_page(context), (uint64_t) palloc());

  return DONOTEXIT;
}

uint64_t engine::handle_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  std::cout << exe_name << " ****************************************\n";
  std::cout << exe_name << ": division by zero at 0x" << std::hex << pc - entry_point << std::dec << "; engine stops\n";
  std::cout << exe_name << " ****************************************\n";
  exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

  set_exit_code(context, EXITCODE_DIVISIONBYZERO);

  return EXIT;
}

uint64_t engine::handle_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  return DONOTEXIT;
}

// -----------------------------------------------------------------------------
// --------------------------------- SYSCALLS ----------------------------------
// -----------------------------------------------------------------------------

void engine::implement_exit(uint64_t* context) {

  set_exit_code(context, sign_shrink(*(get_regs(context) + REG_A0), SYSCALL_BITWIDTH));

  std::cout << std::fixed << exe_name << ": " << get_name(context)
    << " exiting with exit code " << (int64_t) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH)
    << " and " << std::setprecision(2) << (double) (get_program_break(context) - get_original_break(context)) / MEGABYTE << "MB mallocated memory\n";
}

void engine::implement_read(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t read_total;
  uint64_t bytes_to_read;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_read;

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  read_total   = 0;
  bytes_to_read = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_read)
          bytes_to_read = size;

        actually_read = sign_extend(read(fd, buffer, bytes_to_read), SYSCALL_BITWIDTH);

        if (actually_read == bytes_to_read) {
          read_total = read_total + actually_read;

          size = size - actually_read;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signed_less_than(0, actually_read))
            read_total = read_total + actually_read;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;
      }
    } else {
      failed = 1;

      size = 0;
    }
  }

  if (failed == 0)
    *(get_regs(context) + REG_A0) = read_total;
  else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void engine::implement_write(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t written_total;
  uint64_t bytes_to_write;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_written;

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  written_total = 0;
  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_write)
          bytes_to_write = size;

        actually_written = sign_extend(write(fd, buffer, bytes_to_write), SYSCALL_BITWIDTH);

        if (actually_written == bytes_to_write) {
          written_total = written_total + actually_written;

          size = size - actually_written;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signed_less_than(0, actually_written))
            written_total = written_total + actually_written;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;
      }
    } else {
      failed = 1;

      size = 0;
    }
  }

  if (failed == 0)
    *(get_regs(context) + REG_A0) = written_total;
  else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

uint64_t engine::down_load_string(uint64_t* table, uint64_t vaddr, uint64_t* s) {
  uint64_t mrvc;
  uint64_t i;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (is_virtual_address_mapped(table, vaddr)) {
        *(s + i) = load_virtual_memory(table, vaddr);
        j = 0;

        // check if string ends in the current machine word
        while (j < SIZEOFUINT64) {
          if (load_character(s + i, j) == 0)
            return 1;

          j = j + 1;
        }

        // advance to the next machine word in virtual memory
        vaddr = vaddr + SIZEOFUINT64;

        // advance to the next machine word in our memory
        i = i + 1;
      }
    }
  }

  return 0;
}

void engine::implement_open(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  // return value
  uint64_t fd;

  vfilename = *(get_regs(context) + REG_A0);
  flags     = *(get_regs(context) + REG_A1);
  mode      = *(get_regs(context) + REG_A2);

  if (down_load_string(get_pt(context), vfilename, filename_buffer)) {
    fd = sign_extend((uint64_t) open(reinterpret_cast<char*>(filename_buffer), (int) flags, (mode_t) mode), SYSCALL_BITWIDTH);

    *(get_regs(context) + REG_A0) = fd;
  } else {
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void engine::implement_brk(uint64_t* context) {
  // parameter
  uint64_t program_break;

  // local variables
  uint64_t previous_program_break;
  uint64_t valid;
  uint64_t size;

  program_break = *(get_regs(context) + REG_A0);

  previous_program_break = get_program_break(context);

  valid = 0;

  if (program_break >= previous_program_break)
    if (program_break < *(get_regs(context) + REG_SP))
      if (program_break % SIZEOFUINT64 == 0)
        valid = 1;

  if (valid) {
    set_program_break(context, program_break);

  } else {
    // error returns current program break
    program_break = previous_program_break;

    *(get_regs(context) + REG_A0) = program_break;
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// -----------------------------------------------------------------------------
// ------------------------------ INSTRUCTIONS ---------------------------------
// -----------------------------------------------------------------------------

void engine::do_lui() {
  // load upper immediate

  if (rd != REG_ZR)
    // semantics of lui
    *(registers + rd) = left_shift(imm, 12);

  pc = pc + INSTRUCTIONSIZE;

  ic_lui = ic_lui + 1;
}

void engine::do_addi() {
  // add immediate

  if (rd != REG_ZR)
    // semantics of addi
    *(registers + rd) = *(registers + rs1) + imm;

  pc = pc + INSTRUCTIONSIZE;

  ic_addi = ic_addi + 1;
}

void engine::do_add() {
  if (rd != REG_ZR)
    // semantics of add
    *(registers + rd) = *(registers + rs1) + *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_add = ic_add + 1;
}

void engine::do_sub() {
  if (rd != REG_ZR)
    // semantics of sub
    *(registers + rd) = *(registers + rs1) - *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_sub = ic_sub + 1;
}

void engine::do_mul() {
  if (rd != REG_ZR)
    // semantics of mul
    *(registers + rd) = *(registers + rs1) * *(registers + rs2);

  // TODO: 128-bit resolution currently not supported

  pc = pc + INSTRUCTIONSIZE;

  ic_mul = ic_mul + 1;
}

void engine::do_divu() {
  // division unsigned

  if (*(registers + rs2) != 0) {
    if (rd != REG_ZR)
      // semantics of divu
      *(registers + rd) = *(registers + rs1) / *(registers + rs2);

    pc = pc + INSTRUCTIONSIZE;

    ic_divu = ic_divu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

void engine::do_remu() {
  // remainder unsigned

  if (*(registers + rs2) != 0) {
    if (rd != REG_ZR)
      // semantics of remu
      *(registers + rd) = *(registers + rs1) % *(registers + rs2);

    pc = pc + INSTRUCTIONSIZE;

    ic_remu = ic_remu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

void engine::do_xor() {
  if (rd != REG_ZR) {
    registers[rd] = registers[rs1] ^ registers[rs2];

    pc = pc + INSTRUCTIONSIZE;

    ic_xor = ic_xor + 1;
  }
}

void engine::do_sltu() {
  // set on less than unsigned

  if (rd != REG_ZR) {
    // semantics of sltu
    if (*(registers + rs1) < *(registers + rs2))
      *(registers + rd) = 1;
    else
      *(registers + rd) = 0;
  }

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
}

uint64_t engine::do_ld() {
  uint64_t vaddr;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (rd != REG_ZR)
        // semantics of ld
        *(registers + rd) = load_virtual_memory(pt, vaddr);

      // keep track of instruction address for profiling loads
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of loads in total
      ic_ld = ic_ld + 1;

      // and individually
      *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

uint64_t engine::do_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // semantics of sd
      store_virtual_memory(pt, vaddr, *(registers + rs2));

      // keep track of instruction address for profiling stores
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of stores in total
      ic_sd = ic_sd + 1;

      // and individually
      *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

void engine::do_beq() {
  // branch on equal

  // semantics of beq
  if (*(registers + rs1) == *(registers + rs2))
    pc = pc + imm;
  else
    pc = pc + INSTRUCTIONSIZE;

  ic_beq = ic_beq + 1;
}

void engine::do_jal() {
  uint64_t a;

  // jump and link

  if (rd != REG_ZR) {
    // first link
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // then jump for procedure calls
    pc = pc + imm;

    // prologue address for profiling procedure calls
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    // keep track of number of procedure calls in total
    calls = calls + 1;

    // and individually
    *(calls_per_procedure + a) = *(calls_per_procedure + a) + 1;
  } else if (signed_less_than(imm, 0)) {
    // jump backwards to check for another loop iteration
    pc = pc + imm;

    // first loop instruction address for profiling loop iterations
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    // keep track of number of loop iterations in total
    iterations = iterations + 1;

    // and individually
    *(iterations_per_loop + a) = *(iterations_per_loop + a) + 1;
  } else
    // just jump forward
    pc = pc + imm;

  ic_jal = ic_jal + 1;
}

void engine::do_jalr() {
  uint64_t next_pc;

  // jump and link register

  if (rd == REG_ZR)
    // fast path: just return by jumping rs1-relative with LSB reset
    pc = left_shift(right_shift(*(registers + rs1) + imm, 1), 1);
  else {
    // slow path: first prepare jump, then link, just in case rd == rs1

    // prepare jump with LSB reset
    next_pc = left_shift(right_shift(*(registers + rs1) + imm, 1), 1);

    // link to next instruction
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // jump
    pc = next_pc;
  }

  ic_jalr = ic_jalr + 1;
}

void engine::do_ecall() {
  ic_ecall = ic_ecall + 1;

  // all system calls other than switch are handled by exception
  throw_exception(EXCEPTION_SYSCALL, 0);
}

// ------------------------- apply instructions --------------------------------

void engine::apply_lui() {
  do_lui();
}

void engine::apply_addi() {
  do_addi();
}

void engine::apply_add() {
  do_add();
}

void engine::apply_sub() {
  do_sub();
}

void engine::apply_mul() {
  do_mul();
}

void engine::apply_divu() {
  do_divu();
}

void engine::apply_remu() {
  do_remu();
}

void engine::apply_xor() {
  do_xor();
}

void engine::apply_sltu() {
  do_sltu();
}

uint64_t engine::apply_ld() {
  return do_ld();
}

uint64_t engine::apply_sd() {
  return do_sd();
}

void engine::apply_beq() {
  do_beq();
}

void engine::apply_jal() {
  do_jal();
}

void engine::apply_jalr() {
  do_jalr();
}

void engine::apply_ecall() {
  do_ecall();
}

// -----------------------------------------------------------------------------
// ---------------------------------- KERNEL -----------------------------------
// -----------------------------------------------------------------------------

void engine::map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data) {
  // assert: is_valid_virtual_address(vaddr) == 1

  if (is_virtual_address_mapped(get_pt(context), vaddr) == 0)
    map_page(context, get_page_of_virtual_address(vaddr), (uint64_t) palloc());

  store_virtual_memory(get_pt(context), vaddr, data);
}


void engine::set_SP(uint64_t* context) {
  uint64_t SP;

  // the call stack grows top down
  SP = VIRTUALMEMORYSIZE - REGISTERSIZE;

  // store stack pointer value in stack pointer register
  *(get_regs(context) + REG_SP) = SP;
}

uint64_t engine::handle_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK)
    implement_brk(context);
  else if (a7 == SYSCALL_READ)
    implement_read(context);
  else if (a7 == SYSCALL_WRITE)
    implement_write(context);
  else if (a7 == SYSCALL_OPEN)
    implement_open(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    std::cout << exe_name << ": unknown system call " << (int64_t) a7 << '\n';

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t engine::handle_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_division_by_zero(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_timer(context);
  else {
    std::cout << exe_name << ": context " << get_name(context) << " throws uncaught ";
    print_exception(exception, get_faulting_page(context));
    std::cout << '\n';

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

void engine::init_engine(uint64_t peek_argument) {
  init_library();
  init_interpreter();

  init_memory(peek_argument);
}

uint64_t engine::run_engine(uint64_t* to_context) {
  registers = get_regs(to_context);
  pt        = get_pt(to_context);

  while (1) {
    // restore machine state
    pc = get_pc(current_context);

    run_until_exception();

    // save machine state
    set_pc(current_context, pc);

    if (handle_exception(current_context) == EXIT) {
      return get_exit_code(current_context);
    }
  }
}