#include "mit_bvt_engine.hpp"

// ---------------------------- auxiliary functions ----------------------------

uint64_t compute_upper_bound_mit(uint64_t lo, uint64_t step, uint64_t value);

bool mit_bvt_engine::vector_contains_element(std::vector<uint64_t>& vector, uint64_t element) {
  for (std::vector<uint64_t>::iterator it = vector.begin(); it != vector.end(); ++it) {
    if (*it == element)
      return true;
  }

  return false;
}

void mit_bvt_engine::merge_arrays(std::vector<uint64_t>& vector_1, std::vector<uint64_t>& vector_2, size_t vector_1_size, size_t vector_2_size) {
  merged_array.clear();
  for (size_t i = 0; i < vector_1_size; i++) {
    merged_array.push_back(vector_1[i]);
  }
  for (size_t i = 0; i < vector_2_size; i++) {
    if (vector_contains_element(vector_1, vector_2[i])) continue;
    merged_array.push_back(vector_2[i]);
  }
}

// ------------------------- INITIALIZATION ------------------------

void mit_bvt_engine::init_engine(uint64_t peek_argument) {
  init_library();
  init_interpreter();
  init_memory(round_up(10 * MAX_TRACE_LENGTH * SIZEOFUINT64, MEGABYTE) / MEGABYTE + 1);

  // -------------------------
  // trace data-structure
  // -------------------------
  pcs                   = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  tcs                   = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  vaddrs                = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  values                = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  data_types            = (uint8_t*)  malloc(MAX_TRACE_LENGTH  * sizeof(uint8_t) );
  asts                  = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  mr_sds                = (uint64_t*) malloc(MAX_TRACE_LENGTH  * sizeof(uint64_t));
  theory_types          = (uint8_t*)  malloc(MAX_TRACE_LENGTH  * sizeof(uint8_t) );
  bvt_false_branches    = (BoolectorNode**) malloc(MAX_TRACE_LENGTH  * sizeof(BoolectorNode*));

  // -------------------------
  // read trace
  // -------------------------
  // read_values
  // read_los
  // read_ups

  // -------------------------
  // registers
  // -------------------------
  reg_data_type            = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t));
  reg_symb_type            = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t));
  reg_mintervals_los.resize(NUMBEROFREGISTERS);
  reg_mintervals_ups.resize(NUMBEROFREGISTERS);
  reg_steps                = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_mintervals_cnts      = (uint32_t*) malloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_involved_inputs.resize(NUMBEROFREGISTERS);
  reg_involved_inputs_cnts = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_asts                 = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_theory_types         = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t) );
  reg_bvts                 = (BoolectorNode**) malloc(NUMBEROFREGISTERS * sizeof(BoolectorNode*));
  reg_hasmn                = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t) );
  reg_addsub_corr          = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_corr_validity        = (uint8_t*)  zalloc(NUMBEROFREGISTERS * sizeof(uint8_t) );

  // -------------------------
  // AST nodes trace
  // -------------------------
  mintervals_los.reserve(MAX_AST_NODES_TRACE_LENGTH);
  mintervals_ups.reserve(MAX_AST_NODES_TRACE_LENGTH);
  store_trace_ptrs.reserve(MAX_AST_NODES_TRACE_LENGTH);
  involved_sym_inputs_ast_tcs.reserve(MAX_AST_NODES_TRACE_LENGTH);
  mintervals_los.resize(AST_NODES_TRACE_LENGTH);
  mintervals_ups.resize(AST_NODES_TRACE_LENGTH);
  store_trace_ptrs.resize(AST_NODES_TRACE_LENGTH);
  involved_sym_inputs_ast_tcs.resize(AST_NODES_TRACE_LENGTH);
  steps                    = (uint64_t*)       malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(uint64_t));
  ast_nodes                = (struct node*)    malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(struct node*));
  involved_sym_inputs_cnts = (uint64_t*)       malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(uint64_t));
  theory_type_ast_nodes    = (uint8_t*)        malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(uint8_t));
  smt_exprs                = (BoolectorNode**) malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(BoolectorNode*));

  // -------------------------
  // branch evaluation
  // -------------------------
  zero_v.push_back(0);
  one_v.push_back(1);
  value_v.push_back(0);
  true_branch_rs1_minterval_los.resize(MAX_NUM_OF_INTERVALS);
  true_branch_rs1_minterval_ups.resize(MAX_NUM_OF_INTERVALS);
  false_branch_rs1_minterval_los.resize(MAX_NUM_OF_INTERVALS);
  false_branch_rs1_minterval_ups.resize(MAX_NUM_OF_INTERVALS);
  true_branch_rs2_minterval_los.resize(MAX_NUM_OF_INTERVALS);
  true_branch_rs2_minterval_ups.resize(MAX_NUM_OF_INTERVALS);
  false_branch_rs2_minterval_los.resize(MAX_NUM_OF_INTERVALS);
  false_branch_rs2_minterval_ups.resize(MAX_NUM_OF_INTERVALS);

  propagated_minterval_lo.resize(MAX_NUM_OF_INTERVALS);
  propagated_minterval_up.resize(MAX_NUM_OF_INTERVALS);

  // -------------------------
  // SMT solver
  // -------------------------
  btor        = boolector_new();
  bv_sort     = boolector_bitvec_sort(btor, 64);
  boolector_set_opt(btor, BTOR_OPT_INCREMENTAL, 1);
  boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);
  zero_bv     = boolector_unsigned_int(btor, 0, bv_sort);
  one_bv      = boolector_unsigned_int(btor, 1, bv_sort);

  // -------------------------
  // initialization
  // -------------------------
  zero_node = add_ast_node(CONST, 0, 0, 1, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null);
  one_node  = add_ast_node(CONST, 0, 0, 1, one_v , one_v , 1, 0, zero_v, MIT, boolector_null);
  smt_exprs[zero_node] = zero_bv;
  smt_exprs[one_node]  = one_bv;

  reg_asts[REG_ZR] = zero_node;

  for (size_t i = 0; i < NUMBEROFREGISTERS; i++) {
    reg_steps[i]           = 1;
    reg_mintervals_cnts[i] = 1;
    reg_mintervals_los[i].resize(MAX_NUM_OF_INTERVALS);
    reg_mintervals_ups[i].resize(MAX_NUM_OF_INTERVALS);
    reg_involved_inputs[i].resize(MAX_NUM_OF_INVOLVED_INPUTS);
  }

  pcs[0]                = 0;
  tcs[0]                = 0;
  vaddrs[0]             = 0;
  values[0]             = 0;
  data_types[0]         = 0;
  asts[0]               = 0;
  mr_sds[0]             = 0;
  theory_types[0]       = 0;
  bvt_false_branches[0] = boolector_null;

  steps[0]                    = 0;
  involved_sym_inputs_cnts[0] = 0;
  theory_type_ast_nodes[0]    = 0;
  smt_exprs[0]                = boolector_null;

  input_table.reserve(1024);
  path_condition.reserve(1024);

  TWO_TO_THE_POWER_OF_32 = 4294967296ULL;

  if (IS_TEST_MODE) {
    std::string test_output = binary_name;
    test_output += ".result";
    output_results.open(test_output, std::ofstream::trunc);
  }
}

void mit_bvt_engine::print_input_witness(size_t i, size_t j, uint64_t input, uint64_t lo, uint64_t up, uint64_t step) {
  std::cout << std::left << MAGENTA "--INPUT :=  id: " << std::setw(3) << i+1 << ", #: " << std::setw(2) << j << " , abstraction: " << get_abstraction(theory_type_ast_nodes[input]) << " => [lo: " << std::setw(5) << lo << ", up: " << std::setw(5) << up << ", step: " << step << "]" << RESET << std::endl;
}

void mit_bvt_engine::witness_profile() {
  // uint64_t cardinality;

  current_number_of_witnesses = 1;

  if (IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT) std::cout << "\n-------------------------------------------------------------\n";

  for (size_t i = 0; i < input_table.size(); i++) {
    // cardinality = 0;
    for (size_t j = 0; j < mintervals_los[input_table[i]].size(); j++) {
      // cardinality += (mintervals_ups[input_table[i]][j] - mintervals_los[input_table[i]][j]) / steps[input_table[i]] + 1;

      if (IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT) print_input_witness(i, j, input_table[i], mintervals_los[input_table[i]][j], mintervals_ups[input_table[i]][j], steps[input_table[i]]);
    }

    // if (cardinality > 0) {
    //   if (is_number_of_generated_witnesses_overflowed == false) {
    //     if (current_number_of_witnesses * cardinality > UINT64_MAX_T) // overflow?
    //       is_number_of_generated_witnesses_overflowed = true;
    //     else
    //       current_number_of_witnesses *= cardinality;
    //   }
    // } else
    //   std::cout << exe_name << ": cardinality of an input is == zero! " << std::endl;
  }

  // if (current_number_of_witnesses > max_number_of_generated_witnesses_among_all_paths)
  //   max_number_of_generated_witnesses_among_all_paths = current_number_of_witnesses;
  //
  // total_number_of_generated_witnesses_for_all_paths += current_number_of_witnesses;
  // if (total_number_of_generated_witnesses_for_all_paths < current_number_of_witnesses) // overflow?
  //   is_number_of_generated_witnesses_overflowed = true;
}

void print_execution_info(uint64_t paths, uint64_t total_number_of_generated_witnesses_for_all_paths, uint64_t max_number_of_generated_witnesses_among_all_paths, uint64_t queries_reasoned_by_mit, uint64_t queries_reasoned_by_bvt, bool is_number_of_generated_witnesses_overflowed) {
  std::cout << "\n\n";
  std::cout << YELLOW "number of explored paths:= " << paths << RESET << std::endl;

  // if (is_number_of_generated_witnesses_overflowed == false)
  //   std::cout << "number of witnesses:= total: " << total_number_of_generated_witnesses_for_all_paths << ", max: " << max_number_of_generated_witnesses_among_all_paths << std::endl;
  // else
  //   std::cout << "number of witnesses:= total: > " << UINT64_MAX << ", max: !" << std::endl;

  std::cout << GREEN "number of queries:= mit: " << queries_reasoned_by_mit << ", bvt: " << queries_reasoned_by_bvt << RESET << "\n\n";
}

uint64_t mit_bvt_engine::run_engine(uint64_t* to_context) {
  registers = get_regs(to_context);
  pt        = get_pt(to_context);

  while (1) {
    // restore machine state
    pc = get_pc(current_context);

    run_until_exception();

    // save machine state
    set_pc(current_context, pc);

    if (handle_exception(current_context) == EXIT) {
      if (IS_TEST_MODE) {
        for (size_t j = 0; j < input_table.size(); j++) {
          for (size_t i = 0; i < mintervals_los[input_table[j]].size(); i++) {
            output_results << std::left << "I=" << j+1 << ";" << i+1 << ";" << mintervals_los[input_table[j]][i] << ";" << mintervals_ups[input_table[j]][i] << ";" << steps[input_table[j]] << std::endl;
          }
        }
        output_results << "B=" << paths+1 << "\n";
      }

      if (paths == 0) std::cout << exe_name << ": backtracking \n"; else unprint_integer(paths);
      paths++;
      print_integer(paths);
      witness_profile();

      backtrack_trace(current_context);

      if (pc == 0) {
        print_execution_info(paths, total_number_of_generated_witnesses_for_all_paths, max_number_of_generated_witnesses_among_all_paths, queries_reasoned_by_mit, queries_reasoned_by_bvt, is_number_of_generated_witnesses_overflowed);

        if (symbolic_input_cnt != 0)
          std::cout << "symbolic_input_cnt is not zero!\n";

        if (IS_TEST_MODE)
          output_results.close();

        return EXITCODE_NOERROR;
      }
    }

    if (is_execution_timeout) {
      print_execution_info(paths, total_number_of_generated_witnesses_for_all_paths, max_number_of_generated_witnesses_among_all_paths, queries_reasoned_by_mit, queries_reasoned_by_bvt, is_number_of_generated_witnesses_overflowed);

      return EXITCODE_TIMEOUT;
    }
  }
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void mit_bvt_engine::init_interpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_MAXTRACE + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)     = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_MAXTRACE)           = (uint64_t) "trace length exceeded";
}

void mit_bvt_engine::map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data) {
  // assert: is_valid_virtual_address(vaddr) == 1
  uint64_t ast_ptr;

  if (is_virtual_address_mapped(get_pt(context), vaddr) == 0)
    map_page(context, get_page_of_virtual_address(vaddr), (uint64_t) palloc());

  if (is_trace_space_available()) {
    // always track initialized memory by using tc as most recent branch
    value_v[0] = data;
    ast_ptr = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v, MIT, boolector_null);
    store_symbolic_memory(get_pt(context), vaddr, data, 0, ast_ptr, tc, 1, MIT);

  } else {
    std::cout << exe_name << ": ealloc out of memory\n";
    exit((int) EXITCODE_OUTOFTRACEMEMORY);
  }
}

void mit_bvt_engine::set_SP(uint64_t* context) {
  uint64_t SP;

  // the call stack grows top down
  SP = VIRTUALMEMORYSIZE - REGISTERSIZE;

  // set bounds to register value for symbolic execution
  get_regs(context)[REG_SP]        = SP;
  reg_data_type[REG_SP]            = VALUE_T;
  reg_symb_type[REG_SP]            = CONCRETE;
  reg_mintervals_los[REG_SP][0]    = SP;
  reg_mintervals_ups[REG_SP][0]    = SP;
  reg_mintervals_cnts[REG_SP]      = 1;
  reg_steps[REG_SP]                = 1;
  reg_involved_inputs_cnts[REG_SP] = 0;
  reg_asts[REG_SP]                 = 0;
  reg_bvts[REG_SP]                 = boolector_null;
  reg_theory_types[REG_SP]         = MIT;
  set_correction(REG_SP, 0, 0, 0);
}

void mit_bvt_engine::up_load_binary(uint64_t* context) {
  uint64_t baddr;

  // assert: entry_point is multiple of PAGESIZE and REGISTERSIZE

  set_pc(context, entry_point);
  set_lo_page(context, get_page_of_virtual_address(entry_point));
  set_me_page(context, get_page_of_virtual_address(entry_point));
  set_original_break(context, entry_point + binary_length);
  set_program_break(context, get_original_break(context));

  baddr = 0;

  while (baddr < code_length) {
    engine::map_and_store(context, entry_point + baddr, load_data(baddr));

    baddr = baddr + REGISTERSIZE;
  }

  while (baddr < binary_length) {
    map_and_store(context, entry_point + baddr, load_data(baddr));

    baddr = baddr + REGISTERSIZE;
  }

  set_name(context, binary_name);
}

uint64_t mit_bvt_engine::handle_system_call(uint64_t* context) {
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
  else if (a7 == SYSCALL_SYMPOLIC_INPUT)
    implement_symbolic_input(context);
  else if (a7 == SYSCALL_PRINTSV)
    implement_printsv(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  }
  else {
    std::cout << exe_name << ": unknown system call " << (int64_t) a7 << '\n';
    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  if (get_exception(context) == EXCEPTION_MAXTRACE) {
    // exiting during symbolic execution, no exit code necessary
    set_exception(context, EXCEPTION_NOEXCEPTION);

    return EXIT;
  } else
    return DONOTEXIT;
}

uint64_t mit_bvt_engine::handle_max_trace(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_exit_code(context, EXITCODE_OUTOFTRACEMEMORY);

  std::cout << exe_name << " ***************************************\n";
  std::cout << exe_name << " max trace is reached; engine backtracks\n";
  std::cout << exe_name << " ***************************************\n";

  return EXIT;
}

uint64_t mit_bvt_engine::handle_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_division_by_zero(context);
  else if (exception == EXCEPTION_MAXTRACE)
    return handle_max_trace(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_timer(context);
  else {
    std::cout << exe_name << ": context " << get_name(context) << "throws uncaught ";
    print_exception(exception, get_faulting_page(context));
    std::cout << '\n';

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

// -----------------------------------------------------------------
// ------------------------- SMT Solver ----------------------------
// -----------------------------------------------------------------

BoolectorNode* mit_bvt_engine::boolector_unsigned_int_64(uint64_t value) {
  if (value < TWO_TO_THE_POWER_OF_32) {
    return boolector_unsigned_int(btor, value, bv_sort);
  } else {
    sprintf(const_buffer, "%llu", value);
    return boolector_constd(btor, bv_sort, const_buffer);
  }
}

// -----------------------------------------------------------------
// --------------------------- SYSCALLS ----------------------------
// -----------------------------------------------------------------

void mit_bvt_engine::implement_exit(uint64_t* context) {
  set_exit_code(context, sign_shrink(get_regs(context)[REG_A0], SYSCALL_BITWIDTH));
}

void mit_bvt_engine::implement_read(uint64_t* context) {
  std::cout << exe_name << ": symbolic read is not implemented yet\n";
}

std::string mit_bvt_engine::get_abstraction(uint8_t abstraction) {
  if (abstraction == MIT)
    return "MIT";
  else if (abstraction == BOX)
    return "BOX";
  else if (abstraction == BVT)
    return "BVT";
  else
    return "UNKNOWN";
}

void mit_bvt_engine::implement_printsv(uint64_t* context) {
  uint64_t id;

  id = get_regs(context)[REG_A0];

  std::cout << "\n------------------------------------------------------------\n";

  for (size_t i = 0; i < reg_mintervals_cnts[REG_A1]; i++) {
    std::cout << std::left << "PRINTSV :=) id: " << std::setw(3) << id << ", #: " << std::setw(2) << i << " , abstraction: " << get_abstraction(reg_theory_types[REG_A1]) << " => [lo: " << std::setw(5) << reg_mintervals_los[REG_A1][i] << ", up: " << std::setw(5) << reg_mintervals_ups[REG_A1][i] << ", step: " << reg_steps[REG_A1] << "]\n";
  }

  for (size_t j = 0; j < input_table.size(); j++) {
    for (size_t i = 0; i < mintervals_los[input_table[j]].size(); i++) {
      std::cout << std::left << RED "--INPUT :=  id: " << std::setw(3) << j+1 << ", #: " << std::setw(2) << i << " , abstraction: " << get_abstraction(theory_type_ast_nodes[input_table[j]]) << " => [lo: " << std::setw(5) << mintervals_los[input_table[j]][i] << ", up: " << std::setw(5) << mintervals_ups[input_table[j]][i] << ", step: " << steps[input_table[j]] << "]" << RESET << '\n';
    }
  }

  if (IS_TEST_MODE) {
    for (size_t i = 0; i < reg_mintervals_cnts[REG_A1]; i++) {
      output_results << std::left << "P=" << id << ";" << i+1 << ";" << reg_mintervals_los[REG_A1][i] << ";" << reg_mintervals_ups[REG_A1][i] << ";" << reg_steps[REG_A1] << std::endl;
    }
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void mit_bvt_engine::implement_symbolic_input(uint64_t* context) {
  uint64_t lo;
  uint64_t up;
  uint64_t step;
  uint64_t addr;
  uint64_t ast_ptr;
  BoolectorNode* in;
  std::vector<uint64_t> value_v_1(1);
  std::vector<uint64_t> value_v_2(1);

  addr = *(get_regs(context) + REG_A0);
  lo   = *(get_regs(context) + REG_A1);
  up   = *(get_regs(context) + REG_A2);
  step = *(get_regs(context) + REG_A3);

  // it needs page fault to assign memory for addr
  if (is_valid_virtual_address(addr)) {
    if (is_virtual_address_mapped(get_pt(context), addr) == 0)
      map_page(context, get_page_of_virtual_address(addr), (uint64_t) palloc());
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, addr);

  // model range interval as SMT solver input variable
  sprintf(var_buffer, "in_%llu", symbolic_input_cnt);
  boolector_push(btor, 1);
  in = boolector_var(btor, bv_sort, var_buffer);
  // <= up
  boolector_assert(btor, boolector_ulte(btor, in, boolector_unsigned_int_64(up)));
  // >= lo
  boolector_assert(btor, boolector_ugte(btor, in, boolector_unsigned_int_64(lo)));

  if (step != 1) {
    std::cout << exe_name << ": the step of an input interval has to be 1; try to create a step using the multiplication operation. \n";
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (lo > up) {
    std::cout << exe_name << ": an input interval cannot be wrapped; try to create a wrapped interval using the addition operation. \n";
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  // create AST node
  value_v_1[0] = lo; value_v_2[0] = compute_upper_bound_mit(lo, step, up);
  ast_ptr = add_ast_node(VAR, 0, symbolic_input_cnt, 1, value_v_1, value_v_2, step, 0, zero_v, MIT, in);

  // store in symbolic memory
  store_symbolic_memory(pt, addr, lo, VALUE_T, ast_ptr, tc, 1, MIT);

  // insert in input table
  input_table.push_back(ast_ptr);
  input_table_store_trace_ptr.push_back(tc);

  // print on console
  // std::cout << std::left << "read symbolic input interval # " << std::setw(3) << symbolic_input_cnt << " => [lo: " << std::setw(3) << value_v_1[0] << ", up: " << std::setw(5) << value_v_2[0] << ", step: " << step << "]\n";

  symbolic_input_cnt++;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void mit_bvt_engine::implement_write(uint64_t* context) {
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

  fd      = get_regs(context)[REG_A0];
  vbuffer = get_regs(context)[REG_A1];
  size    = get_regs(context)[REG_A2];

  written_total = 0;
  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_write)
          bytes_to_write = size;

        actually_written = bytes_to_write;

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
    get_regs(context)[REG_A0] = written_total;
  else
    get_regs(context)[REG_A0] = sign_shrink(-1, SYSCALL_BITWIDTH);

  reg_data_type[REG_A0]            = VALUE_T;
  reg_symb_type[REG_A0]            = CONCRETE;
  reg_mintervals_los[REG_A0][0]    = get_regs(context)[REG_A0];
  reg_mintervals_ups[REG_A0][0]    = get_regs(context)[REG_A0];
  reg_mintervals_cnts[REG_A0]      = 1;
  reg_steps[REG_A0]                = 1;
  reg_involved_inputs_cnts[REG_A0] = 0;
  reg_asts[REG_A0]                 = 0;
  reg_bvts[REG_A0]                 = boolector_null;
  reg_theory_types[REG_A0]         = MIT;
  set_correction(REG_A0, 0, 0, 0);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

uint64_t mit_bvt_engine::down_load_string(uint64_t* table, uint64_t vaddr, uint64_t* s) {
  uint64_t mrvc;
  uint64_t i;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (is_virtual_address_mapped(table, vaddr)) {
        mrvc = load_symbolic_memory(table, vaddr);

        *(s + i) = *(values + mrvc);

        if (is_symbolic_value(data_types[mrvc], mintervals_los[mrvc].size(), mintervals_los[mrvc][0], mintervals_ups[mrvc][0], MIT)) {
          std::cout << exe_name << ": detected symbolic value in filename of open call\n";
          exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
        }

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

void mit_bvt_engine::implement_open(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  // return value
  uint64_t fd;

  vfilename = get_regs(context)[REG_A0];
  flags     = get_regs(context)[REG_A1];
  mode      = get_regs(context)[REG_A2];

  if (down_load_string(get_pt(context), vfilename, filename_buffer)) {
    fd = sign_extend((uint64_t) open(reinterpret_cast<char*>(filename_buffer), (int) flags, (mode_t) mode), SYSCALL_BITWIDTH);

    get_regs(context)[REG_A0] = fd;
  } else {
    get_regs(context)[REG_A0] = sign_shrink(-1, SYSCALL_BITWIDTH);
  }

  reg_data_type[REG_A0]            = VALUE_T;
  reg_symb_type[REG_A0]            = CONCRETE;
  reg_mintervals_los[REG_A0][0]    = get_regs(context)[REG_A0];
  reg_mintervals_ups[REG_A0][0]    = get_regs(context)[REG_A0];
  reg_mintervals_cnts[REG_A0]      = 1;
  reg_steps[REG_A0]                = 1;
  reg_involved_inputs_cnts[REG_A0] = 0;
  reg_asts[REG_A0]                 = 0;
  reg_bvts[REG_A0]                 = boolector_null;
  reg_theory_types[REG_A0]         = MIT;
  set_correction(REG_A0, 0, 0, 0);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void mit_bvt_engine::implement_brk(uint64_t* context) {
  // parameter
  uint64_t program_break;

  // local variables
  uint64_t previous_program_break;
  uint64_t valid;
  uint64_t size;

  program_break = get_regs(context)[REG_A0];

  previous_program_break = get_program_break(context);

  valid = 0;

  if (program_break >= previous_program_break)
    if (program_break < get_regs(context)[REG_SP])
      if (program_break % SIZEOFUINT64 == 0)
        valid = 1;

  if (valid) {
    set_program_break(context, program_break);

    size = program_break - previous_program_break;

    get_regs(context)[REG_A0]        = previous_program_break;
    reg_data_type[REG_A0]            = POINTER_T;              // interval is memory range, not symbolic value
    reg_symb_type[REG_A0]            = CONCRETE;
    reg_mintervals_los[REG_A0][0]    = previous_program_break; // remember start and size of memory block for checking memory safety
    reg_mintervals_ups[REG_A0][0]    = size;                   // remember start and size of memory block for checking memory safety
    reg_mintervals_cnts[REG_A0]      = 1;
    reg_steps[REG_A0]                = 1;
    reg_involved_inputs_cnts[REG_A0] = 0;
    reg_asts[REG_A0]                 = 0;
    reg_bvts[REG_A0]                 = boolector_null;
    reg_theory_types[REG_A0]         = MIT;
    set_correction(REG_A0, 0, 0, 0);

    if (mrcc > 0) {
      if (is_trace_space_available()) {
        // since there has been branching record brk using vaddr == 0
        uint64_t ast_ptr = add_ast_node(CONST, 0, 0, 1, reg_mintervals_los[REG_A0], reg_mintervals_ups[REG_A0], 1, 0, zero_v, MIT, reg_bvts[REG_A0]);
        store_symbolic_memory(get_pt(context), 0, previous_program_break, POINTER_T, ast_ptr, tc, 1, MIT);
      } else {
        throw_exception(EXCEPTION_MAXTRACE, 0);
        return;
      }
    }

  } else {
    // error returns current program break
    program_break = previous_program_break;

    get_regs(context)[REG_A0]        = program_break;
    reg_data_type[REG_A0]            = POINTER_T;
    reg_symb_type[REG_A0]            = CONCRETE;
    reg_mintervals_los[REG_A0][0]    = 0;
    reg_mintervals_ups[REG_A0][0]    = 0;
    reg_mintervals_cnts[REG_A0]      = 1;
    reg_steps[REG_A0]                = 1;
    reg_involved_inputs_cnts[REG_A0] = 0;
    reg_asts[REG_A0]                 = 0;
    reg_bvts[REG_A0]                 = boolector_null;
    reg_theory_types[REG_A0]         = MIT;
    set_correction(REG_A0, 0, 0, 0);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// --------------------------- auxiliary functions -----------------------------

uint64_t gcd(uint64_t n1, uint64_t n2) {
  if (n1 == 0)
    return n2;

  return gcd(n2 % n1, n1);
}

// uint64_t lcm(uint64_t n1, uint64_t n2) {
//   if (n1 > n2)
//     return (n1 / gcd(n1, n2)) * n2;
//   else
//     return (n2 / gcd(n1, n2)) * n1;
// }

bool is_power_of_two(uint64_t v) {
  return v && (!(v & (v - 1)));
}

// bool add_sub_condition(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
//   uint64_t c1;
//   uint64_t c2;
//
//   c1 = up1 - lo1;
//   c2 = 18446744073709551615ULL - (up2 - lo2);
//
//   if (c1 <= c2)
//     return 1;
//   else
//     return 0;
// }

bool mul_condition_mit(uint64_t lo, uint64_t up, uint64_t k) {
  uint64_t c1;
  uint64_t c2;

  if (k == 0)
    return true;

  c1 = up - lo;
  c2 = 18446744073709551615ULL / k;

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

uint64_t compute_upper_bound_mit(uint64_t lo, uint64_t step, uint64_t value) {
  return lo + ((value - lo) / step) * step;
}

uint64_t compute_lower_bound_mit(uint64_t lo, uint64_t step, uint64_t value) {
  if ((value - lo) % step)
    return lo + (((value - lo) / step) + 1) * step;
  else
    return value;
}

uint64_t reverse_division_up(uint64_t up_ast_tc, uint64_t up, uint64_t codiv) {
  if (up_ast_tc < up * codiv + (codiv - 1))
    return up_ast_tc - up * codiv;
  else
    return codiv - 1;
}

// ---------------------------- corrections ------------------------------------

void mit_bvt_engine::set_correction(uint64_t reg, uint8_t hasmn, uint64_t addsub_corr, uint8_t corr_validity) {
  reg_hasmn[reg]          = hasmn;
  reg_addsub_corr[reg]    = addsub_corr;
  reg_corr_validity[reg]  = corr_validity;
}

void mit_bvt_engine::create_ast_node_entry_for_accumulated_corr(uint64_t sym_reg) {
  value_v[0] = reg_addsub_corr[sym_reg];
  uint64_t crt_ptr = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v, MIT, boolector_null);
  if (reg_hasmn[sym_reg]) {
    reg_asts[sym_reg] = add_ast_node(SUB, crt_ptr, reg_asts[sym_reg], reg_mintervals_cnts[sym_reg], reg_mintervals_los[sym_reg], reg_mintervals_ups[sym_reg], reg_steps[sym_reg], reg_involved_inputs_cnts[sym_reg], reg_involved_inputs[sym_reg], reg_theory_types[sym_reg], reg_bvts[sym_reg]);
  } else {
    reg_asts[sym_reg] = add_ast_node(ADD, crt_ptr, reg_asts[sym_reg], reg_mintervals_cnts[sym_reg], reg_mintervals_los[sym_reg], reg_mintervals_ups[sym_reg], reg_steps[sym_reg], reg_involved_inputs_cnts[sym_reg], reg_involved_inputs[sym_reg], reg_theory_types[sym_reg], reg_bvts[sym_reg]);
  }
}

void mit_bvt_engine::create_ast_node_entry_for_concrete_operand(uint64_t crt_reg) {
  value_v[0]        = reg_mintervals_los[crt_reg][0];
  reg_asts[crt_reg] = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v, MIT, reg_bvts[crt_reg]);
}

void mit_bvt_engine::evaluate_correction(uint64_t reg) {
  if (reg_addsub_corr[reg] || reg_hasmn[reg]) {
    create_ast_node_entry_for_accumulated_corr(reg);
  }
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void mit_bvt_engine::apply_lui() {
  do_lui();

  if (rd != REG_ZR) {
    // interval semantics of lui
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = imm << 12;
    reg_mintervals_ups[rd][0]    = imm << 12;
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);
  }
}

void mit_bvt_engine::apply_addi() {
  uint64_t crt_ptr;

  do_addi();

  if (rd == REG_ZR)
    return;

  if (reg_data_type[rs1] == POINTER_T) {
    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs1][0];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);

    return;
  }

  reg_data_type[rd] = VALUE_T;

  if (reg_symb_type[rs1] == SYMBOLIC) {
    // rd inherits rs1 constraint
    reg_symb_type[rd] = SYMBOLIC;

    for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
      reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] + imm;
      reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] + imm;
    }
    reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
    reg_steps[rd]           = reg_steps[rs1];
    set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

    reg_bvts[rd]         = boolector_null;
    reg_theory_types[rd] = reg_theory_types[rs1];

    if (reg_corr_validity[rs1] == 0) {
      set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] + imm, 0);
      reg_asts[rd] = reg_asts[rs1];
    } else {
      set_correction(rd, 0, 0, 1);
      value_v[0] = imm; crt_ptr = add_ast_node(CONST, 0, 0, 1, value_v, value_v, 1, 0, zero_v, MIT, boolector_null);
      reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], crt_ptr, reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
    }

  } else {
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);
  }
}

bool mit_bvt_engine::apply_add_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      // adding two pointers is undefined
      std::cout << exe_name << ": undefined addition of two pointers at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs1][0];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);

    return 1;
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);

    return 1;
  }

  return 0;
}

void mit_bvt_engine::apply_add() {
  uint64_t add_lo;
  uint64_t add_up;

  do_add();

  if (rd != REG_ZR) {
    if (apply_add_pointer())
      return;

    reg_data_type[rd] = VALUE_T;
    reg_bvts[rd]      = boolector_null;

    // interval semantics of add
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        reg_symb_type[rd] = SYMBOLIC;

        set_involved_inputs_two_symbolic_operands();

        evaluate_correction(rs1);
        evaluate_correction(rs2);
        set_correction(rd, 0, 0, 1);

        // TODO: interval semantics of add

        reg_mintervals_los[rd][0] = registers[rd]; // one witness
        reg_mintervals_ups[rd][0] = registers[rd]; // one witness
        reg_mintervals_cnts[rd]   = 1;
        reg_steps[rd]             = 1;
        reg_theory_types[rd]      = std::max(std::max(reg_theory_types[rs1], reg_theory_types[rs2]), BVT);
        reg_asts[rd]              = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        reg_symb_type[rd] = SYMBOLIC;

        uint64_t addend = reg_mintervals_los[rs2][0];

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] + addend;
          reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] + addend;
        }
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
        reg_steps[rd]           = reg_steps[rs1];
        reg_theory_types[rd]    = reg_theory_types[rs1];

        if (reg_corr_validity[rs1] == 0) {
          set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] + addend, 0);
          reg_asts[rd] = reg_asts[rs1];
        } else {
          set_correction(rd, 0, 0, 1);
          reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
        }
      }

    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      reg_symb_type[rd] = SYMBOLIC;

      uint64_t addend = reg_mintervals_los[rs1][0];

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      for (size_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        reg_mintervals_los[rd][i] = addend + reg_mintervals_los[rs2][i];
        reg_mintervals_ups[rd][i] = addend + reg_mintervals_ups[rs2][i];
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
      reg_steps[rd]           = reg_steps[rs2];
      reg_theory_types[rd]    = reg_theory_types[rs2];

      if (reg_corr_validity[rs2] == 0) {
        set_correction(rd, reg_hasmn[rs2], reg_addsub_corr[rs2] + addend, 0);
        reg_asts[rd] = reg_asts[rs2];
      } else {
        set_correction(rd, 0, 0, 1);
        reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
      }

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);
    }
  }
}

bool mit_bvt_engine::apply_sub_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      if (reg_mintervals_los[rs1][0] == reg_mintervals_los[rs2][0])
        if (reg_mintervals_ups[rs1][0] == reg_mintervals_ups[rs2][0]) {
          reg_data_type[rd]            = POINTER_T;
          reg_symb_type[rd]            = CONCRETE;
          reg_mintervals_los[rd][0]    = registers[rd];
          reg_mintervals_ups[rd][0]    = registers[rd];
          reg_mintervals_cnts[rd]      = 1;
          reg_steps[rd]                = 1;
          reg_involved_inputs_cnts[rd] = 0;
          reg_asts[rd]                 = 0;
          reg_bvts[rd]                 = boolector_null;
          reg_theory_types[rd]         = MIT;

          set_correction(rd, 0, 0, 0);

          return 1;
        }

      // subtracting incompatible pointers
      std::cout << exe_name << ": sub invalid address\n";
      throw_exception(EXCEPTION_INVALIDADDRESS, 0);

      return 1;
    } else {
      reg_data_type[rd]            = POINTER_T;
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = reg_mintervals_los[rs1][0];
      reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs1][0];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_bvts[rd]                 = boolector_null;
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);

      return 1;
    }
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs2][0];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);

    return 1;
  }

  return 0;
}

void mit_bvt_engine::apply_sub() {
  uint64_t sub_tmp;

  do_sub();

  if (rd != REG_ZR) {
    if (apply_sub_pointer())
      return;

    reg_data_type[rd] = VALUE_T;
    reg_bvts[rd]      = boolector_null;

    // interval semantics of sub
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        reg_symb_type[rd] = SYMBOLIC;

        set_involved_inputs_two_symbolic_operands();

        evaluate_correction(rs1);
        evaluate_correction(rs2);
        set_correction(rd, 0, 0, 1);

        // TODO: interval semantics of sub

        reg_mintervals_los[rd][0] = registers[rd]; // one witness
        reg_mintervals_ups[rd][0] = registers[rd]; // one witness
        reg_mintervals_cnts[rd]   = 1;
        reg_steps[rd]             = 1;
        reg_theory_types[rd]      = std::max(std::max(reg_theory_types[rs1], reg_theory_types[rs2]), BVT);
        reg_asts[rd]              = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        reg_symb_type[rd] = SYMBOLIC;

        uint64_t subend = reg_mintervals_los[rs2][0];

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] - subend;
          reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] - subend;
        }
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
        reg_steps[rd]           = reg_steps[rs1];
        reg_theory_types[rd]    = reg_theory_types[rs1];

        if (reg_corr_validity[rs1] == 0) {
          set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] - subend, 0);
          reg_asts[rd] = reg_asts[rs1];
        } else {
          set_correction(rd, 0, 0, 1);
          reg_asts[rd] = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
        }
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      reg_symb_type[rd] = SYMBOLIC;

      uint64_t subend = reg_mintervals_los[rs1][0];

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      for (size_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        sub_tmp                   = subend - reg_mintervals_ups[rs2][i];
        reg_mintervals_ups[rd][i] = subend - reg_mintervals_los[rs2][i];
        reg_mintervals_los[rd][i] = sub_tmp;
      }
      reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
      reg_steps[rd]           = reg_steps[rs2];
      reg_theory_types[rd]    = reg_theory_types[rs2];

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
        reg_asts[rd] = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
      }

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void mit_bvt_engine::apply_mul_zero() {
  reg_symb_type[rd] = CONCRETE;
  reg_mintervals_los[rd][0]    = 0;
  reg_mintervals_ups[rd][0]    = 0;
  reg_mintervals_cnts[rd]      = 1;
  reg_steps[rd]                = 1;
  reg_involved_inputs_cnts[rd] = 0;
  reg_theory_types[rd]         = MIT;
  reg_asts[rd]                 = add_ast_node(CONST, 0, 0, reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);

  set_correction(rd, 0, 0, 0);
}

void mit_bvt_engine::apply_mul() {
  uint64_t multiplier;

  do_mul();

  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;
    reg_bvts[rd]      = boolector_null;

    // interval semantics of mul
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        std::cout << exe_name << ": detected non-linear expression in mul at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton

        multiplier = reg_mintervals_los[rs2][0];
        if (multiplier == 0) {
          apply_mul_zero();
          return;
        }

        reg_symb_type[rd] = SYMBOLIC;

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        evaluate_correction(rs1);
        if (reg_asts[rs2] == 0) { create_ast_node_entry_for_concrete_operand(rs2); }
        set_correction(rd, 0, 0, 1);

        bool cnd = false;
        for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
          cnd = mul_condition_mit(reg_mintervals_los[rs1][i], reg_mintervals_ups[rs1][i], multiplier);
          if (cnd == true) {
            reg_mintervals_los[rd][i] = reg_mintervals_los[rs1][i] * multiplier;
            reg_mintervals_ups[rd][i] = reg_mintervals_ups[rs1][i] * multiplier;
          } else {
            std::cout << exe_name << ": cnd failure in mul upgrades theory to BVT at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
            // upgrade to bvt
            reg_mintervals_los[rd][0] = registers[rd]; // one witness
            reg_mintervals_ups[rd][0] = registers[rd];
            break;
          }
        }

        if (cnd) {
          reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs1];
          reg_steps[rd]           = reg_steps[rs1] * multiplier;
          reg_theory_types[rd]    = reg_theory_types[rs1];
        } else {
          reg_mintervals_cnts[rd] = 1;
          reg_steps[rd]           = 1;
          reg_theory_types[rd]    = BVT;
        }

        reg_asts[rd] = add_ast_node(MUL, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
      }

    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton

      multiplier = reg_mintervals_los[rs1][0];
      if (multiplier == 0) {
        apply_mul_zero();
        return;
      }

      reg_symb_type[rd] = SYMBOLIC;

      evaluate_correction(rs2);
      if (reg_asts[rs1] == 0) { create_ast_node_entry_for_concrete_operand(rs1); }
      set_correction(rd, 0, 0, 1);

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      bool cnd = false;
      for (size_t i = 0; i < reg_mintervals_cnts[rs2]; i++) {
        cnd = mul_condition_mit(reg_mintervals_los[rs2][i], reg_mintervals_ups[rs2][i], multiplier);
        if (cnd == true) {
          reg_mintervals_los[rd][i] = multiplier * reg_mintervals_los[rs2][i];
          reg_mintervals_ups[rd][i] = multiplier * reg_mintervals_ups[rs2][i];
        } else {
          std::cout << exe_name << ": cnd failure in mul upgrades theory to BVT at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
          // upgrade to bvt
          reg_mintervals_los[rd][0] = registers[rd]; // one witness
          reg_mintervals_ups[rd][0] = registers[rd];
          break;
        }
      }

      if (cnd) {
        reg_mintervals_cnts[rd] = reg_mintervals_cnts[rs2];
        reg_steps[rd]           = reg_steps[rs2] * multiplier;
        reg_theory_types[rd]    = reg_theory_types[rs2];
      } else {
        reg_mintervals_cnts[rd] = 1;
        reg_steps[rd]           = 1;
        reg_theory_types[rd]    = BVT;
      }

      reg_asts[rd] = add_ast_node(MUL, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);
    }
  }
}

bool mit_bvt_engine::apply_divu_mit() {
  uint64_t div_lo;
  uint64_t div_up;
  uint64_t k;
  uint64_t step;
  uint64_t step_rd;

  if (reg_theory_types[rs1] != MIT || reg_mintervals_cnts[rs1] > 1 || reg_mintervals_cnts[rs2] > 1)
    return false;

  k = reg_mintervals_los[rs2][0];
  div_lo = reg_mintervals_los[rs1][0] / k;
  div_up = reg_mintervals_ups[rs1][0] / k;
  step = reg_steps[rs1];

  // step computation
  if (reg_steps[rs1] < k) {
    if (k % reg_steps[rs1] != 0) {
      // steps in divison are not consistent
      return false;
    }
    step_rd = 1;
  } else {
    if (reg_steps[rs1] % k != 0) {
      // steps in divison are not consistent
      return false;
    }
    step_rd = reg_steps[rs1] / k;
  }

  // interval semantics of divu
  if (reg_mintervals_los[rs1][0] > reg_mintervals_ups[rs1][0]) {
    // rs1 constraint is wrapped

    // lo/k == up/k (or) == up/k + step_rd ==> ok
    if (div_lo != div_up)
      if (div_lo != div_up + step_rd) {
        // wrapped divison results two intervals
        return false;
      }

    uint64_t max = compute_upper_bound_mit(reg_mintervals_los[rs1][0], step, UINT64_MAX_T);
    reg_mintervals_los[rd][0] = (max + step) / k;
    reg_mintervals_ups[rd][0] = max          / k;

  } else {
    // rs1 constraint is not wrapped
    reg_mintervals_los[rd][0] = div_lo;
    reg_mintervals_ups[rd][0] = div_up;
  }

  reg_steps[rd]           = step_rd;
  reg_mintervals_cnts[rd] = 1;
  reg_theory_types[rd]    = reg_theory_types[rs1];

  return true;
}

void mit_bvt_engine::apply_divu() {
  // TODO: if theory is ABVT may raise an unreal divison by zero
  do_divu();

  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;
    reg_bvts[rd]      = boolector_null;

    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        std::cout << exe_name << ": detected non-linear expression in divu at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        reg_symb_type[rd] = SYMBOLIC;

        evaluate_correction(rs1);
        if (reg_asts[rs2] == 0) { create_ast_node_entry_for_concrete_operand(rs2); }
        set_correction(rd, 0, 0, 1);

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        if (apply_divu_mit() == false) {
          reg_mintervals_los[rd][0] = registers[rd]; // one witness
          reg_mintervals_ups[rd][0] = registers[rd];
          reg_mintervals_cnts[rd]   = 1;
          reg_steps[rd]             = 1;
          reg_theory_types[rd]      = std::max(reg_theory_types[rs1], BVT);
        }

        reg_asts[rd] = add_ast_node(DIVU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton
      reg_symb_type[rd] = SYMBOLIC;

      evaluate_correction(rs2);
      if (reg_asts[rs1] == 0) { create_ast_node_entry_for_concrete_operand(rs1); }
      set_correction(rd, 0, 0, 1);

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd]; // one witness
      reg_mintervals_ups[rd][0] = registers[rd];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_theory_types[rd]      = std::max(reg_theory_types[rs2], BVT);
      reg_asts[rd]              = add_ast_node(DIVU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);
    }
  }
}

bool mit_bvt_engine::apply_remu_mit() {
  uint64_t rem_lo;
  uint64_t rem_up;
  uint64_t step_rd;
  uint64_t divisor = reg_mintervals_los[rs2][0];
  uint64_t step    = reg_steps[rs1];

  if (reg_theory_types[rs1] != MIT || reg_mintervals_cnts[rs1] > 1 || reg_mintervals_cnts[rs2] > 1)
    return false;

  if (reg_mintervals_los[rs1][0] <= reg_mintervals_ups[rs1][0]) {
    // rs1 interval is not wrapped
    int rem_typ = remu_condition(reg_mintervals_los[rs1][0], reg_mintervals_ups[rs1][0], step, divisor);
    if (rem_typ == 0) {
      rem_lo  = reg_mintervals_los[rs1][0] % divisor;
      rem_up  = reg_mintervals_ups[rs1][0] % divisor;
      step_rd = step;
    } else if (rem_typ == 1) {
      return false;
    } else if (rem_typ == 2) {
      uint64_t gcd_step_k = gcd(step, divisor);
      rem_lo  = reg_mintervals_los[rs1][0]%divisor - ((reg_mintervals_los[rs1][0]%divisor) / gcd_step_k) * gcd_step_k;
      rem_up  = compute_upper_bound_mit(rem_lo, gcd_step_k, divisor - 1);
      step_rd = gcd_step_k;
    } else {
      return false;
    }

  } else if (is_power_of_two(divisor)) {
    // rs1 interval is wrapped
    uint64_t gcd_step_k = gcd(step, divisor);
    uint64_t lcm        = (step * divisor) / gcd_step_k;

    if (reg_mintervals_ups[rs1][0] - reg_mintervals_los[rs1][0] < lcm - step)
      return false;

    rem_lo  = reg_mintervals_los[rs1][0]%divisor - ((reg_mintervals_los[rs1][0]%divisor) / gcd_step_k) * gcd_step_k;
    rem_up  = compute_upper_bound_mit(rem_lo, gcd_step_k, divisor - 1);
    step_rd = gcd_step_k;

  } else {
    return false;
  }

  reg_mintervals_los[rd][0] = rem_lo;
  reg_mintervals_ups[rd][0] = rem_up;
  reg_mintervals_cnts[rd]   = 1;
  reg_steps[rd]             = step_rd;
  reg_theory_types[rd]      = MIT;

  return true;
}

void mit_bvt_engine::apply_remu() {
  do_remu();

  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;
    reg_bvts[rd]      = boolector_null;

    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        std::cout << exe_name << ": detected non-linear expression in remu at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        reg_symb_type[rd] = SYMBOLIC;

        evaluate_correction(rs1);
        if (reg_asts[rs2] == 0) { create_ast_node_entry_for_concrete_operand(rs2); }
        set_correction(rd, 0, 0, 1);

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        if (apply_remu_mit() == false) {
          reg_mintervals_los[rd][0] = registers[rd]; // one witness
          reg_mintervals_ups[rd][0] = registers[rd];
          reg_mintervals_cnts[rd]   = 1;
          reg_steps[rd]             = 1;
          reg_theory_types[rd]      = std::max(reg_theory_types[rs1], BVT);
        }

        reg_asts[rd] = add_ast_node(REMU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton
      reg_symb_type[rd] = SYMBOLIC;

      evaluate_correction(rs2);
      if (reg_asts[rs1] == 0) { create_ast_node_entry_for_concrete_operand(rs1); }
      set_correction(rd, 0, 0, 1);

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd]; // one witness
      reg_mintervals_ups[rd][0] = registers[rd];
      reg_mintervals_cnts[rd]   = 1;
      reg_steps[rd]             = 1;
      reg_theory_types[rd]      = std::max(reg_theory_types[rs2], BVT);
      reg_asts[rd]              = add_ast_node(REMU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_cnts[rd], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_steps[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_theory_types[rd], reg_bvts[rd]);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void mit_bvt_engine::apply_sltu() {
  if (backtrack) { backtrack_sltu(); return; }

  if (rd != REG_ZR) {
    if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
      // concrete semantics of sltu
      registers[rd] = (registers[rs1] < registers[rs2]) ? 1 : 0;

      reg_data_type[rd]            = VALUE_T;
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = (registers[rd] == 0) ? zero_node : one_node;
      reg_bvts[rd]                 = (registers[rd] == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);

      pc = pc + INSTRUCTIONSIZE;
      ic_sltu = ic_sltu + 1;

      return;
    }

    // -------------------
    // evaluate_correction
    // -------------------
    if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
      create_ast_node_entry_for_accumulated_corr(rs1);
      // now reg_asts[rs1] is updated
    } else if (reg_asts[rs1] == 0 && reg_symb_type[rs1] == CONCRETE) {
      create_ast_node_entry_for_concrete_operand(rs1);
    } else if (reg_asts[rs1] == 0 && reg_symb_type[rs1] == SYMBOLIC) {
      std::cout << exe_name << ": error in apply_sltu at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    }
    if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
      create_ast_node_entry_for_accumulated_corr(rs2);
      // now reg_asts[rs1] is updated
    } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == CONCRETE) {
      create_ast_node_entry_for_concrete_operand(rs2);
    } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == SYMBOLIC) {
      std::cout << exe_name << ": error in apply_sltu at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    }

    // -------------------
    // save input_table
    // -------------------
    input_table_ast_tcs_before_branch_evaluation.clear();
    for (size_t i = 0; i < input_table.size(); i++) {
      input_table_ast_tcs_before_branch_evaluation.push_back(input_table[i]);
    }

    if (reg_data_type[rs1] != POINTER_T) {
      if (reg_data_type[rs2] != POINTER_T) {
        create_sltu_constraints(reg_mintervals_los[rs1], reg_mintervals_ups[rs1], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], mrcc, false);
      } else
        std::cout << exe_name << ": detected pointer data-type in comparison\n";
    } else
      std::cout << exe_name << ": detected pointer data-type in comparison\n";
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_sltu = ic_sltu + 1;
}

void mit_bvt_engine::apply_xor() {
  if (backtrack) { backtrack_sltu(); return; }

  if (rd != REG_ZR) {
    if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
      // concrete semantics of xor
      registers[rd] = registers[rs1] ^ registers[rs2];

      reg_data_type[rd]            = VALUE_T;
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_mintervals_cnts[rd]      = 1;
      reg_steps[rd]                = 1;
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = (registers[rd] == 0) ? zero_node : one_node;
      reg_bvts[rd]                 = (registers[rd] == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];
      reg_theory_types[rd]         = MIT;

      set_correction(rd, 0, 0, 0);

      pc = pc + INSTRUCTIONSIZE;
      ic_xor = ic_xor + 1;

      return;
    }

    // -------------------
    // evaluate_correction
    // -------------------
    if (reg_addsub_corr[rs1] || reg_hasmn[rs1]) {
      create_ast_node_entry_for_accumulated_corr(rs1);
      // now reg_asts[rs1] is updated
    } else if (reg_asts[rs1] == 0 && reg_symb_type[rs1] == CONCRETE) {
      create_ast_node_entry_for_concrete_operand(rs1);
    } else if (reg_asts[rs1] == 0 && reg_symb_type[rs1] == SYMBOLIC) {
      std::cout << exe_name << ": error in apply_xor at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    }
    if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
      create_ast_node_entry_for_accumulated_corr(rs2);
      // now reg_asts[rs1] is updated
    } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == CONCRETE) {
      create_ast_node_entry_for_concrete_operand(rs2);
    } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == SYMBOLIC) {
      std::cout << exe_name << ": error in apply_xor at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    }

    // -------------------
    // save input_table
    // -------------------
    input_table_ast_tcs_before_branch_evaluation.clear();
    for (size_t i = 0; i < input_table.size(); i++) {
      input_table_ast_tcs_before_branch_evaluation.push_back(input_table[i]);
    }

    if (reg_data_type[rs1] != POINTER_T) {
      if (reg_data_type[rs2] != POINTER_T) {
        create_xor_constraints(reg_mintervals_los[rs1], reg_mintervals_ups[rs1], reg_mintervals_los[rs2], reg_mintervals_ups[rs2], mrcc, false);
      } else
        std::cout << exe_name << ": detected pointer data-type in comparison\n";
    } else
      std::cout << exe_name << ": detected pointer data-type in comparison\n";
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_xor = ic_xor + 1;
}

uint64_t mit_bvt_engine::check_memory_vaddr_whether_represents_most_recent_constraint(uint64_t mrvc) {
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
    update_current_constraint_on_ast_expression(ast_tc);
    return load_symbolic_memory(pt, vaddrs[mrvc]);
  } else
    return mrvc;
}

uint64_t mit_bvt_engine::apply_ld() {
  uint64_t vaddr;
  uint64_t mrvc;
  uint64_t a;

  if (backtrack) { backtrack_ld(); return 0; }

  // load double word

  vaddr = registers[rs1] + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (rd != REG_ZR) {
        mrvc = check_memory_vaddr_whether_represents_most_recent_constraint(load_symbolic_memory(pt, vaddr));

        // it is important because we have prevousely freed stack addresses on the trace
        if (vaddr >= get_program_break(current_context))
          if (vaddr < registers[REG_SP]) {
            // free memory
            std::cout << exe_name << ": loading a freed memory " << vaddr << " at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
            exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
          }

        // interval semantics of ld
        reg_theory_types[rd]    = theory_types[mrvc];
        reg_asts[rd]            = asts[mrvc];
        reg_bvts[rd]            = smt_exprs[reg_asts[rd]];
        reg_data_type[rd]       = data_types[mrvc];
        registers[rd]           = values[mrvc];
        reg_mintervals_cnts[rd] = mintervals_los[reg_asts[rd]].size();
        reg_steps[rd]           = steps[reg_asts[rd]];

        if (reg_mintervals_cnts[rd] == 0)
          std::cout << exe_name << ": reg_mintervals_cnts is zero for theory " << reg_theory_types[rd] << " ast " << asts[mrvc] << '\n';

        for (size_t i = 0; i < reg_mintervals_cnts[rd]; i++) {
          reg_mintervals_los[rd][i] = mintervals_los[reg_asts[rd]][i];
          reg_mintervals_ups[rd][i] = mintervals_ups[reg_asts[rd]][i];
        }

        // assert: vaddr == *(vaddrs + mrvc)

        if (is_symbolic_value(reg_data_type[rd], reg_mintervals_cnts[rd], reg_mintervals_los[rd][0], reg_mintervals_ups[rd][0], reg_theory_types[rd])) {
          // vaddr is constrained by rd if value interval is not singleton
          reg_symb_type[rd]            = SYMBOLIC;
          reg_involved_inputs_cnts[rd] = involved_sym_inputs_cnts[reg_asts[rd]];
          for (size_t i = 0; i < reg_involved_inputs_cnts[rd]; i++) {
            reg_involved_inputs[rd][i] = involved_sym_inputs_ast_tcs[reg_asts[rd]][i];
          }
        } else {
          reg_symb_type[rd]            = CONCRETE;
          reg_involved_inputs_cnts[rd] = 0;
        }

        set_correction(rd, 0, 0, 0);
      }

      a = (pc - entry_point) / INSTRUCTIONSIZE; // keep track of instruction address for profiling loads
      pc = pc + INSTRUCTIONSIZE;
      ic_ld = ic_ld + 1;                        // keep track of number of loads in total

      // and individually
      loads_per_instruction[a] = loads_per_instruction[a] + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

uint64_t mit_bvt_engine::apply_sd() {
  uint64_t vaddr;
  uint64_t a;

  if (backtrack) { backtrack_sd(); return 0; }

  // store double word

  vaddr = registers[rs1] + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // interval semantics of sd

      // evaluate corrections
      if (reg_addsub_corr[rs2] || reg_hasmn[rs2]) {
        create_ast_node_entry_for_accumulated_corr(rs2);
        // now reg_asts[rs2] is updated
      } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == CONCRETE) {
        reg_asts[rs2] = add_ast_node(CONST, 0, 0, 1, reg_mintervals_los[rs2], reg_mintervals_ups[rs2], 1, 0, zero_v, MIT, boolector_null);
      } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == SYMBOLIC) {
        std::cout << exe_name << ": detected symbolic value with reg_asts = 0 in sd operation at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_type[rs2], reg_asts[rs2], mrcc, 1, reg_theory_types[rs2]);

      a = (pc - entry_point) / INSTRUCTIONSIZE; // keep track of instruction address for profiling stores
      pc = pc + INSTRUCTIONSIZE;
      ic_sd = ic_sd + 1;                        // keep track of number of stores in total

      // and individually
      stores_per_instruction[a] = stores_per_instruction[a] + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else {
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

void mit_bvt_engine::apply_jal() {
  do_jal();

  if (rd != REG_ZR) {
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);
  }
}

void mit_bvt_engine::apply_jalr() {
  do_jalr();

  if (rd != REG_ZR) {
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);
  }
}

void mit_bvt_engine::apply_ecall() {
  if (backtrack) { backtrack_ecall(); return; }

  do_ecall();
}

// -----------------------------------------------------------------------------
// ----------------------------- backtracking ----------------------------------
// -----------------------------------------------------------------------------

void mit_bvt_engine::backtrack_sltu() {
  uint64_t vaddr;

  vaddr = vaddrs[tc];

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      reg_data_type[vaddr]            = data_types[tc];
      reg_symb_type[vaddr]            = CONCRETE;
      registers[vaddr]                = values[tc];
      reg_mintervals_los[vaddr][0]    = values[tc];
      reg_mintervals_ups[vaddr][0]    = values[tc];
      reg_mintervals_cnts[vaddr]      = 1;
      reg_steps[vaddr]                = 1;
      reg_involved_inputs_cnts[vaddr] = 0;
      reg_asts[vaddr]                 = 0;
      reg_bvts[vaddr]                 = boolector_null;
      reg_theory_types[vaddr]         = MIT;

      set_correction(vaddr, 0, 0, 0);

      // restoring mrcc
      mrcc = tcs[tc];

      if (vaddr != REG_FP) {
        if (vaddr != REG_SP) {
          // stop backtracking and try next case
          pc = pc + INSTRUCTIONSIZE;
          ic_sltu = ic_sltu + 1;

          reg_asts[vaddr] = (registers[vaddr] == 0) ? zero_node : one_node;
          reg_bvts[vaddr] = (registers[vaddr] == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];

          // there are two cases when (bvt_false_branches[tc] == boolector_null)
          // 1. when theory is MIT; may happen that we have to pop more than one constraint (when was going through false branches)
          // 2. when theory was MIT and then we needed BVT so we dumped path_condition, and now we backtrack.
          if (bvt_false_branches[tc] == boolector_null) {
            while (path_condition.size() > 0 && path_condition.back() > asts[tc]) {
              path_condition.pop_back();
            }

            if (theory_type_ast_nodes[asts[tc]] == BVT) { // important: look at assert_path_condition_into_smt_expression
              boolector_pop(btor, 1);
              path_condition.clear();
            }

            path_condition.push_back(asts[tc]);
          } else {
            // when asts[tc] == 0 means theory of bvt take care of everything.
            /* when bvt_false_branches[tc] != boolector_null && theory_type_ast_nodes[asts[tc]] == BVT then points to box theory,
               for when box can decide true-case and not false. In that case true may not be evaluated as a smt expr so no pop
            */
            if (asts[tc] == 0 || theory_type_ast_nodes[asts[tc]] == BVT) // important: look at box theory
              boolector_pop(btor, 1);
            boolector_assert(btor, bvt_false_branches[tc]);
            path_condition.clear();
          }
        }
      } else {
        // look at store_symbolic_memory for registers
        if (ast_trace_cnt > most_recent_if_on_ast_trace) {
          ast_trace_cnt = most_recent_if_on_ast_trace;
        }
        most_recent_if_on_ast_trace = asts[tc];
      }
    }
  } else if (vaddr == NUMBEROFREGISTERS) { // means input_t record
    input_table.at(ast_nodes[asts[tc]].right_node) = values[tc];
  } else {
    if (store_trace_ptrs[asts[tc]].size() > 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else if (store_trace_ptrs[asts[tc]].size() == 1) {
      if (ast_nodes[asts[tc]].type == VAR) input_table.at(ast_nodes[asts[tc]].right_node) = asts[tcs[tc]];
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      std::cout << exe_name << ": error occured during sltu backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    store_virtual_memory(pt, vaddr, tcs[tc]);
  }

  efree();
}

void mit_bvt_engine::backtrack_sd() {
  if (theory_types[tc] < BVT) {
    if (store_trace_ptrs[asts[tc]].size() >= 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      std::cout << exe_name << ": error occured during sd backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

  } else if (theory_types[tc] == BVT && asts[tc] != 0) {
    if (store_trace_ptrs[asts[tc]].size() >= 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      std::cout << exe_name << ": error occured during sd backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }

  store_virtual_memory(pt, vaddrs[tc], tcs[tc]);

  efree();
}

void mit_bvt_engine::backtrack_ld() {
  if (store_trace_ptrs[asts[tc]].size() > 1) {
    store_trace_ptrs[asts[tc]].pop_back();
  } else if (store_trace_ptrs[asts[tc]].size() == 1) {
    if (ast_nodes[asts[tc]].type == VAR) input_table.at(ast_nodes[asts[tc]].right_node) = asts[tcs[tc]];
    store_trace_ptrs[asts[tc]].pop_back();
  } else {
    std::cout << exe_name << ": error occured during ld backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  store_virtual_memory(pt, vaddrs[tc], tcs[tc]);

  efree();
}

void mit_bvt_engine::backtrack_ecall() {
  if (vaddrs[tc] == 0) {
    // backtracking malloc
    if (get_program_break(current_context) == mintervals_los[asts[tc]][0] + mintervals_ups[asts[tc]][0])
      set_program_break(current_context, mintervals_los[asts[tc]][0]);
    else {
      std::cout << exe_name << ": error occured during malloc backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking input
    input_table.pop_back();
    symbolic_input_cnt = input_table.size();
    store_trace_ptrs[asts[tc]].pop_back();
    input_table_store_trace_ptr.pop_back();

    // input assertions should be poped
    boolector_pop(btor, 1);

    store_virtual_memory(pt, vaddrs[tc], tcs[tc]);
  }

  // TODO: backtracking read

  efree();
}

void mit_bvt_engine::backtrack_trace(uint64_t* context) {
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

// -----------------------------------------------------------------------------
// ------------------------- SYMBOLIC functions --------------------------------
// -----------------------------------------------------------------------------

uint8_t mit_bvt_engine::is_symbolic_value(uint8_t type, uint32_t mints_num, uint64_t lo, uint64_t up, uint8_t theory_type) {
  if (type == POINTER_T)
    // memory range
    return CONCRETE;
  else if (mints_num > 1)
    return SYMBOLIC;
  else if (theory_type > MIT)
    return SYMBOLIC;
  else if (lo == up)
    // singleton interval
    return CONCRETE;
  else
    // non-singleton interval
    return SYMBOLIC;
}

uint64_t mit_bvt_engine::is_safe_address(uint64_t vaddr, uint64_t reg) {
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
    std::cout << exe_name << ": detected unsupported symbolic access of memory interval at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t mit_bvt_engine::load_symbolic_memory(uint64_t* pt, uint64_t vaddr) {
  uint64_t mrvc;

  // assert: vaddr is valid and mapped
  mrvc = load_virtual_memory(pt, vaddr);

  if (mrvc <= tc)
    return mrvc;
  else {
    std::cout << exe_name << ": detected most recent value counter " << mrvc << " at vaddr " << std::hex << vaddr << " greater than current trace counter " << tc << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t mit_bvt_engine::is_trace_space_available() {
  return tc + 1 < MAX_TRACE_LENGTH;
}

uint64_t mit_bvt_engine::get_current_tc() {
  return tc;
}

void mit_bvt_engine::ealloc() {
  tc = tc + 1;
}

void mit_bvt_engine::efree() {
  // assert: tc > 0
  tc = tc - 1;
}

void mit_bvt_engine::store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint8_t data_type, uint64_t ast_ptr, uint64_t trb, uint64_t is_store, uint8_t theory_type) {
  uint64_t mrvc;

  if (vaddr == 0)
    // tracking program break and size for malloc
    mrvc = 0;
  else if (vaddr < NUMBEROFREGISTERS)
    // tracking a register value for sltu
    mrvc = mrcc;
  else if (vaddr == NUMBEROFREGISTERS) {
    if (is_trace_space_available()) {
      ealloc();

      pcs[tc]          = pc;
      tcs[tc]          = 0;
      data_types[tc]   = data_type;
      values[tc]       = value;
      vaddrs[tc]       = vaddr;
      asts[tc]         = ast_ptr;
      mr_sds[tc]       = tc;
      theory_types[tc] = theory_type;
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

          if (ast_ptr) { store_trace_ptrs[ast_ptr].push_back(mrvc); }

          if (is_store) {
            mr_sds[mrvc] = mrvc;
          }

          theory_types[mrvc] = theory_type;

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

    theory_types[tc] = theory_type;

    if (vaddr < NUMBEROFREGISTERS) {
      if (vaddr > 0) {
        // register tracking marks most recent constraint
        mrcc = tc;
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

void mit_bvt_engine::store_register_memory(uint64_t reg, std::vector<uint64_t>& value) {
  // always track register memory by using tc as most recent branch
  store_symbolic_memory(pt, reg, value[0], VALUE_T, 0, tc, 1, MIT);
}

void mit_bvt_engine::store_input_record(uint64_t ast_ptr, uint64_t prev_input_record, uint8_t theory_type) {
  store_symbolic_memory(pt, NUMBEROFREGISTERS, prev_input_record, INPUT_T, ast_ptr, tc, 0, theory_type);
}

// -----------------------------------------------------------------------------
// ------------------------ reasoning/decision core ----------------------------
// -----------------------------------------------------------------------------

uint64_t mit_bvt_engine::add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, uint32_t mints_num, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t step, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs, uint8_t theory_type, BoolectorNode* smt_expr) {
  ast_trace_cnt++;

  if (ast_trace_cnt >= AST_NODES_TRACE_LENGTH) {
    AST_NODES_TRACE_LENGTH = (AST_NODES_TRACE_LENGTH + MEMORY_ALLOCATION_STEP_AST_NODES_TRACE < MAX_AST_NODES_TRACE_LENGTH) ?
                              AST_NODES_TRACE_LENGTH + MEMORY_ALLOCATION_STEP_AST_NODES_TRACE :
                              MAX_AST_NODES_TRACE_LENGTH;

    if (ast_trace_cnt >= AST_NODES_TRACE_LENGTH) {
      std::cout << exe_name << ": MAX_AST_NODES_TRACE_LENGTH reached at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    mintervals_los.resize(AST_NODES_TRACE_LENGTH);
    mintervals_ups.resize(AST_NODES_TRACE_LENGTH);
    store_trace_ptrs.resize(AST_NODES_TRACE_LENGTH);
    involved_sym_inputs_ast_tcs.resize(AST_NODES_TRACE_LENGTH);
  }

  if (mints_num >= MAX_NUM_OF_INTERVALS) {
    std::cout << exe_name << ": MAX_NUM_OF_INTERVALS reached at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
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
  steps[ast_trace_cnt] = step;

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

  theory_type_ast_nodes[ast_trace_cnt] = theory_type;

  smt_exprs[ast_trace_cnt] = smt_expr;

  return ast_trace_cnt;
}

void mit_bvt_engine::set_involved_inputs(uint64_t reg, std::vector<uint64_t>& involved_inputs, size_t in_num) {
  reg_involved_inputs_cnts[reg] = in_num;
  for (size_t i = 0; i < in_num; i++) {
    reg_involved_inputs[reg][i] = involved_inputs[i];
  }
}

void mit_bvt_engine::set_involved_inputs_two_symbolic_operands() {
  merge_arrays(reg_involved_inputs[rs1], reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs1], reg_involved_inputs_cnts[rs2]);
  for (size_t i = 0; i < merged_array.size(); i++) {
    reg_involved_inputs[rd][i] = merged_array[i];
  }
  reg_involved_inputs_cnts[rd] = merged_array.size();
}

void mit_bvt_engine::take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0) {
    value_v[0] = b;
    store_register_memory(rd, value_v);     // record that we need to set rd to true
    value_v[0] = registers[REG_FP];
    store_register_memory(REG_FP, value_v); // record frame pointer
    value_v[0] = registers[REG_SP];
    store_register_memory(REG_SP, value_v); // record stack pointer
  } else {
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    registers[rd]                = b;
    reg_mintervals_los[rd][0]    = b;
    reg_mintervals_ups[rd][0]    = b;
    reg_mintervals_cnts[rd]      = 1;
    reg_steps[rd]                = 1;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = (b == 0) ? zero_node : one_node;
    reg_bvts[rd]                 = (b == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];
    reg_theory_types[rd]         = MIT;

    set_correction(rd, 0, 0, 0);
  }
}

uint8_t mit_bvt_engine::detect_symbolic_operand(uint64_t ast_tc) {
  uint8_t left_typ = is_symbolic_value(VALUE_T, mintervals_los[ast_nodes[ast_tc].left_node].size(), mintervals_los[ast_nodes[ast_tc].left_node][0], mintervals_ups[ast_nodes[ast_tc].left_node][0], theory_type_ast_nodes[ast_nodes[ast_tc].left_node]);
  uint8_t right_typ = is_symbolic_value(VALUE_T, mintervals_los[ast_nodes[ast_tc].right_node].size(), mintervals_los[ast_nodes[ast_tc].right_node][0], mintervals_ups[ast_nodes[ast_tc].right_node][0], theory_type_ast_nodes[ast_nodes[ast_tc].right_node]);

  if (left_typ == SYMBOLIC && right_typ == CONCRETE) {
    sym_operand_ast_tc = ast_nodes[ast_tc].left_node;
    crt_operand_ast_tc = ast_nodes[ast_tc].right_node;
    return LEFT;
  } else if (left_typ == CONCRETE && right_typ == SYMBOLIC) {
    sym_operand_ast_tc = ast_nodes[ast_tc].right_node;
    crt_operand_ast_tc = ast_nodes[ast_tc].left_node;
    return RIGHT;
  } else {
    return BOTH;
  }
}

bool mit_bvt_engine::backward_propagation_divu_wrapped_mit(uint64_t sym_operand_ast_tc, uint64_t divisor) {
  uint64_t lo_1;
  uint64_t up_1;
  uint64_t lo_2;
  uint64_t up_2;

  uint64_t max = compute_upper_bound_mit(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], UINT64_MAX_T);
  uint64_t min = max + steps[sym_operand_ast_tc];
  uint64_t  which_solution_is_empty;

  if (propagated_minterval_lo[0] * divisor > min)
    propagated_minterval_lo[0] = compute_lower_bound_mit(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_lo[0] * divisor);
  else
    propagated_minterval_lo[0] = min;

  propagated_minterval_up[0] = compute_upper_bound_mit(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_up[0] * divisor + reverse_division_up(max, propagated_minterval_up[0], divisor));

  // intersection of [propagated_minterval_lo, propagated_minterval_up] with the original sub-intervals

  which_solution_is_empty = 0;
  if (propagated_minterval_lo[0] <= mintervals_ups[sym_operand_ast_tc][0]) {
    lo_1 = propagated_minterval_lo[0];
    up_1 = (propagated_minterval_up[0] < mintervals_ups[sym_operand_ast_tc][0]) ? propagated_minterval_up[0] : mintervals_ups[sym_operand_ast_tc][0];
  } else {
    which_solution_is_empty = 1;
  }

  if (propagated_minterval_up[0] >= mintervals_los[sym_operand_ast_tc][0]) {
    lo_2 = (propagated_minterval_lo[0] > mintervals_los[sym_operand_ast_tc][0]) ? propagated_minterval_lo[0] : mintervals_los[sym_operand_ast_tc][0];
    up_2 = propagated_minterval_up[0];
  } else {
    which_solution_is_empty = (which_solution_is_empty == 1) ? 4 : 2;
  }

  if (which_solution_is_empty == 0) {
    if (up_1 + steps[sym_operand_ast_tc] >= lo_2) {
      propagated_minterval_lo[0] = lo_1;
      propagated_minterval_up[0] = up_2;
    } else {
      std::cout << exe_name << ": divu theory upgrade at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      return false;
    }
  } else if (which_solution_is_empty == 1) {
    propagated_minterval_lo[0] = lo_2;
    propagated_minterval_up[0] = up_2;
  } else if (which_solution_is_empty == 2) {
    propagated_minterval_lo[0] = lo_1;
    propagated_minterval_up[0] = up_1;
  } else if (which_solution_is_empty == 4) {
    std::cout << exe_name << ": divu theory upgrade at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    return false;
  }

  return true;
}

uint64_t mit_bvt_engine::backward_propagation_of_value_intervals(uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint8_t theory_type) {
  std::vector<uint64_t> saved_lo;
  std::vector<uint64_t> saved_up;
  std::vector<uint32_t> idxs;
  uint8_t left_or_right_is_sym;
  uint64_t ast_ptr;
  uint64_t stored_to_tc, mr_stored_to_tc;
  bool is_assigned = false;

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
    propagated_minterval_lo[i] = compute_lower_bound_mit(mintervals_los[ast_tc][j], steps[ast_tc], lo[i]);
    propagated_minterval_up[i] = compute_upper_bound_mit(mintervals_los[ast_tc][j], steps[ast_tc], up[i]);
  }

  if (ast_nodes[ast_tc].type == VAR) {
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[ast_tc].right_node, mints_num, propagated_minterval_lo, propagated_minterval_up, steps[ast_tc], 0, zero_v, MIT, smt_exprs[ast_tc]);

    for (size_t i = 0; i < store_trace_ptrs[ast_tc].size(); i++) {
      stored_to_tc    = store_trace_ptrs[ast_tc][i];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, MIT);
        is_assigned = true;
      }
    }

    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[ast_tc].right_node), MIT);
    }
    input_table.at(ast_nodes[ast_tc].right_node) = ast_ptr;

    return ast_ptr;
  }

  left_or_right_is_sym = detect_symbolic_operand(ast_tc);

  if (left_or_right_is_sym == BOTH) {
    std::cout << exe_name << ": both operands are symbolic in backward_propagation_of_value_intervals!\n";
    return 0;
  }

  for (size_t i = 0; i < mints_num; i++) {
    saved_lo.push_back(propagated_minterval_lo[i]);
    saved_up.push_back(propagated_minterval_up[i]);
  }

  switch (ast_nodes[ast_tc].type) {
    case mit_bvt_engine::ADD: {
      for (size_t i = 0; i < mints_num; i++) {
        propagated_minterval_lo[i] = propagated_minterval_lo[i] - mintervals_los[crt_operand_ast_tc][0];
        propagated_minterval_up[i] = propagated_minterval_up[i] - mintervals_los[crt_operand_ast_tc][0];
      }
      break;
    }
    case mit_bvt_engine::SUB: {
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
    case mit_bvt_engine::MUL: {
      // <9223372036854775808, 2^64 - 1, 1> * 2 = <0, 2^64 - 2, 2>
      // <9223372036854775809, 15372286728091293014, 1> * 3 = <9223372036854775811, 9223372036854775810, 3>
      for (size_t i = 0; i < mints_num; i++) {
        propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][idxs[i]] + (propagated_minterval_lo[i] - mintervals_los[ast_tc][idxs[i]]) / mintervals_los[crt_operand_ast_tc][0];
        propagated_minterval_up[i] = mintervals_los[sym_operand_ast_tc][idxs[i]] + (propagated_minterval_up[i] - mintervals_los[ast_tc][idxs[i]]) / mintervals_los[crt_operand_ast_tc][0];
      }
      break;
    }
    case mit_bvt_engine::DIVU: {
      if (mints_num > 1) {
        return 0;
      }

      uint64_t divisor = mintervals_los[crt_operand_ast_tc][0];

      if (mintervals_los[sym_operand_ast_tc][0] <= mintervals_ups[sym_operand_ast_tc][0]) {
        // non-wrapped
        if (propagated_minterval_lo[0] * divisor > mintervals_los[sym_operand_ast_tc][0])
          propagated_minterval_lo[0] = compute_lower_bound_mit(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_lo[0] * divisor);
        else
          propagated_minterval_lo[0] = mintervals_los[sym_operand_ast_tc][0];

        propagated_minterval_up[0] = compute_upper_bound_mit(mintervals_los[sym_operand_ast_tc][0], steps[sym_operand_ast_tc], propagated_minterval_up[0] * divisor + reverse_division_up(mintervals_ups[sym_operand_ast_tc][0], propagated_minterval_up[0], divisor));
      } else {
        // wrapped
        if (backward_propagation_divu_wrapped_mit(sym_operand_ast_tc, divisor) == false)
          return 0;
      }

      break;
    }
    case mit_bvt_engine::REMU: {
      return 0;

      break;
    }
    default: {
      std::cout << exe_name << ": detected an unknown operation during backward_propagation_of_value_intervals at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
  }

  uint64_t sym_operand_ptr = backward_propagation_of_value_intervals(sym_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, mints_num, theory_type);

  if (sym_operand_ptr == 0) {
    return 0;
  }

  if (left_or_right_is_sym == LEFT)
    ast_ptr = add_ast_node(ast_nodes[ast_tc].type, sym_operand_ptr, ast_nodes[ast_tc].right_node, mints_num, saved_lo, saved_up, steps[ast_tc], involved_sym_inputs_cnts[sym_operand_ptr], involved_sym_inputs_ast_tcs[sym_operand_ptr], MIT, smt_exprs[ast_tc]);
  else
    ast_ptr = add_ast_node(ast_nodes[ast_tc].type, ast_nodes[ast_tc].left_node, sym_operand_ptr, mints_num, saved_lo, saved_up, steps[ast_tc], involved_sym_inputs_cnts[sym_operand_ptr], involved_sym_inputs_ast_tcs[sym_operand_ptr], MIT, smt_exprs[ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], saved_lo[0], VALUE_T, ast_ptr, tc, 0, MIT);
  }

  return ast_ptr;
}

bool mit_bvt_engine::constrain_memory_mit(uint64_t reg, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint32_t mints_num, uint64_t trb, bool only_reachable_branch) {
  if (reg_symb_type[reg] == SYMBOLIC) {
    if (only_reachable_branch == false) {
      if (backward_propagation_of_value_intervals(reg_asts[reg], lo, up, mints_num, reg_theory_types[reg]) == 0)
        return false;
    }
  }

  return true;
}

bool mit_bvt_engine::evaluate_sltu_true_false_branch_mit(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
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
            lo_p = compute_lower_bound_mit(lo2, reg_steps[rs1], lo1 + 1);
            up_p = compute_upper_bound_mit(lo1, reg_steps[rs1], UINT64_MAX_T);
            if (lo_p <= up_p) {
              true_branch_rs1_minterval_los[true_branch_rs1_minterval_cnt]   = lo1;
              true_branch_rs1_minterval_ups[true_branch_rs1_minterval_cnt++] = up1;
              true_branch_rs2_minterval_los[true_branch_rs2_minterval_cnt]   = lo_p;
              true_branch_rs2_minterval_ups[true_branch_rs2_minterval_cnt++] = up_p;
            }
          }

        } else { // lower part
          // false case
          lo_p = compute_lower_bound_mit(lo2, reg_steps[rs1], 0);
          up_p = compute_upper_bound_mit(lo1, reg_steps[rs1], lo1);
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
        lo_p = compute_lower_bound_mit(lo1, reg_steps[rs1], lo2);
        up_p = compute_upper_bound_mit(lo1, reg_steps[rs1], UINT64_MAX_T);
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
          lo_p = compute_lower_bound_mit(lo1, reg_steps[rs1], 0);
          up_p = compute_upper_bound_mit(lo1, reg_steps[rs1], lo2 - 1);
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
    std::cout << exe_name << ": < of two non-wrapped intervals are not supported for now at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  return cannot_handle;
}

void mit_bvt_engine::create_sltu_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb, bool cannot_handle) {
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

  if (reg_theory_types[rs1] > MIT || reg_theory_types[rs2] > MIT) {
    cannot_handle = true;
  } else if (cannot_handle != true) {
    for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
      lo1 = lo1_p[i];
      up1 = up1_p[i];
      for (size_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
        lo2 = lo2_p[j];
        up2 = up2_p[j];
        cannot_handle = evaluate_sltu_true_false_branch_mit(lo1, up1, lo2, up2);
      }
    }
  }

  if (cannot_handle) {
    assert_path_condition_into_smt_expression();
    check_operands_smt_expressions();

    true_reachable  = check_sat_true_branch_bvt(boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
    false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq() == LGTE) {
          // false
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          take_branch(1, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_false_branch_bvt();
          dump_all_input_variables_on_trace_false_branch_bvt();
          take_branch(0, 0);
        } else {
          // false
          dump_involving_input_variables_false_branch_bvt();
          dump_all_input_variables_on_trace_false_branch_bvt();
          take_branch(0, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]); // carefull

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          take_branch(1, 0);
        }
      } else {
        dump_involving_input_variables_true_branch_bvt();
        dump_all_input_variables_on_trace_true_branch_bvt();
        take_branch(1, 0);
      }
    } else if (false_reachable) {
      dump_involving_input_variables_false_branch_bvt();
      dump_all_input_variables_on_trace_false_branch_bvt();
      take_branch(0, 0);
    } else {
      std::cout << exe_name << ": both branches unreachable! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    return;
  }

  queries_reasoned_by_mit+=2;

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  save_trace_state();
  bool is_handled = false;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq() == LGTE) {
        is_handled = constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(1, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // careful

        path_condition.push_back(add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        is_handled = constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        take_branch(0, 0);
      } else {
        is_handled = constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(0, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // careful

        path_condition.push_back(add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        is_handled = constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_sltu(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        take_branch(1, 0);
      }
    } else {
      constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    take_branch(0, 0);
  } else {
    std::cout << exe_name << ": both branches unreachable! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

bool mit_bvt_engine::evaluate_xor_true_false_branch_mit(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
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

void mit_bvt_engine::create_xor_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb, bool cannot_handle) {
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

  if (reg_theory_types[rs1] > MIT || reg_theory_types[rs2] > MIT) {
    cannot_handle = true;
  } else if (cannot_handle != true) {
    for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
      lo1 = lo1_p[i];
      up1 = up1_p[i];
      for (size_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
        lo2 = lo2_p[j];
        up2 = up2_p[j];
        cannot_handle = evaluate_xor_true_false_branch_mit(lo1, up1, lo2, up2);
      }
    }
  }

  if (cannot_handle) {
    // xor result:
    assert_path_condition_into_smt_expression();
    check_operands_smt_expressions();

    true_reachable  = check_sat_true_branch_bvt(boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
    false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_whether_is_equality_or_disequality() == EQ) {
          // false
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          take_branch(1, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]); // carefull

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_false_branch_bvt();
          dump_all_input_variables_on_trace_false_branch_bvt();
          take_branch(0, 0);
        } else {
          // false
          dump_involving_input_variables_false_branch_bvt();
          dump_all_input_variables_on_trace_false_branch_bvt();
          take_branch(0, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]); // carefull

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          take_branch(1, 0);
        }
      } else {
        dump_involving_input_variables_true_branch_bvt();
        dump_all_input_variables_on_trace_true_branch_bvt();
        take_branch(1, 0);
      }
    } else if (false_reachable) {
      dump_involving_input_variables_false_branch_bvt();
      dump_all_input_variables_on_trace_false_branch_bvt();
      take_branch(0, 0);
    } else {
      std::cout << exe_name << ": both branches unreachable! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    return;
  }

  queries_reasoned_by_mit+=2;

  if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0)
    true_reachable  = true;
  if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0)
    false_reachable = true;

  save_trace_state();
  bool is_handled = false;

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_whether_is_equality_or_disequality() == EQ) {
        is_handled = constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(1, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // careful

        path_condition.push_back(add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        is_handled = constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        take_branch(0, 0);
      } else {
        is_handled = constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(0, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // carful

        path_condition.push_back(add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        is_handled = constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        is_handled = constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        if (is_handled == false) { upgrade_to_bvt_xor(lo1_p, up1_p, lo2_p, up2_p, trb); return; }
        take_branch(1, 0);
      }
    } else {
      constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, true);
      constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, true);
      take_branch(1, 0);
    }
  } else if (false_reachable) {
    constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, true);
    constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, true);
    take_branch(0, 0);
  } else {
    std::cout << exe_name << ": both branches unreachable! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

bool mit_bvt_engine::check_sat_true_branch_bvt(BoolectorNode* assert) {
  bool result = false;
  boolector_push(btor, 1);
  boolector_assert(btor, assert);
  queries_reasoned_by_bvt++;
  true_input_assignments.clear();
  if (boolector_sat(btor) == BOOLECTOR_SAT) {
    result = true;
    for (size_t i = 0; i < input_table.size(); i++) {
      true_input_assignments.push_back(boolector_bv_assignment(btor, smt_exprs[asts[input_table_store_trace_ptr[i]]] ) );
    }
    queries_reasoned_by_bvt_sat++;
  }
  boolector_pop(btor, 1);

  return result;
}

bool mit_bvt_engine::check_sat_false_branch_bvt(BoolectorNode* assert) {
  bool result = false;
  boolector_push(btor, 1);
  boolector_assert(btor, assert);
  queries_reasoned_by_bvt++;
  false_input_assignments.clear();
  if (boolector_sat(btor) == BOOLECTOR_SAT) {
    result = true;
    for (size_t i = 0; i < input_table.size(); i++) {
      false_input_assignments.push_back(boolector_bv_assignment(btor, smt_exprs[asts[input_table_store_trace_ptr[i]]] ) );
    }
    queries_reasoned_by_bvt_sat++;
  }
  boolector_pop(btor, 1);

  return result;
}

void mit_bvt_engine::dump_involving_input_variables_true_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  involved_inputs_in_current_conditional_expression_rs1_operand.clear();
  if (reg_symb_type[rs1] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs1]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs1]][i];
      involved_inputs_in_current_conditional_expression_rs1_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      value_v[0] = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), BVT);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }

  involved_inputs_in_current_conditional_expression_rs2_operand.clear();
  if (reg_symb_type[rs2] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs2]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs2]][i];
      involved_inputs_in_current_conditional_expression_rs2_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      value_v[0] = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), BVT);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }
}

void mit_bvt_engine::dump_involving_input_variables_false_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  involved_inputs_in_current_conditional_expression_rs1_operand.clear();
  if (reg_symb_type[rs1] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs1]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs1]][i];
      involved_inputs_in_current_conditional_expression_rs1_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      value_v[0] = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), BVT);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }

  involved_inputs_in_current_conditional_expression_rs2_operand.clear();
  if (reg_symb_type[rs2] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs2]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs2]][i];
      involved_inputs_in_current_conditional_expression_rs2_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      value_v[0] = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), BVT);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }
}

void mit_bvt_engine::dump_all_input_variables_on_trace_true_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  for (size_t i = 0; i < input_table.size(); i++) {
    if (vector_contains_element(involved_inputs_in_current_conditional_expression_rs1_operand, i) ||
        vector_contains_element(involved_inputs_in_current_conditional_expression_rs2_operand, i) ) continue;
    involved_input_ast_tc = input_table_ast_tcs_before_branch_evaluation[i];
    if (theory_type_ast_nodes[involved_input_ast_tc] == MIT) continue;
    value_v[0] = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input_ast_tc]);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), BVT);
    }
    input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
  }

}

void mit_bvt_engine::dump_all_input_variables_on_trace_false_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  for (size_t i = 0; i < input_table.size(); i++) {
    if (vector_contains_element(involved_inputs_in_current_conditional_expression_rs1_operand, i) ||
        vector_contains_element(involved_inputs_in_current_conditional_expression_rs2_operand, i) ) continue;
    involved_input_ast_tc = input_table_ast_tcs_before_branch_evaluation[i];
    if (theory_type_ast_nodes[involved_input_ast_tc] == MIT) continue;
    value_v[0] = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input_ast_tc]);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), BVT);
    }
    input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
  }
}

void mit_bvt_engine::refine_abvt_abstraction_by_dumping_all_input_variables_on_trace_bvt() {
  uint64_t ast_ptr, involved_input, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  input_assignments.clear();
  for (size_t i = 0; i < input_table.size(); i++) {
    input_assignments.push_back(boolector_bv_assignment(btor, smt_exprs[asts[input_table_store_trace_ptr[i]]] ) );
  }

  for (size_t i = 0; i < input_table.size(); i++) {
    involved_input = input_table[i];
    if (theory_type_ast_nodes[involved_input] == MIT) continue;
    is_assigned = false;
    value_v[0] = std::stoull(input_assignments[ast_nodes[involved_input].right_node], 0, 2);
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input].right_node, 1, value_v, value_v, 1, 0, zero_v, BVT, smt_exprs[involved_input]);
    for (size_t k = 0; k < store_trace_ptrs[involved_input].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, BVT); pcs[tc] = sltu_instruction; // careful
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input].right_node), BVT); pcs[tc] = sltu_instruction; // careful
    }
    input_table.at(ast_nodes[involved_input].right_node) = ast_ptr;
  }
}

// --------------------------- conditional expression --------------------------

bool mit_bvt_engine::match_addi_instruction() {
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

bool mit_bvt_engine::match_sub_instruction(uint64_t prev_instr_rd) {
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

uint8_t mit_bvt_engine::check_conditional_type_whether_is_equality_or_disequality() {
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
    std::cout << exe_name << ": XOR instruction is incorrectly used at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  return 0;
}

uint8_t mit_bvt_engine::check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq() {
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

// -----------------------------------------------------------------------------
// ------------------------- on-demand bvt layer -------------------------------
// -----------------------------------------------------------------------------

BoolectorNode* mit_bvt_engine::boolector_op(uint8_t op, uint64_t ast_tc) {
  switch (op) {
    case CONST: {
      return smt_exprs[ast_tc] = boolector_unsigned_int_64(mintervals_los[ast_tc][0]);
    }
    case ADD: {
      return smt_exprs[ast_tc] = boolector_add(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case SUB: {
      return smt_exprs[ast_tc] = boolector_sub(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case MUL: {
      return smt_exprs[ast_tc] = boolector_mul(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case DIVU: {
      return smt_exprs[ast_tc] = boolector_udiv(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case REMU: {
      return smt_exprs[ast_tc] = boolector_urem(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case ILT: {
      return smt_exprs[ast_tc] = boolector_ult(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case IGTE: {
      return smt_exprs[ast_tc] = boolector_ugte(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case IEQ: {
      return smt_exprs[ast_tc] = boolector_eq(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    case INEQ: {
      return smt_exprs[ast_tc] = boolector_ne(btor, smt_exprs[ast_nodes[ast_tc].left_node], smt_exprs[ast_nodes[ast_tc].right_node]);
    }
    default: {
      std::cout << "never be reached" << '\n';
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }
}

BoolectorNode* mit_bvt_engine::create_smt_expression(uint64_t ast_tc) {
  if (ast_tc == 0) {
    std::cout << exe_name << ": detected error, ast_tc = 0 in create_smt_expression at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  if (smt_exprs[ast_tc] != boolector_null)
    return smt_exprs[ast_tc];

  // VAR always has a smt_expr

  if (ast_nodes[ast_tc].type == CONST)
    return boolector_op(CONST, ast_tc);

  create_smt_expression(ast_nodes[ast_tc].left_node);
  create_smt_expression(ast_nodes[ast_tc].right_node);

  return boolector_op(ast_nodes[ast_tc].type, ast_tc);
}

void mit_bvt_engine::check_operands_smt_expressions() {
  reg_bvts[rs1] = create_smt_expression(reg_asts[rs1]);
  reg_bvts[rs2] = create_smt_expression(reg_asts[rs2]);
}

BoolectorNode* mit_bvt_engine::create_smt_expression_of_the_conditional_expression(uint64_t ast_tc) {
  create_smt_expression(ast_nodes[ast_tc].left_node);
  create_smt_expression(ast_nodes[ast_tc].right_node);

  return boolector_op(ast_nodes[ast_tc].type, ast_tc);
}

void mit_bvt_engine::assert_path_condition_into_smt_expression() {
  for (size_t i = 0; i < path_condition.size(); i++) {
    if (steps[path_condition[i]] == 1) {
      theory_type_ast_nodes[path_condition[i] - 1] = BVT;
      boolector_push(btor, 1);
    }
    boolector_assert(btor, create_smt_expression_of_the_conditional_expression(path_condition[i]));
  }
  path_condition.clear();
}

// -----------------------------------------------------------------------------
// ----------------------- on-demand propagation on ld -------------------------
// -----------------------------------------------------------------------------

uint64_t mit_bvt_engine::compute_add(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t addend, ast_ptr;
  uint64_t stored_to_tc, mr_stored_to_tc;

  if (symbolic_operands == LEFT) {
    crt_operand_ast_tc = right_operand_ast_tc;
    sym_operand_ast_tc = left_operand_ast_tc;
    addend = mintervals_los[crt_operand_ast_tc][0];

    for (size_t i = 0; i < mintervals_los[sym_operand_ast_tc].size(); i++) {
      propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][i] + addend;
      propagated_minterval_up[i] = mintervals_ups[sym_operand_ast_tc][i] + addend;
    }

    ast_ptr = add_ast_node(ADD, sym_operand_ast_tc, crt_operand_ast_tc, mintervals_los[sym_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);

  } else if (symbolic_operands == RIGHT) {
    crt_operand_ast_tc = left_operand_ast_tc;
    sym_operand_ast_tc = right_operand_ast_tc;
    addend = mintervals_los[crt_operand_ast_tc][0];

    for (size_t i = 0; i < mintervals_los[sym_operand_ast_tc].size(); i++) {
      propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][i] + addend;
      propagated_minterval_up[i] = mintervals_ups[sym_operand_ast_tc][i] + addend;
    }

    ast_ptr = add_ast_node(ADD, sym_operand_ast_tc, crt_operand_ast_tc, mintervals_los[sym_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);

  } else {
    // the result is of either BVT or ABVT
    // thus the value interval for the result contain *one* witness.

    uint64_t resulting_witness = mintervals_los[left_operand_ast_tc][0] + mintervals_los[right_operand_ast_tc][0];
    propagated_minterval_lo[0] = resulting_witness;
    propagated_minterval_up[0] = resulting_witness;

    merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

    ast_ptr = add_ast_node(ADD, left_operand_ast_tc, right_operand_ast_tc, 1, propagated_minterval_lo, propagated_minterval_up, 1, merged_array.size(), merged_array, theory_type, smt_exprs[old_ast_tc]);
  }

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, theory_type);
  }

  return ast_ptr;
}

uint64_t mit_bvt_engine::compute_sub(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t sub_lo, sub_up, ast_ptr;
  uint64_t stored_to_tc, mr_stored_to_tc;

  if (symbolic_operands == LEFT) {
    sub_lo = mintervals_los[right_operand_ast_tc][0];
    sub_up = mintervals_ups[right_operand_ast_tc][0];
    for (size_t i = 0; i < mintervals_los[left_operand_ast_tc].size(); i++) {
      propagated_minterval_lo[i] = mintervals_los[left_operand_ast_tc][i] - sub_up;
      propagated_minterval_up[i] = mintervals_ups[left_operand_ast_tc][i] - sub_lo;
    }

    ast_ptr = add_ast_node(SUB, left_operand_ast_tc, right_operand_ast_tc, mintervals_los[left_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_ast_tcs[left_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);

  } else if (symbolic_operands == RIGHT) {
    sub_lo = mintervals_los[left_operand_ast_tc][0];
    sub_up = mintervals_ups[left_operand_ast_tc][0];
    for (size_t i = 0; i < mintervals_los[right_operand_ast_tc].size(); i++) {
      propagated_minterval_lo[i] = sub_lo - mintervals_ups[right_operand_ast_tc][i];
      propagated_minterval_up[i] = sub_up - mintervals_los[right_operand_ast_tc][i];
    }

    ast_ptr = add_ast_node(SUB, left_operand_ast_tc, right_operand_ast_tc, mintervals_los[right_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);

  } else {
    // the result is of either BVT or ABVT
    // thus the value interval for the result contain *one* witness.

    uint64_t resulting_witness = mintervals_los[left_operand_ast_tc][0] - mintervals_los[right_operand_ast_tc][0];
    propagated_minterval_lo[0] = resulting_witness;
    propagated_minterval_up[0] = resulting_witness;

    merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

    ast_ptr = add_ast_node(SUB, left_operand_ast_tc, right_operand_ast_tc, 1, propagated_minterval_lo, propagated_minterval_up, 1, merged_array.size(), merged_array, theory_type, smt_exprs[old_ast_tc]);
  }

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, theory_type);
  }

  return ast_ptr;
}

uint64_t mit_bvt_engine::compute_mul(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  bool cnd = false;
  uint64_t multiplier;
  uint64_t stored_to_tc, mr_stored_to_tc;

  if (symbolic_operands == LEFT) {
    crt_operand_ast_tc = right_operand_ast_tc;
    sym_operand_ast_tc = left_operand_ast_tc;
  } else if (symbolic_operands == RIGHT) {
    crt_operand_ast_tc = left_operand_ast_tc;
    sym_operand_ast_tc = right_operand_ast_tc;
  } else {
    // BOTH
    // non-linear arithmetic is not supported
    std::cout << exe_name << ": detected a non-linear mul in compute_mul!!! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  multiplier = mintervals_los[crt_operand_ast_tc][0];

  if (multiplier == 0) {
    // TODO: handle this case
    std::cout << exe_name << ": multiplier is zero in compute_mul\n";
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  for (size_t i = 0; i < mintervals_los[sym_operand_ast_tc].size(); i++) {
    cnd = mul_condition_mit(mintervals_los[sym_operand_ast_tc][i], mintervals_ups[sym_operand_ast_tc][i], multiplier);
    if (cnd == true) {
      propagated_minterval_lo[i] = mintervals_los[sym_operand_ast_tc][i] * multiplier;
      propagated_minterval_up[i] = mintervals_ups[sym_operand_ast_tc][i] * multiplier;
    } else {
      // assert: never must be reached
      std::cout << exe_name << ": detected an overflow case in compute_mul upgrades theory at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      propagated_minterval_lo[0] = mintervals_los[sym_operand_ast_tc][0] * multiplier;
      propagated_minterval_up[0] = propagated_minterval_lo[0];
      break;
    }
  }

  uint64_t ast_ptr;
  if (cnd) {
    ast_ptr = add_ast_node(MUL, sym_operand_ast_tc, crt_operand_ast_tc, mintervals_los[sym_operand_ast_tc].size(), propagated_minterval_lo, propagated_minterval_up, steps[old_ast_tc], involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);
  } else {
    ast_ptr = add_ast_node(MUL, sym_operand_ast_tc, crt_operand_ast_tc, 1, propagated_minterval_lo, propagated_minterval_up, 1, involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc], BVT, smt_exprs[old_ast_tc]);
  }

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, theory_type);
  }

  return ast_ptr;
}

bool mit_bvt_engine::compute_divu_mit(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc) {
  uint64_t divisor = mintervals_los[right_operand_ast_tc][0];
  uint64_t div_lo = mintervals_los[left_operand_ast_tc][0] / divisor;
  uint64_t div_up = mintervals_ups[left_operand_ast_tc][0] / divisor;

  // step computation
  if (steps[left_operand_ast_tc] < divisor) {
    if (divisor % steps[left_operand_ast_tc] != 0) {
      // steps in divison are not consistent
      return false;
    }
    propagated_step = 1;
  } else {
    if (steps[left_operand_ast_tc] % divisor != 0) {
      // steps in divison are not consistent
      return false;
    }
    propagated_step = steps[left_operand_ast_tc] / divisor;
  }

  // interval semantics of divu
  if (mintervals_los[left_operand_ast_tc][0] > mintervals_ups[left_operand_ast_tc][0]) {
    // rs1 constraint is wrapped

    // lo/k == up/k (or) == up/k + step_rd ==> mergable
    if (div_lo != div_up)
      if (div_lo != div_up + propagated_step) {
        // wrapped divison results two intervals
        return false;
      }

    uint64_t max = compute_upper_bound_mit(mintervals_los[left_operand_ast_tc][0], steps[left_operand_ast_tc], UINT64_MAX_T);
    propagated_minterval_lo[0] = (max + steps[left_operand_ast_tc]) / divisor;
    propagated_minterval_up[0] = max          / divisor;

  } else {
    // rs1 constraint is not wrapped
    propagated_minterval_lo[0] = div_lo;
    propagated_minterval_up[0] = div_up;
  }

  return true;
}

uint64_t mit_bvt_engine::compute_divu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t dividend;
  uint64_t divisor;
  uint64_t stored_to_tc, mr_stored_to_tc;

  if (symbolic_operands == LEFT) {
    sym_operand_ast_tc = left_operand_ast_tc;
  } else if (symbolic_operands == RIGHT) {
    sym_operand_ast_tc = right_operand_ast_tc;
  } else {
    // BOTH
    // non-linear arithmetic is not supported
    std::cout << exe_name << ": detected a non-linear divu in compute_divu! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  bool is_handled = false;
  if (theory_type == MIT && symbolic_operands == LEFT && mintervals_los[left_operand_ast_tc].size() == 1) {
    is_handled = compute_divu_mit(left_operand_ast_tc, right_operand_ast_tc);
  }

  if (is_handled == true) {
    theory_type = MIT;
  } else {
    dividend = mintervals_los[left_operand_ast_tc][0];
    divisor  = mintervals_los[right_operand_ast_tc][0];
    uint64_t resulting_witness = dividend / divisor;
    propagated_minterval_lo[0] = resulting_witness;
    propagated_minterval_up[0] = resulting_witness;
    propagated_step = 1;
    theory_type = BVT;
  }

  uint64_t ast_ptr = add_ast_node(DIVU, left_operand_ast_tc, right_operand_ast_tc, 1, propagated_minterval_lo, propagated_minterval_up, propagated_step, involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, theory_type);
  }

  return ast_ptr;
}

bool mit_bvt_engine::compute_remu_mit(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc) {
  uint64_t rem_lo;
  uint64_t rem_up;
  uint64_t step_rd;
  uint64_t divisor = mintervals_los[right_operand_ast_tc][0];
  uint64_t step    = steps[left_operand_ast_tc];

  if (mintervals_los[left_operand_ast_tc][0] <= mintervals_ups[left_operand_ast_tc][0]) {
    // rs1 interval is not wrapped
    int rem_typ = remu_condition(mintervals_los[left_operand_ast_tc][0], mintervals_ups[left_operand_ast_tc][0], step, divisor);
    if (rem_typ == 0) {
      rem_lo  = mintervals_los[left_operand_ast_tc][0] % divisor;
      rem_up  = mintervals_ups[left_operand_ast_tc][0] % divisor;
      step_rd = step;
    } else if (rem_typ == 1) {
      return false;
    } else if (rem_typ == 2) {
      uint64_t gcd_step_k = gcd(step, divisor);
      rem_lo  = mintervals_los[left_operand_ast_tc][0]%divisor - ((mintervals_los[left_operand_ast_tc][0]%divisor) / gcd_step_k) * gcd_step_k;
      rem_up  = compute_upper_bound_mit(rem_lo, gcd_step_k, divisor - 1);
      step_rd = gcd_step_k;
    } else {
      return false;
    }

  } else if (is_power_of_two(divisor)) {
    // rs1 interval is wrapped
    uint64_t gcd_step_k = gcd(step, divisor);
    uint64_t lcm        = (step * divisor) / gcd_step_k;

    if (mintervals_ups[left_operand_ast_tc][0] - mintervals_los[left_operand_ast_tc][0] < lcm - step)
      return false;

    rem_lo  = mintervals_los[left_operand_ast_tc][0]%divisor - ((mintervals_los[left_operand_ast_tc][0]%divisor) / gcd_step_k) * gcd_step_k;
    rem_up  = compute_upper_bound_mit(rem_lo, gcd_step_k, divisor - 1);
    step_rd = gcd_step_k;

  } else {
    return false;
  }

  propagated_minterval_lo[0] = rem_lo;
  propagated_minterval_up[0] = rem_up;
  propagated_step            = step_rd;

  return true;
}

uint64_t mit_bvt_engine::compute_remu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t remaindend;
  uint64_t divisor;
  uint64_t stored_to_tc, mr_stored_to_tc;

  if (symbolic_operands == LEFT) {
    sym_operand_ast_tc = left_operand_ast_tc;
  } else if (symbolic_operands == RIGHT) {
    sym_operand_ast_tc = right_operand_ast_tc;
  } else {
    // BOTH
    // non-linear arithmetic is not supported
    std::cout << exe_name << ": detected a non-linear remu in compute_remu! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  bool is_handled = false;
  if (theory_type == MIT && symbolic_operands == LEFT && mintervals_los[left_operand_ast_tc].size() == 1) {
    is_handled = compute_remu_mit(left_operand_ast_tc, right_operand_ast_tc);
  }

  if (is_handled == true) {
    theory_type = MIT;
  } else {
    remaindend = mintervals_los[left_operand_ast_tc][0];
    divisor    = mintervals_los[right_operand_ast_tc][0];
    uint64_t resulting_witness = remaindend % divisor;
    propagated_minterval_lo[0] = resulting_witness;
    propagated_minterval_up[0] = resulting_witness;
    propagated_step = 1;
    theory_type = BVT;
  }

  uint64_t ast_ptr = add_ast_node(REMU, left_operand_ast_tc, right_operand_ast_tc, 1, propagated_minterval_lo, propagated_minterval_up, propagated_step, involved_sym_inputs_cnts[sym_operand_ast_tc], involved_sym_inputs_ast_tcs[sym_operand_ast_tc], theory_type, smt_exprs[old_ast_tc]);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, theory_type);
  }

  return ast_ptr;
}

uint64_t mit_bvt_engine::recompute_operation(uint8_t op, uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  switch (op) {
    case ADD:
      return compute_add(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc, theory_type, symbolic_operands);
    case SUB:
      return compute_sub(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc, theory_type, symbolic_operands);
    case MUL:
      return compute_mul(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc, theory_type, symbolic_operands);
    case DIVU:
      return compute_divu(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc, theory_type, symbolic_operands);
    case REMU:
      return compute_remu(left_operand_ast_tc, right_operand_ast_tc, old_ast_tc, theory_type, symbolic_operands);
    default: {
      std::cout << "never be reached" << '\n';
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }
}

uint64_t mit_bvt_engine::update_current_constraint_on_ast_expression(uint64_t ast_tc) {
  uint64_t left_operand_ast_tc;
  uint64_t right_operand_ast_tc;
  uint64_t ast_ptr;
  uint8_t  symbolic_operands;
  uint8_t  theory_type;

  if (ast_nodes[ast_tc].type == VAR)
    return input_table[ast_nodes[ast_tc].right_node];

  // operation which both operands are symbolic will be detected by detect_symbolic_operand function
  symbolic_operands = detect_symbolic_operand(ast_tc);
  if (symbolic_operands == LEFT) {
    left_operand_ast_tc  = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].left_node);
    right_operand_ast_tc = ast_nodes[ast_tc].right_node;
    theory_type = std::max(theory_type_ast_nodes[left_operand_ast_tc], theory_type_ast_nodes[ast_tc]);
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc, theory_type, symbolic_operands);
  } else if (symbolic_operands == RIGHT) {
    right_operand_ast_tc = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].right_node);
    left_operand_ast_tc  = ast_nodes[ast_tc].left_node;
    theory_type = std::max(theory_type_ast_nodes[right_operand_ast_tc], theory_type_ast_nodes[ast_tc]);
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc, theory_type, symbolic_operands);
  } else {
    left_operand_ast_tc  = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].left_node);
    right_operand_ast_tc = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].right_node);

    if (theory_type_ast_nodes[ast_tc] < BVT)
      std::cout << exe_name << ": an error detected in update_current_constraint_on_ast_expression at 0x" << std::hex << pc - entry_point << std::dec << std::endl;

    theory_type = std::max(std::max(theory_type_ast_nodes[left_operand_ast_tc], theory_type_ast_nodes[right_operand_ast_tc]), theory_type_ast_nodes[ast_tc]);
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc, theory_type, symbolic_operands);
  }
}

// -----------------------------------------------------------------------------
// ----------- upgrade theory on backward_propagation failure ------------------
// -----------------------------------------------------------------------------

void mit_bvt_engine::save_trace_state() {
  saved_tc_before_branch_evaluation_using_mit = tc;
  saved_ast_trace_cnt_before_branch_evaluation_using_mit = ast_trace_cnt;
  saved_path_condition_size_before_branch_evaluation_using_mit = path_condition.size();
}

void mit_bvt_engine::restore_trace_state() {
  tc = saved_tc_before_branch_evaluation_using_mit;
  ast_trace_cnt = saved_ast_trace_cnt_before_branch_evaluation_using_mit;

  while (saved_path_condition_size_before_branch_evaluation_using_mit < path_condition.size()) {
    path_condition.pop_back();
  }

  queries_reasoned_by_mit-=2;
}

void mit_bvt_engine::backtrack_branch_evaluation_effect_on_trace() {
  while (saved_tc_before_branch_evaluation_using_mit < tc) {
    undo_effects();
  }
}

void mit_bvt_engine::upgrade_to_bvt_sltu(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  backtrack_branch_evaluation_effect_on_trace();
  restore_trace_state();
  create_sltu_constraints(lo1_p, up1_p, lo2_p, up2_p, trb, true);
}

void mit_bvt_engine::upgrade_to_bvt_xor(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  backtrack_branch_evaluation_effect_on_trace();
  restore_trace_state();
  create_xor_constraints(lo1_p, up1_p, lo2_p, up2_p, trb, true);
}

void mit_bvt_engine::undo_effects() {
  uint64_t vaddr;

  vaddr = vaddrs[tc];

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      if (vaddr == REG_FP) {
        // restoring mrcc
        mrcc = tcs[tc];

        // look at store_symbolic_memory for registers
        if (ast_trace_cnt > most_recent_if_on_ast_trace) {
          ast_trace_cnt = most_recent_if_on_ast_trace;
        }
        most_recent_if_on_ast_trace = asts[tc];
      }
    }
  } else if (vaddr == NUMBEROFREGISTERS) { // means input_t record
    input_table.at(ast_nodes[asts[tc]].right_node) = values[tc];
  } else {
    if (store_trace_ptrs[asts[tc]].size() > 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else if (store_trace_ptrs[asts[tc]].size() == 1) {
      if (ast_nodes[asts[tc]].type == VAR) input_table.at(ast_nodes[asts[tc]].right_node) = asts[tcs[tc]];
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      std::cout << exe_name << ": error occured during sltu backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

    store_virtual_memory(pt, vaddr, tcs[tc]);
  }

  efree();
}