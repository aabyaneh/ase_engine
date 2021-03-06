#include "bvt_engine.hpp"

// --------------------------- auxiliary functions -----------------------------

bool bvt_engine::vector_contains_element(std::vector<uint64_t>& vector, uint64_t element) {
  for (std::vector<uint64_t>::iterator it = vector.begin(); it != vector.end(); ++it) {
    if (*it == element)
      return true;
  }

  return false;
}

void bvt_engine::merge_arrays(std::vector<uint64_t>& vector_1, std::vector<uint64_t>& vector_2, size_t vector_1_size, size_t vector_2_size) {
  merged_array.clear();
  for (size_t i = 0; i < vector_1_size; i++) {
    merged_array.push_back(vector_1[i]);
  }
  for (size_t i = 0; i < vector_2_size; i++) {
    if (vector_contains_element(vector_1, vector_2[i])) continue;
    merged_array.push_back(vector_2[i]);
  }
}

void bvt_engine::init_engine(uint64_t peek_argument) {
  init_library();
  init_interpreter();
  init_memory(round_up(10 * MAX_TRACE_LENGTH * SIZEOFUINT64, MEGABYTE) / MEGABYTE + 1);

  // ------------------ symbolic engine initialization -------------------------

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
  reg_involved_inputs.resize(NUMBEROFREGISTERS);
  reg_involved_inputs_cnts = (uint32_t*) zalloc(NUMBEROFREGISTERS * sizeof(uint32_t));
  reg_asts                 = (uint64_t*) malloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  reg_bvts                = (BoolectorNode**) malloc(NUMBEROFREGISTERS * sizeof(BoolectorNode*));
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

  ast_nodes                = (struct node*)    malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(struct node*));
  involved_sym_inputs_cnts = (uint64_t*)       malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(uint64_t));
  smt_exprs                = (BoolectorNode**) malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(BoolectorNode*));
  symb_types               = (uint8_t*)        malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(uint8_t));

  // -------------------------
  // branch evaluation
  // -------------------------
  zero_v.push_back(0);
  one_v.push_back(1);
  value_v.push_back(0);

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
  zero_node        = add_ast_node(CONST, 0, 0, zero_v, zero_v, 0, zero_v, boolector_null, CONCRETE);
  one_node         = add_ast_node(CONST, 0, 0, one_v , one_v , 0, zero_v, boolector_null, CONCRETE);
  smt_exprs[zero_node] = zero_bv;
  smt_exprs[one_node]  = one_bv;

  reg_asts[REG_ZR] = zero_node;

  for (size_t i = 0; i < NUMBEROFREGISTERS; i++) {
    reg_mintervals_los[i].resize(MAX_NUM_OF_INTERVALS);
    reg_mintervals_ups[i].resize(MAX_NUM_OF_INTERVALS);
    reg_involved_inputs[i].resize(MAX_NUM_OF_INVOLVED_INPUTS);
  }

  pcs[0]             = 0;
  tcs[0]             = 0;
  vaddrs[0]          = 0;
  values[0]          = 0;
  data_types[0]      = 0;
  asts[0]            = 0;
  mr_sds[0]          = 0;
  bvt_false_branches[0] = boolector_null;

  involved_sym_inputs_cnts[0] = 0;
  smt_exprs[0]                = boolector_null;
  symb_types[0]               = 0;

  input_table.reserve(1000);

  TWO_TO_THE_POWER_OF_32 = 4294967296ULL;

  if (IS_TEST_MODE) {
    std::string test_output = binary_name;
    test_output += ".result";
    output_results.open(test_output, std::ofstream::trunc);
  }
}

void bvt_engine::print_input_witness(size_t i, size_t j, uint64_t lo, uint64_t up) {
  std::cout << std::left << MAGENTA "--INPUT :=  id: " << std::setw(3) << i+1 << ", #: " << std::setw(2) << j << " => [lo: " << std::setw(5) << lo << ", up: " << std::setw(5) << up << ", step: " << 1 << "]" << RESET << std::endl;
}

void bvt_engine::witness_profile() {
  uint64_t cardinality;

  current_number_of_witnesses = 1;

  if (IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT) std::cout << "\n-------------------------------------------------------------\n";

  for (size_t i = 0; i < input_table.size(); i++) {
    cardinality = 0;
    for (size_t j = 0; j < mintervals_los[input_table[i]].size(); j++) {
      cardinality += (mintervals_ups[input_table[i]][j] - mintervals_los[input_table[i]][j] + 1);

      if (IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT) print_input_witness(i, j, mintervals_los[input_table[i]][j], mintervals_ups[input_table[i]][j]);
    }

    if (cardinality > 0) {
      if (is_number_of_generated_witnesses_overflowed == false) {
        if (current_number_of_witnesses * cardinality > UINT64_MAX_T) // overflow?
          is_number_of_generated_witnesses_overflowed = true;
        else
          current_number_of_witnesses *= cardinality;
      }
    } else
      std::cout << exe_name << ": cardinality of an input is == zero! " << std::endl;
  }

  if (current_number_of_witnesses > max_number_of_generated_witnesses_among_all_paths)
    max_number_of_generated_witnesses_among_all_paths = current_number_of_witnesses;

  total_number_of_generated_witnesses_for_all_paths += current_number_of_witnesses;
  if (total_number_of_generated_witnesses_for_all_paths < current_number_of_witnesses) // overflow?
    is_number_of_generated_witnesses_overflowed = true;
}

void print_execution_info(uint64_t paths, uint64_t total_number_of_generated_witnesses_for_all_paths, uint64_t max_number_of_generated_witnesses_among_all_paths, uint64_t queries_reasoned_by_bvt, bool is_number_of_generated_witnesses_overflowed) {
  std::cout << "\n";
  std::cout << "number of explored paths:= " << paths << std::endl;

  if (is_number_of_generated_witnesses_overflowed == false)
    std::cout << "number of witnesses:= total: " << total_number_of_generated_witnesses_for_all_paths << ", max: " << max_number_of_generated_witnesses_among_all_paths << std::endl;
  else
    std::cout << "number of witnesses:= total: > " << UINT64_MAX << ", max: !" << std::endl;

  std::cout << "number of queries:= bvt: " << queries_reasoned_by_bvt << "\n\n";
}

uint64_t bvt_engine::run_engine(uint64_t* to_context) {
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
            output_results << std::left << "I=" << j+1 << ";" << i+1 << ";" << mintervals_los[input_table[j]][i] << ";" << mintervals_ups[input_table[j]][i] << ";" << 1 << std::endl;
          }
        }
        output_results << "B=" << paths+1 << "\n";
      }

      if (does_path_need_to_be_reasoned_by_smt == false) {
        if (paths == 0) std::cout << exe_name << ": backtracking \n"; else unprint_integer(paths);
        paths++;
        print_integer(paths);
        witness_profile();

      } else {
        queries_reasoned_by_bvt++;
        if (boolector_sat(btor) == BOOLECTOR_SAT) {
          if (paths == 0) std::cout << exe_name << ": backtracking \n"; else unprint_integer(paths);
          paths++;
          print_integer(paths);

          // dump inputs taken from smt, because this path was reasoned lazily so at end-point inputs should be updated with correct values
          // for print and test generation purpose
          refine_abvt_abstraction_by_dumping_all_input_variables_on_trace_bvt();

          does_path_need_to_be_reasoned_by_smt = false;

          witness_profile();
        }
      }

      backtrack_trace(current_context);

      if (pc == 0) {
        print_execution_info(paths, total_number_of_generated_witnesses_for_all_paths, max_number_of_generated_witnesses_among_all_paths, queries_reasoned_by_bvt, is_number_of_generated_witnesses_overflowed);

        if (symbolic_input_cnt != 0)
          std::cout << "symbolic_input_cnt is not zero!\n";

        if (IS_TEST_MODE)
          output_results.close();

        return EXITCODE_NOERROR;
      }
    }

    if (is_execution_timeout) {
      print_execution_info(paths, total_number_of_generated_witnesses_for_all_paths, max_number_of_generated_witnesses_among_all_paths, queries_reasoned_by_bvt, is_number_of_generated_witnesses_overflowed);

      return EXITCODE_TIMEOUT;
    }
  }
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void bvt_engine::init_interpreter() {
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

void bvt_engine::map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data) {
  // assert: is_valid_virtual_address(vaddr) == 1
  uint64_t ast_ptr;

  if (is_virtual_address_mapped(get_pt(context), vaddr) == 0)
    map_page(context, get_page_of_virtual_address(vaddr), (uint64_t) palloc());

  if (is_trace_space_available()) {
    // always track initialized memory by using tc as most recent branch
    value_v[0] = data;
    ast_ptr = add_ast_node(CONST, 0, 0, value_v, value_v, 0, zero_v, boolector_null, CONCRETE);
    store_symbolic_memory(get_pt(context), vaddr, data, 0, ast_ptr, tc, 1, CONCRETE);

  } else {
    std::cout << exe_name << ": ealloc out of memory\n";
    exit((int) EXITCODE_OUTOFTRACEMEMORY);
  }
}

void bvt_engine::set_SP(uint64_t* context) {
  uint64_t SP;

  // the call stack grows top down
  SP = VIRTUALMEMORYSIZE - REGISTERSIZE;

  // set bounds to register value for symbolic execution
  get_regs(context)[REG_SP]        = SP;
  reg_data_type[REG_SP]            = VALUE_T;
  reg_symb_type[REG_SP]            = CONCRETE;
  reg_mintervals_los[REG_SP][0]    = SP;
  reg_mintervals_ups[REG_SP][0]    = SP;
  reg_involved_inputs_cnts[REG_SP] = 0;
  reg_asts[REG_SP]                 = 0;
  reg_bvts[REG_SP]                 = boolector_null;
  set_correction(REG_SP, 0, 0, 0);
}

void bvt_engine::up_load_binary(uint64_t* context) {
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

uint64_t bvt_engine::handle_system_call(uint64_t* context) {
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

uint64_t bvt_engine::handle_max_trace(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_exit_code(context, EXITCODE_OUTOFTRACEMEMORY);

  std::cout << exe_name << " ***************************************\n";
  std::cout << exe_name << " max trace is reached; engine backtracks\n";
  std::cout << exe_name << " ***************************************\n";

  return EXIT;
}

uint64_t bvt_engine::handle_exception(uint64_t* context) {
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

BoolectorNode* bvt_engine::boolector_unsigned_int_64(uint64_t value) {
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

void bvt_engine::implement_exit(uint64_t* context) {
  set_exit_code(context, sign_shrink(get_regs(context)[REG_A0], SYSCALL_BITWIDTH));
}

void bvt_engine::implement_read(uint64_t* context) {
  std::cout << exe_name << ": symbolic read is not implemented yet\n";
}

void bvt_engine::implement_printsv(uint64_t* context) {
  uint64_t id;

  id = get_regs(context)[REG_A0];

  std::cout << "\n------------------------------------------------------------\n";

  for (size_t i = 0; i < 1; i++) {
    std::cout << std::left << "PRINTSV :=) id: " << std::setw(3) << id << ", #: " << std::setw(2) << i <<
      " => [lo: " << std::setw(5) << reg_mintervals_los[REG_A1][i] << ", up: " << std::setw(5) << reg_mintervals_ups[REG_A1][i] <<
      ", step: " << 1 << "]\n";
  }

  for (size_t j = 0; j < input_table.size(); j++) {
    for (size_t i = 0; i < mintervals_los[input_table[j]].size(); i++) {
      std::cout << std::left << RED "--INPUT :=  id: " << std::setw(3) << j+1 << ", #: " << std::setw(2) << i << " => [lo: " << std::setw(5) << mintervals_los[input_table[j]][i] << ", up: " << std::setw(5) << mintervals_ups[input_table[j]][i] << ", step: " << 1 << "]" << RESET << '\n';
    }
  }

  if (IS_TEST_MODE) {
    for (size_t i = 0; i < 1; i++) {
      output_results << std::left << "P=" << id << ";" << i+1 << ";" << reg_mintervals_los[REG_A1][i] << ";" << reg_mintervals_ups[REG_A1][i] << ";" << 1 << std::endl;
    }
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void bvt_engine::implement_symbolic_input(uint64_t* context) {
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

  if (step > 1) {
    std::cout << exe_name << ": engine doesn't support steps of more than 1 for bit-vector theory\n";
  }

  // create AST node
  value_v_1[0] = lo; value_v_2[0] = lo;
  ast_ptr = add_ast_node(VAR, 0, symbolic_input_cnt, value_v_1, value_v_2, 0, zero_v, in, SYMBOLIC);

  // store in symbolic memory
  store_symbolic_memory(pt, addr, lo, VALUE_T, ast_ptr, tc, 1, SYMBOLIC);

  // insert in input table
  input_table.push_back(ast_ptr);
  input_table_store_trace_ptr.push_back(tc);

  // print on console
  // std::cout << std::left << "read symbolic input interval # " << std::setw(3) << symbolic_input_cnt << " => [lo: " << lo << ", up: " << up << ", step: " << 1 << "]\n";

  symbolic_input_cnt++;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void bvt_engine::implement_write(uint64_t* context) {
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

        // TODO: What should symbolically executed code output?
        // buffer points to a trace counter that refers to the actual value
        // actually_written = sign_extend(write(fd, values + load_physical_memory(buffer), bytes_to_write), SYSCALL_BITWIDTH);
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
  reg_involved_inputs_cnts[REG_A0] = 0;
  reg_asts[REG_A0]                 = 0;
  reg_bvts[REG_A0]                 = boolector_null;
  set_correction(REG_A0, 0, 0, 0);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

uint64_t bvt_engine::down_load_string(uint64_t* table, uint64_t vaddr, uint64_t* s) {
  uint64_t mrvc;
  uint64_t i;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (is_virtual_address_mapped(table, vaddr)) {
        mrvc = load_symbolic_memory(table, vaddr);

        *(s + i) = *(values + mrvc);

        if (symb_types[asts[mrvc]] == SYMBOLIC) {
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

void bvt_engine::implement_open(uint64_t* context) {
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

  reg_data_type[REG_A0]            = VALUE_T;
  reg_symb_type[REG_A0]            = CONCRETE;
  reg_mintervals_los[REG_A0][0]    = get_regs(context)[REG_A0];
  reg_mintervals_ups[REG_A0][0]    = get_regs(context)[REG_A0];
  reg_involved_inputs_cnts[REG_A0] = 0;
  reg_asts[REG_A0]                 = 0;
  reg_bvts[REG_A0]                 = boolector_null;
  set_correction(REG_A0, 0, 0, 0);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

void bvt_engine::implement_brk(uint64_t* context) {
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

    size = program_break - previous_program_break;


    reg_data_type[REG_A0]            = POINTER_T;              // interval is memory range, not symbolic value
    reg_symb_type[REG_A0]            = CONCRETE;
    get_regs(context)[REG_A0]        = previous_program_break;
    reg_mintervals_los[REG_A0][0]    = previous_program_break; // remember start and size of memory block for checking memory safety
    reg_mintervals_ups[REG_A0][0]    = size;                   // remember start and size of memory block for checking memory safety
    reg_involved_inputs_cnts[REG_A0] = 0;
    reg_asts[REG_A0]                 = 0;
    reg_bvts[REG_A0]                 = boolector_null;
    set_correction(REG_A0, 0, 0, 0);

    if (mrcc > 0) {
      if (is_trace_space_available()) {
        // since there has been branching record brk using vaddr == 0
        uint64_t ast_ptr = add_ast_node(CONST, 0, 0, reg_mintervals_los[REG_A0], reg_mintervals_ups[REG_A0], 0, zero_v, reg_bvts[REG_A0], CONCRETE);
        store_symbolic_memory(get_pt(context), 0, previous_program_break, POINTER_T, ast_ptr, tc, 1, CONCRETE);
      } else {
        throw_exception(EXCEPTION_MAXTRACE, 0);
        return;
      }
    }

  } else {
    // error returns current program break
    program_break = previous_program_break;

    reg_data_type[REG_A0]            = POINTER_T;
    reg_symb_type[REG_A0]            = CONCRETE;
    get_regs(context)[REG_A0]        = program_break;
    reg_mintervals_los[REG_A0][0]    = 0;
    reg_mintervals_ups[REG_A0][0]    = 0;
    reg_involved_inputs_cnts[REG_A0] = 0;
    reg_asts[REG_A0]                 = 0;
    reg_bvts[REG_A0]                 = boolector_null;
    set_correction(REG_A0, 0, 0, 0);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// ---------------------------- corrections ------------------------------------

void bvt_engine::set_correction(uint64_t reg, uint8_t hasmn, uint64_t addsub_corr, uint8_t corr_validity) {
  reg_hasmn[reg]          = hasmn;
  reg_addsub_corr[reg]    = addsub_corr;
  reg_corr_validity[reg]  = corr_validity;
}

void bvt_engine::create_ast_node_entry_for_accumulated_corr(uint64_t sym_reg) {
  value_v[0] = reg_addsub_corr[sym_reg];
  uint64_t crt_ptr = add_ast_node(CONST, 0, 0, value_v, value_v, 0, zero_v, boolector_null, CONCRETE);
  if (reg_hasmn[sym_reg]) {
    reg_asts[sym_reg] = add_ast_node(SUB, crt_ptr, reg_asts[sym_reg], reg_mintervals_los[sym_reg], reg_mintervals_ups[sym_reg], reg_involved_inputs_cnts[sym_reg], reg_involved_inputs[sym_reg], reg_bvts[sym_reg], SYMBOLIC);
  } else {
    reg_asts[sym_reg] = add_ast_node(ADD, crt_ptr, reg_asts[sym_reg], reg_mintervals_los[sym_reg], reg_mintervals_ups[sym_reg], reg_involved_inputs_cnts[sym_reg], reg_involved_inputs[sym_reg], reg_bvts[sym_reg], SYMBOLIC);
  }
}

void bvt_engine::create_ast_node_entry_for_concrete_operand(uint64_t crt_reg) {
  value_v[0]        = reg_mintervals_los[crt_reg][0];
  reg_asts[crt_reg] = add_ast_node(CONST, 0, 0, value_v, value_v, 0, zero_v, reg_bvts[crt_reg], CONCRETE);
}

void bvt_engine::evaluate_correction(uint64_t reg) {
  if (reg_addsub_corr[reg] || reg_hasmn[reg]) {
    create_ast_node_entry_for_accumulated_corr(reg);
  }
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void bvt_engine::apply_lui() {
  do_lui();

  if (rd != REG_ZR) {
    // interval semantics of lui
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);
  }
}

void bvt_engine::apply_addi() {
  uint64_t crt_ptr;

  do_addi();

  if (rd == REG_ZR)
    return;

  if (reg_data_type[rs1] == POINTER_T) {
    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs1][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs1][0];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);

    return;
  }

  reg_data_type[rd] = VALUE_T;

  if (reg_symb_type[rs1] == SYMBOLIC) {
    // rd inherits rs1 constraint
    reg_symb_type[rd]         = SYMBOLIC;
    reg_mintervals_los[rd][0] = registers[rd];
    reg_mintervals_ups[rd][0] = registers[rd];
    reg_bvts[rd]              = boolector_null;
    set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

    if (reg_corr_validity[rs1] == 0) {
      set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] + imm, 0);
      reg_asts[rd] = reg_asts[rs1];
    } else {
      set_correction(rd, 0, 0, 1);
      value_v[0] = imm; crt_ptr = add_ast_node(CONST, 0, 0, value_v, value_v, 0, zero_v, boolector_null, CONCRETE);
      reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], crt_ptr, reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
    }

  } else {
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_involved_inputs_cnts[rd] = 0;
    reg_bvts[rd]                 = boolector_null;
    reg_asts[rd]                 = 0;

    set_correction(rd, 0, 0, 0);
  }
}

bool bvt_engine::apply_add_pointer() {
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
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);

    return 1;
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs2][0];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);

    return 1;
  }

  return 0;
}

void bvt_engine::apply_add() {
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

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];
        reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        uint64_t addend = reg_mintervals_los[rs2][0];
        reg_symb_type[rd] = SYMBOLIC;

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];

        if (reg_corr_validity[rs1] == 0) {
          set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] + addend, 0);
          reg_asts[rd] = reg_asts[rs1];
        } else {
          set_correction(rd, 0, 0, 1);
          reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
        }
      }

    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      uint64_t addend = reg_mintervals_los[rs1][0];
      reg_symb_type[rd] = SYMBOLIC;

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];

      if (reg_corr_validity[rs2] == 0) {
        set_correction(rd, reg_hasmn[rs2], reg_addsub_corr[rs2] + addend, 0);
        reg_asts[rd] = reg_asts[rs2];
      } else {
        set_correction(rd, 0, 0, 1);
        reg_asts[rd] = add_ast_node(ADD, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
      }

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

bool bvt_engine::apply_sub_pointer() {
  if (reg_data_type[rs1] == POINTER_T) {
    if (reg_data_type[rs2] == POINTER_T) {
      if (reg_mintervals_los[rs1][0] == reg_mintervals_los[rs2][0])
        if (reg_mintervals_ups[rs1][0] == reg_mintervals_ups[rs2][0]) {
          reg_data_type[rd]            = POINTER_T;
          reg_symb_type[rd]            = CONCRETE;
          reg_mintervals_los[rd][0]    = registers[rd];
          reg_mintervals_ups[rd][0]    = registers[rd];
          reg_involved_inputs_cnts[rd] = 0;
          reg_asts[rd]                 = 0;
          reg_bvts[rd]                 = boolector_null;

          set_correction(rd, 0, 0, 0);

          return 1;
        }

      // subtracting incompatible pointers
      std::cout << exe_name << ": sub invalid address at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      throw_exception(EXCEPTION_INVALIDADDRESS, 0);

      return 1;
    } else {
      reg_data_type[rd]            = POINTER_T;
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = reg_mintervals_los[rs1][0];
      reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs1][0];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;
      reg_bvts[rd]                 = boolector_null;

      set_correction(rd, 0, 0, 0);

      return 1;
    }
  } else if (reg_data_type[rs2] == POINTER_T) {
    reg_data_type[rd]            = POINTER_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = reg_mintervals_los[rs2][0];
    reg_mintervals_ups[rd][0]    = reg_mintervals_ups[rs2][0];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);

    return 1;
  }

  return 0;
}

void bvt_engine::apply_sub() {
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

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];
        reg_asts[rd]              = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        uint64_t subend = reg_mintervals_los[rs2][0];
        reg_symb_type[rd] = SYMBOLIC;

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];

        if (reg_corr_validity[rs1] == 0) {
          set_correction(rd, reg_hasmn[rs1], reg_addsub_corr[rs1] - subend, 0);
          reg_asts[rd] = reg_asts[rs1];
        } else {
          set_correction(rd, 0, 0, 1);
          reg_asts[rd] = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
        }
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      uint64_t subend = reg_mintervals_los[rs1][0];
      reg_symb_type[rd] = SYMBOLIC;

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];

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
        reg_asts[rd] = add_ast_node(SUB, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
      }

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void bvt_engine::apply_mul() {
  do_mul();

  if (rd != REG_ZR) {
    reg_data_type[rd] = VALUE_T;

    reg_bvts[rd] = boolector_null;

    // interval semantics of mul
    if (reg_symb_type[rs1] == SYMBOLIC) {
      if (reg_symb_type[rs2] == SYMBOLIC) {
        // non-linear expressions are not supported
        std::cout << exe_name << ": detected non-linear expression in mul at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);

      } else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        reg_symb_type[rd] = SYMBOLIC;

        evaluate_correction(rs1);
        if (reg_asts[rs2] == 0) { create_ast_node_entry_for_concrete_operand(rs2); }
        set_correction(rd, 0, 0, 1);

        set_involved_inputs(rd, reg_involved_inputs[rs1], reg_involved_inputs_cnts[rs1]);

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];

        reg_asts[rd] = add_ast_node(MUL, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
      }

    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton
      reg_symb_type[rd] = SYMBOLIC;

      evaluate_correction(rs2);
      if (reg_asts[rs1] == 0) { create_ast_node_entry_for_concrete_operand(rs1); }
      set_correction(rd, 0, 0, 1);

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];

      reg_asts[rd] = add_ast_node(MUL, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void bvt_engine::apply_divu() {
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

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];
        reg_asts[rd] = add_ast_node(DIVU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton
      reg_symb_type[rd] = SYMBOLIC;

      evaluate_correction(rs2);
      if (reg_asts[rs1] == 0) { create_ast_node_entry_for_concrete_operand(rs1); }
      set_correction(rd, 0, 0, 1);

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];
      reg_asts[rd] = add_ast_node(DIVU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void bvt_engine::apply_remu() {
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

        reg_mintervals_los[rd][0] = registers[rd];
        reg_mintervals_ups[rd][0] = registers[rd];
        reg_asts[rd] = add_ast_node(REMU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);
      }
    } else if (reg_symb_type[rs2] == SYMBOLIC) {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton
      reg_symb_type[rd] = SYMBOLIC;

      evaluate_correction(rs2);
      if (reg_asts[rs1] == 0) { create_ast_node_entry_for_concrete_operand(rs1); }
      set_correction(rd, 0, 0, 1);

      set_involved_inputs(rd, reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs2]);

      reg_mintervals_los[rd][0] = registers[rd];
      reg_mintervals_ups[rd][0] = registers[rd];
      reg_asts[rd] = add_ast_node(REMU, reg_asts[rs1], reg_asts[rs2], reg_mintervals_los[rd], reg_mintervals_ups[rd], reg_involved_inputs_cnts[rd], reg_involved_inputs[rd], reg_bvts[rd], SYMBOLIC);

    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = 0;

      set_correction(rd, 0, 0, 0);
    }
  }
}

void bvt_engine::apply_sltu() {
  if (backtrack) { backtrack_sltu(); return; }

  if (rd != REG_ZR) {
    if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
      // concrete semantics of sltu
      registers[rd] = (registers[rs1] < registers[rs2]) ? 1 : 0;

      reg_data_type[rd]            = VALUE_T;
      reg_symb_type[rd]            = CONCRETE;
      reg_mintervals_los[rd][0]    = registers[rd];
      reg_mintervals_ups[rd][0]    = registers[rd];
      reg_involved_inputs_cnts[rd] = 0;
      reg_asts[rd]                 = (registers[rd] == 0) ? zero_node : one_node;
      reg_bvts[rd]                 = (registers[rd] == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];

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
        create_sltu_constraints();
      } else
        std::cout << exe_name << ": detected a pointer variable in comparison! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    } else
      std::cout << exe_name << ": detected a pointer variable in comparison! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_sltu = ic_sltu + 1;
}

void bvt_engine::apply_xor() {
  if (backtrack) { backtrack_sltu(); return; }

  if (rd == REG_ZR)
    return;

  if (reg_symb_type[rs1] != SYMBOLIC && reg_symb_type[rs2] != SYMBOLIC) {
    // concrete semantics of xor
    registers[rd] = registers[rs1] ^ registers[rs2];

    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = (registers[rd] == 0) ? zero_node : one_node;
    reg_bvts[rd]                 = (registers[rd] == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];

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
      create_xor_constraints();
    } else
      std::cout << exe_name << ": detected a pointer variable in comparison! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
  } else
    std::cout << exe_name << ": detected a pointer variable in comparison! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;

  pc = pc + INSTRUCTIONSIZE;
  ic_xor = ic_xor + 1;

}

uint64_t bvt_engine::check_memory_vaddr_whether_represents_most_recent_constraint(uint64_t mrvc) {
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

uint64_t bvt_engine::apply_ld() {
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

        reg_data_type[rd]       = data_types[mrvc];
        registers[rd]           = values[mrvc];
        reg_asts[rd]            = asts[mrvc];
        reg_bvts[rd]            = smt_exprs[reg_asts[rd]];
        reg_symb_type[rd]       = symb_types[reg_asts[rd]];

        reg_mintervals_los[rd][0] = mintervals_los[reg_asts[rd]][0];
        reg_mintervals_ups[rd][0] = mintervals_ups[reg_asts[rd]][0];

        if (mintervals_los[reg_asts[rd]].size() > 1) {
          std::cout << exe_name << ": size is (> 1) \n";
        }

        // assert: vaddr == *(vaddrs + mrvc)

        if (reg_symb_type[rd] == SYMBOLIC) {
          reg_involved_inputs_cnts[rd] = involved_sym_inputs_cnts[reg_asts[rd]];
          for (size_t i = 0; i < reg_involved_inputs_cnts[rd]; i++) {
            reg_involved_inputs[rd][i] = involved_sym_inputs_ast_tcs[reg_asts[rd]][i];
          }
        } else {
          reg_involved_inputs_cnts[rd] = 0;
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
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
  }

  return vaddr;
}

uint64_t bvt_engine::apply_sd() {
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
        reg_asts[rs2] = add_ast_node(CONST, 0, 0, reg_mintervals_los[rs2], reg_mintervals_ups[rs2], 0, zero_v, boolector_null, CONCRETE);
      } else if (reg_asts[rs2] == 0 && reg_symb_type[rs2] == SYMBOLIC) {
        std::cout << exe_name << ": detected symbolic value with reg_asts = 0 in sd operation at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
        exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      store_symbolic_memory(pt, vaddr, registers[rs2], reg_data_type[rs2], reg_asts[rs2], mrcc, 1, reg_symb_type[rs2]);

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

void bvt_engine::apply_jal() {
  do_jal();

  if (rd != REG_ZR) {
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);
  }
}

void bvt_engine::apply_jalr() {
  do_jalr();

  if (rd != REG_ZR) {
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    reg_mintervals_los[rd][0]    = registers[rd];
    reg_mintervals_ups[rd][0]    = registers[rd];
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = 0;
    reg_bvts[rd]                 = boolector_null;

    set_correction(rd, 0, 0, 0);
  }
}

void bvt_engine::apply_ecall() {
  if (backtrack) { backtrack_ecall(); return; }

  do_ecall();
}

// -----------------------------------------------------------------------------
// ----------------------------- backtracking ----------------------------------
// -----------------------------------------------------------------------------

void bvt_engine::backtrack_sltu() {
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
      reg_involved_inputs_cnts[vaddr] = 0;
      reg_asts[vaddr]                 = 0;
      reg_bvts[vaddr]                 = boolector_null;

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

          boolector_pop(btor, 1);
          boolector_assert(btor, bvt_false_branches[tc]);
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

void bvt_engine::backtrack_sd() {
  if (asts[tc] != 0) {
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

void bvt_engine::backtrack_ld() {
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

void bvt_engine::backtrack_ecall() {
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

void bvt_engine::backtrack_trace(uint64_t* context) {
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

uint64_t bvt_engine::is_safe_address(uint64_t vaddr, uint64_t reg) {
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

uint64_t bvt_engine::load_symbolic_memory(uint64_t* pt, uint64_t vaddr) {
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

uint64_t bvt_engine::is_trace_space_available() {
  return tc + 1 < MAX_TRACE_LENGTH;
}

uint64_t bvt_engine::get_current_tc() {
  return tc;
}

void bvt_engine::ealloc() {
  tc = tc + 1;
}

void bvt_engine::efree() {
  // assert: tc > 0
  tc = tc - 1;
}

void bvt_engine::store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint8_t data_type, uint64_t ast_ptr, uint64_t trb, uint64_t is_store, uint8_t symbolic_type) {
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

void bvt_engine::store_register_memory(uint64_t reg, std::vector<uint64_t>& value) {
  // always track register memory by using tc as most recent branch
  store_symbolic_memory(pt, reg, value[0], VALUE_T, 0, tc, 1, CONCRETE);
}

void bvt_engine::store_input_record(uint64_t ast_ptr, uint64_t prev_input_record, uint8_t symbolic_type) {
  store_symbolic_memory(pt, NUMBEROFREGISTERS, prev_input_record, INPUT_T, ast_ptr, tc, 0, symbolic_type);
}

// -----------------------------------------------------------------------------
// ------------------------ reasoning/decision core ----------------------------
// -----------------------------------------------------------------------------

uint64_t bvt_engine::add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs, BoolectorNode* smt_expr, uint8_t symbolic_type) {
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

  ast_nodes[ast_trace_cnt].type       = typ;
  ast_nodes[ast_trace_cnt].left_node  = left_node;
  ast_nodes[ast_trace_cnt].right_node = right_node;
  store_trace_ptrs[ast_trace_cnt].clear();

  mintervals_los[ast_trace_cnt].clear();
  mintervals_ups[ast_trace_cnt].clear();
  mintervals_los[ast_trace_cnt].push_back(lo[0]);
  mintervals_ups[ast_trace_cnt].push_back(up[0]);

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

  smt_exprs[ast_trace_cnt]  = smt_expr;
  symb_types[ast_trace_cnt] = symbolic_type;

  return ast_trace_cnt;
}

void bvt_engine::set_involved_inputs(uint64_t reg, std::vector<uint64_t>& involved_inputs, size_t in_num) {
  reg_involved_inputs_cnts[reg] = in_num;
  for (size_t i = 0; i < in_num; i++) {
    reg_involved_inputs[reg][i] = involved_inputs[i];
  }
}

void bvt_engine::set_involved_inputs_two_symbolic_operands() {
  merge_arrays(reg_involved_inputs[rs1], reg_involved_inputs[rs2], reg_involved_inputs_cnts[rs1], reg_involved_inputs_cnts[rs2]);
  for (size_t i = 0; i < merged_array.size(); i++) {
    reg_involved_inputs[rd][i] = merged_array[i];
  }
  reg_involved_inputs_cnts[rd] = merged_array.size();
}

void bvt_engine::take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0) {
    value_v[0] = b;                 // record that we need to set rd to true
    store_register_memory(rd, value_v);
    value_v[0] = registers[REG_FP]; // record frame and stack pointer
    store_register_memory(REG_FP, value_v);
    value_v[0] = registers[REG_SP];
    store_register_memory(REG_SP, value_v);
  } else {
    reg_data_type[rd]            = VALUE_T;
    reg_symb_type[rd]            = CONCRETE;
    registers[rd]                = b;
    reg_mintervals_los[rd][0]    = b;
    reg_mintervals_ups[rd][0]    = b;
    reg_involved_inputs_cnts[rd] = 0;
    reg_asts[rd]                 = (b == 0) ? zero_node : one_node;
    reg_bvts[rd]                 = (b == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];

    set_correction(rd, 0, 0, 0);
  }
}

uint8_t bvt_engine::detect_symbolic_operand(uint64_t ast_tc) {
  uint8_t left_typ  = symb_types[ast_nodes[ast_tc].left_node];
  uint8_t right_typ = symb_types[ast_nodes[ast_tc].right_node];

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

void bvt_engine::create_sltu_constraints() {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;

  cannot_handle = true;

  if (cannot_handle) {
    check_operands_smt_expressions();

    true_reachable  = check_sat_true_branch_bvt(boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
    if (true_reachable == false) {
      false_reachable = true;
      does_path_need_to_be_reasoned_by_smt = true;
      sltu_instruction = pc; // this is because I need to change pc of the trace entry when dump inputs at end-point (don't want to be exit syscall)
    } else {
      false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
      does_path_need_to_be_reasoned_by_smt = false;
    }

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
}

void bvt_engine::create_xor_constraints() {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;

  cannot_handle = true;

  if (cannot_handle) {
    check_operands_smt_expressions();

    true_reachable  = check_sat_true_branch_bvt(boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
    if (true_reachable == false) {
      false_reachable = true;
      does_path_need_to_be_reasoned_by_smt = true;
      sltu_instruction = pc; // this is because I need to change pc of the trace entry when dump inputs at end-point (don't want to be exit syscall)
    } else {
      false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
      does_path_need_to_be_reasoned_by_smt = false;
    }

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
}

bool bvt_engine::check_sat_true_branch_bvt(BoolectorNode* assert) {
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
  }
  boolector_pop(btor, 1);

  return result;
}

bool bvt_engine::check_sat_false_branch_bvt(BoolectorNode* assert) {
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
  }
  boolector_pop(btor, 1);

  return result;
}

void bvt_engine::dump_involving_input_variables_true_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  involved_inputs_in_current_conditional_expression_rs1_operand.clear();
  if (reg_symb_type[rs1] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs1]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs1]][i];
      involved_inputs_in_current_conditional_expression_rs1_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      value_v[0] = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input_ast_tc], SYMBOLIC);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), SYMBOLIC);
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
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input_ast_tc], SYMBOLIC);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), SYMBOLIC);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }
}

void bvt_engine::dump_involving_input_variables_false_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  involved_inputs_in_current_conditional_expression_rs1_operand.clear();
  if (reg_symb_type[rs1] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs1]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs1]][i];
      involved_inputs_in_current_conditional_expression_rs1_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      value_v[0] = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input_ast_tc], SYMBOLIC);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), SYMBOLIC);
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
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input_ast_tc], SYMBOLIC);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), SYMBOLIC);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }
}

void bvt_engine::dump_all_input_variables_on_trace_true_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  for (size_t i = 0; i < input_table.size(); i++) {
    if (vector_contains_element(involved_inputs_in_current_conditional_expression_rs1_operand, i) ||
        vector_contains_element(involved_inputs_in_current_conditional_expression_rs2_operand, i) ) continue;
    involved_input_ast_tc = input_table_ast_tcs_before_branch_evaluation[i];
    value_v[0] = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input_ast_tc], SYMBOLIC);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), SYMBOLIC);
    }
    input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
  }

}

void bvt_engine::dump_all_input_variables_on_trace_false_branch_bvt() {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  for (size_t i = 0; i < input_table.size(); i++) {
    if (vector_contains_element(involved_inputs_in_current_conditional_expression_rs1_operand, i) ||
        vector_contains_element(involved_inputs_in_current_conditional_expression_rs2_operand, i) ) continue;
    involved_input_ast_tc = input_table_ast_tcs_before_branch_evaluation[i];
    value_v[0] = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input_ast_tc], SYMBOLIC);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), SYMBOLIC);
    }
    input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
  }
}

// --------------------------- conditional expression --------------------------

bool bvt_engine::match_addi_instruction() {
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

bool bvt_engine::match_sub_instruction(uint64_t prev_instr_rd) {
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

uint8_t bvt_engine::check_conditional_type_whether_is_equality_or_disequality() {
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
    std::cout << exe_name << ": XOR instruction is incorrectly used! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  return 0;
}

uint8_t bvt_engine::check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq() {
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

BoolectorNode* bvt_engine::boolector_op(uint8_t op, uint64_t ast_tc) {
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

BoolectorNode* bvt_engine::create_smt_expression(uint64_t ast_tc) {
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

void bvt_engine::check_operands_smt_expressions() {
  reg_bvts[rs1] = create_smt_expression(reg_asts[rs1]);
  reg_bvts[rs2] = create_smt_expression(reg_asts[rs2]);
}

// -----------------------------------------------------------------------------
// ----------------------- on-demand propagation on ld -------------------------
// -----------------------------------------------------------------------------

uint64_t bvt_engine::compute_add(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t ast_ptr;
  uint64_t stored_to_tc, mr_stored_to_tc;

  // the result is of either BVT or ABVT
  // thus the value interval for the result contain *one* witness.

  uint64_t resulting_witness = mintervals_los[left_operand_ast_tc][0] + mintervals_los[right_operand_ast_tc][0];
  propagated_minterval_lo[0] = resulting_witness;
  propagated_minterval_up[0] = resulting_witness;

  merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

  ast_ptr = add_ast_node(ADD, left_operand_ast_tc, right_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, merged_array.size(), merged_array, smt_exprs[old_ast_tc], SYMBOLIC);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
  }

  return ast_ptr;
}

uint64_t bvt_engine::compute_sub(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t ast_ptr;
  uint64_t stored_to_tc, mr_stored_to_tc;

  // the result is of either BVT or ABVT
  // thus the value interval for the result contain *one* witness.

  uint64_t resulting_witness = mintervals_los[left_operand_ast_tc][0] - mintervals_los[right_operand_ast_tc][0];
  propagated_minterval_lo[0] = resulting_witness;
  propagated_minterval_up[0] = resulting_witness;

  merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

  ast_ptr = add_ast_node(SUB, left_operand_ast_tc, right_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, merged_array.size(), merged_array, smt_exprs[old_ast_tc], SYMBOLIC);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
  }

  return ast_ptr;
}

uint64_t bvt_engine::compute_mul(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  bool cnd;
  uint64_t multiplier;
  uint64_t stored_to_tc, mr_stored_to_tc;

  if (symbolic_operands == BOTH) {
    // BOTH
    // non-linear arithmetic is not supported
    std::cout << exe_name << ": detected a non-linear mul in compute_mul!!! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  uint64_t resulting_witness = mintervals_los[left_operand_ast_tc][0] * mintervals_los[right_operand_ast_tc][0];
  propagated_minterval_lo[0] = resulting_witness;
  propagated_minterval_up[0] = resulting_witness;

  merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

  uint64_t ast_ptr = add_ast_node(MUL, left_operand_ast_tc, right_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, merged_array.size(), merged_array, smt_exprs[old_ast_tc], SYMBOLIC);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
  }

  return ast_ptr;
}

uint64_t bvt_engine::compute_divu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t dividend;
  uint64_t divisor;
  uint64_t stored_to_tc, mr_stored_to_tc;

  // assert: symbolic division is always covered by BVT
  // therefore intervals contain a witness or nothing
  if (theory_type < BVT)
    std::cout << exe_name << ": detected an error in compute_divu at 0x" << std::hex << pc - entry_point << std::dec << std::endl;

  if (symbolic_operands == BOTH) {
    // BOTH
    // non-linear arithmetic is not supported
    std::cout << exe_name << ": detected a non-linear divu in compute_divu!!! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  dividend = mintervals_los[left_operand_ast_tc][0];
  divisor  = mintervals_los[right_operand_ast_tc][0];
  if (divisor == 0) throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
  uint64_t resulting_witness = dividend / divisor;
  propagated_minterval_lo[0] = resulting_witness;
  propagated_minterval_up[0] = resulting_witness;

  merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

  uint64_t ast_ptr = add_ast_node(DIVU, left_operand_ast_tc, right_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, merged_array.size(), merged_array, smt_exprs[old_ast_tc], SYMBOLIC);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
  }

  return ast_ptr;
}

uint64_t bvt_engine::compute_remu(uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
  uint64_t remaindend;
  uint64_t divisor;
  uint64_t stored_to_tc, mr_stored_to_tc;

  // assert: symbolic remainder is always covered by BVT
  // therefore intervals contain a witness
  if (theory_type < BVT)
    std::cout << exe_name << ": detected an error in compute_remu at 0x" << std::hex << pc - entry_point << std::dec << std::endl;

  if (symbolic_operands == BOTH) {
    // BOTH
    // non-linear arithmetic is not supported
    std::cout << exe_name << ": detected a non-linear remu in compute_remu!!! at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  remaindend = mintervals_los[left_operand_ast_tc][0];
  divisor    = mintervals_los[right_operand_ast_tc][0];
  if (divisor == 0) throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
  uint64_t resulting_witness = remaindend % divisor;
  propagated_minterval_lo[0] = resulting_witness;
  propagated_minterval_up[0] = resulting_witness;

  merge_arrays(involved_sym_inputs_ast_tcs[left_operand_ast_tc], involved_sym_inputs_ast_tcs[right_operand_ast_tc], involved_sym_inputs_cnts[left_operand_ast_tc], involved_sym_inputs_cnts[right_operand_ast_tc]);

  uint64_t ast_ptr = add_ast_node(REMU, left_operand_ast_tc, right_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, merged_array.size(), merged_array, smt_exprs[old_ast_tc], SYMBOLIC);

  for (size_t i = 0; i < store_trace_ptrs[old_ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[old_ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc)
      store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC);
  }

  return ast_ptr;
}

uint64_t bvt_engine::recompute_operation(uint8_t op, uint64_t left_operand_ast_tc, uint64_t right_operand_ast_tc, uint64_t old_ast_tc, uint8_t theory_type, uint8_t symbolic_operands) {
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

uint64_t bvt_engine::update_current_constraint_on_ast_expression(uint64_t ast_tc) {
  uint64_t left_operand_ast_tc;
  uint64_t right_operand_ast_tc;
  uint64_t ast_ptr;
  uint8_t  symbolic_operands;
  uint8_t  theory_type = BVT;

  if (ast_nodes[ast_tc].type == VAR)
    return input_table[ast_nodes[ast_tc].right_node];

  // operation which both operands are symbolic will be detected by detect_symbolic_operand function
  symbolic_operands = detect_symbolic_operand(ast_tc);
  if (symbolic_operands == LEFT) {
    left_operand_ast_tc  = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].left_node);
    right_operand_ast_tc = ast_nodes[ast_tc].right_node;
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc, theory_type, symbolic_operands);
  } else if (symbolic_operands == RIGHT) {
    right_operand_ast_tc = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].right_node);
    left_operand_ast_tc  = ast_nodes[ast_tc].left_node;
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc, theory_type, symbolic_operands);
  } else {
    left_operand_ast_tc  = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].left_node);
    right_operand_ast_tc = update_current_constraint_on_ast_expression(ast_nodes[ast_tc].right_node);
    return recompute_operation(ast_nodes[ast_tc].type, left_operand_ast_tc, right_operand_ast_tc, ast_tc, theory_type, symbolic_operands);
  }
}

void bvt_engine::refine_abvt_abstraction_by_dumping_all_input_variables_on_trace_bvt() {
  uint64_t ast_ptr, involved_input, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  input_assignments.clear();
  for (size_t i = 0; i < input_table.size(); i++) {
    input_assignments.push_back(boolector_bv_assignment(btor, smt_exprs[asts[input_table_store_trace_ptr[i]]] ) );
  }

  for (size_t i = 0; i < input_table.size(); i++) {
    involved_input = input_table[i];
    is_assigned = false;
    value_v[0] = std::stoull(input_assignments[ast_nodes[involved_input].right_node], 0, 2);
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input].right_node, value_v, value_v, 0, zero_v, smt_exprs[involved_input], SYMBOLIC);
    for (size_t k = 0; k < store_trace_ptrs[involved_input].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, SYMBOLIC); pcs[tc] = sltu_instruction; // careful
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input].right_node), SYMBOLIC); pcs[tc] = sltu_instruction; // careful
    }
    input_table.at(ast_nodes[involved_input].right_node) = ast_ptr;
  }
}