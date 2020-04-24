#include "mit_box_bvt_engine.hpp"

// ------------------------------ INITIALIZATION -------------------------------

void mit_box_bvt_engine::init_engine(uint64_t peek_argument) {
  // AST nodes trace
  boxes    = (uint64_t*) malloc(MAX_AST_NODES_TRACE_LENGTH  * sizeof(uint64_t));
  boxes[0] = 0;

  mit_bvt_engine::init_engine(peek_argument);
}

void mit_box_bvt_engine::witness_profile() {
  int64_t  cardinality;
  uint64_t current_number_of_witnesses = 1;

  for (size_t i = 0; i < input_table.size(); i++) {
    cardinality = 0;
    for (size_t j = 0; j < mintervals_los[input_table[i]].size(); j++) {
      cardinality += (mintervals_ups[input_table[i]][j] - mintervals_los[input_table[i]][j] + 1) / steps[input_table[i]];
      if (theory_type_ast_nodes[input_table[i]] == BOX) break;
    }

    if (cardinality > 0)
      current_number_of_witnesses *= cardinality;
    else
      std::cout << exe_name << ": cardinality of an input is <= zero! " << std::endl;
  }

  if (current_number_of_witnesses > max_number_of_generated_witnesses_among_all_paths)
    max_number_of_generated_witnesses_among_all_paths = current_number_of_witnesses;

  total_number_of_generated_witnesses_for_all_paths += current_number_of_witnesses;
}

void print_execution_info(uint64_t paths, uint64_t total_number_of_generated_witnesses_for_all_paths, uint64_t max_number_of_generated_witnesses_among_all_paths, uint64_t queries_reasoned_by_mit, uint64_t queries_reasoned_by_box, uint64_t queries_reasoned_by_bvt) {
  std::cout << "\n\n";
  std::cout << YELLOW "number of explored paths:= " << paths << RESET << std::endl;
  std::cout << CYAN "number of witnesses:= total: " << total_number_of_generated_witnesses_for_all_paths << ", max: " << max_number_of_generated_witnesses_among_all_paths << RESET << std::endl;
  std::cout << GREEN "number of queries:= mit: " << queries_reasoned_by_mit << ", box: " << queries_reasoned_by_box << ", bvt: " << queries_reasoned_by_bvt << RESET << "\n\n";
}

uint64_t mit_box_bvt_engine::run_engine(uint64_t* to_context) {
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

      witness_profile();

      backtrack_trace(current_context);

      if (paths == 0) std::cout << exe_name << ": backtracking \n"; else unprint_integer(paths);
      paths++;
      print_integer(paths);

      if (pc == 0) {
        print_execution_info(paths, total_number_of_generated_witnesses_for_all_paths, max_number_of_generated_witnesses_among_all_paths, queries_reasoned_by_mit, queries_reasoned_by_box, queries_reasoned_by_bvt);

        if (symbolic_input_cnt != 0)
          std::cout << "symbolic_input_cnt is not zero!\n";

        if (IS_TEST_MODE)
          output_results.close();

        return EXITCODE_NOERROR;
      }
    }
  }
}

// -----------------------------------------------------------------------------
// ------------------------ reasoning/decision core ----------------------------
// -----------------------------------------------------------------------------

uint64_t mit_box_bvt_engine::add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, uint32_t mints_num, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t step, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs, uint8_t theory_type, BoolectorNode* smt_expr) {
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
    std::cout << exe_name << ": maximum number of possible intervals for a variable is reached at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
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

  boxes[ast_trace_cnt] = 0;

  return ast_trace_cnt;
}

void mit_box_bvt_engine::create_sltu_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
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

  if (reg_theory_types[rs1] > MIT || reg_theory_types[rs2] > MIT) {
    cannot_handle = true;
  } else {
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

    if (apply_sltu_under_approximate_box_decision_procedure(lo1_p, up1_p, lo2_p, up2_p))
      return;

    assert_path_condition_into_smt_expression();
    check_operands_smt_expressions();
    false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
    true_reachable  = check_sat_true_branch_bvt (boolector_ult (btor, reg_bvts[rs1], reg_bvts[rs2]));

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

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq() == LGTE) {
        constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(1, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // important place be careful

        path_condition.push_back(add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(0, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // careful

        path_condition.push_back(add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
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

void mit_box_bvt_engine::create_xor_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
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

  if (reg_theory_types[rs1] > MIT || reg_theory_types[rs2] > MIT) {
    cannot_handle = true;
  } else {
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

    if (apply_diseq_under_approximate_box_decision_procedure(lo1_p, up1_p, lo2_p, up2_p))
      return;

    // xor result:
    assert_path_condition_into_smt_expression();
    check_operands_smt_expressions();
    false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
    true_reachable  = check_sat_true_branch_bvt (boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));

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

  if (true_reachable) {
    if (false_reachable) {
      if (check_conditional_type_whether_is_equality_or_disequality() == EQ) {
        constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
        uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(1, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // careful

        path_condition.push_back(add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        take_branch(0, 0);
      } else {
        constrain_memory_mit(rs1, false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups,false_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups,false_branch_rs2_minterval_cnt, trb, false);
        uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, MIT, boolector_null);
        take_branch(0, 1);
        asts[tc-2]               = false_ast_ptr;
        bvt_false_branches[tc-2] = boolector_null; // carful

        path_condition.push_back(add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, MIT, boolector_null));

        constrain_memory_mit(rs1, true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, true_branch_rs1_minterval_cnt, trb, false);
        constrain_memory_mit(rs2, true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, true_branch_rs2_minterval_cnt, trb, false);
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

// -----------------------------------------------------------------------------
// ------------------- under_approximate decision procedure --------------------
// -----------------------------------------------------------------------------

uint64_t mit_box_bvt_engine::constrain_memory_under_approximate_box(uint64_t reg, uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint64_t input_box) {
  if (reg_symb_type[reg] == SYMBOLIC) {
    backward_propagation_of_under_approximate_box(ast_tc, lo, up, mints_num, input_box);
  }
}

uint64_t mit_box_bvt_engine::backward_propagation_of_under_approximate_box(uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint64_t input_box) {
  uint8_t  left_or_right_is_sym;
  uint64_t ast_ptr;
  bool     is_assigned = false;
  uint64_t stored_to_tc, mr_stored_to_tc;

  //////////////////////////////////////////////////////////////
  // assert: the operand's interval cnt and also its step are 1;
  //////////////////////////////////////////////////////////////

  std::vector<uint64_t> saved_lo;
  std::vector<uint64_t> saved_up;
  for (size_t i = 0; i < mints_num; i++) {
    propagated_minterval_lo[i] = lo[i];
    propagated_minterval_up[i] = up[i];
    saved_lo.push_back(lo[i]);
    saved_up.push_back(up[i]);
  }

  if (ast_nodes[ast_tc].type == VAR) {
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[ast_tc].right_node, mints_num, propagated_minterval_lo, propagated_minterval_up, steps[ast_tc], 0, zero_v, BOX, smt_exprs[ast_tc]);
    boxes[ast_trace_cnt] = input_box; // careful

    for (size_t i = 0; i < store_trace_ptrs[ast_tc].size(); i++) {
      stored_to_tc    = store_trace_ptrs[ast_tc][i];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, BOX);
        is_assigned = true;
      }
    }

    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[ast_tc].right_node), BOX);
    }
    input_table.at(ast_nodes[ast_tc].right_node) = ast_ptr;

    return ast_ptr;
  }

  left_or_right_is_sym = detect_symbolic_operand(ast_tc);

  if (left_or_right_is_sym == BOTH) {
    std::cout << exe_name << ": both operands are symbolic in backward_propagation_of_under_approximate_box!!!\n";
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  switch (ast_nodes[ast_tc].type) {
    case ADD: {
      for (size_t i = 0; i < mints_num; i++) {
        propagated_minterval_lo[i] = propagated_minterval_lo[i] - mintervals_los[crt_operand_ast_tc][0];
        propagated_minterval_up[i] = propagated_minterval_up[i] - mintervals_los[crt_operand_ast_tc][0];
      }
      break;
    }
    case SUB: {
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
    case MUL: {
      std::cout << exe_name << ": inverse of mul in under_approximate decision procedure is unsupported at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
    case DIVU: {
      std::cout << exe_name << ": inverse of divu in under_approximate decision procedure is unsupported at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
    case REMU: {
      std::cout << exe_name << ": inverse of remu in under_approximate decision procedure is unsupported at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
    default: {
      std::cout << exe_name << ": detected an unknown operation in under_approximate decision procedure at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
      break;
    }
  }

  uint64_t sym_operand_ptr = backward_propagation_of_under_approximate_box(sym_operand_ast_tc, propagated_minterval_lo, propagated_minterval_up, mints_num, input_box);

  if (left_or_right_is_sym == LEFT)
    ast_ptr = add_ast_node(ast_nodes[ast_tc].type, sym_operand_ptr, ast_nodes[ast_tc].right_node, mints_num, saved_lo, saved_up, steps[ast_tc], involved_sym_inputs_cnts[sym_operand_ptr], involved_sym_inputs_ast_tcs[sym_operand_ptr], BOX, smt_exprs[ast_tc]);
  else
    ast_ptr = add_ast_node(ast_nodes[ast_tc].type, ast_nodes[ast_tc].left_node, sym_operand_ptr, mints_num, saved_lo, saved_up, steps[ast_tc], involved_sym_inputs_cnts[sym_operand_ptr], involved_sym_inputs_ast_tcs[sym_operand_ptr], BOX, smt_exprs[ast_tc]);

  boxes[ast_trace_cnt] = input_box; // careful

  for (size_t i = 0; i < store_trace_ptrs[ast_tc].size(); i++) {
    stored_to_tc    = store_trace_ptrs[ast_tc][i];
    mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
    mr_stored_to_tc = mr_sds[mr_stored_to_tc];
    if (mr_stored_to_tc <= stored_to_tc) {
      store_symbolic_memory(pt, vaddrs[stored_to_tc], saved_lo[0], VALUE_T, ast_ptr, tc, 0, BOX);
    }
  }

  return ast_ptr;
}

void mit_box_bvt_engine::evaluate_sltu_true_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  // std::cout << "-- evaluate_sltu_true_branch_under_approximate_box -- \n";

  // box1: . < priority
  if (lo1 >= lo2) {
    true_branch_rs1_minterval_los[0] = lo1;
    true_branch_rs1_minterval_ups[0] = lo1;
    true_branch_rs2_minterval_los[0] = lo1+1; // no problem
    true_branch_rs2_minterval_ups[0] = up2;

    // std::cout << "box1: [" << lo1 << ", " << lo1 << "]; [" << lo1+1 << ", " << up2 << "]\n";
  } else {
    true_branch_rs1_minterval_los[0] = lo1;
    true_branch_rs1_minterval_ups[0] = lo2-1; // no problem
    true_branch_rs2_minterval_los[0] = lo2;
    true_branch_rs2_minterval_ups[0] = up2;

    // std::cout << "box1: [" << lo1 << ", " << lo2-1 << "]; [" << lo2 << ", " << up2 << "]\n";
  }

  // box2: priority < .
  if (up2 <= up1) {
    true_branch_rs1_minterval_los[1] = lo1;
    true_branch_rs1_minterval_ups[1] = (up2-1 > lo1) ? up2-1 : lo1;
    true_branch_rs2_minterval_los[1] = up2;
    true_branch_rs2_minterval_ups[1] = up2;

    // std::cout << "box2: [" << lo1 << ", " << std::max(lo1, up2-1) << "]; [" << up2 << ", " << up2 << "]\n";
  } else {
    true_branch_rs1_minterval_los[1] = lo1;
    true_branch_rs1_minterval_ups[1] = up1;
    true_branch_rs2_minterval_los[1] = up2;
    true_branch_rs2_minterval_ups[1] = up2;

    // std::cout << "box2: [" << lo1 << ", " << up1 << "]; [" << up2 << ", " << up2 << "]\n";
  }

  constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 2, involved_sym_inputs_ast_tcs[reg_asts[rs2]][0]);
  constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 2, involved_sym_inputs_ast_tcs[reg_asts[rs1]][0]);
}

void mit_box_bvt_engine::evaluate_sltu_false_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  // std::cout << "-- evaluate_sltu_false_branch_under_approximate_box -- \n";

  // box1: priority >= .
  if (lo1 <= lo2) {
    false_branch_rs1_minterval_los[0] = lo2; // no problem
    false_branch_rs1_minterval_ups[0] = up1;
    false_branch_rs2_minterval_los[0] = lo2;
    false_branch_rs2_minterval_ups[0] = lo2;

    // std::cout << "box1: [" << lo2 << ", " << up1 << "]; [" << lo2 << ", " << lo2 << "]\n";
  } else {
    false_branch_rs1_minterval_los[0] = lo1;
    false_branch_rs1_minterval_ups[0] = up1;
    false_branch_rs2_minterval_los[0] = lo2;
    false_branch_rs2_minterval_ups[0] = lo1; // no problem

    // std::cout << "box1: [" << lo1 << ", " << up1 << "]; [" << lo2 << ", " << lo1 << "]\n";
  }

  // box2: . >= priority
  if (up2 >= up1) {
    false_branch_rs1_minterval_los[1] = up1;
    false_branch_rs1_minterval_ups[1] = up1;
    false_branch_rs2_minterval_los[1] = lo2;
    false_branch_rs2_minterval_ups[1] = up1; // no problem

    // std::cout << "box2: [" << up1 << ", " << up1 << "]; [" << lo2 << ", " << up1 << "]\n";
  } else {
    false_branch_rs1_minterval_los[1] = up1;
    false_branch_rs1_minterval_ups[1] = up1;
    false_branch_rs2_minterval_los[1] = lo2;
    false_branch_rs2_minterval_ups[1] = up2;

    // std::cout << "box2: [" << up1 << ", " << up1 << "]; [" << lo2 << ", " << up2 << "]\n";
  }

  constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 2, involved_sym_inputs_ast_tcs[reg_asts[rs2]][0]);
  constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 2, involved_sym_inputs_ast_tcs[reg_asts[rs1]][0]);
}

void mit_box_bvt_engine::choose_best_local_choice_between_boxes(size_t index_true_i, size_t index_true_j) {
  uint64_t ast_ptr, involved_input, related_input, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;

  if (reg_theory_types[rs1] == BOX && reg_mintervals_cnts[rs1] > 1) { // this means previous decision was our heuristic which picks several box choices
    involved_input = involved_sym_inputs_ast_tcs[reg_asts[rs1]][0];
    related_input  = boxes[input_table.at(ast_nodes[involved_input].right_node)];
    related_input  = input_table.at(ast_nodes[related_input].right_node);
    propagated_minterval_lo[0] = mintervals_los[related_input][index_true_i];
    propagated_minterval_up[0] = mintervals_ups[related_input][index_true_i];
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[related_input].right_node, 1, propagated_minterval_lo, propagated_minterval_up, 1, 0, zero_v, BOX, smt_exprs[related_input]);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[related_input].size(); k++) {
      stored_to_tc    = store_trace_ptrs[related_input][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, BOX);
        is_assigned = true;
      }
    }

    if (is_assigned == false) {
      store_input_record(ast_ptr, related_input, BOX);
    }
    input_table.at(ast_nodes[related_input].right_node) = ast_ptr;
  }

  if (reg_theory_types[rs2] == BOX && reg_mintervals_cnts[rs2] > 1) {
    involved_input = involved_sym_inputs_ast_tcs[reg_asts[rs2]][0];
    related_input = boxes[input_table.at(ast_nodes[involved_input].right_node)];
    related_input = input_table.at(ast_nodes[related_input].right_node);
    propagated_minterval_lo[0] = mintervals_los[related_input][index_true_j];
    propagated_minterval_up[0] = mintervals_ups[related_input][index_true_j];
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[related_input].right_node, 1, propagated_minterval_lo, propagated_minterval_up, 1, 0, zero_v, BOX, smt_exprs[related_input]);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[related_input].size(); k++) {
      stored_to_tc    = store_trace_ptrs[related_input][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], propagated_minterval_lo[0], VALUE_T, ast_ptr, tc, 0, BOX);
        is_assigned = true;
      }
    }

    if (is_assigned == false) {
      store_input_record(ast_ptr, related_input, BOX);
    }
    input_table.at(ast_nodes[related_input].right_node) = ast_ptr;
  }
}

bool mit_box_bvt_engine::apply_sltu_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2) {
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t ast_ptr, involved_input, stored_to_tc, mr_stored_to_tc;

  // exclude cases where box theory cannot be applied
  if (reg_theory_types[rs1] >= BVT || reg_theory_types[rs2] >= BVT) {
    return false;
  } else if ((reg_mintervals_cnts[rs1] > NUMBER_OF_HEURISTIC_UNDER_APPROX_BOXES) ||
             (reg_mintervals_cnts[rs2] > NUMBER_OF_HEURISTIC_UNDER_APPROX_BOXES)) {
    return false;
  } else if (reg_steps[rs1] > 1 || reg_steps[rs2] > 1) {
    return false;
  } else if ((reg_mintervals_cnts[rs1] > 1 && reg_theory_types[rs1] == MIT) || (reg_mintervals_cnts[rs2] > 1 && reg_theory_types[rs2] == MIT)) {
    return false;
  } else if (reg_involved_inputs_cnts[rs1] > 1 || reg_involved_inputs_cnts[rs2] > 1) {
    return false;
  }

  // must not be from same input variables: not related
  if (reg_involved_inputs_cnts[rs1]) {
    if (reg_involved_inputs_cnts[rs2]) {
      if (reg_involved_inputs[rs1][0] == reg_involved_inputs[rs2][0])
        return false;
    }
  }

  uint8_t conditional_type = check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq();

  if (reg_theory_types[rs1] == MIT && reg_theory_types[rs2] == MIT) {
    if (lo1[0] > up1[0] || lo2[0] > up2[0]) {
      // wrapped are not acceptable
      return false;
    }

    if (conditional_type == LGTE) {
      evaluate_sltu_true_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
      take_branch(1, 1);
      asts[tc-2]               = false_ast_ptr;
      bvt_false_branches[tc-2] = boolector_null; // careful

      path_condition.push_back(add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

      evaluate_sltu_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      take_branch(0, 0);
    } else {
      evaluate_sltu_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
      take_branch(0, 1);
      asts[tc-2]               = false_ast_ptr;
      bvt_false_branches[tc-2] = boolector_null; // careful

      path_condition.push_back(add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

      evaluate_sltu_true_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      take_branch(1, 0);
    }

    // will be (reg_mintervals_cnts[rs1] > 1 && reg_theory_types[rs1] == BOX)
    // will be (reg_mintervals_cnts[rs2] > 1 && reg_theory_types[rs2] == BOX)

    queries_reasoned_by_box+=2;
    return true;

  } else {
    bool cannot_handle = false;
    std::vector<uint64_t> box_true_case_rs1_lo;
    std::vector<uint64_t> box_true_case_rs1_up;
    std::vector<uint64_t> box_true_case_rs2_lo;
    std::vector<uint64_t> box_true_case_rs2_up;
    std::vector<uint64_t> box_false_case_rs1_lo;
    std::vector<uint64_t> box_false_case_rs1_up;
    std::vector<uint64_t> box_false_case_rs2_lo;
    std::vector<uint64_t> box_false_case_rs2_up;
    std::vector<uint64_t> box_index_true_i;
    std::vector<uint64_t> box_index_true_j;
    std::vector<uint64_t> box_index_false_i;
    std::vector<uint64_t> box_index_false_j;
    uint8_t branch = 0;

    if (reg_theory_types[rs1] == MIT || reg_theory_types[rs2] == MIT) {
      for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
        if (lo1[i] > up1[i]) {
          // wrapped are not acceptable
          return false;
        }
        for (size_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
          if (lo2[j] > up2[j]) {
            // wrapped are not acceptable
            return false;
          }

          true_branch_rs1_minterval_cnt  = 0;
          true_branch_rs2_minterval_cnt  = 0;
          false_branch_rs1_minterval_cnt = 0;
          false_branch_rs2_minterval_cnt = 0;
          branch = 0;

          cannot_handle = evaluate_sltu_true_false_branch_mit(lo1[i], up1[i], lo2[j], up2[j]);

          if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0) {
            branch++;
            box_true_case_rs1_lo.push_back(true_branch_rs1_minterval_los[0]);
            box_true_case_rs1_up.push_back(true_branch_rs1_minterval_ups[0]);
            box_true_case_rs2_lo.push_back(true_branch_rs2_minterval_los[0]);
            box_true_case_rs2_up.push_back(true_branch_rs2_minterval_ups[0]);
            box_index_true_i.push_back(i);
            box_index_true_j.push_back(j);
          }

          if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0) {
            branch++;
            box_false_case_rs1_lo.push_back(false_branch_rs1_minterval_los[0]);
            box_false_case_rs1_up.push_back(false_branch_rs1_minterval_ups[0]);
            box_false_case_rs2_lo.push_back(false_branch_rs2_minterval_los[0]);
            box_false_case_rs2_up.push_back(false_branch_rs2_minterval_ups[0]);
            box_index_false_i.push_back(i);
            box_index_false_j.push_back(j);
          }

          if (branch == 2) {
            true_reachable  = true;
            false_reachable = true;
            goto lab;
          }
        }
      }

      // means cannot be reasoned by boxes
      if (box_true_case_rs1_lo.size() == 0 && box_false_case_rs1_lo.size() == 0) return false;

    } else {
      // both are BOX
      // first box with first box, second box with second box => to be sure about correctness
      size_t i = 0;
      size_t j = 0;
      while (i < reg_mintervals_cnts[rs1] && j < reg_mintervals_cnts[rs2]) {
        if (lo1[i] > up1[i] || lo2[j] > up2[j]) {
          // wrapped are not acceptable
          return false;
        }

        true_branch_rs1_minterval_cnt  = 0;
        true_branch_rs2_minterval_cnt  = 0;
        false_branch_rs1_minterval_cnt = 0;
        false_branch_rs2_minterval_cnt = 0;
        branch = 0;

        cannot_handle = evaluate_sltu_true_false_branch_mit(lo1[i], up1[i], lo2[j], up2[j]);

        if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0) {
          branch++;
          box_true_case_rs1_lo.push_back(true_branch_rs1_minterval_los[0]);
          box_true_case_rs1_up.push_back(true_branch_rs1_minterval_ups[0]);
          box_true_case_rs2_lo.push_back(true_branch_rs2_minterval_los[0]);
          box_true_case_rs2_up.push_back(true_branch_rs2_minterval_ups[0]);
          box_index_true_i.push_back(i);
          box_index_true_j.push_back(j);
        }

        if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0) {
          branch++;
          box_false_case_rs1_lo.push_back(false_branch_rs1_minterval_los[0]);
          box_false_case_rs1_up.push_back(false_branch_rs1_minterval_ups[0]);
          box_false_case_rs2_lo.push_back(false_branch_rs2_minterval_los[0]);
          box_false_case_rs2_up.push_back(false_branch_rs2_minterval_ups[0]);
          box_index_false_i.push_back(i);
          box_index_false_j.push_back(j);
        }

        if (branch == 2) {
          true_reachable  = true;
          false_reachable = true;
          goto lab;
        }

        i++; j++;
      }

      // means cannot be reasoned by boxes
      if (box_true_case_rs1_lo.size() == 0 && box_false_case_rs1_lo.size() == 0) return false;
    }

    lab:
    if (true_reachable == false) { // means both are not reachable (box decision)
      if (box_true_case_rs1_lo.size() > 0) {
        // this is just to choose one box choice for the original operand var
        choose_best_local_choice_between_boxes(box_index_true_i[0], box_index_true_j[0]);

        true_reachable  = true;
        true_branch_rs1_minterval_los[0] = box_true_case_rs1_lo[0];
        true_branch_rs1_minterval_ups[0] = box_true_case_rs1_up[0];
        true_branch_rs2_minterval_los[0] = box_true_case_rs2_lo[0];
        true_branch_rs2_minterval_ups[0] = box_true_case_rs2_up[0];
      } else if (box_false_case_rs1_lo.size() > 0) {
        // this is just to choose one box choice for the original operand var
        choose_best_local_choice_between_boxes(box_index_false_i[0], box_index_false_j[0]);

        false_reachable = true;
        false_branch_rs1_minterval_los[0] = box_false_case_rs1_lo[0];
        false_branch_rs1_minterval_ups[0] = box_false_case_rs1_up[0];
        false_branch_rs2_minterval_los[0] = box_false_case_rs2_lo[0];
        false_branch_rs2_minterval_ups[0] = box_false_case_rs2_up[0];
      }
    } else {
      // this is just to choose one box choice for the original operand var
      choose_best_local_choice_between_boxes(box_index_true_i.back(), box_index_true_j.back());
      // don't need for false

      true_branch_rs1_minterval_los[0]  = box_true_case_rs1_lo.back();
      true_branch_rs1_minterval_ups[0]  = box_true_case_rs1_up.back();
      true_branch_rs2_minterval_los[0]  = box_true_case_rs2_lo.back();
      true_branch_rs2_minterval_ups[0]  = box_true_case_rs2_up.back();

      false_branch_rs1_minterval_los[0] = box_false_case_rs1_lo.back();
      false_branch_rs1_minterval_ups[0] = box_false_case_rs1_up.back();
      false_branch_rs2_minterval_los[0] = box_false_case_rs2_lo.back();
      false_branch_rs2_minterval_ups[0] = box_false_case_rs2_up.back();
    }

    if (true_reachable) {
      if (false_reachable) {
        if (conditional_type == LGTE) {
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
          uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
          take_branch(1, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_null; // careful

          path_condition.push_back(add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          take_branch(0, 0);
        } else {
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
          take_branch(0, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_null; // careful

          path_condition.push_back(add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
          take_branch(1, 0);
        }

        queries_reasoned_by_box+=2;
        return true;
      } else {
        // false query to smt
        assert_path_condition_into_smt_expression();
        check_operands_smt_expressions();
        false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));

        if (false_reachable) {
          if (conditional_type == LGTE) {
            // false
            constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
            constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
            uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BVT, boolector_null); // important should be BVT so that in backtrack_sltu it does boolector_pop
            take_branch(1, 1);
            asts[tc-2]               = false_ast_ptr;
            bvt_false_branches[tc-2] = boolector_null; // careful

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
            uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
            take_branch(0, 1);
            asts[tc-2]               = false_ast_ptr;
            bvt_false_branches[tc-2] = boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful

            path_condition.push_back(add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

            // important: if on true branch we need BVT in future it will apply boolector_push() later in assert_path_condition_into_smt_expression
            // so no worries

            // true under_approximate
            constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
            constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
            take_branch(1, 0);
          }
        } else {
          // true under_approximate
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
          take_branch(1, 0);
        }

        queries_reasoned_by_box++;
        return true;
      }
    } else if (false_reachable) {
      // true query to smt
      assert_path_condition_into_smt_expression();
      check_operands_smt_expressions();
      true_reachable = check_sat_true_branch_bvt(boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));

      if (true_reachable) {
        if (conditional_type == LGTE) {
          // false
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
          take_branch(1, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful

          path_condition.push_back(add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

          // important: if on true branch we need BVT in future it will apply boolector_push() later in assert_path_condition_into_smt_expression
          // so no worries

          // true
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          take_branch(0, 0);

        } else {
          // false under_approximate
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BVT, boolector_null); // important should be BVT so that in backtrack_sltu it does boolector_pop
          take_branch(0, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_null; // careful

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          take_branch(1, 0);
        }

      } else {
        // false under_approximate
        constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
        constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
        take_branch(0, 0);
      }

      queries_reasoned_by_box++;
      return true;
    } else {
      // cannot decide
      return false;
    }
  }
}

bool mit_box_bvt_engine::apply_diseq_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2) {
  bool true_reachable  = false;
  bool false_reachable = false;
  uint64_t ast_ptr, involved_input, stored_to_tc, mr_stored_to_tc;

  // exclude cases where box theory cannot be applied
  if (reg_theory_types[rs1] >= BVT || reg_theory_types[rs2] >= BVT) {
    return false;
  } else if ((reg_mintervals_cnts[rs1] > NUMBER_OF_HEURISTIC_UNDER_APPROX_BOXES) ||
             (reg_mintervals_cnts[rs2] > NUMBER_OF_HEURISTIC_UNDER_APPROX_BOXES)) {
    return false;
  } else if (reg_steps[rs1] > 1 || reg_steps[rs2] > 1) {
    return false;
  } else if ((reg_mintervals_cnts[rs1] > 1 && reg_theory_types[rs1] == MIT) || (reg_mintervals_cnts[rs2] > 1 && reg_theory_types[rs2] == MIT)) {
    return false;
  } else if (reg_involved_inputs_cnts[rs1] > 1 || reg_involved_inputs_cnts[rs2] > 1) {
    return false;
  }

  // must not be from same input variables: not related
  if (reg_involved_inputs_cnts[rs1]) {
    if (reg_involved_inputs_cnts[rs2]) {
      if (reg_involved_inputs[rs1][0] == reg_involved_inputs[rs2][0])
        return false;
    }
  }

  uint8_t conditional_type = check_conditional_type_whether_is_equality_or_disequality();

  if (reg_theory_types[rs1] == MIT && reg_theory_types[rs2] == MIT) {
    if (lo1[0] > up1[0] || lo2[0] > up2[0]) {
      // wrapped are not acceptable
      return false;
    }

    if (conditional_type == EQ) {
      evaluate_sltu_true_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
      take_branch(1, 1);
      asts[tc-2]               = false_ast_ptr;
      bvt_false_branches[tc-2] = boolector_null; // careful

      path_condition.push_back(add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

      evaluate_diseq_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      take_branch(0, 0);
    } else {
      evaluate_diseq_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
      take_branch(0, 1);
      asts[tc-2]               = false_ast_ptr;
      bvt_false_branches[tc-2] = boolector_null; // careful

      path_condition.push_back(add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

      evaluate_sltu_true_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      take_branch(1, 0);
    }

    queries_reasoned_by_box+=2;
    return true;

  } else {
    bool cannot_handle = false;
    std::vector<uint64_t> box_true_case_rs1_lo;
    std::vector<uint64_t> box_true_case_rs1_up;
    std::vector<uint64_t> box_true_case_rs2_lo;
    std::vector<uint64_t> box_true_case_rs2_up;
    std::vector<uint64_t> box_false_case_rs1_lo;
    std::vector<uint64_t> box_false_case_rs1_up;
    std::vector<uint64_t> box_false_case_rs2_lo;
    std::vector<uint64_t> box_false_case_rs2_up;
    std::vector<uint64_t> box_index_true_i;
    std::vector<uint64_t> box_index_true_j;
    std::vector<uint64_t> box_index_false_i;
    std::vector<uint64_t> box_index_false_j;
    uint8_t branch = 0;

    if (reg_theory_types[rs1] == MIT || reg_theory_types[rs2] == MIT) {
      for (size_t i = 0; i < reg_mintervals_cnts[rs1]; i++) {
        if (lo1[i] > up1[i]) {
          // wrapped are not acceptable
          return false;
        }
        for (size_t j = 0; j < reg_mintervals_cnts[rs2]; j++) {
          if (lo2[j] > up2[j]) {
            // wrapped are not acceptable
            return false;
          }

          true_branch_rs1_minterval_cnt  = 0;
          true_branch_rs2_minterval_cnt  = 0;
          false_branch_rs1_minterval_cnt = 0;
          false_branch_rs2_minterval_cnt = 0;
          branch = 0;

          cannot_handle = evaluate_xor_true_false_branch_mit(lo1[i], up1[i], lo2[j], up2[j]);

          if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0) {
            branch++;
            box_true_case_rs1_lo.push_back(true_branch_rs1_minterval_los[0]);
            box_true_case_rs1_up.push_back(true_branch_rs1_minterval_ups[0]);
            box_true_case_rs2_lo.push_back(true_branch_rs2_minterval_los[0]);
            box_true_case_rs2_up.push_back(true_branch_rs2_minterval_ups[0]);
            box_index_true_i.push_back(i);
            box_index_true_j.push_back(j);
          }

          if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0) {
            branch++;
            box_false_case_rs1_lo.push_back(false_branch_rs1_minterval_los[0]);
            box_false_case_rs1_up.push_back(false_branch_rs1_minterval_ups[0]);
            box_false_case_rs2_lo.push_back(false_branch_rs2_minterval_los[0]);
            box_false_case_rs2_up.push_back(false_branch_rs2_minterval_ups[0]);
            box_index_false_i.push_back(i);
            box_index_false_j.push_back(j);
          }

          if (branch == 2) {
            true_reachable  = true;
            false_reachable = true;
            goto lab;
          }
        }
      }

      // means cannot be reasoned by boxes
      if (box_true_case_rs1_lo.size() == 0 && box_false_case_rs1_lo.size() == 0) return false;

    } else {
      // both are BOX
      // first box with first box, second box with second box => to be sure about correctness
      size_t i = 0;
      size_t j = 0;
      while (i < reg_mintervals_cnts[rs1] && j < reg_mintervals_cnts[rs2]) {
        if (lo1[i] > up1[i] || lo2[j] > up2[j]) {
          // wrapped are not acceptable
          return false;
        }

        true_branch_rs1_minterval_cnt  = 0;
        true_branch_rs2_minterval_cnt  = 0;
        false_branch_rs1_minterval_cnt = 0;
        false_branch_rs2_minterval_cnt = 0;
        branch = 0;

        cannot_handle = evaluate_xor_true_false_branch_mit(lo1[i], up1[i], lo2[j], up2[j]);

        if (true_branch_rs1_minterval_cnt > 0 && true_branch_rs2_minterval_cnt > 0) {
          branch++;
          box_true_case_rs1_lo.push_back(true_branch_rs1_minterval_los[0]);
          box_true_case_rs1_up.push_back(true_branch_rs1_minterval_ups[0]);
          box_true_case_rs2_lo.push_back(true_branch_rs2_minterval_los[0]);
          box_true_case_rs2_up.push_back(true_branch_rs2_minterval_ups[0]);
          box_index_true_i.push_back(i);
          box_index_true_j.push_back(j);
        }

        if (false_branch_rs1_minterval_cnt > 0 && false_branch_rs2_minterval_cnt > 0) {
          branch++;
          box_false_case_rs1_lo.push_back(false_branch_rs1_minterval_los[0]);
          box_false_case_rs1_up.push_back(false_branch_rs1_minterval_ups[0]);
          box_false_case_rs2_lo.push_back(false_branch_rs2_minterval_los[0]);
          box_false_case_rs2_up.push_back(false_branch_rs2_minterval_ups[0]);
          box_index_false_i.push_back(i);
          box_index_false_j.push_back(j);
        }

        if (branch == 2) {
          true_reachable  = true;
          false_reachable = true;
          goto lab;
        }

        i++; j++;
      }

      // means cannot be reasoned by boxes
      if (box_true_case_rs1_lo.size() == 0 && box_false_case_rs1_lo.size() == 0) return false;
    }

    lab:
    if (true_reachable == false) { // means both are not reachable (box decision)
      if (box_true_case_rs1_lo.size() > 0) {
        // this is just to choose one box choice for the original operand var
        choose_best_local_choice_between_boxes(box_index_true_i[0], box_index_true_j[0]);

        true_reachable  = true;
        true_branch_rs1_minterval_los[0] = box_true_case_rs1_lo[0];
        true_branch_rs1_minterval_ups[0] = box_true_case_rs1_up[0];
        true_branch_rs2_minterval_los[0] = box_true_case_rs2_lo[0];
        true_branch_rs2_minterval_ups[0] = box_true_case_rs2_up[0];
      } else if (box_false_case_rs1_lo.size() > 0) {
        // this is just to choose one box choice for the original operand var
        choose_best_local_choice_between_boxes(box_index_false_i[0], box_index_false_j[0]);

        false_reachable = true;
        false_branch_rs1_minterval_los[0] = box_false_case_rs1_lo[0];
        false_branch_rs1_minterval_ups[0] = box_false_case_rs1_up[0];
        false_branch_rs2_minterval_los[0] = box_false_case_rs2_lo[0];
        false_branch_rs2_minterval_ups[0] = box_false_case_rs2_up[0];
      }
    } else {
      // this is just to choose one box choice for the original operand var
      choose_best_local_choice_between_boxes(box_index_true_i.back(), box_index_true_j.back());
      // don't need for false

      true_branch_rs1_minterval_los[0]  = box_true_case_rs1_lo.back();
      true_branch_rs1_minterval_ups[0]  = box_true_case_rs1_up.back();
      true_branch_rs2_minterval_los[0]  = box_true_case_rs2_lo.back();
      true_branch_rs2_minterval_ups[0]  = box_true_case_rs2_up.back();

      false_branch_rs1_minterval_los[0] = box_false_case_rs1_lo.back();
      false_branch_rs1_minterval_ups[0] = box_false_case_rs1_up.back();
      false_branch_rs2_minterval_los[0] = box_false_case_rs2_lo.back();
      false_branch_rs2_minterval_ups[0] = box_false_case_rs2_up.back();
    }

    if (true_reachable) {
      if (false_reachable) {
        if (conditional_type == EQ) {
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
          uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
          take_branch(1, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_null; // careful

          path_condition.push_back(add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          take_branch(0, 0);
        } else {
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
          take_branch(0, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_null; // careful

          path_condition.push_back(add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
          take_branch(1, 0);
        }

        queries_reasoned_by_box+=2;
        return true;
      } else {
        // false query to smt
        assert_path_condition_into_smt_expression();
        check_operands_smt_expressions();
        false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));

        if (false_reachable) {
          if (conditional_type == EQ) {
            constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
            constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
            uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BVT, boolector_null); // important should be BVT so that in backtrack_sltu it does boolector_pop
            take_branch(1, 1);
            asts[tc-2]               = false_ast_ptr;
            bvt_false_branches[tc-2] = boolector_null; // careful

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
            uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
            take_branch(0, 1);
            asts[tc-2]               = false_ast_ptr;
            bvt_false_branches[tc-2] = boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful

            path_condition.push_back(add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

            // important: if on true branch we need BVT in future it will apply boolector_push() later in assert_path_condition_into_smt_expression
            // so no worries

            // true under_approximate
            constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
            constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
            take_branch(1, 0);
          }
        } else {
          // true under_approximate
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], true_branch_rs1_minterval_los, true_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], true_branch_rs2_minterval_los, true_branch_rs2_minterval_ups, 1, 0);
          take_branch(1, 0);
        }

        queries_reasoned_by_box++;
        return true;
      }
    } else if (false_reachable) {
      // true query to smt
      assert_path_condition_into_smt_expression();
      check_operands_smt_expressions();
      true_reachable = check_sat_true_branch_bvt(boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));

      if (true_reachable) {
        if (conditional_type == EQ) {
          // false
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
          take_branch(1, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]); // carefull

          path_condition.push_back(add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

          // true
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          take_branch(0, 0);
        } else {
          // false under_approximate
          constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
          constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
          uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BVT, boolector_null); // important should be BVT so that in backtrack_sltu it does boolector_pop
          take_branch(0, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_null; // careful

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt();
          dump_all_input_variables_on_trace_true_branch_bvt();
          take_branch(1, 0);
        }

      } else {
        // false under_approximate
        constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, 0);
        constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, 0);
        take_branch(0, 0);
      }

      queries_reasoned_by_box++;
      return true;
    } else {
      // cannot decide
      return false;
    }
  }
}

void mit_box_bvt_engine::evaluate_diseq_false_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  // std::cout << "-- evaluate_diseq_false_branch_under_approximate_box -- \n";

  // assert: intervals have intersection, non-wrapped

  uint64_t intersection_lo = std::max(lo1, lo2);
  uint64_t intersection_up = std::min(up1, up2);

  if (intersection_lo > intersection_up) {
    std::cout << exe_name << ": intersection is empty! \n";
    exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  // box
  false_branch_rs1_minterval_los[0] = intersection_lo;
  false_branch_rs1_minterval_ups[0] = intersection_lo;
  false_branch_rs2_minterval_los[0] = intersection_lo;
  false_branch_rs2_minterval_ups[0] = intersection_lo;

  // std::cout << "box: [" << intersection_lo << ", " << intersection_lo << "]; [" << intersection_lo << ", " << intersection_lo << "]\n";

  constrain_memory_under_approximate_box(rs1, reg_asts[rs1], false_branch_rs1_minterval_los, false_branch_rs1_minterval_ups, 1, involved_sym_inputs_ast_tcs[reg_asts[rs2]][0]);
  constrain_memory_under_approximate_box(rs2, reg_asts[rs2], false_branch_rs2_minterval_los, false_branch_rs2_minterval_ups, 1, involved_sym_inputs_ast_tcs[reg_asts[rs1]][0]);
}