#include "mit_box_abvt_engine.hpp"

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

// ------------------------- INITIALIZATION ------------------------

void mit_box_abvt_engine::init_engine(uint64_t peek_argument) {
  max_bvt_sat_check_period = peek_argument;

  mit_box_bvt_engine::init_engine(peek_argument);
}

uint64_t mit_box_abvt_engine::run_engine(uint64_t* to_context) {
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

      // -----------------------------------------------------------------------
      // lazy over-approximate decision procedure
      // -----------------------------------------------------------------------

      if (bvt_sat_check_counter == 0 && unreachable_path == false) {
        // it is not an unreachable path, and last condition is reasoned exactly.

        // for correctness check
        // if (boolector_sat(btor) != BOOLECTOR_SAT) {
        //   std::cout << exe_name << ": path must not be unsat!\n";
        // }

        if (paths == 0) std::cout << exe_name << ": backtracking \n"; else unprint_integer(paths);
        paths++;
        print_integer(paths);

      } else if (unreachable_path == true) {
        // unreachable path has been explored; backtrack
        unreachable_path = false;
      } else {
        /*
          an end-point is reached where the reasoning is yet not exact: bvt_sat_check_counter > 0;
          so satisfiability must be checked: if sat then it is a real path dump the generated witness by smt
          if not sat means unreachable path so backtrack;
        */

        /*
          don't need to bvt_sat_check_counter = 0; because it will be managed in backtrack_sltu
          here we have unreachable_path = false;
        */
        queries_reasoned_by_bvt++;
        if (boolector_sat(btor) == BOOLECTOR_SAT) {
          if (paths == 0) std::cout << exe_name << ": backtracking \n"; else unprint_integer(paths);
          paths++;
          print_integer(paths);

          // dump inputs taken from smt, because this path was reasoned lazily so at end-point inputs should be updated with correct values
          // for print and test generation purpose
          refine_abvt_abstraction_by_dumping_all_input_variables_on_trace_bvt();

          queries_reasoned_by_bvt_sat++;
        }
      }

      // -----------------------------------------------------------------------

      backtrack_trace(current_context);

      if (pc == 0) {
        std::cout << "\n\n";
        std::cout << YELLOW "backtracking: " << paths << RESET << '\n';
        std::cout << GREEN "number of queries:= mit: " << queries_reasoned_by_mit << ", box: " << queries_reasoned_by_box << ", bvt: " << queries_reasoned_by_bvt << RESET << "\n";
        std::cout << GREEN "--- bvt queries:= #sat: " << queries_reasoned_by_bvt_sat << ", #unsat: " << queries_reasoned_by_bvt - queries_reasoned_by_bvt_sat << RESET << "\n\n";

        if (symbolic_input_cnt != 0)
          std::cout << "symbolic_input_cnt is not zero!\n";

        if (IS_TEST_MODE)
          output_results.close();

        return EXITCODE_NOERROR;
      }
    }
  }
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void mit_box_abvt_engine::init_interpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_UNREACH_EXPLORE + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)     = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_MAXTRACE)           = (uint64_t) "trace length exceeded";
  *(EXCEPTIONS + EXCEPTION_UNREACH_EXPLORE)    = (uint64_t) "unreachable exploration";
}

uint64_t mit_box_abvt_engine::handle_unreachable_exploration(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_exit_code(context, EXITCODE_UNREACH_EXPLORE);

  return EXIT;
}

uint64_t mit_box_abvt_engine::handle_exception(uint64_t* context) {
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
  else if (exception == EXCEPTION_UNREACH_EXPLORE)
    return handle_unreachable_exploration(context);
  else {
    std::cout << exe_name << ": context " << get_name(context) << "throws uncaught ";
    print_exception(exception, get_faulting_page(context));
    std::cout << '\n';

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

// -----------------------------------------------------------------------------
// ----------------------------- backtracking ----------------------------------
// -----------------------------------------------------------------------------

void mit_box_abvt_engine::backtrack_sltu() {
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

          // -------------------------------------------------------------------
          // lazy decision
          // -------------------------------------------------------------------
          if (mr_sds[tc] == 0) {
            bvt_sat_check_counter = 0;
          } else {
            bvt_sat_check_counter = mr_sds[tc]; // restore the value of bvt_sat_check_counter
            // bvt_sat_check_counter = max_bvt_sat_check_period/2+1;
          }
          // -------------------------------------------------------------------

          reg_asts[vaddr] = (registers[vaddr] == 0) ? zero_node : one_node;
          reg_bvts[vaddr] = (registers[vaddr] == 0) ? smt_exprs[zero_node] : smt_exprs[one_node];

          // there are two cases when (bvt_false_branches[tc] == boolector_null)
          // 1. when theory is MIT; may happen that we have to pop more than one constraint (when was going through false branches)
          // 2. when theory was MIT and then we needed BVT so we dumped path_condition, and now we backtrack.
          if (bvt_false_branches[tc] == boolector_null) {
            while (path_condition.size() > 0 && path_condition.back() > asts[tc]) {
              path_condition.pop_back();
            }

            if (theory_type_ast_nodes[asts[tc]] >= BVT) {
              boolector_pop(btor, 1);
              path_condition.clear();
            }

            path_condition.push_back(asts[tc]);
          } else {
            // when asts[tc] == 0 means theory of bvt take care of everything.
            /* when bvt_false_branches[tc] != boolector_null && theory_type_ast_nodes[asts[tc]] == BVT then points to box theory,
               for when box can decide true-case and not false. In that case true may not be evaluated as a smt expr so no pop */
            if (asts[tc] == 0 || theory_type_ast_nodes[asts[tc]] >= BVT)
              boolector_pop(btor, 1);
            boolector_assert(btor, bvt_false_branches[tc]);
            path_condition.clear();
          }
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

void mit_box_abvt_engine::backtrack_sd() {
  if (theory_types[tc] < BVT) {
    if (store_trace_ptrs[asts[tc]].size() >= 1) {
      store_trace_ptrs[asts[tc]].pop_back();
    } else {
      std::cout << exe_name << ": error occured during sd backtracking at 0x" << std::hex << pc - entry_point << std::dec << std::endl;
      exit((int) EXITCODE_SYMBOLICEXECUTIONERROR);
    }

  } else if (theory_types[tc] >= BVT && asts[tc] != 0) {
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

// -----------------------------------------------------------------------------
// ------------------------ reasoning/decision core ----------------------------
// -----------------------------------------------------------------------------

void mit_box_abvt_engine::create_sltu_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  bool is_true_guess   = false;
  bool is_false_guess  = false;
  uint64_t true_branch_is_over_approximated_by  = 0; // these are because true and false cases are reverse, when < or <=
  uint64_t false_branch_is_over_approximated_by = 0; // these are because true and false cases are reverse, when < or <=
  uint64_t branch_is_over_approximated_by       = 0;
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
    // false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
    // true_reachable  = check_sat_true_branch_bvt (boolector_ult (btor, reg_bvts[rs1], reg_bvts[rs2]));

    // -------------------------------------------------------------------------
    // lazy decision, once a while
    // lazy reachability check
    // -------------------------------------------------------------------------

    // restore the cached previous decision value for reachability of branches at pc
    if (max_bvt_sat_check_period) {
      branch_is_found_in_cache = cached_reachability_results_for_explored_branches.find(pc);
      if (branch_is_found_in_cache != cached_reachability_results_for_explored_branches.end()) {
        false_reachable_prediction = branch_is_found_in_cache->second & 1;
        true_reachable_prediction  = branch_is_found_in_cache->second & 2;
      }
    }

    if (bvt_sat_check_counter >= max_bvt_sat_check_period) {
      // check reachability using complete smt solver
      false_reachable_prediction = false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
      true_reachable_prediction  = true_reachable  = check_sat_true_branch_bvt (boolector_ult (btor, reg_bvts[rs1], reg_bvts[rs2]));

      bvt_sat_check_counter = 0;

    } else {
      // check reachability using previous decision
      sltu_instruction = pc; // this is because I need to change pc of the trace entry when dump inputs at end-point (don't want to be exit syscall)

      if (false_reachable_prediction == true && true_reachable_prediction == true) {
        false_reachable = true;
        true_reachable  = true;
        is_false_guess  = true;
        is_true_guess   = true;
        true_branch_is_over_approximated_by  = bvt_sat_check_counter + 1;
        false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
      } else if (false_reachable_prediction == true && true_reachable_prediction == false) {
        false_reachable = true;
        is_false_guess  = true;
        false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;

        true_reachable = check_sat_true_branch_bvt(boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (true_reachable) {
          is_true_guess = false;
          true_branch_is_over_approximated_by = 0;
        } else {
          is_true_guess = true;
          true_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }
      } else if (false_reachable_prediction == false && true_reachable_prediction == true) {
        false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (false_reachable) {
          is_false_guess = false;
          false_branch_is_over_approximated_by = 0;
        } else {
          is_false_guess = true;
          false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }

        true_reachable = true;
        is_true_guess  = true;
        true_branch_is_over_approximated_by = bvt_sat_check_counter + 1;

      } else {
        false_reachable = check_sat_false_branch_bvt(boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (false_reachable) {
          is_false_guess = false;
          false_branch_is_over_approximated_by = 0;
        } else {
          is_false_guess = true;
          false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }

        true_reachable = check_sat_true_branch_bvt(boolector_ult (btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (true_reachable) {
          is_true_guess = false;
          true_branch_is_over_approximated_by = 0;
        } else {
          is_true_guess = true;
          true_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }
      }

    }

    // cache the decision for if at pc
    if (max_bvt_sat_check_period) {
      if (branch_is_found_in_cache != cached_reachability_results_for_explored_branches.end()) {
        cached_reachability_results_for_explored_branches[pc] = (true_reachable << 1) | false_reachable;
      } else {
        cached_reachability_results_for_explored_branches.insert(std::make_pair<uint64_t, uint8_t>(pc, (true_reachable << 1) | false_reachable) );
      }
    }

    // -------------------------------------------------------------------------

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_whether_is_strict_less_than_or_is_less_greater_than_eq() == LGTE) {
          // false
          dump_involving_input_variables_true_branch_bvt(is_true_guess);
          dump_all_input_variables_on_trace_true_branch_bvt(is_true_guess);
          take_branch(1, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
          mr_sds[tc-2]             = true_branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_false_branch_bvt(is_false_guess);
          dump_all_input_variables_on_trace_false_branch_bvt(is_false_guess);
          take_branch(0, 0);
          bvt_sat_check_counter = false_branch_is_over_approximated_by;

        } else {
          // false
          dump_involving_input_variables_false_branch_bvt(is_false_guess);
          dump_all_input_variables_on_trace_false_branch_bvt(is_false_guess);
          take_branch(0, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
          mr_sds[tc-2]             = false_branch_is_over_approximated_by;

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt(is_true_guess);
          dump_all_input_variables_on_trace_true_branch_bvt(is_true_guess);
          take_branch(1, 0);
          bvt_sat_check_counter = true_branch_is_over_approximated_by;

        }
      } else {
        dump_involving_input_variables_true_branch_bvt(is_true_guess);
        dump_all_input_variables_on_trace_true_branch_bvt(is_true_guess);
        take_branch(1, 0);
        bvt_sat_check_counter = true_branch_is_over_approximated_by;
      }
    } else if (false_reachable) {
      dump_involving_input_variables_false_branch_bvt(is_false_guess);
      dump_all_input_variables_on_trace_false_branch_bvt(is_false_guess);
      take_branch(0, 0);
      bvt_sat_check_counter = false_branch_is_over_approximated_by;
    } else {
      unreachable_path = true;
      throw_exception(EXCEPTION_UNREACH_EXPLORE, 0);
    }

    return;
  }

  /*
     this is the case when the path is already over-approximated because a conditional reasoned by BVT
     and now we reach another conditional which is independent of the previous BVT-reasoned ones
     and thus is reasoned by MIT; however the path is still over-approximated in total.
  */
  if (bvt_sat_check_counter) branch_is_over_approximated_by = ++bvt_sat_check_counter;

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
        mr_sds[tc-2]             = branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

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
        mr_sds[tc-2]             = branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

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

void mit_box_abvt_engine::create_xor_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb) {
  bool cannot_handle   = false;
  bool true_reachable  = false;
  bool false_reachable = false;
  bool is_true_guess   = false;
  bool is_false_guess  = false;
  uint64_t true_branch_is_over_approximated_by  = 0; // these are because true and false cases are reverse, when < or <=
  uint64_t false_branch_is_over_approximated_by = 0; // these are because true and false cases are reverse, when < or <=
  uint64_t branch_is_over_approximated_by       = 0;
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
    // false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
    // true_reachable  = check_sat_true_branch_bvt (boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));

    // -------------------------------------------------------------------------
    // lazy decision, once a while
    // lazy reachability check
    // -------------------------------------------------------------------------

    // restore the cached previous decision value for reachability of branches at pc
    if (max_bvt_sat_check_period) {
      branch_is_found_in_cache = cached_reachability_results_for_explored_branches.find(pc);
      if (branch_is_found_in_cache != cached_reachability_results_for_explored_branches.end()) {
        false_reachable_prediction = branch_is_found_in_cache->second & 1;
        true_reachable_prediction  = branch_is_found_in_cache->second & 2;
      }
    }

    if (bvt_sat_check_counter >= max_bvt_sat_check_period) {
      // check reachability using complete smt solver
      false_reachable_prediction = false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
      true_reachable_prediction  = true_reachable  = check_sat_true_branch_bvt (boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));

      bvt_sat_check_counter = 0;

    } else {
      // check reachability using previous decision
      sltu_instruction = pc; // this is because I need to change pc of the trace entry when dump inputs at end-point (don't want to be exit syscall)

      if (false_reachable_prediction == true && true_reachable_prediction == true) {
        false_reachable = true;
        true_reachable  = true;
        is_false_guess  = true;
        is_true_guess   = true;
        true_branch_is_over_approximated_by  = bvt_sat_check_counter + 1;
        false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
      } else if (false_reachable_prediction == true && true_reachable_prediction == false) {
        false_reachable = true;
        is_false_guess  = true;
        false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;

        true_reachable = check_sat_true_branch_bvt(boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (true_reachable) {
          is_true_guess = false;
          true_branch_is_over_approximated_by = 0;
        } else {
          is_true_guess = true;
          true_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }
      } else if (false_reachable_prediction == false && true_reachable_prediction == true) {
        false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (false_reachable) {
          is_false_guess = false;
          false_branch_is_over_approximated_by = 0;
        } else {
          is_false_guess = true;
          false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }

        true_reachable = true;
        is_true_guess  = true;
        true_branch_is_over_approximated_by = bvt_sat_check_counter + 1;

      } else {
        false_reachable = check_sat_false_branch_bvt(boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (false_reachable) {
          is_false_guess = false;
          false_branch_is_over_approximated_by = 0;
        } else {
          is_false_guess = true;
          false_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }

        true_reachable = check_sat_true_branch_bvt(boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
        if (true_reachable) {
          is_true_guess = false;
          true_branch_is_over_approximated_by = 0;
        } else {
          is_true_guess = true;
          true_branch_is_over_approximated_by = bvt_sat_check_counter + 1;
        }
      }
    }

    // cache the decision for if at pc
    if (max_bvt_sat_check_period) {
      if (branch_is_found_in_cache != cached_reachability_results_for_explored_branches.end()) {
        cached_reachability_results_for_explored_branches[pc] = (true_reachable << 1) | false_reachable;
      } else {
        cached_reachability_results_for_explored_branches.insert(std::make_pair<uint64_t, uint8_t>(pc, (true_reachable << 1) | false_reachable) );
      }
    }

    // -------------------------------------------------------------------------

    if (true_reachable) {
      if (false_reachable) {
        if (check_conditional_type_whether_is_equality_or_disequality() == EQ) {
          // false
          dump_involving_input_variables_true_branch_bvt(is_true_guess);
          dump_all_input_variables_on_trace_true_branch_bvt(is_true_guess);
          take_branch(1, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
          mr_sds[tc-2]             = true_branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_false_branch_bvt(is_false_guess);
          dump_all_input_variables_on_trace_false_branch_bvt(is_false_guess);
          take_branch(0, 0);
          bvt_sat_check_counter = false_branch_is_over_approximated_by;

        } else {
          // false
          dump_involving_input_variables_false_branch_bvt(is_false_guess);
          dump_all_input_variables_on_trace_false_branch_bvt(is_false_guess);
          take_branch(0, 1);
          asts[tc-2]               = 0; // important for backtracking
          bvt_false_branches[tc-2] = boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
          mr_sds[tc-2]             = false_branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt(is_true_guess);
          dump_all_input_variables_on_trace_true_branch_bvt(is_true_guess);
          take_branch(1, 0);
          bvt_sat_check_counter = true_branch_is_over_approximated_by;

        }
      } else {
        dump_involving_input_variables_true_branch_bvt(is_true_guess);
        dump_all_input_variables_on_trace_true_branch_bvt(is_true_guess);
        take_branch(1, 0);
        bvt_sat_check_counter = true_branch_is_over_approximated_by;
      }
    } else if (false_reachable) {
      dump_involving_input_variables_false_branch_bvt(is_false_guess);
      dump_all_input_variables_on_trace_false_branch_bvt(is_false_guess);
      take_branch(0, 0);
      bvt_sat_check_counter = false_branch_is_over_approximated_by;
    } else {
      unreachable_path = true;
      throw_exception(EXCEPTION_UNREACH_EXPLORE, 0);
    }

    return;
  }

  if (bvt_sat_check_counter) branch_is_over_approximated_by = ++bvt_sat_check_counter;

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
        mr_sds[tc-2]             = branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

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
        bvt_false_branches[tc-2] = boolector_null; // careful
        mr_sds[tc-2]             = branch_is_over_approximated_by; // for backtracking restores the value of bvt_sat_check_counter

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

void mit_box_abvt_engine::dump_involving_input_variables_true_branch_bvt(bool is_branch_reasoned_based_on_guess) {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;
  uint8_t abstraction;

  involved_inputs_in_current_conditional_expression_rs1_operand.clear();
  if (reg_symb_type[rs1] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs1]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs1]][i];
      involved_inputs_in_current_conditional_expression_rs1_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      if (!is_branch_reasoned_based_on_guess) {
        value_v[0]  = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
        abstraction = BVT;
      } else {
        value_v[0]  = mintervals_los[involved_input_ast_tc][0]; // previous witness, might be an incorrect witness after applicatio of the current conditional
        abstraction = ABVT;
      }
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, abstraction, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, abstraction);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), abstraction);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }

  involved_inputs_in_current_conditional_expression_rs2_operand.clear();
  if (reg_symb_type[rs2] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs2]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs2]][i];
      involved_inputs_in_current_conditional_expression_rs2_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      if (!is_branch_reasoned_based_on_guess) {
        value_v[0]  = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
        abstraction = BVT;
      } else {
        value_v[0]  = mintervals_los[involved_input_ast_tc][0]; // previous witness, might be an incorrect witness after applicatio of the current conditional
        abstraction = ABVT;
      }
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, abstraction, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, abstraction);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), abstraction);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }
}

void mit_box_abvt_engine::dump_involving_input_variables_false_branch_bvt(bool is_branch_reasoned_based_on_guess) {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;
  uint8_t abstraction;

  involved_inputs_in_current_conditional_expression_rs1_operand.clear();
  if (reg_symb_type[rs1] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs1]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs1]][i];
      involved_inputs_in_current_conditional_expression_rs1_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      if (!is_branch_reasoned_based_on_guess) {
        value_v[0]  = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
        abstraction = BVT;
      } else {
        value_v[0]  = mintervals_los[involved_input_ast_tc][0]; // previous witness, might be an incorrect witness after applicatio of the current conditional
        abstraction = ABVT;
      }
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, abstraction, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, abstraction);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), abstraction);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }

  involved_inputs_in_current_conditional_expression_rs2_operand.clear();
  if (reg_symb_type[rs2] == SYMBOLIC) {
    for (size_t i = 0; i < involved_sym_inputs_cnts[reg_asts[rs2]]; i++) {
      involved_input_ast_tc = involved_sym_inputs_ast_tcs[reg_asts[rs2]][i];
      involved_inputs_in_current_conditional_expression_rs2_operand.push_back(ast_nodes[involved_input_ast_tc].right_node);
      if (!is_branch_reasoned_based_on_guess) {
        value_v[0]  = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
        abstraction = BVT;
      } else {
        value_v[0]  = mintervals_los[involved_input_ast_tc][0]; // previous witness, might be an incorrect witness after applicatio of the current conditional
        abstraction = ABVT;
      }
      ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, abstraction, smt_exprs[involved_input_ast_tc]);
      is_assigned = false;
      for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
        stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
        mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
        mr_stored_to_tc = mr_sds[mr_stored_to_tc];
        if (mr_stored_to_tc <= stored_to_tc) {
          store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, abstraction);
          is_assigned = true;
        }
      }

      if (is_assigned == false) {
        store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), abstraction);
      }
      input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
    }
  }
}

void mit_box_abvt_engine::dump_all_input_variables_on_trace_true_branch_bvt(bool is_branch_reasoned_based_on_guess) {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;
  uint8_t abstraction;

  for (size_t i = 0; i < input_table.size(); i++) {
    if (vector_contains_element(involved_inputs_in_current_conditional_expression_rs1_operand, i) ||
        vector_contains_element(involved_inputs_in_current_conditional_expression_rs2_operand, i) ) continue;
    involved_input_ast_tc = input_table_ast_tcs_before_branch_evaluation[i];
    if (theory_type_ast_nodes[involved_input_ast_tc] == MIT) continue;
    if (!is_branch_reasoned_based_on_guess) {
      value_v[0]  = std::stoull(true_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      abstraction = BVT;
    } else {
      value_v[0]  = mintervals_los[involved_input_ast_tc][0]; // previous witness, might be an incorrect witness after applicatio of the current conditional
      abstraction = ABVT;
    }
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, abstraction, smt_exprs[involved_input_ast_tc]);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, abstraction);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), abstraction);
    }
    input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
  }

}

void mit_box_abvt_engine::dump_all_input_variables_on_trace_false_branch_bvt(bool is_branch_reasoned_based_on_guess) {
  uint64_t ast_ptr, involved_input_ast_tc, stored_to_tc, mr_stored_to_tc;
  bool is_assigned;
  uint8_t abstraction;

  for (size_t i = 0; i < input_table.size(); i++) {
    if (vector_contains_element(involved_inputs_in_current_conditional_expression_rs1_operand, i) ||
        vector_contains_element(involved_inputs_in_current_conditional_expression_rs2_operand, i) ) continue;
    involved_input_ast_tc = input_table_ast_tcs_before_branch_evaluation[i];
    if (theory_type_ast_nodes[involved_input_ast_tc] == MIT) continue;
    if (!is_branch_reasoned_based_on_guess) {
      value_v[0]  = std::stoull(false_input_assignments[ast_nodes[involved_input_ast_tc].right_node], 0, 2);
      abstraction = BVT;
    } else {
      value_v[0]  = mintervals_los[involved_input_ast_tc][0]; // previous witness, might be an incorrect witness after applicatio of the current conditional
      abstraction = ABVT;
    }
    ast_ptr = add_ast_node(VAR, 0, ast_nodes[involved_input_ast_tc].right_node, 1, value_v, value_v, 1, 0, zero_v, abstraction, smt_exprs[involved_input_ast_tc]);
    is_assigned = false;
    for (size_t k = 0; k < store_trace_ptrs[involved_input_ast_tc].size(); k++) {
      stored_to_tc    = store_trace_ptrs[involved_input_ast_tc][k];
      mr_stored_to_tc = load_symbolic_memory(pt, vaddrs[stored_to_tc]);
      mr_stored_to_tc = mr_sds[mr_stored_to_tc];
      if (mr_stored_to_tc <= stored_to_tc) {
        store_symbolic_memory(pt, vaddrs[stored_to_tc], value_v[0], VALUE_T, ast_ptr, tc, 0, abstraction);
        is_assigned = true;
      }
    }
    if (is_assigned == false) {
      store_input_record(ast_ptr, input_table.at(ast_nodes[involved_input_ast_tc].right_node), abstraction);
    }
    input_table.at(ast_nodes[involved_input_ast_tc].right_node) = ast_ptr;
  }
}

// -----------------------------------------------------------------------------
// ------------------- under_approximate decision procedure --------------------
// -----------------------------------------------------------------------------

bool mit_box_abvt_engine::apply_sltu_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2) {
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
      mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

      path_condition.push_back(add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

      evaluate_sltu_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      take_branch(0, 0);
    } else {
      evaluate_sltu_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
      take_branch(0, 1);
      asts[tc-2]               = false_ast_ptr;
      bvt_false_branches[tc-2] = boolector_null; // careful
      mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

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
          mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

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
          mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

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
            mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

            // true
            boolector_push(btor, 1);
            boolector_assert(btor, boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]));
            dump_involving_input_variables_false_branch_bvt(false);
            dump_all_input_variables_on_trace_false_branch_bvt(false);
            take_branch(0, 0);

          } else {
            // false
            dump_involving_input_variables_false_branch_bvt(false);
            dump_all_input_variables_on_trace_false_branch_bvt(false);
            uint64_t false_ast_ptr   = add_ast_node(IGTE, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
            take_branch(0, 1);
            asts[tc-2]               = false_ast_ptr;
            bvt_false_branches[tc-2] = boolector_ugte(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
            mr_sds[tc-2]             = 0;

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
          dump_involving_input_variables_true_branch_bvt(false);
          dump_all_input_variables_on_trace_true_branch_bvt(false);
          uint64_t false_ast_ptr   = add_ast_node(ILT, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
          take_branch(1, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
          mr_sds[tc-2]             = 0;

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
          mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ult(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt(false);
          dump_all_input_variables_on_trace_true_branch_bvt(false);
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

bool mit_box_abvt_engine::apply_diseq_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2) {
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
      mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

      path_condition.push_back(add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 1, 0, zero_v, BOX, boolector_null));

      evaluate_diseq_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      take_branch(0, 0);
    } else {
      evaluate_diseq_false_branch_under_approximate_box(lo1[0], up1[0], lo2[0], up2[0]);
      uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null);
      take_branch(0, 1);
      asts[tc-2]               = false_ast_ptr;
      bvt_false_branches[tc-2] = boolector_null; // careful
      mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

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
          mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

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
          mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

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
            mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

            // true
            boolector_push(btor, 1);
            boolector_assert(btor, boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]));
            dump_involving_input_variables_false_branch_bvt(false);
            dump_all_input_variables_on_trace_false_branch_bvt(false);
            take_branch(0, 0);

          } else {
            // false
            dump_involving_input_variables_false_branch_bvt(false);
            dump_all_input_variables_on_trace_false_branch_bvt(false);
            uint64_t false_ast_ptr   = add_ast_node(IEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
            take_branch(0, 1);
            asts[tc-2]               = false_ast_ptr;
            bvt_false_branches[tc-2] = boolector_eq(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
            mr_sds[tc-2]             = 0;

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
          dump_involving_input_variables_true_branch_bvt(false);
          dump_all_input_variables_on_trace_true_branch_bvt(false);
          uint64_t false_ast_ptr   = add_ast_node(INEQ, reg_asts[rs1], reg_asts[rs2], 0, zero_v, zero_v, 0, 0, zero_v, BOX, boolector_null); // important: should remain BOX
          take_branch(1, 1);
          asts[tc-2]               = false_ast_ptr;
          bvt_false_branches[tc-2] = boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]); // careful
          mr_sds[tc-2]             = 0;

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
          mr_sds[tc-2]             = (bvt_sat_check_counter) ? ++bvt_sat_check_counter : 0;

          // true
          boolector_push(btor, 1);
          boolector_assert(btor, boolector_ne(btor, reg_bvts[rs1], reg_bvts[rs2]));
          dump_involving_input_variables_true_branch_bvt(false);
          dump_all_input_variables_on_trace_true_branch_bvt(false);
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

// -----------------------------------------------------------------------------
// lazy path reachability check; over-approximation of branches
// -----------------------------------------------------------------------------

void mit_box_abvt_engine::refine_abvt_abstraction_by_dumping_all_input_variables_on_trace_bvt() {
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