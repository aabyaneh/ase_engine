#include "mit_box_bvt_engine.hpp"
#include <unordered_map>

class mit_box_abvt_engine : public mit_box_bvt_engine {
  public:
    // ------------------------------------
    // over-approximate bit-vector approach
    // ------------------------------------
    uint64_t EXCEPTION_UNREACH_EXPLORE  = 8;
    uint64_t EXITCODE_UNREACH_EXPLORE   = 15;

    uint64_t sltu_instruction           = -1;
    uint64_t max_bvt_sat_check_period   = 0;
    uint64_t bvt_sat_check_counter      = 0;
    bool     unreachable_path           = false;
    bool     false_reachable_prediction = false;
    bool     true_reachable_prediction  = false;
    std::unordered_map<uint64_t, uint8_t> cached_reachability_results_for_explored_branches;
    std::unordered_map<uint64_t, uint8_t>::const_iterator branch_is_found_in_cache;

    std::vector<const char*> input_assignments;
    void refine_abvt_abstraction_by_dumping_all_input_variables_on_trace_bvt();
    uint64_t handle_unreachable_exploration(uint64_t* context);

    // overriding functions
    void     init_engine(uint64_t peek_argument);
    uint64_t run_engine(uint64_t* to_context);
    void     init_interpreter();
    uint64_t handle_exception(uint64_t* context);
    void     backtrack_sltu();
    void     backtrack_sd();
    void     create_sltu_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
    void     create_xor_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
    bool     apply_sltu_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);

    // overloading functions
    void dump_involving_input_variables_true_branch_bvt(bool);
    void dump_involving_input_variables_false_branch_bvt(bool);
    void dump_all_input_variables_on_trace_true_branch_bvt(bool);
    void dump_all_input_variables_on_trace_false_branch_bvt(bool);
};