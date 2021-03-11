#include "mit_bvt_engine.hpp"

class mit_box_bvt_engine : public mit_bvt_engine {
  public:
    // ---------------------------
    // run-time functions
    // ---------------------------
    virtual void     init_engine(uint64_t peek_argument);
    virtual uint64_t run_engine(uint64_t* to_context);
    void    witness_profile();

    // ---------------------------
    // reasoning/decision core
    // ---------------------------
    uint64_t add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, uint32_t mints_num, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t step, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs, uint8_t theory_type, BoolectorNode* smt_expr);
    virtual void create_sltu_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
    virtual void create_xor_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);

    // ---------------------------
    // under_approximate box decision procedure
    // ---------------------------
    uint8_t   which_heuristic = 3;
    uint64_t* boxes;
    uint32_t  NUMBER_OF_HEURISTIC_UNDER_APPROX_BOXES = 2;

    uint64_t backward_propagation_of_under_approximate_box(uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint64_t input_box);
    void     constrain_memory_under_approximate_box(uint64_t reg, uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint64_t input_box);
    void     evaluate_sltu_true_branch_under_approximate_box_h2(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    void     evaluate_sltu_false_branch_under_approximate_box_h2(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    bool     evaluate_sltu_true_branch_under_approximate_box_h3(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    bool     evaluate_sltu_false_branch_under_approximate_box_h3(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual  void generate_and_apply_sltu_boxes_h2(uint8_t conditional_type, uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual  bool generate_and_apply_sltu_boxes_h3(uint8_t conditional_type, uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual  bool apply_sltu_under_approximate_box_decision_procedure_h2(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);
    virtual  bool apply_sltu_under_approximate_box_decision_procedure_h3(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);
    bool     evaluate_diseq_false_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual  bool generate_and_apply_diseq_boxes_h2(uint8_t conditional_type, uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual  bool generate_and_apply_diseq_boxes_h3(uint8_t conditional_type, uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual  bool apply_diseq_under_approximate_box_decision_procedure_h2(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);
    virtual  bool apply_diseq_under_approximate_box_decision_procedure_h3(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);

    enum returned_value : uint8_t {
      CANNOT_BE_HANDLED = 0,
      HANDLED = 1,
      CAN_BE_HANDLED = 2
    };

    uint8_t sltu_box_decision_heuristic_1(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2, bool& true_reachable, bool& false_reachable);
    uint8_t sltu_box_decision_heuristic_2(uint8_t conditional_type, std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2, bool& true_reachable, bool& false_reachable);
    uint8_t sltu_box_decision_heuristic_3(uint8_t conditional_type, std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2, bool& true_reachable, bool& false_reachable);
    uint8_t diseq_box_decision_heuristic_1(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2, bool& true_reachable, bool& false_reachable);
    uint8_t diseq_box_decision_heuristic_2(uint8_t conditional_type, std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2, bool& true_reachable, bool& false_reachable);
    uint8_t diseq_box_decision_heuristic_3(uint8_t conditional_type, std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2, bool& true_reachable, bool& false_reachable);
    void    choose_best_local_choice_between_boxes(size_t index_true_i, size_t index_true_j);
    void    restore_input_table_to_before_applying_bvt_dumps();
};