#include "mit_bvt_engine.hpp"

class mit_box_bvt_engine : public mit_bvt_engine {
  public:
    // ---------------------------
    // run-time functions
    // ---------------------------
    virtual void     init_engine(uint64_t peek_argument);
    virtual uint64_t run_engine(uint64_t* to_context);

    // ---------------------------
    // reasoning/decision core
    // ---------------------------
    uint64_t add_ast_node(uint8_t typ, uint64_t left_node, uint64_t right_node, uint32_t mints_num, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, uint64_t step, uint64_t sym_input_num, std::vector<uint64_t>& sym_input_ast_tcs, uint8_t theory_type, BoolectorNode* smt_expr);
    virtual void create_sltu_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);
    virtual void create_xor_constraints(std::vector<uint64_t>& lo1_p, std::vector<uint64_t>& up1_p, std::vector<uint64_t>& lo2_p, std::vector<uint64_t>& up2_p, uint64_t trb);

    // ---------------------------
    // under_approximate box decision procedure
    // ---------------------------
    uint64_t* boxes;
    uint64_t  queries_reasoned_by_box = 0; // number of queries handled by box
    uint32_t  NUMBER_OF_HEURISTIC_UNDER_APPROX_BOXES = 2;

    uint64_t backward_propagation_of_under_approximate_box(uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint64_t input_box);
    uint64_t constrain_memory_under_approximate_box(uint64_t reg, uint64_t ast_tc, std::vector<uint64_t>& lo, std::vector<uint64_t>& up, size_t mints_num, uint64_t input_box);
    void evaluate_sltu_true_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    void evaluate_sltu_false_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    void choose_best_local_choice_between_boxes(size_t index_true_i, size_t index_true_j);
    virtual bool apply_sltu_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);
    void evaluate_diseq_false_branch_under_approximate_box(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
    virtual bool apply_diseq_under_approximate_box_decision_procedure(std::vector<uint64_t>& lo1, std::vector<uint64_t>& up1, std::vector<uint64_t>& lo2, std::vector<uint64_t>& up2);
};