// ------------------------ INSTRUCTIONS -----------------------

void constrain_lui();
void constrain_addi();
void constrain_add();
void constrain_sub();
void constrain_mul();
void constrain_divu();
void constrain_remu();
void constrain_sltu();
void constrain_jal_jalr();
uint64_t constrain_ld();
uint64_t constrain_sd();

void backtrack_sltu();
void backtrack_sd();
void backtrack_ecall();

void backtrack_trace(uint64_t* context);

void init_symbolic_engine();

void print_symbolic_memory(uint64_t svc);

uint64_t cardinality(uint64_t lo, uint64_t up);
uint64_t combined_cardinality(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);

uint64_t is_symbolic_value(uint64_t type, uint64_t lo, uint64_t up);
uint64_t is_safe_address(uint64_t vaddr, uint64_t reg);
uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);

uint64_t is_trace_space_available();

void ealloc();
void efree();

void store_symbolic_memory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint64_t type, uint64_t lo, uint64_t up, uint64_t trb);

void store_constrained_memory(uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t trb);
void store_register_memory(uint64_t reg, uint64_t value);

void constrain_memory(uint64_t reg, uint64_t lo, uint64_t up, uint64_t trb);

void set_constraint(uint64_t reg, uint64_t hasco, uint64_t vaddr, uint64_t hasmn, uint64_t colos, uint64_t coups);

void take_branch(uint64_t b, uint64_t how_many_more);
void create_constraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb, uint64_t how_many_more);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_symbolic = 0;
uint64_t symbolic    = 0; // flag for symbolically executing code
uint64_t backtrack   = 0; // flag for backtracking symbolic execution

extern uint64_t rc;
extern uint64_t* read_values;
extern uint64_t* read_los;
extern uint64_t* read_ups;