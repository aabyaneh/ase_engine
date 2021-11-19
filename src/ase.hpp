#include "pvi_ubox_bvt_engine.hpp"
#include "bvt_engine.hpp"
#include <sys/time.h>
#include <thread>
#include <chrono>

engine*  current_engine;
uint64_t EXITCODE_BADARGUMENTS = 1;

struct timeval symbolic_execution_begin;
struct timeval symbolic_execution_end;
double time_elapsed_in_mcseconds;
double time_elapsed_in_seconds;
std::ofstream output_csv;
std::string file_name;
std::string method_name;

uint64_t timeout = 120;
uint64_t timeout_check_step = 1;

int    _argc    = 0;
char** _argv    = (char**) 0;
char*  exe_name = (char*) 0;

uint64_t max_trace_length               = 20000000;
uint64_t max_ast_nodes_trace_length     = 10 * max_trace_length;
uint64_t initial_ast_nodes_trace_length = max_ast_nodes_trace_length / 8;
uint64_t max_number_of_intervals        = 2001;
uint64_t max_number_of_involved_inputs  = 100;
uint64_t memory_allocation_step_ast_nodes_trace = 10000000;