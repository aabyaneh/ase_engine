/*
  This project uses parts of the *Selfie Project* source code
  which is governed by a BSD license. For further information
  and LICENSE conditions see the following website:
  selfie.cs.uni-salzburg.at
*/

#include "mit_box_bvt_engine.hpp"
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

uint64_t timeout = 120;
uint64_t timeout_check_step = 1;

void run_timeout_thread() {
  uint64_t elapsed_time = 0;
  while (!current_engine->is_execution_finished && elapsed_time < timeout) {
    std::this_thread::sleep_for(std::chrono::seconds(timeout_check_step));
    elapsed_time += timeout_check_step;
  }

  if (elapsed_time >= timeout) {
    current_engine->is_execution_timeout = true;
  }
}

void write_to_csv() {
  output_csv.open("output.csv", std::ofstream::app);
  output_csv << file_name << ","
             << current_engine->paths << ","
             << time_elapsed_in_seconds << ","
             << current_engine->queries_reasoned_by_mit << ","
             << current_engine->queries_reasoned_by_box << ","
             << current_engine->queries_reasoned_by_overapprx << ","
             << current_engine->queries_reasoned_by_bvt << ","
             << current_engine->queries_reasoned_by_bvt_sat << ","
             << current_engine->queries_reasoned_by_bvt - current_engine->queries_reasoned_by_bvt_sat << std::endl;
  output_csv.close();
}

uint64_t run() {
  uint64_t exit_code;

  if (sizeof(uint64_t) != 8) {
    std::cout << "sizeof uint64_t is not 8!\n";
    return EXITCODE_BADARGUMENTS;
  }

  if (current_engine->binary_length == 0) {
    std::cout << "nothing to run \n";

    return EXITCODE_BADARGUMENTS;
  }

  std::thread timeout_thread(run_timeout_thread);

  gettimeofday(&symbolic_execution_begin, NULL);

  current_engine->execute = 1;

  current_engine->reset_interpreter();
  current_engine->reset_microkernel();

  current_engine->create_context(current_engine->MY_CONTEXT, 0);

  current_engine->up_load_binary(current_engine->current_context);

  current_engine->set_SP(current_engine->current_context);

  std::cout << current_engine->exe_name << ": engine executing " << current_engine->binary_name << " with " << (int64_t) (current_engine->page_frame_memory / current_engine->MEGABYTE) << "MB physical memory \n\n";

  exit_code = current_engine->run_engine(current_engine->current_context);

  current_engine->execute = 0;

  if (!current_engine->is_execution_timeout) {
    std::cout << current_engine->exe_name << ": engine terminating " << current_engine->get_name(current_engine->current_context) << " with exit code " << (int64_t) current_engine->sign_extend(exit_code, current_engine->SYSCALL_BITWIDTH) << '\n';
  } else {
    std::cout << " * TIMEOUT * \n" << std::endl;
  }

  current_engine->print_profile();

  current_engine->is_execution_finished = true;

  gettimeofday(&symbolic_execution_end, NULL);

  time_elapsed_in_mcseconds = (symbolic_execution_end.tv_sec - symbolic_execution_begin.tv_sec) * 1000000 + (symbolic_execution_end.tv_usec - symbolic_execution_begin.tv_usec);
  time_elapsed_in_seconds = time_elapsed_in_mcseconds / 1000000;
  std::cout << CYAN "\ntotal time (second): " << time_elapsed_in_seconds << RESET << "\n\n";

  // write_to_csv();

  timeout_thread.join();

  return exit_code;
}

// -----------------------------------------------------------------------------
// ---------------------------------- MAIN -------------------------------------
// -----------------------------------------------------------------------------

int    _argc    = 0;
char** _argv    = (char**) 0;
char*  exe_name = (char*) 0;

int number_of_remaining_arguments() {
  return _argc;
}

char** remaining_arguments() {
  return _argv;
}

char* peek_argument() {
  if (number_of_remaining_arguments() > 0)
    return *_argv;
  else
    return (char*) 0;
}

char* get_argument() {
  char* argument;

  argument = peek_argument();

  if (number_of_remaining_arguments() > 0) {
    _argc = _argc - 1;
    _argv = _argv + 1;
  }

  return argument;
}

void init_args(int argc, char* argv[]) {
  _argc = argc;
  _argv = argv;
}

void print_usage() {
  std::cout << YELLOW "usage:\n";
  std::cout << "- concrete engine:                               executable -l binary -concrete \"memory\"\n";
  std::cout << "- ase engine\n";
  std::cout << "   bit-vector abstraction:                       executable -l binary -bvt\n";
  std::cout << "   mit, bit-vector abstractions:                 executable -l binary -mit_bvt\n";
  std::cout << "   mit, box, bit-vector abstractions:            executable -l binary -mit_box_bvt \"heuristic\"\n";
  std::cout << "- ase engine with printing witnesses\n";
  std::cout << "   bit-vector abstraction:                       executable -l binary -witness -bvt\n";
  std::cout << "   mit, bit-vector abstractions:                 executable -l binary -witness -mit_bvt\n";
  std::cout << "   mit, box, bit-vector abstractions:            executable -l binary -witness -mit_box_bvt \"heuristic\"\n";
  std::cout << "- ase engine with printing witnesses and timeout\n";
  std::cout << "   bit-vector abstraction:                       executable -l binary -witness -timeout \"seconds\" -bvt\n";
  std::cout << "   mit, bit-vector abstractions:                 executable -l binary -witness -timeout \"seconds\" -mit_bvt\n";
  std::cout << "   mit, box, bit-vector abstractions:            executable -l binary -witness -timeout \"seconds\" -mit_box_bvt \"heuristic\"\n";
  std::cout << RESET << '\n';
}

int main(int argc, char* argv[]) {
  char* option;
  char* exe_name = (char*) 0;
  char* load_file_name = (char*) 0;
  uint64_t running_arg = 0;
  bool print_witness = false;

  init_args(argc, argv);
  exe_name = get_argument();

  if (number_of_remaining_arguments() < 3) {
    print_usage();
  } else {
    option = get_argument();
    if (!strcmp(option, "-l")) {
      load_file_name = get_argument();
      file_name = load_file_name;
    } else {
      print_usage();
      return EXITCODE_BADARGUMENTS;
    }

    option = get_argument();

    if (!strcmp(option, "-witness")) {
      print_witness = true;
      option = get_argument();
    }

    if (!strcmp(option, "-timeout")) {
      timeout = std::atoi(get_argument());
      option = get_argument();
    }

    if (!strcmp(option, "-concrete")) {
      running_arg = std::atoi(get_argument());
      current_engine = new engine();
      current_engine->exe_name = exe_name;
      current_engine->init_engine(running_arg);
      current_engine->selfie_load(load_file_name);
      if (print_witness) current_engine->IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT = true;
      return run();
    } else if (!strcmp(option, "-bvt")) {
      current_engine = new bvt_engine();
      current_engine->exe_name = exe_name;
      current_engine->init_engine(running_arg);
      current_engine->selfie_load(load_file_name);
      if (print_witness) current_engine->IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT = true;
      return run();
    }
    else if (!strcmp(option, "-mit_bvt")) {
      current_engine = new mit_bvt_engine();
      current_engine->exe_name = exe_name;
      current_engine->init_engine(running_arg);
      current_engine->selfie_load(load_file_name);
      if (print_witness) current_engine->IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT = true;
      return run();
    }
    else if (!strcmp(option, "-mit_box_bvt")) {
      char* arg = get_argument();
      running_arg = arg != (char*)0 ? std::atoi(arg) : -1;
      current_engine = new mit_box_bvt_engine();
      current_engine->exe_name = exe_name;
      current_engine->init_engine(running_arg);
      current_engine->selfie_load(load_file_name);
      if (print_witness) current_engine->IS_PRINT_INPUT_WITNESSES_AT_ENDPOINT = true;
      return run();
    }
    else {
      print_usage();
      return EXITCODE_BADARGUMENTS;
    }
  }

  return 0;
}