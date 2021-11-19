# Abstract Symbolic Execution (ASE) Engine

ASE is a symbolic execution engine which works on a subset of RISC-V (compiled from [C*](https://github.com/cksystemsteaching/selfie) programming language). The engine uses a decision procedure which is based on *strided value interval* abstraction domain and *bit-vectors*.

Here is a program written in C*:
```
uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  interval(&a, 0, 100, 1);
  c = a / 2;
  b = a - 10;
  if (b <= 10) {
    c = c + 1;
  } else {
    c = c - 1;
  }

  return 0;
}
```
A symbolic value in this program is determined by `interval(&a, 0, 100, 1)` which assigns integer value interval of `<0, 100, 1>` (values from 0 to 100 with step 1) to memory address `&a`.

This program is first compiled into a subset of RISC-V using the compiler provided in the `compiler` folder. Then, the generated binary can be analyzed by the ASE engine symbolically and witnesses for each path of the program can be printed at each endpoint of the program.

## How to install the ASE engine:
Please check `INSTALL.md` file.

## General Usage:
The engine can analyze programs written in the [C*](https://github.com/cksystemsteaching/selfie) programming language. You can see the available benchmarks in `benchmarks` folder. For more information about C* refer to https://github.com/cksystemsteaching/selfie.

A symbolic value can be defined as `interval(memory_address, lower_bound, upper_bound, step)`, for example:
```
uint64_t a;
interval(&a, 0, 1000, 1);
```
where `interval(&a, 0, 1000, 1)` assigns integer value interval of `<0, 1000, 1>` (values from 0 to 1000 with step 1) to memory address `&a`.
```
uint64_t b;
b = malloc(10 * 8);
interval(b, 0, 1000, 1);
```
where `interval(b, 0, 1000, 1)` assigns integer value interval of `<0, 1000, 1>` (values from 0 to 1000 with step 1) to memory address `b`.

Once you have written a program in C*, first the input program should be compiled to binary using the command below:
```
./selfie -c code.c -o binary
```

Then, the generated binary should be passed to the ASE engine as input by using the `-l` flag. You can see list of different approaches provided in the ASE engine by running:
```
./ase -h
```

#### Configuration parameters:
To run the engine on very large input programs you may need to increase the configuration parameters in `ase.hpp` file of the source code and then rebuild the source code:

- max_trace_length: the maximum length of the trace used by the engine.
- max_ast_nodes_trace_length: the maximum length of the AST (Abstract Syntax Tree) nodes trace.
- initial_ast_nodes_trace_length: the initial length of the AST nodes trace.
- max_number_of_intervals: the maximum number of value intervals used to represent the set of values for a variable.
- max_number_of_involved_inputs: the maximum number of involved input values in a variable.
- memory_allocation_step_ast_nodes_trace: the memory allocation step for AST nodes trace.
