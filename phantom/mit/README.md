## SE using Modular Interval Theory
- **mit.c**: the implementation of SE using modular interval theory as backend (old approach)
- **sase.c**: the implementation of SE using boolector smt solver as backend (**old approach**)
- **phantom.c**: source file which includes subset of selfie.c

#### How to compile:
**prerequisite**: boolector smt solver should be installed first.
```
make;
cd compiler;
make;
```
#### How to execute:
SE using "mit":
```
./selfie -c code.c -o code
./phantom -l code -i 0
```
SE using bvt (only SMT):
```
./selfie -c code.c -o code
./phantom -l code -k 0
```

Careful: input syscall in source code should be defined as:
```
x = input(lo, up, step);
```

#### Sample Benchmarks:
can be found in test folder.