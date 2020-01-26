## SE using "modular interval theory + bit-vector theory"
- **mit.c**: the implementation of SE using "mit + bvt" as backend
- **sase.c**: the implementation of SE using boolector smt solver as backend
- **phantom.c**: source file which includes subset of selfie.c

#### How to compile:
**prerequisite**: boolector smt solver should be installed first.
```
make
make selfie
```
#### How to execute:
SE using "mit + bvt" with eager approach to send queries to SMT:
```
./selfie -c code.c -o code
./phantom -l code -i 0
```
SE using "mit + bvt" with lazy approach to send queries to SMT:
```
./selfie -c code.c -o code
./phantom -l code -lazy step -i 0
```
SE using bvt (only SMT):
```
./selfie -c code.c -o code
./phantom -l code -k 0
```

Careful: input syscall in source code should be defined as:
```
input(&x, lo, up, step);
```
where the first argument is the address of x.

#### Sample Benchmarks:
can be found in test folder.