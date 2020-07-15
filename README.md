# Abstract Symbolic Execution Engine

## Prerequisite
[Boolector](https://boolector.github.io) SMT solver.

## Build
#### build compiler:
```
make selfie
```
#### build symbolic execution engine:
```
make ase
```

## Usage
#### compile source code:
```
./selfie -c code.c -o code
```
#### run symbolic execution engine:
```
./ase -h
```