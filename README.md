# multi-kleene-algebra

This project has been checked to compile properly with `The Coq Proof Assistant, version 8.20.1`, working on a `Manjaro Linux 25.0.8` system.

To compile, first call 
```
coq_makefile -f _CoqProject -o CoqMakefile
```
 to generate the `CoqMakefile` file.
Then, the standard build option are available, as documented on [rocq-prover.org](https://rocq-prover.org/doc/master/refman/practical-tools/utilities.html#building-a-rocq-project-with-rocq-makefile-details).
We recommend the following code, to compile the sources and generate the documentation in directory `html/`:
```
make -f CoqMakefile gallinahtml
``` 
