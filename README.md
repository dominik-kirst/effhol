# README

This repository contains the Coq development of our paper submitted for review. To build, with a running Coq installation simply run `make` from the root folder. The code has been implemented using v8.20.1 of Coq.

## File overview:

- `hopl.sig`: the signature used to generate the syntax with Autosubst
- `core.v`, `core_axioms.v`, `unscoped.v`, `unscoped_axioms.v`: Autosubst boilerplate files
- `hopl.v`: the generated syntax file
- `translation.v`: the realizability translation, including typing judgements and deduction systems
- `instantiations.v`: syntactic instantiations and correctness theorems