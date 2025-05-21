# README

This repository contains the Coq development of our paper on effectful higher-order logic at LICS'25. To build, with a running Coq installation simply run `make` from the root folder. The code has been implemented using v8.20.1 of Coq.

## File overview:

- `hopl.sig`: the signature used to generate the syntax with Autosubst
- `core.v`, `core_axioms.v`, `unscoped.v`, `unscoped_axioms.v`: Autosubst boilerplate files
- `syntaxl.v`: the generated syntax file
- `HOL.v`: type system and deduction system of HOL
- `EffHOL.v`: type system and deduction system of EffHOL
- `EffHOL_to_HOL.v`: forgetful translation from EffHOL to HOL
- `HOL_to_EffHOL.v`: the realizability translation from HOL to EffHOL
- `EffHOL_to_Fw.v`: syntactic instantiations and correctness theorems

## Notes about the formalisation:
- We don't have the base membership formulas to avoid redundancy.
- Type-level conversion is defined by reduction first.
- The HOPL deduction system is untyped for simplicity.
- We just have the minimal reduction rules.