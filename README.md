IFPL
====

implementing interesting stuff from Simon Peyton-Jones' "Implementation of Functional Programming Languages".

This project has slowly mutated into an attempt to implement as much of a Haskell/Miranda-like language as I can. 

So far, we have:

ELC.hs An enriched lambda calculus (analogous to Haskell's Core, if I understand correctly)
which compiles to
LC.hs plainer, simpler lambda calculus, with an interpreter.
which can be further compiled to
SKI.hs The SKI combinatory calculus (plus a fixpoint combinator), also with an interpreter.
The LC to SKI translation is in LCtoSKI.hs

Shared definitions and an evaluator for constant terms and built-in functions are in Constants.hs.
Utilities for working with variables are in Variables.hs