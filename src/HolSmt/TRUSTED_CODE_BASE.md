# HolSmt trusted translation note

The canonical trusted-code-base and soundness audit is maintained in the
`Trusted-code-base boundary and soundness audit` section of `README`.  This
focused note records the higher-order translation boundary.

HolSmt's failure-triggered higher-order regime has two printers.  Standard27
emits SMT-LIB 2.7 HO-Core arrows, lambdas, and application for cvc5.
Z3LambdaArray lowers a map `A -> B` to `Array A B`, map application to
`select`, and nested maps to nested arrays.  This lowering is trusted
translation code.

The lowering preserves the relevant semantics because SMT-LIB 2.7 section
3.9 maps and Z3 arrays are both total, extensional maps: application is
selection and map equality is extensional equality.  Partially applied
ranked constants are eta-expanded.  That expansion is independently
HOL-side-provable by the eta theorem `f = (\x. f x)`; it is not a solver
axiom.

Neither printer creates an oracle path.  `Z3_TAC` and `CVC_TAC` must replay
the solver proof to the original HOL goal and reject unexpected oracle tags.
See `README` for the complete parser, replay, solver-process, and HOL-kernel
boundary.
