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

Native Unicode string printing is also part of the trusted translation
surface.  `smtstringTheory` supplies the HOL-checked UnicodeStrings and
RegLan definitions.  Its `smtstr` carrier is a HOL type definition over the
code-point-bounded `num list`s, so SMT `String` is a distinct HOL type whose
universe is exactly the SMT-LIB String universe: `wfstr` holds of every
`:smtstr`, and binders need no wellformedness relativization in either
translation direction.  `SmtLib_String_Literal.sml` chooses and emits the
corresponding SMT-LIB literal encoding, wrapping decoded code-point payloads
in `SmtStr`.  The definitions, derivative engine, and correspondence lemmas
are checked in HOL; trust attaches to choosing those definitions as the
SMT-LIB meanings and to the decoder/encoder that crosses the textual
boundary.  Z3's reverse-engineered internal string symbols are defined in
`smtstringz3Theory`, then their emitted clauses are re-proved in HOL rather
than assumed.

Native FloatingPoint printing is also part of the trusted translation
surface.  `smtfloatTheory` defines the canonical-NaN `smtfp` carrier and the
SMT-LIB FloatingPoint operations.  Trust attaches to choosing these
definitions as the SMT-LIB meanings: in particular, the RNA rounding rule,
the totalizations of min/max/rem and the conversions, the specified choices
for SMT-LIB's underspecified results, and the one chosen canonical NaN.

The carrier is a HOL type definition over exactly the canonical floats, not
an assumed quotient.  Its exact-universe property, the `smtfp_intro`
transfer kit for native `binary_ieee` terms, and the word-level and staged
circuit correspondence lemmas are proved in HOL.  They are not trusted
axioms.  The transfer kit covers the enumerated invariant operation surface;
a residual raw `float`, including raw record equality, is emitted using an
uninterpreted sort and is never treated as an SMT FloatingPoint value.

`SmtResource.sml` is the single budget module for checked FP replay.  It
defines the fixed D12 limits: 16 MiB of proof text before parsing, 10 seconds
per bit-blast step, and 200,000 term nodes.  A limit breach is an explicit
`resource-gated: fp-bitblast;` outcome, distinct from the D2 unsupported-
shape diagnostic; neither outcome accepts a theorem.

Replay uses the certifying `binary_ieeeLib`/Arbrat evaluation path.
`native_ieeeLib`, `fp64_machineLib`, and hardware evaluation are never
enabled in replay because they produce oracle-tagged theorems.  Every
accepted Z3 or cvc5 theorem is checked for unexpected oracle tags.

## Seq/Set/Bag boundary

Native Seq, Set, and Bag translation adds no trusted axiom or oracle path.
The HOL models are respectively lists, predicates, and bags; their operators
are stock HOL definitions or proved transfer lemmas.  Z3 bags are emitted as
an `Array a Int` encoding, with `(_ map ...)` used for pointwise bag
operations.  That encoding is a definitional translation choice, not an
assumed bag theory: array/count correspondence and arithmetic side conditions
are reconstructed in HOL where the replay supports the emitted array
lemmas.  Z3 Bag proofs that require unsupported array lemmas remain
oracle-only and are not accepted by checked `Z3_TAC`.

The cvc5 native Set/Bag dialect is finite.  Native emission is selected by
an ML-side eligibility check: structural finiteness, finite element types, or
an existing `FINITE`/`FINITE_BAG` assumption.  Such assumptions select the
finite model and are omitted from the serialized SMT assertions; this is a
translation-correctness obligation, not generated HOL evidence.  Otherwise,
HolSmt uses the quantified plain-array fallback.  `set.card` and `bag.card`
require native-backend eligibility and are rejected otherwise (and are
unavailable on Z3).  Both paths replay the solver proof and reject unexpected
oracle tags.
