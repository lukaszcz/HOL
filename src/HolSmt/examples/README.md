# HolSmt examples

These examples show `HolSmtLib` as it is normally used in a HOL4
development.  Each file is a complete theory that can be copied, edited, and
built independently.

## Prerequisites

Install a supported Z3 4.x release and set `$HOL4_Z3_EXECUTABLE` to its
path.  Install cvc5 1.3.4 as well to build the cvc5 example.  HolSmt checks
`$HOL4_CVC_EXECUTABLE`, then `$CVC5`, then looks for `cvc5` on `$PATH`.
The exact tested solver versions and feature coverage are documented in the
parent [`README`](../README).

From this directory, build every example with:

```sh
Holmake
```

To build one example while experimenting, name its theory:

```sh
Holmake HolSmtArithmeticTheory
```

For example, a shell session using explicit solver paths might start with:

```sh
export HOL4_Z3_EXECUTABLE=/path/to/z3
export HOL4_CVC_EXECUTABLE=/path/to/cvc5
Holmake
```

## Where to start

| File | What it demonstrates |
| --- | --- |
| `HolSmtBasicsScript.sml` | Checked tactics, assumptions, quantifiers, and supplying lemmas |
| `HolSmtApiScript.sml` | `term -> thm` functions and the checked/oracle distinction |
| `HolSmtArithmeticScript.sml` | Natural, integer, real, linear, and nonlinear arithmetic |
| `HolSmtFunctionsScript.sml` | Uninterpreted functions, arrays, extensionality, and lambdas |
| `HolSmtDataScript.sml` | User datatypes, records, options, and case expressions |
| `HolSmtCollectionsScript.sml` | Lists/sequences and sets |
| `HolSmtWordsScript.sml` | Fixed-width bit-vector operations |
| `HolSmtStringsScript.sml` | Native SMT Unicode strings and regular languages |
| `HolSmtFloatingPointScript.sml` | Native SMT floating-point terms |
| `HolSmtCvc5Script.sml` | Checked cvc5 tactics, bags, lemmas, and `CVC_PROVE` |

## The usual workflow

Load and open the library, then use the checked tactic in a proof:

```sml
open HolKernel Parse boolLib bossLib;
open HolSmtLib;

Theorem order_example:
  (x : int) <= y /\ y <= z ==> x <= z
Proof
  Z3_TAC
QED
```

`Z3_TAC` and `CVC_TAC` request solver proofs and replay them in HOL.  Prefer
these checked tactics in finished developments.  `z3_tac [thm1, thm2]` and
`cvc_tac [thm1, thm2]` add existing HOL theorems to the solver context,
similarly to `metis_tac [...]`.

`Z3_PROVE tm` and `CVC_PROVE tm` are useful when Standard ML code needs a
theorem directly.  They have type `term -> thm`.  The `*_ORACLE_TAC` and
`*_ORACLE_PROVE` variants trust the external solver and mark their results
with a `HolSmtLib` oracle tag.  The API example uses one deliberately so the
trust boundary is visible.

## Public API at a glance

| Operation | Checked | Uses supplied theorems |
| --- | --- | --- |
| Z3 tactic | `Z3_TAC` | `z3_tac [thms]` |
| cvc5 tactic | `CVC_TAC` | `cvc_tac [thms]` |
| Z3 theorem function | `Z3_PROVE tm` | — |
| cvc5 theorem function | `CVC_PROVE tm` | — |

The oracle equivalents are `Z3_ORACLE_TAC`, `z3o_tac [thms]`,
`Z3_ORACLE_PROVE`, `CVC_ORACLE_TAC`, `cvco_tac [thms]`,
`CVC_ORACLE_PROVE`, `YICES_ORACLE_TAC`, and `YICES_ORACLE_PROVE`.  The Yices
interface requires legacy Yices 1 rather than Yices 2, and has no proof
reconstruction: `YICES_TAC` and `YICES_PROVE` therefore fail closed.  The
checked Z3 and cvc5 paths are the recommended starting point.

`GENERIC_SMT_TAC` is the low-level adapter for integrating another solver;
ordinary proof developments do not need it.  The `include_theorems` reference
controls whether HolSmt adds its background HOL theorems and is primarily a
debugging tunable.  Leave it at its default for normal proofs.

## When a tactic fails

HolSmt proves a goal by asking whether its assumptions together with the
negated conclusion are unsatisfiable.  If the formula is satisfiable, the
tactic fails; this often means the proposed theorem is false.  For example,
this is not a theorem over integers:

```sml
Theorem false_claim:
  (x : int) + y = 0 ==> x = 0
Proof
  Z3_TAC
QED
```

The failure reports that the negated goal is satisfiable.  HolSmt does not
currently turn the solver model into a HOL counterexample theorem.

An `unknown` result usually means that the goal is outside the selected
solver's fragment, needs unsupported proof-replay rules, or is too hard.
Simplify the goal, supply relevant lemmas, or try the other checked solver.
Use an oracle only when its larger trust boundary is acceptable.

## Seeing the generated query

Tracing is helpful when a supported-looking term is translated as an
uninterpreted symbol or a solver rejects the generated query:

```sml
val _ = Feedback.set_trace "HolSmtLib" 4;
```

Higher levels show more translation detail and temporary file names.  Reset
the trace after debugging:

```sml
val _ = Feedback.reset_trace "HolSmtLib";
```

The authoritative operator-by-operator support contract is the coverage
matrix referenced by the parent [`README`](../README); solver capabilities
are not interchangeable, especially for collections, higher-order terms,
strings, and floating point.
