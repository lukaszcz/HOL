# Phase 6 ledger burn-down

## Before/after

The regenerated `Z3_Extensions` slice contains 323 cases.  The prior
complete manifest contained 549 implementation-red expected outcomes in this
slice; the regenerated manifest contains **0**.  The final mode inventory is
958 pass, 188 expected negative-input fail, and 14 documented unsupported
outcomes.

The fresh filtered replay (`/tmp/phase6-final-extension/conformance.json`)
ran all scheduled modes (`typecheck-only`, `z3-tac`, proof parse/replay, Z3
oracle and cvc5 oracle) and reported **837 matched, 0 unexpected**.  This
includes the expanded Seq/Set/Bag surface and real proof inputs.  The normal
expected failures are malformed/type-error tests, not implementation gates.

| Mode | Result |
| --- | --- |
| typecheck-only | accepted supported surface; negative type tests fail |
| z3-tac | matched including documented D2 outcomes |
| proof-parse / proof-replay | matched including documented D2 outcomes |
| Z3 / cvc5 oracle | matched; solver `unknown` is documented where applicable |

`tools/conformance-corpus/v2/phase6_ledger_expectations.json` is the
rerunnable observed-mode ledger used by the corpus generator.  It removes an
implementation obligation only after recording the mode result.

## Gate inventory

The inventory contains only the two permitted classes.

### D2 gates

The 14 D2 rows are listed individually in
`phase6_ledger_expectations.json:gate_inventory`, with this report as their
documentation pointer.  They comprise Seq fold proof inputs for which Z3
returns sat/has no proof, and the two regexp-replace Seq families for which
Z3 returns `unknown`.  Each has the checked diagnostic substring in the
manifest.  No D12 row is present.

### Solver-availability gates

The per-operator solver/version matrix remains the authoritative
`solver_availability` field on every corpus row.  Its documentation pointer
is `phase6_ledger_expectations.json:solver_availability_documentation`.
Unscheduled dialect/version cells are solver-availability gates, not red
implementation claims.  External pins are therefore represented by their
matrix cells and their actual oracle results.

## Coverage transitions

The three `Sequences, sets, bags` coverage successors now record
`implemented` for translation/solve/reconstruction, with source and corpus
positive evidence for native Seq, predicate-set, and Bag handling.  The
separate predicate-set representation row was not changed.  The `ALL` logic
and advanced `th-lemma` rows now point at the native sequence checked-prover
dispatch instead of the obsolete broad unsupported claim.

The coverage data was regenerated (`tools/coverage/SMTLIB_COVERAGE.md`).
The standalone complete coverage audit in this worktree stops while parsing
`SmtLib_Logics.sml` because this validation checkout expects the removed
`parsedicts_of_logic` expression; this is a validation/source checkout skew,
not a Seq/Set/Bag obligation.  Corpus generation validation and the complete
extension replay above both pass.

## Build

`bin/build -t --seq=tools/sequences/upto-parallel` completed successfully
before the ledger regeneration.
