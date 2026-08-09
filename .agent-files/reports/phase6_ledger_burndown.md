# Phase 6 ledger burn-down

## Before/after

The widened `Z3_Extensions` bucket has 323 cases.  Its stored complete
conformance result (`/tmp/phase6-final-extension/conformance.json`) has 837
scheduled results, all **matched**: 635 pass, 188 expected negative-input
failures, and 14 documented unsupported outcomes.  Thus it has zero
unexpected results and zero implementation-red outcomes.

| theory | pass | expected fail | documented unsupported | total |
| --- | ---: | ---: | ---: | ---: |
| Seq | 275 | 118 | 14 | 407 |
| Set | 231 | 42 | 0 | 273 |
| Bag | 125 | 28 | 0 | 153 |
| P6.4 finiteness boundaries | 4 | 0 | 0 | 4 |
| **total** | **635** | **188** | **14** | **837** |

The mode inventory is 202 `typecheck-only`, 149 `z3-tac`, 25
`proof-parse`, 25 `proof-replay`, five `z3-oracle`, and two `cvc5-oracle`
ledger entries.  `tools/conformance-corpus/v2/phase6_ledger_expectations.json`
is the rerunnable expected-mode ledger used by generation.

The validation audit was regenerated against the current source with
validation commit `995d838` (`HolSmt: audit Phase 6 dialect coverage`).  It
now parses the shared and cvc5-specific dictionaries, uses the corpus slugs
for the shared sequence operators, and does not demand Z3 proof modes for
cvc5-only inputs.  The resulting Phase-6 dictionary/corpus slice has zero
audit findings.  (The unfiltered audit still reports unrelated omissions in
other SMT-LIB theories; they are outside this Phase-6 task.)

## Gate inventory

`phase6_ledger_expectations.json:gate_inventory` lists 14, and only 14, D2
rows.  Each points back to this report.  They are the Seq fold proof inputs
where Z3 returns sat/no proof and the two regexp-replace Seq families where
Z3 returns `unknown`; each has its checked diagnostic in the manifest.
There are no D12 rows.

Every corpus row has the solver/version matrix in its
`solver_availability` field.  Its documentation pointer is
`phase6_ledger_expectations.json:solver_availability_documentation`.
Consequently, unavailable dialect/version cells (in particular cvc5-only
native Set/Bag operations) are solver-availability dispositions rather than
missing Z3 proof obligations.  The TASK_06 external pins remain represented
by those cells and their recorded oracle outcomes.

## Coverage transitions

Ran:

```sh
HOLSMT_ROOT=$PWD python3 "$HOLSMT_VALIDATION_DIR/tools/coverage/generate_smtlib_coverage.py" \
  --coverage "$HOLSMT_VALIDATION_DIR/tools/coverage/smtlib_coverage.json" \
  --manifest "$HOLSMT_VALIDATION_DIR/tools/coverage/coverage_manifest.json" \
  --complete-manifest "$HOLSMT_VALIDATION_DIR/tools/conformance-corpus/v2/manifest.json" \
  --report "$HOLSMT_VALIDATION_DIR/tools/coverage/SMTLIB_COVERAGE.md"
HOLSMT_ROOT=$PWD python3 "$HOLSMT_VALIDATION_DIR/tools/coverage/audit_coverage_manifest.py" \
  --manifest "$HOLSMT_VALIDATION_DIR/tools/coverage/coverage_manifest.json"
```

Generation succeeded and the audit reports 109 coverage rows, 219 manifest
entries, and zero missing obligations.  The three `Sequences, sets, bags`
coverage successors are `implemented` for translation, solve, and
reconstruction; the distinct sets-as-predicates row is unchanged.  The
`ALL` logic and advanced `th-lemma` rows retain the native checked sequence
prover evidence rather than an unsupported claim.

## Build

`bin/build -t --seq=tools/sequences/upto-parallel` completed successfully.
