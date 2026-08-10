# Phase 6 exit audit: Seq/Set/Bag

Date: 2026-08-10

This audit applies `.agent-files/PLAN_phase_6.md` section 11.  Phase 6 is
closed: all remaining non-pass outcomes are the enumerated D2 or
solver-availability dispositions permitted by section 8.

## Evidence base

- Operator and version evidence:
  `.agent-files/reports/seq_set_bag_operator_matrix.md`.
- Z3 and cvc5 proof evidence:
  `.agent-files/reports/phase6_proof_shape_inventory.md`.
- Ledger, coverage, and complete-conformance evidence:
  `.agent-files/reports/phase6_ledger_burndown.md`.
- Validation revision: `holsmt-validation` `995d838`.

## Exit criteria

### 1. Widened bucket and admissible gates — PASS

The 323-case widened bucket has 837 scheduled results: 635 pass, 188 expected
negative-input failures, and 14 documented unsupported outcomes.  It has zero
unexpected and zero implementation-red results.  The 14 residues are all D2
entries in `phase6_ledger_expectations.json:gate_inventory`; every unavailable
solver/dialect/version cell instead cites the operator matrix as a
solver-availability disposition.  There are no D12 or unclassified gates.

Evidence: `phase6_ledger_burndown.md`, especially its gate inventory, and the
matrix report.

### 2. Coverage and advanced Seq replay — PASS

The coverage generator and manifest audit report 109 coverage rows, 219
manifest entries, and zero missing obligations.  The three Seq/Set/Bag
successors are `implemented`/`reconstructed`; the separate sets-as-predicates
row is unchanged.  The `ALL` row and advanced `th-lemma` row record the native
checked Seq dispatcher.

Evidence: `phase6_ledger_burndown.md` and
`$HOLSMT_VALIDATION_DIR/tools/coverage/SMTLIB_COVERAGE.md`.

### 3. Z3 checked replay and oracle boundary — PASS

The five-anchor corpus has checked genuine Seq, Array-encoded Set, and
Array-Int Bag replay.  The Z3 captures and selftests check every reconstructed
theorem with `Library.check_oracle_tags`; no checked path uses an oracle.

Evidence: `phase6_proof_shape_inventory.md` (TASK_10, TASK_14, and TASK_19)
and the eight-shard both-solver selftest at `/tmp/phase6-exit-selftest`.

### 4. cvc5 CPC and the finiteness guard — PASS

The frozen cvc5 1.3.4 corpus replays all 17 Seq, 21 Set, and 20 Bag inputs
through CPC without oracle or resource gates.  The two P6.4 boundary rows
exercise both finite native emission and the quantified plain-array fallback.

Evidence: `phase6_proof_shape_inventory.md`,
`phase6_ledger_burndown.md`, and the P6.4 rows in the v2 manifest.

### 5. Per-operator and per-version semantics — PASS

The generated matrix records each operator's dialect, result sort/probe edge,
Z3 4.11.2/4.12.4/4.13.0/4.14.1/4.15.3 cells, cvc5 1.3.4 cell, counterpart,
and raw-transcript pointer.  It distinguishes documented and
reverse-engineered Z3 semantics.

Evidence: `seq_set_bag_operator_matrix.md` and its raw JSON transcript.

### 6. Gates and documentation — PASS

`bin/build -t --seq=tools/sequences/upto-parallel` passed.  The full
both-solver sharded selftest passed 8/8 shards.  The recorded complete
conformance closure has zero unexpected regressions; the current closure
rerun regenerated the corpus and passed parser, both typecheck, both oracle,
proof-parse, and proof-replay bands before the long whole-corpus `z3-tac`
band exceeded the local command time limit.  It does not alter the recorded
complete result because no compiled source changed after that result.

README, the trusted-code-base note, and release notes now describe the
per-theory dialects, checked boundaries, and native-by-default outcome.

## Risk disposition and owner escalation

- **Risk 5 (P6.4 fallback rate):** the Phase-6 corpus has two boundary cases:
  one finite-native and one non-finite fallback case for each of Set and Bag,
  so the intentional boundary sample is 2/4 native and 2/4 fallback.  This is
  coverage evidence, not a production-use rate.  Recommendation: retain the
  guard and collect real goal telemetry before widening entailment.
- **Risk 6 (D2 tail):** 14 explicit D2 mode rows remain: fold/sequence
  no-theorem outcomes and the two regexp-replace sequence families returning
  `unknown`.  Options are (a) retain the enumerated gates, (b) fund solver or
  prover work for those shapes, or (c) narrow the advertised surface.
  Recommendation: retain them; they are small, classified, and no oracle is
  admitted.  **Owner question:** accept these 14 D2 dispositions for the
  current support contract?

## D11 review

TASK_12 required no bridge constants: all implemented Bag operators use stock
`bagTheory` counterparts and support lemmas in `HolSmtScript.sml`.  Therefore
there is no accumulated support theory to promote and no D11 owner decision
point to raise.
