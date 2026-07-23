# Phase 3 exit audit

Audit date: 2026-07-23

Source checkout:
`/home/lukasz/dev/HOL/worktrees/smt`

Validation checkout:
`$HOLSMT_VALIDATION_DIR`

This audit applies the eight criteria in `PLAN_phase_3.md` section 10
without narrowing them.  The COMPLETE corpus still contains obligations
for later SMT-LIB phases; those are outside this phase audit.  Every
Phase-3 row is green except the two explicitly permitted, enumerated
Z3 proof-rule residues recorded below.

## 1. Complete conformance and red-first burn-down

Status: **PASS, with two permitted per-rule obligations.**

- The final complete-conformance report records zero unexpected
  regressions and zero infrastructure errors across 5,314 classified
  results.
- It retains 1,213 enumerated nonblocking obligations from the full
  multi-phase corpus; the function-sorts category contains exactly the
  two permitted rows below.
- The only red cases carrying any of the `function-sort`,
  `function-valued`, `higher-order`, `lambda`, or `ho-core` needles are:
  - `proof-rule:ho:lambda-equality`: checked `z3-tac` stops at the
    precise `proof rule: rewrite` diagnostic.
  - `proof-rule:ho:lambda-under-quantifier`: checked `z3-tac` stops at
    the precise `failed to parse 'pull-quant'` diagnostic.
- Both rows carry `implementation_obligation` records naming the replay
  files, test ID, failure phase, and endpoint-version reproduction.

Evidence:

- `$HOLSMT_VALIDATION_DIR/tools/conformance-corpus/v2/manifest.json`
- `/tmp/holsmt-phase3-closure-complete-final-v2/`
- `$HOLSMT_VALIDATION_DIR/tools/run_complete_smtlib_conformance.sh`

Phase-blocking obligations: none.  The two `proof-rule:*` rows above
are the C4 residue explicitly allowed by this criterion; there is no
theory/surface/logic residue in the function-sorts bucket.

## 2. Coverage matrix

Status: **PASS.**

- `HO-Core` is classified as SMT-LIB 2.7, all five phase columns are
  `implemented`, and COMPLETE status is `reconstructed`.
- All ten extension logics (`HO_ALL`, `HO_UF`, `HO_QF_UF`, `HO_UFLIA`,
  `HO_QF_UFLIA`, `HO_UFLRA`, `HO_QF_UFLRA`, `HO_AUFLIA`,
  `HO_AUFLIRA`, `HO_QF_AUFLIA`) are `implemented` and
  `reconstructed`.
- The old higher-order scope deferral is gone.  The
  `theory:HO_Core:native-function-sort` case is SMT-LIB 2.7 and green
  in parser, typechecker, and checked `z3-tac` modes.
- Coverage matching keeps proof-rule cases on proof-rule rows, so the
  permitted residues do not incorrectly make the HO-Core theory row
  red.

Evidence:

- `$HOLSMT_VALIDATION_DIR/tools/coverage/SMTLIB_COVERAGE.md`
- `$HOLSMT_VALIDATION_DIR/tools/coverage/smtlib_coverage.json`
- `$HOLSMT_VALIDATION_DIR/tools/coverage/coverage_manifest.json`
- `$HOLSMT_VALIDATION_DIR/tools/coverage/audit_coverage_manifest.py`
- `$HOLSMT_VALIDATION_DIR/tools/tests/test_audit_coverage_manifest.py`

Blocking obligations: none.

## 3. Standard SMT-LIB 2.7 higher-order surface

Status: **PASS.**

- The HO-Core corpus covers `lambda`, `->` sorts, `_` and `@`
  application, omission sugar, curried map sorts, and map-term partial
  application.
- The ranked-symbol partial-application row is an expected failure with
  the section 3.9 teaching diagnostic.
- FO-logic negative rows cover lambda, arrow sorts, and application
  with precise A4 fragment diagnostics.  Deterministic unit tests also
  cover the partial-application fragment flag.

Evidence:

- `$HOLSMT_VALIDATION_DIR/tools/conformance-corpus/v2/manifest.json`
- `src/HolSmt/Unittest.sml`:
  `smtlib_higher_order_fragment_enforcement`,
  `smtlib_partial_application_success`, and the lambda/apply tests
- `src/HolSmt/SmtLib_Parser.sml`
- `src/HolSmt/SmtLib_Logics.sml`

Blocking obligations: none.

## 4. First-order byte identity

Status: **PASS.**

- `smtlib_fo_emission_golden_success` still checks representative
  arithmetic, bit-vector, array, quantifier, and function-valued goals
  under both ordinary and proof-producing emission.
- Every case asserts that the selected regime remains `FirstOrder` and
  compares the full emitted line list byte-for-byte.
- Complete conformance reports zero unexpected regressions.

Evidence:

- `src/HolSmt/Unittest.sml`:
  `smtlib_fo_emission_golden_success`
- `src/HolSmt/SmtLib.sml`: failure-driven regime selection
- `/tmp/holsmt-phase3-closure-complete-final-v2/`

Blocking obligations: none.

## 5. Checked Z3 replay

Status: **PASS, with the two criterion-1 per-rule obligations.**

- The six-case C1 corpus is recorded for Z3 4.11.2, 4.12.4, 4.13.0,
  4.14.1, and 4.15.3.
- Four shapes are green under direct checked `z3-tac` replay.  The two
  resisting shapes are the precise `proof-rule:*` obligations listed
  in criterion 1, reproduced at the oldest and newest endpoints.
- `selftest.sml` exercises lambda, beta/eta, ranked partial
  application, and binder congruence under `thm_Z3p` and
  `thm_Z3p_v4`; theorem acceptance runs `check_oracle_tags`.

Evidence:

- `$HOLSMT_VALIDATION_DIR/tools/proof-corpus/complete/manifest.json`
- `$HOLSMT_VALIDATION_DIR/tools/proof-corpus/complete/summary.json`
- `$HOLSMT_VALIDATION_DIR/tools/record_z3_proof_corpus.py`
- `src/HolSmt/selftest.sml`, higher-order and lambda bands
- `src/HolSmt/Z3_ProofParser.sml`
- `src/HolSmt/Z3_ProofReplay.sml`

Phase-blocking obligations: none.  The permitted residue is
`proof-rule:ho:lambda-equality` and
`proof-rule:ho:lambda-under-quantifier`.

## 6. cvc5 oracle and checked CPC replay

Status: **PASS.**

- The cvc5 1.3.4 HO corpus contains 9/9 successful native queries,
  155 proof steps, and 30 rules.
- The higher-order `selftest.sml` band proves under `thm_CVCp`;
  theorem acceptance checks hypotheses, conclusion, and oracle tags.
- The ten-logic extension band is green in its declared
  `cvc5-oracle` modes.  The two standard underscore-apply rows are
  precise expected cvc5 dialect failures, not implementation gaps.
- `tools/cvc5-version-matrix.md` contains the HO version row.
- The `_`-apply divergence report is drafted.

Evidence:

- `$HOLSMT_VALIDATION_DIR/tools/cpc-ho-corpus/cvc5-1.3.4/report.json`
- `$HOLSMT_VALIDATION_DIR/tools/cvc5-version-matrix.md`
- `src/HolSmt/selftest.sml`, `thm_CVCp` higher-order band
- `.agent-files/reports/PHASE3_cvc5_underscore_apply_upstream.md`

Blocking obligations: none.  The corpus's two CPC `trust` steps are
reproved by the checked HOL handler and are not oracle admissions.

## 7. Five-version Z3 proof recordings

Status: **PASS.**

- The complete proof corpus contains the six HO cases and names all
  five supported Z3 anchors.
- Per-version summaries and rule-gate reports exist for 4.11.2,
  4.12.4, 4.13.0, 4.14.1, and 4.15.3.
- `record_z3_proof_corpus.py` fixes the HO case-ID set and validates
  that every required case is present.
- The final five-version verification also records why the satisfiable
  proof-enabled HO witness is limited to Z3 4.11: 4.12--4.15 report
  that no proof is available, while all checked theorem/replay tests
  remain enabled across the five anchors.

Evidence:

- `$HOLSMT_VALIDATION_DIR/tools/proof-corpus/complete/`
- `$HOLSMT_VALIDATION_DIR/tools/proof-corpus/complete/summary.json`
- `$HOLSMT_VALIDATION_DIR/tools/record_z3_proof_corpus.py`
- `$HOLSMT_VALIDATION_DIR/tools/tests/test_record_z3_proof_corpus.py`

Blocking obligations: none.

## 8. Build, tests, CI, and documentation

Status: **PASS.**

- The full source build, both-solver sharded selftest, complete
  conformance, default conformance, and five-version Z3 gate pass; see
  the verification table below.
- The coverage generator unit tests and enforcing audit pass.
- Both validation-repository workflows check out the exact pinned
  HolSmt source revision.  Their conformance lanes provision cvc5;
  Docker lanes mount the separately versioned validation checkout,
  and validation accepts the Docker image's
  `HOL4_CVC_EXECUTABLE` contract.
  Both workflow files parse as YAML and their local command
  equivalents are covered by the gates below.  Remote run status is
  available only after the commits are pushed.
- `src/HolSmt/README` contains the HO support rows and the ten
  extension logics, and its stale rejection prose has been replaced by
  the actual two-regime trigger.
- `src/HolSmt/TRUSTED_CODE_BASE.md` and the canonical README audit
  describe the trusted Z3 lowering, map/array equivalence, and
  HOL-provable eta expansion.
- `release-notes/next-release.md` records the higher-order surface and
  checked replay feature.

Evidence:

- `.github/workflows/holsmt-contract.yml` in the validation checkout
- `.github/workflows/holsmt-external-benchmarks.yml` there
- `src/HolSmt/README`
- `src/HolSmt/TRUSTED_CODE_BASE.md`
- `release-notes/next-release.md`

Blocking obligations: none.

## Verification

- `tools/run_selftest.sh --keep-going`: **PASS** — Z3 4.15.3 and
  cvc5 1.3.4; 8/8 shards.
- `tools/run_complete_smtlib_conformance.sh`: **PASS** — 5,314
  classified results, 0 unexpected, function-sorts bucket 2.
- `python3 tools/run_conformance_suite.py`: **PASS** — 310 cases and
  1,230/1,230 conforming results.
- `bin/build -t --seq=tools/sequences/upto-parallel`: **PASS** —
  `Hol built successfully`.
- `tools/verify_z3_versions.sh`: **PASS** — 5/5 versions; report at
  `/tmp/holsmt-phase3-z3-matrix-final/report.json`.
- Validation tools and coverage audit: **PASS** — 109 tests, 108 rows,
  216 entries, and 0 missing obligations.
