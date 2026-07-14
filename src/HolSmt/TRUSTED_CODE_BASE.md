# HolSmt Trusted-Code-Base Boundary

This note documents the checked boundary for `Z3_TAC`. It is an audit guide,
not a completeness claim. The generated coverage report
`$HOLSMT_VALIDATION_DIR/src/HolSmt/tools/coverage/SMTLIB_COVERAGE.md` contains the cross-referenced
support and semantic-mismatch matrix. The report is generated from
`$HOLSMT_VALIDATION_DIR/src/HolSmt/tools/coverage/smtlib_coverage.json` plus manifest-backed evidence
in `$HOLSMT_VALIDATION_DIR/src/HolSmt/tools/coverage/coverage_manifest.json`; tested support rows must
carry executable test IDs, and unsupported rows must carry diagnostic test IDs.

## Checked `Z3_TAC` Path

`Z3_TAC` is `HolSmtLib.GENERIC_SMT_TAC Z3.Z3_SMT_Prover`.

For a theorem-producing result, the trusted path is:

- `src/HolSmt/SmtLib.sml`: translates the HOL goal to SMT-LIB and records the
  selected logic, emitted symbols and HOL theory encodings.
- `src/HolSmt/SmtLib_Datatypes.sml`: elaborates SMT-LIB datatype
  declarations to HOL datatypes and builds selector/tester case expressions.
- `src/HolSmt/Z3.sml`: invokes the configured Z3 executable, requests proof
  output, parses only `unsat` proof-producing results and calls
  `Library.check_oracle_tags` on the reconstructed theorem.
- `src/HolSmt/Z3_ProofParser.sml`: parses Z3 proof terms through the versioned
  proof-rule registry and rejects unknown rules.
- `src/HolSmt/Z3_ProofReplay.sml`: replays supported proof rules in HOL and
  reports unsupported theory-lemma families with explicit diagnostics.
- HOL kernel, primitive inference rules, accepted HOL theories and trusted
  external process execution are part of the surrounding HOL4 TCB.

`Z3_ORACLE_TAC` and `Z3.Z3_SMT_Oracle` are outside this checked boundary. The
generic tactic's `UNSAT NONE` oracle branch is not an acceptable result for
`Z3_TAC`; `Z3.Z3_SMT_Prover` must return `UNSAT (SOME thm)` after proof replay.

Nonlinear real arithmetic replay may invoke CSDP through `SOSLib.REAL_SOS`.
CSDP is an untrusted semidefinite-solver dependency: it searches for SOS
certificates, while HOL checks the resulting certificate before any theorem is
accepted. If CSDP is unavailable, checked replay must fail with the explicit
dependency diagnostic rather than use an oracle or skip replay.

## CI and Regression Gate

The HolSmt selftest target is the CI gate for this boundary:

- `src/HolSmt/selftest.sml` checks that theorem-producing Z3 proof tests return
  the requested theorem and have no unexpected oracle or axiom tags.
- `src/HolSmt/Z3.sml` checks tags immediately after `Z3_SMT_Prover` replay.
- `src/HolSmt/Unittest.sml` contains deterministic regressions for the tag gate,
  parser/typechecker audit edges, and `sat`/`unknown` negative outcomes.

Any accepted `Z3_TAC` theorem with an unexpected oracle tag is a test failure.

## Semantic Mismatches and Obligations

The explicit list is generated in
`$HOLSMT_VALIDATION_DIR/src/HolSmt/tools/coverage/SMTLIB_COVERAGE.md` under `Soundness Audit and
Semantic Mismatches`. Current manifest-backed audit items include:

- binder scoping, shadowing, quoted identifiers and local definitions;
- indexed and parametric sort reconstruction;
- SMT-LIB division-by-zero underspecification versus HOL encodings;
- bit-vector division, remainder, overflow, shift and rotation edge cases;
- FloatingPoint NaN, infinity and rounding-mode semantics;
- HOL char-list strings versus SMT-LIB UnicodeStrings and regex languages;
- ArraysEx select/store versus current HOL function encoding;
- SMT-LIB datatype selectors are total but underspecified on constructors that
  do not own the selector.  The HOL encoding chooses the `ARB` value for those
  branches, which is one concrete interpretation of the SMT-LIB semantics.
  An SMT `unsat` result holds for all such interpretations, so this HOL
  instance preserves checked replay soundness.
- `sat` and `unknown` solver results as non-theorem-producing outcomes.

For each item, accepted reconstruction needs a checked proof path, a
preprocessing theorem that relates the HOL and SMT-LIB meanings, or an explicit
unsupported diagnostic before replay. Silent acceptance or oracle fallback is
outside the audited boundary.
