# TASK_16 C4 wiring and checked Z3 replay

## Result

The production solver drivers now select their higher-order dialects
explicitly at the call sites:

- Z3 uses `Z3LambdaArray` for oracle and proof-producing translations.
- cvc5 uses `Standard27` with the standard `@` application operator.

Driver-shaped unit tests assert the automatic higher-order regime,
dialect, and `RegimeSelection` reason for both paths.  Direct Z3 tests
reconstruct exact, hypothesis-free, oracle-free theorems for a
first-class lambda argument, lambda equality, eta, and ranked partial
application.

The functional selftest adds the same four checked cases and enables
checked Z3 replay for the pair-lambda case.  The requested expression

```sml
(\x. x (\x. x)) = (\y. y x)
```

is not a theorem: Z3 produces a satisfying model for it.  It therefore
cannot soundly use `thm_Z3p` or `thm_Z3p_v4`.  The selftest preserves
the genuine SAT boundary on Z3 releases before 4.15 and adds the
adjacent guarded theorem

```sml
x = (\x. x) ==> ((\x. x (\x. x)) = (\y. y x))
```

under both checked backends.  Z3 4.15.3 is excluded only from the SAT
probe because its proof-enabled command reports that a proof is
unavailable for this satisfiable query; checked UNSAT replay remains
enabled and green.

## Corpus burn-down

All six higher-order proof-corpus rows now pass `proof-replay`.  Four
also pass end-to-end `z3-tac` on Z3 4.11.2 and 4.15.3:

- beta instance
- eta partial application
- lambda extensionality
- map-valued conditional

The two observed solver-proof residuals remain explicit red
`proof-rule:*` obligations:

- lambda equality: unsupported `rewrite` proof rule
- lambda under a quantifier: unsupported `pull-quant` proof syntax

The generated manifest and generator tests record those exact
diagnostics; no higher-order row is silently skipped.

## Verification

- Generator unit tests: 13 passed.
- Focused higher-order conformance on Z3 4.11.2: 107 matched, no
  diagnostic mismatch.
- Focused higher-order conformance on Z3 4.15.3: 107 matched, no
  diagnostic mismatch.
- Eight-shard functional selftest with Z3 4.11.2 and cvc5: pass.
- Eight-shard `verify_z3_versions.sh` matrix:
  - Z3 4.11.2: pass
  - Z3 4.15.3: pass
- `tools/h4pedant/h4pedant src/HolSmt`: pass.
- `Holmake` in `src/HolSmt`: pass.
- Complete conformance:
  - 4,065 matched and 33 accepted results
  - 1,213 catalogued red obligations
  - 0 unexpected regressions
  - 0 infrastructure errors
  - all conformance, external, and Z3 4.11.2/4.15.3 proof-version
    steps passed
- `bin/build -t --seq=tools/sequences/upto-parallel`: pass
  (`Hol built successfully`).

The matrix includes the registered `Unittest.sml` tests, the
TASK_01 byte-identical first-order golden test, and the complete
functional selftest.
