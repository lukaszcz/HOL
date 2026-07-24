# Phase 4 TASK_01 baseline snapshot

Date: 2026-07-23

Source revision: `95d32f763`

Validation revision: `1f331dd`

## Verification

- `Holmake clean && Holmake` in `src/HolSmt` passed.  This rebuilt
  `smtheap`, `HolSmtTheory`, `selftest.exe`, and the conformance
  drivers from a fresh heap.
- The sharded functional test passed with Z3 4.15.3 and cvc5:
  `run_selftest.sh --keep-going --no-build` reported 8/8 shards
  passed.  Shard 0 ran `Unittest.run_unittests`; every shard ended
  with `all tests successful`.
- The full complete-conformance sweep classified 5,314 results with
  zero unexpected regressions.  All eight corpus modes, all seven
  applicable external modes, and all five Z3-version proof checks
  passed.  The aggregate initially recorded one audit step twice as
  two infrastructure errors because of the validation drift below.
  After the temporary compatibility adjustment, a complete-script
  parser-mode smoke reported status `pass`, zero infrastructure
  errors, and zero unexpected regressions.
- The standalone `run_conformance_suite.py` cross-check passed:
  310 cases, 1,230/1,230 conforming results, and all nine
  metamorphic groups passed.

The locally pinned validation generator at `1f331dd` predates the
higher-order wrapper added around `parsedicts_of_logic` in source
commit `c6d66659e`.  Its source-scanning regular expression therefore
rejects the current, valid function shape before conformance starts.
The complete rerun used a temporary copy of the validation checkout
under `/tmp`, with the generator and audit expressions widened only to
find the same `case logic of` after that wrapper, and with the ten
tracked `HO_` extension names derived from their accepted base
logics.  No HOL source or checked-in validation file was changed by
this compatibility adjustment.

## UnicodeStrings ledger

The checked-in v2 manifest has 148 genuine
`theory:UnicodeStrings*` rows: 37 symbols, each with four behavior
bands.  Mode presence is:

| Band | Rows | Parser | Typecheck | Z3 oracle | P-parse | P-replay | Z3 tac |
|---|---:|---:|---:|---:|---:|---:|---:|
| boundary | 37 | 37 | 37 | 37 | 0 | 0 | 36 |
| sat | 37 | 37 | 37 | 37 | 0 | 0 | 37 |
| type-error | 37 | 37 | 37 | 0 | 0 | 0 | 37 |
| unsat-proof | 37 | 37 | 37 | 37 | 37 | 37 | 37 |
| total | 148 | 148 | 148 | 111 | 37 | 37 | 147 |

All 148 parser-only rows pass.  Expected-status details for the two
implementation-facing modes are:

| Band | Typecheck-only | Z3 tac |
|---|---|---|
| boundary | 36 red, 1 pass | 36 red, 1 absent |
| sat | 36 red, 1 pass | 36 red, 1 pass |
| type-error | 36 red, 1 intended fail | 36 red, 1 intended fail |
| unsat-proof | 36 red, 1 pass | 27 red, 10 pass |
| total | 144 red, 3 pass, 1 fail | 135 red, 11 pass, 1 fail, 1 absent |

The non-red typecheck rows are the four `string-literal` bands.  The
ten passing unsat-proof Z3-tac rows are `re.all`, `re.allchar`,
`re.none`, `reglan`, `str.from-code`, `str.from-int`, `str.is-digit`,
`str.to-int`, `string-literal`, and `string`.

### Per-symbol unsat-proof inventory

There are 37 scripts, so the plan's drafting-time figure of 36 is
stale.  All are under
`tools/conformance-corpus/v2/cases/theories/strings/`:

```text
theory_unicodestrings_re_all_unsat_proof.smt2
theory_unicodestrings_re_allchar_unsat_proof.smt2
theory_unicodestrings_re_concat_unsat_proof.smt2
theory_unicodestrings_re_diff_unsat_proof.smt2
theory_unicodestrings_re_inter_unsat_proof.smt2
theory_unicodestrings_re_loop_unsat_proof.smt2
theory_unicodestrings_re_none_unsat_proof.smt2
theory_unicodestrings_re_opt_unsat_proof.smt2
theory_unicodestrings_re_plus_unsat_proof.smt2
theory_unicodestrings_re_power_unsat_proof.smt2
theory_unicodestrings_re_range_unsat_proof.smt2
theory_unicodestrings_re_star_unsat_proof.smt2
theory_unicodestrings_re_union_unsat_proof.smt2
theory_unicodestrings_reglan_unsat_proof.smt2
theory_unicodestrings_str_at_unsat_proof.smt2
theory_unicodestrings_str_concat_unsat_proof.smt2
theory_unicodestrings_str_contains_unsat_proof.smt2
theory_unicodestrings_str_from_code_unsat_proof.smt2
theory_unicodestrings_str_from_int_unsat_proof.smt2
theory_unicodestrings_str_in_re_unsat_proof.smt2
theory_unicodestrings_str_indexof_unsat_proof.smt2
theory_unicodestrings_str_is_digit_unsat_proof.smt2
theory_unicodestrings_str_le_unsat_proof.smt2
theory_unicodestrings_str_len_unsat_proof.smt2
theory_unicodestrings_str_lt_unsat_proof.smt2
theory_unicodestrings_str_prefixof_unsat_proof.smt2
theory_unicodestrings_str_replace_all_unsat_proof.smt2
theory_unicodestrings_str_replace_re_all_unsat_proof.smt2
theory_unicodestrings_str_replace_re_unsat_proof.smt2
theory_unicodestrings_str_replace_unsat_proof.smt2
theory_unicodestrings_str_substr_unsat_proof.smt2
theory_unicodestrings_str_suffixof_unsat_proof.smt2
theory_unicodestrings_str_to_code_unsat_proof.smt2
theory_unicodestrings_str_to_int_unsat_proof.smt2
theory_unicodestrings_str_to_re_unsat_proof.smt2
theory_unicodestrings_string_literal_unsat_proof.smt2
theory_unicodestrings_string_unsat_proof.smt2
```

### Bucket mismatch

The checked-in `RED_OBLIGATIONS.md` reports 335 strings/regex
obligations, versus the 148 genuine UnicodeStrings manifest rows.
The 187-count excess is not 187 additional UnicodeStrings cases: the
bucket scans obligation text and also matches proof rows,
`z3_extensions` seq/set/bag rows, and string/regex proof-rule rows.
This is the pinned before-state for TASK_04's needle correction.

## Anchor spot-check

No anchor re-survey was needed:

- `git log 95d32f763..HEAD -- src/HolSmt` is empty; source `HEAD` is
  exactly `95d32f763`.
- Local validation `HEAD` is `1f331dd` at 2026-07-23 15:27:35 UTC,
  before the source survey anchor at 20:47:04 UTC.  Its log has no
  later local commits.

The plan's 2026-07-23 line anchors therefore have no post-survey
source or locally available validation drift to record.
