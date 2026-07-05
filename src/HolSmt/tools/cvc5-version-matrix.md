# HolSmt cvc5 Version Matrix

HolSmt supports cvc5 Alethe proof reconstruction as an evidence-backed
compatibility point, not as an assumption that cvc5 proof output is stable.
The current local verification target is:

```sh
HOL4_CVC_EXECUTABLE=$HOME/.local/bin/cvc5 \
  Holmake -C src/HolSmt selftest.exe

(cd src/HolSmt && \
  HOL4_CVC_EXECUTABLE=$HOME/.local/bin/cvc5 ./selftest.exe)
```

The checked local cvc5 binary is:

```text
cvc5 1.3.4 [git f3b21c4 on branch HEAD]
```

## Local Evaluation Notes

On 2026-07-05, the cases previously disabled because cvc5 1.1.2
segfaulted, aborted with `Fresh Skolems are not allowed`, or produced an
oversized proof were re-run against cvc5 1.3.4 on `Linux-aarch64`.

Summary:

```text
1.1.2  historical  multiple proof-production failures in selftest history
1.3.4  pass        selftest proof-production blockers re-evaluated
```

The 1.3.4 run showed that the old upstream proof-production failures are no
longer reproducible for the selftest cases.  Passing rows were restored in
`src/HolSmt/selftest.sml`.

The remaining disabled rows in the evaluated set are not current upstream cvc5
proof-production failures.  cvc5 1.3.4 produces Alethe proofs for them, but
HolSmt replay still lacks local support:

```text
num_to_real_mono      replay_hole fails on a real_of_int arithmetic step
flrtoks_pos_frac      unknown Alethe rule: to_int_intro
flrtoks_neg_frac      unknown Alethe rule: to_int_intro
clgtoks_pos_frac      unknown Alethe rule: to_int_intro
clgtoks_neg_frac      unknown Alethe rule: to_int_intro
num_min_imp           replay METIS fallback fails on MIN/MAX ite expansion
num_max_imp           replay METIS fallback fails on MIN/MAX ite expansion
int_min_imp           replay METIS fallback fails on MIN/MAX ite expansion
real_max_imp          replay METIS fallback fails on MIN/MAX ite expansion
```

Those rows are TASK_20 Alethe replay obligations, not upstream cvc5 issues.
No external cvc5 issue is filed or drafted for them.

## Restored 1.3.4 Rows

The following historical cvc5 1.1.2 blocker families now pass checked replay
with cvc5 1.3.4 and were restored:

```text
num successor/addition variable lemmas
num subtraction associativity formerly marked as oversized proof
num MIN/MAX basic lemmas
integer ABS lemmas
integer MIN/MAX basic lemmas, plus int_max implication
real division by 42 bounded by abs
real power square and positive-base lemmas
real ABS lemmas
real MIN/MAX basic lemmas, plus real_min implication
num order reflexivity, transitivity, nonnegativity, interval lemmas
num-to-int and int-to-num monotonicity lemmas
flr/clg negative, zero, and variable non-positive to-num lemmas
clgtoks integer lemmas
existential over an uninterpreted sort
Abbrev marker regression
```

## Status Labels

Report statuses:

```text
pass      cvc5 produced an Alethe proof and HolSmt checked replay passed.
fail      cvc5/HolSmt ran and exposed a parser, replay or proof-production
          incompatibility.
blocked   A local prerequisite is missing.
not-run   The tool could not obtain a compatible cvc5 executable.
error     The configured executable or test harness setup was invalid.
historical
          Behavior recorded in source history but not re-run locally.
```

Broad support claims should cite the exact cvc5 version and this matrix.
Expanding the cvc5 support range requires re-running the full HolSmt selftest
with proofs enabled and updating this file with any cvc5 proof-production or
HolSmt Alethe replay changes.
