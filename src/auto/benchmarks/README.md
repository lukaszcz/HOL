# Automation parity benchmarks

This directory contains a data-driven comparison of Isabelle automation
methods and their closest HOL4 tactic counterparts.  The complete results
and definitions of every reported category are in
[`../PARITY.md`](../PARITY.md).

Each benchmark goal records:

- a HOL4 theorem statement;
- the Isabelle source file, line, commit, and method;
- the structured HOL4 method recipe assigned as that invocation's closest
  counterpart, including local rewrites, splits, classical rules, facts,
  and method composition;
- whether the goal belongs to the fixed routine selftest subset; and
- any HOL4 theorem that must be excluded to avoid solving the goal by
  reusing its direct analogue.

The SML interfaces call the complete collection a `corpus`.  They call an
expected non-solution a `shortfall`: a dated record saying that a goal is
outside the accepted scope, exposes a current tactic limitation, or could
not be translated faithfully.  The selftest compares actual results with
those records in both directions.  Consequently, both a new failure and
an unrecorded improvement fail until the data is updated.

`HOLSELFTESTLEVEL=1` runs the explicitly marked representative goals.  This
is a fixed subset, not random sampling.  Level 2 or higher runs every
executable goal and also tries selected alternative tactics for
informational counts.  Alternative-tactic results never decide whether
the test passes.

Source mining found 1,070 relevant Isabelle results.  Nine translated to
duplicate HOL4 statements up to bound-variable renaming, leaving 1,061
distinct source-derived results.  Eleven existing HOL4 integer regression
goals are added.  Every result is either an executable goal or an explicit
unavailable-translation record.

To build and run both test levels from this directory:

```sh
Holmake
./selftest.exe
HOLSELFTESTLEVEL=2 ./selftest.exe
```

`./genparity.exe` performs the exhaustive measurement and rewrites
`../PARITY.md` deterministically.
