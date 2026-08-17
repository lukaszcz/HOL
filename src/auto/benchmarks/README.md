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

The SML interfaces call the complete collection a `corpus`.  A `shortfall`
is a dated record saying that a goal is outside the accepted scope, exposes
a current tactic limitation, or could not be translated faithfully.  The
selftest compares actual results with those records in both directions.
The current execution and translation shortfall ledgers are empty: every
assigned recipe succeeds.

Corpus recipes are stored as literal structured values.  The source method,
goal text, identifier, and provenance are reporting and accounting data only;
they are never parsed to choose recipe arguments or tactic behavior.

`HOLSELFTESTLEVEL=1` runs the explicitly marked representative goals.  This
is a fixed subset, not random sampling.  Level 2 or higher runs every
executable goal and also tries selected alternative tactics for
informational counts.  Alternative-tactic results never decide whether
the test passes.

Source mining produced 1,061 distinct executable Isabelle results after
deduplicating translated statements up to bound-variable renaming.  Eleven
existing HOL4 integer regression goals are added, for 1,072 executable goals
in total.

To build and run both test levels from this directory:

```sh
Holmake
./selftest.exe
HOLSELFTESTLEVEL=2 ./selftest.exe
```

`./genparity.exe` performs the exhaustive measurement and rewrites
`../PARITY.md` deterministically.

Set `HOLBENCHDIAGNOSTICS=1` to emit a diagnostic block for every selected
goal.  Set it to a path instead to append those blocks to a manifest file.
Set `HOLBENCHSHORTFALLSONLY=1` to select only executable registered
shortfalls in the requested family.
Diagnostics report the source method, legally translated recipe, excluded
ambient analogues, residual outcome, elapsed time, exposed search statistics,
and the working root-cause classification.  This mode observes the ordinary
tactic run and does not change its recipe or timeout.

For focused debugging, `HOLBENCHBLASTRESIDUAL=1` prints residual tableau
goals and `HOLBENCHPATTERNTRACE=1` traces restricted predicate abstraction.
The HOL trace family `clasimp` reports the selected search engine and stage;
level 2 also reports available search statistics.  The exhaustive alternative
tactic battery is informational and never contributes to the assigned count.
