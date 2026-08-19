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

## Corpus integrity detectors

`benchGuards` answers the questions a corpus entry cannot be trusted to
answer about itself.  Each detector reports findings; the caller decides
whether a finding is fatal.

- **A1 recognition** — whether a supplied theorem alone closes the goal,
  by `MATCH_ACCEPT_TAC`, `REWRITE_TAC`, its `GSYM`, a pure boolean
  simplification, `MATCH_MP_TAC` followed by safe steps, or a
  minimum-budget `METIS_TAC`.  A route counts only when the same route
  without the theorem fails, so an ambient tautology is not mistaken for
  recognition.  The syntactic `benchLib.theorem_is_goal` test is kept as a
  cheap accepting pre-filter.
- **A2 provenance** — every `parityTranslation$source_X` argument must be
  named by the entry's Isabelle method, modulo a closed suffix list, or be
  a registered definition of a constant occurring in the goal.
- **A3 search work** — a goal whose Isabelle method is a search method
  must do search work.  The engines report node expansions, tableau depth,
  branches, inferences and rule applications to the shared `searchWork`
  meter, which brackets the run.
- **A4 single-use rules** — a translation lemma used by exactly one corpus
  goal must be named by that goal's method.
- **A5 alias audit** — every hand-mapped display name in
  `benchExplicit.special`, reported unless it renders a real lemma under a
  documented Isabelle attribute.
- **A6 goal-term pin** — a structural hash of every goal statement, de
  Bruijn for bound variables and theory-qualified for constants, pinned per
  family in `selftest.sml`.  A changed hash means a goal statement moved.

Detector logic, thresholds and pins are owner-signed.  Widening one to make
a run green is the defect they exist to catch.

`./guards.exe` sweeps the whole corpus and writes the findings list.
`HOLGUARDSOUT` names the output file, `HOLGUARDSSKIP` leaves detectors out,
`HOLGUARDSFAMILY` restricts the sweep to one family, `HOLGUARDSLIMIT` caps
the goals per family, and `HOLGUARDSPROGRESS=1` names each goal as it is
swept.  Each restriction is recorded in the generated header.

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
