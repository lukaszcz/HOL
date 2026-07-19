This file provides guidance to AI agents when working with code in
the automation project of the HOL4 repository.

Scope: `src/auto/` — the opt-in automation project: Isabelle/HOL-parity automation layer.

## Project ground rules

- The goal is HOL4 analogues of Isabelle/HOL's automation (`auto`,
  `blast`, `force`, `safe`, `clarify`, `arith`, …) that are **at least
  as strong** as the originals.  The target is parity in **automation
  strength**, not Isabelle-style surface syntax — judge every design by
  resulting tactic strength, not resemblance to Isabelle.
- Naming is HOL4 uppercase convention only: `AUTO_TAC`, `BLAST_TAC`,
  `SAFE_TAC`, `CLARIFY_TAC`, `ARITH_TAC`, …  No lowercase Isabelle-alias
  layer.
- Solutions must be general, principled and extensible — no pragmatic
  fixes.
- Architectural decisions are the owner's: present them one-by-one with
  options and a recommendation; never decide silently.  Settled
  decisions are not re-litigated.

## Building and testing

From the repo root:

    bin/build -t --seq=tools/sequences/upto-auto

is the routine development gate building kernel + core theories + this layer,
with selftests. `bin/build -F -t` (full distribution) is the gate at phase
boundaries.

Per-directory: plain `Holmake` inside `src/auto/rules/` works — its
Holmakefile pins `HOLHEAP = $(HOLDIR)/bin/hol.state0` itself.  The
selftest is `selftest.exe` (built by `Holmake`, run directly, or via
`HOLSELFTESTLEVEL` which tees into `ntactical-selftest.log`).
Cross-theory persistence scenarios live in `rules/theory_tests/` with
their own Holmakefile (diamond merges, reload idempotence, batched
delta replay).

The layer is registered in `SRCRELNAMES` in
`src/parallel_builds/core/Holmakefile`, so `bin/build -F` exercises it.

## Architecture

Phased subtree layout:

    rules/       rule DB, attributes, netpairs, seeds
    classical/   SAFE/CLARIFY step tactics, FAST/BEST/DEEPEN
    blast/       tableau prover (Paulson's blast)
    clasimp/     AUTO/FORCE/FASTFORCE/CLARSIMP, [iff]
    aesop/       best-first engine (aesop-style)
    linarith/    generic linear arith, ARITH_TAC registry
    presburger/  PRESBURGER_TAC front end (Omega first, Cooper fallback)
    algebra/     instance registry, ALGEBRA_TAC/RING_TAC (Gröbner)

### Constraints that are easy to violate

- **Dependency stratification**: code here may depend only on
  libraries built before `src/boss` (`portableML`, `src/1`,
  `src/parse`, `src/marker`, `src/basicProof`); `rules/` must not
  depend on `src/simp`.  This keeps eventual promotion into the core
  build a sequence edit only.
- **Portability**: the build entry is not `[poly]`-tagged — code must
  be Moscow-ML-compatible SML (no Poly/ML-isms).
- **No goal metavariables in HOL4**: safe steps run as genuine tactics
  on the goal state; unsafe search (rules needing undetermined
  witnesses) runs on an engine-internal proof-state representation
  with metavariables, followed by kernel replay of the found proof
  (the blast/MESON pattern). Don't design search that instantiates
  goal unknowns directly.
- **Wrappers and tactic-valued rules are never persisted** — they are
  closures; libraries re-establish them at load via `augment_claset`.
- Preserve observable claset behaviour when refactoring: `rules_of`
  contents and order, wrapper lists, exact candidate-query sequences,
  `process_claset_tags` leftovers, and the existing warnings for
  stale/ill-formed/duplicate/cross-kind declarations.

## Testing Guidelines

- Write tests in the changed directory's `selftest.sml` (`testutils`);
  persistence/attribute changes also get `theory_tests/` scenarios
  (child-theory visibility, diamond merge, reload idempotence).
- Tactic tests: run successes through `Tactical.VALID`; assert exact
  residual goals for non-closing (`SAFE_TAC`-style) tactics; add
  negative cases (safe tactics must refuse unsafe steps); no theory or
  claset/simpset state left behind on success or failure.
- Strength benchmarks (Pelletier, translated Isabelle goals, arith/
  algebra corpora) are selftest assertions: solved-goal counts + time
  budgets.  Exhaustive corpora sit behind a higher `HOLSELFTESTLEVEL`;
  never prune goals to make a gate pass.
- Benchmark goals are closed by search, never recognition: no tactic,
  preprocessor, rewrite set or seed may name a problem, its statement,
  or a lemma that only discharges one.  Seeds carry general rule
  schemas with claset attributes and nothing else.
- Preprocessing normalizes forms, not instances; a justification that
  needs a problem's name is recognition.
- Unsolved problems are asserted expected failures citing the planned
  remedy — checked to fail, so passing turns the suite red.
- Test specified behavior (solved goals, residues, warnings), not
  internals — nets and `claset` internals may change.
- Bug fixes get a failing-first regression test.
- Run: `Holmake` + `./selftest.exe` in the directory while editing;
  the `upto-auto` gate before a change is done; `bin/build -F -t` at
  phase boundaries, PRs, and any change outside `src/auto/` (simp,
  seeding).  New subdirectories go into `tools/sequences/upto-auto`
  and `SRCRELNAMES`.
