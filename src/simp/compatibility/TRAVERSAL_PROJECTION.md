# TASK_04: restored public legacy traversal projection

Landing identifier (commit subject):
`[TASK_04] Restore the public legacy traversal projection`.

## Implementation and API decisions

- Entry HEAD: `a5ec9cbe9e8fb0a88b1bbdf72bf498599495714c` (TASK_03),
  on the existing `simplifier` branch. No branch/reset/merge operation.
  The caller's pre-existing TASK_03 status/commit corrections in
  `.agent-files/tasks/PROGRESS.md` are preserved.
- `simpLib.sml` now has separate `default_traversedata_for_ss` and
  `configured_traversedata_for_ss_prepared` builders. The former uses
  `legacy_rewriter_for_ss_prepared ss []`, equality, the original traversal
  rules, unchanged decision-procedure list and limit.
- `traversedata_for_ss` calls the default builder unconditionally. It does
  not gate on eligibility or unwrap the optional dispatch accessor.
  Its native rewriter is again `Traverse.REDUCER`, even when the simpset
  has configured traversal settings or nonordinary supplied procedures.
  Simpset-specific traversal configuration is deliberately omitted.
- `legacy_traversedata_for_ss` keeps pure, conservative eligibility, then
  shares that builder. `SIMP_QCONV` and `congLib` native/configured dispatch
  are unchanged; ordinary tactics are not routed through the extended
  engine. No preparation, collector invocation or quota reset was added.
- `xtraversedata_for_ss` retains configured extraction. Its private native
  rewriter helper is also explicitly named `configured_...`. Prepared and
  child-first consumers still use the configured path.
- `simpLib.sig`, `notes.md`, the optional-accessor docfile and new public
  legacy/configured docfiles document this split and the branch-only
  migration to `#1 (xtraversedata_for_ss ss)` for configured data alone.

## Caller audit

Repository searches for `traversedata_for_ss` (including extended/private
names and constructor assumptions) found no downstream production clients
of the public extraction API outside `simpLib`. `congLib.sml:288-312`
already uses optional native dispatch with extended fallback and needs no
change. Existing `simpLib` child-first, prepared and tactic consumers
already use complete extended data.

In `src/simp/src/selftest.sml`:

- Migrated `pure_data` (873) and `bool_data` (1057) to explicit configured
  extraction. They feed depth/order, subgoaler, solver and child-first
  tests; these tests must retain their configured native rewriter.
- Migrated configured quota, view, eligibility-shape and fallback assertions
  near the end to explicit extended extraction. The quota test now uses
  the public legacy projection against the explicit configured projection,
  in both starting orders, with the original no-recompilation assertions.
  Optional-native view/replay and remaining-quota assertions are retained.
- Kept public default traversal and `dest_reducer` tests (763, 810), R2
  context/Once lifetime and mixed-reducer tests (4605-4729), and P1 default
  binder/fact tests (5272-5346) on legacy extraction. R2 intentionally also
  passes legacy data plus `default_config` to the explicit engines to test
  their refresh contract; configured reducers are not required there.
- TASK_02's literal `val Traverse.REDUCER _ = hd (...)` is now in normal
  selftest coverage. Constructor checks include `empty_ss`, `bool_ss`, an
  ordinary custom decision procedure, four configured settings and both
  nonordinary procedure constructors rejected by the optional accessor.
  Pointer-identity checks assert that the procedure list and traversal
  rules are forwarded, and counters bracket extraction to detect collectors.
- Added legacy configuration-omission checks with real conditional rewrites:
  configured subgoaler/solver/order callbacks are not called, public
  extraction retains limit 3 and uses the live default, while extended
  explicit depth zero prevents rewriting. Positive controls also require
  an extended unsafe solver to solve an otherwise unsolved condition, and
  an extended custom order to reverse a permutative rewrite. Public
  extraction does neither and invokes neither callback. Theorems,
  hypotheses and free variables are checked, not just RHSs.

Maintained legacy failure probes and archival investigation inputs remain
unchanged. Historical TASK_01/02 evidence describing the old failure is not
rewritten as a current API contract. No configured public extraction
assumption remains in maintained executable consumers.

## Validation

Exact expanded argv, exit codes, source/probe SHA-256, selected routine
output and compact log receipts are in `results/task04/validation.json`.
The tested source is identified by the entry revision plus those hashes;
tests ran on working-tree changes, not a different committed revision.
From the repository root, focused commands were:

```sh
(cd src/simp/src && ../../../bin/Holmake --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" selftest.exe && ./selftest.exe)
(cd src/marker && ../../bin/Holmake --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" selftest.exe && ./selftest.exe)
bin/build -t --seq=tools/sequences/upto-parallel
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
tools/h4pedant/h4pedant src/simp/src
git diff --check
```

Here `$HOLDIR` denotes the absolute repository root. All commands above
exited **0**. Simplifier: **429 OK**; marker: **61 OK**. The routine build
ran the normal `simp-selftest.log` target and ended
`Hol built successfully.` It is the incremental upto-parallel sanity gate,
not `bin/build -t -F`. Configured depth/order/subgoaler/solver, child-first,
native fallback, quota and context-lifetime tests all pass; selected lines
are retained in `results/task04/simplifier-selected.log`. Ordinary SF
registration warnings in the suite are not suppressed.

The unchanged TASK_02 `probes/legacy/reducer-shape.sml` and its shared
`LegacyFailures.sml` were copied verbatim to a temporary selftest directory
with `INCLUDES = $HOLDIR/src/simp/src`. The ordinary Holmake selftest recipe
and exact commands are recorded in the receipt (the same focused flags,
plus `--no_prereqs`, target `selftest.exe`, then `./selftest.exe`). Build and
run both exited **0**, with **7 OK**, `REDUCER`, no observed warnings or
exceptions, and the ordinary-simplification control passing. Raw combined
output is retained as `results/task04/reducer-shape.run.log`. This is a
host-library focused run, not an independent reference build. TASK_02's
pinned red/reference-green evidence remains in `results/task02/`.

One preliminary `h4pedant` invocation incorrectly supplied file paths; the
tool requires directories and exited 1 without output. The corrected
invocation above passes. As it excludes `selftest.sml` and non-SML files,
a separate changed-text whitespace check also covers tests/docs/evidence.

Temporary probe sources/products were automatically removed immediately
after the probe. Scratch build logs and audit listings were removed after
extracting compact evidence. No caller-owned artifacts were removed.

## Handoff to TASK_05

Changed files: `simpLib.{sml,sig}`, `selftest.sml`, `notes.md`, three
traversal docfiles, the compatibility README, this handoff,
`results/task04/`, and task progress.
TASK_04 has no remaining acceptance blockers. The repository-wide
exclusion and fresh-load red probes are outside this bounded repair and
remain assigned to their existing tasks; no red was reclassified as green.

Retained executable lifetime coverage in `selftest.sml`:

- R2 (4605-4729): construction/application collector counts, reusable Once,
  ordinary and mixed fallback, delayed wrappers, explicit refresh, and
  tactic-only versus conversion settings.
- 4792-4986: malformed-bound exception staging, exact maker/trace callbacks,
  congruence/weakener factory ordering and reuse, abort/rejection behavior.
- P1/C2 (5272-5408): binder capture, exact reducer/solver fact order, reusable
  private contexts, weakener staging, live depth/order controls.
- 5410-5551: reflexivity-before-factory staging, foreign exception payloads,
  paired theorem/hypothesis/free-variable preservation, live default versus
  explicit-depth isolation, solver wrapping and Interrupt.
- 5562 onward: both-order public/configured shared quotas without compiling,
  optional-native view/replay sharing, pure eligibility, unconditional public
  constructors, configuration omission and configured fallback.
- 1199-1255: live default mutation between candidates versus explicit zero.

These are passing finite assertions, not universal observational
equivalence. TASK_05 must perform its separately specified pinned-reference
lifetime/default/exception comparisons; this task did not run a new paired
harness or claim that evidence. Full-build and broad differential validation
remain separate plan gates, not TASK_04 acceptance claims.
