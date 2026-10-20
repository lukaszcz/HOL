# TASK_02: frozen reducer-shape and literal-exclusion failures

Landing identifier (commit subject):
`[TASK_02] Freeze legacy reducer and literal exclusion failures`.

## Inputs and scope

- Reference: `cccaa27d7099cbadc886983020cbe745db7793f3`.
- Audited implementation: `62a6bdc3453c29e8f31faa72f2b70a245f44840d`.
- Task entry HEAD: `2ef0942dd` (TASK_01). The only intervening commit
  establishes the harness/evidence; it makes no implementation repairs.
- Existing branch: `simplifier`; no branch/reset/merge operation.
- Pre-existing work: `.agent-files/tasks/PROGRESS.md` had a caller edit
  clarifying TASK_01's status and landing ID. That edit is preserved.
- No simplifier/marker implementation, ordinary selftest or its Holmakefile
  changed. The original develop input and its expectations remain byte
  identical to the pinned git blob; `inputs/SHA256SUMS` remains unchanged.

All eleven probes use only legacy APIs and express desired develop
behavior. They are separately identifiable sources in `probes/legacy/`,
run verbatim as `selftest.sml` in separate processes/theories. Their common
assertions are in `probes/support/LegacyFailures.sml`. There is no xfail,
expected-exception success path, Remember mode, or error swallowing. The
helper records exceptions and re-raises the original exception. Warnings
are forwarded to the original sink and recorded in order; the sink is
restored before asserting or re-raising. Unexpected warnings fail a probe.
Raw combined logs also retain diagnostics emitted during module loading.

This is the TASK_01 **mixed-source** harness: separate pinned library
sources/products but shared host kernel, dependencies and generated
markerTheory, not independent repository builds. See [README.md](README.md)
for isolation/audit limits. No observational equivalence beyond these
finite tests, compatibility repair, or full-build gate is claimed.

## Fixture preconditions and assertions

Every new probe checks fail-fast testutils mode, enabled warnings with
`WARNINGs_as_ERRs = false`, and ordinary simplification of `T /\ compat_p`
to `compat_p` with no hypotheses. Each observed operation records its
stage, warning count/events and exception status; theorem results record
conclusions/hypotheses. `OBS setup.result=ready` appears only after all
fixture preconditions pass. The intended assertion begins afterward.

- `reducer-shape`: projection succeeds and has at least one public
  rewriter. Then performs the literal legacy binding:

  ```sml
  val Traverse.REDUCER _ =
    hd (#rewriters (simpLib.traversedata_for_ss simpLib.empty_ss))
  ```

  Success must record `assertion.constructor.result=REDUCER`, no exception
  and no warnings. It cannot mistake an empty list or loading failure for
  the constructor failure.
- Each `excl-*-unmatched`: `empty_ss` has no fragments and leaves the test
  term unchanged; no conversion is installed. Constructs
  `Excl "<prefix>compat_missing"`, then applies it with `&&`. Exclusion
  must be silent, not throw, and leave simplification unchanged.
- Each `excl-*-installed`: starts with the same empty baseline, installs
  exactly one `std_conv_ss` named `"<prefix>compat_probe"`. Its real rewrite
  reduces `T /\ compat_p` to `compat_p` using `AND_CLAUSES`; setup checks
  both the theorem (including no hypotheses) and a nonempty callback trace.
  After `Excl` the term must remain unchanged **and** the conversion must
  never be called. Thus an inert/misconfigured conversion cannot masquerade
  as successful deletion. The callback trace is reset before exclusion.

All setup/precondition observations passed on both pinned revisions. No
warnings were captured at any observed setup or assertion stage, and no
raw load-time warning was emitted. Successful reference exclusions yield
`(T /\ compat_p) = (T /\ compat_p)`, with no hypotheses/callbacks. This is
not merely a test that exclusion construction avoids an exception.

## Reproduction and retained results

From the repository root, after the routine host build below:

```sh
python3 src/simp/compatibility/run.py \
  --branch 62a6bdc3453c29e8f31faa72f2b70a245f44840d \
  --output src/simp/compatibility/results/task02
```

**Exit 1**, deliberately still red: the runner executes all suites on both
lanes, does not stop at the first red probe, and does not classify the red
runs as passing. For reproduction choose a new output directory. The
manifest hashes every probe and shared helper, all pinned library sources,
tools and shared recipe inputs; it records exact expanded commands, build
and run statuses, loader audits, and complete ordered OBS lists. Each
`*.run.log` retains raw combined stdout/stderr, not just the OBS subset.

Fixture targets are `$WORK/{reference,branch}/<suite>/selftest.exe` for
each suite below. The runner's generated suite Holmakefile and commands
are documented in README.md; the exact targets are always built via:

```sh
$HOLDIR/bin/Holmake --no-project --no-cache --no_prereqs -j1 \
  --holstate=$HOLDIR/bin/hol.state0 selftest.exe
./selftest.exe
```

Both private library builds and **all 26 executable builds exited 0**.
Here `H` means an unexpected `HOL_ERR` at `simpLib.process_tags`, message
`Excl did not match <literal.name>` (full literals shown below).

| Suite | Literal name | Desired | Reference run | Audited run |
| --- | --- | --- | --- | --- |
| `reducer-shape` | n/a | REDUCER, silent | 0, REDUCER | 1, Bind |
| `excl-rule-unmatched` | `rule:compat_missing` | silent no-op | 0 | 1, H |
| `excl-rule-installed` | `rule:compat_probe` | delete conversion | 0 | 1, H |
| `excl-solver-unmatched` | `solver:compat_missing` | silent no-op | 0 | 1, H |
| `excl-solver-installed` | `solver:compat_probe` | delete conversion | 0 | 1, H |
| `excl-looper-unmatched` | `looper:compat_missing` | silent no-op | 0 | 1, H |
| `excl-looper-installed` | `looper:compat_probe` | delete conversion | 0 | 1, H |
| `excl-split-unmatched` | `split:compat_missing` | silent no-op | 0 | 1, H |
| `excl-split-installed` | `split:compat_probe` | delete conversion | 0 | 1, H |
| `excl-case-unmatched` | `case:compat_missing` | silent no-op | 0 | 1, H |
| `excl-case-installed` | `case:compat_probe` | delete conversion | 0 | 1, H |
| `control` | n/a | ordinary control | 0, 4 OK | 0, 4 OK |
| `develop-selftest` | n/a | unchanged assertions | 0, 73 OK | 0, 73 OK |

All reference prefix probes have 14 OK; the reference constructor has 7.
The audited prefix probes have 11 setup OK before `assertion.exclude`
throws; the audited constructor has 6 setup OK before
`assertion.constructor` raises Bind. The ordered control observations are
equal; each of the eleven failing probes differs as expected. The unchanged
original suite has no OBS records, so its comparison is `null`, not a claim
of full trace equivalence.

## Additional validation and cleanup

```sh
bin/build -t --seq=tools/sequences/upto-parallel
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
tools/h4pedant/h4pedant src/simp/compatibility/probes
git diff --check
```

All exit 0; routine build ends `Hol built successfully.` It is the normal
incremental sanity pass, not `bin/build -t -F`. Compact receipts are in
`results/task02/validation.json`. No SML was piped to `bin/hol`.

A first development run stopped at the recipe audit because the new helper
had not imported boolSimps. Adding the explicit per-probe ordinary control
fixed that fixture issue. A second trial reproduced all eleven failures;
its redundant results were removed after inspection. The retained final
run is after the successful routine host build. All runner-owned private
copies/products were automatically removed; temporary trial results and
the routine build log were removed after extracting compact receipts.
Caller-owned artifacts were not touched.

## Handoff to TASK_04 / TASK_07

Changed files: eleven `probes/legacy/` inputs, the shared support module,
`run.py` (snapshot/stage/hash support sources), README.md, this handoff,
`results/task02/`, and `.agent-files/tasks/PROGRESS.md`. Finalized API
changes: **none**. TASK_02 has no remaining acceptance blockers.

- **TASK_04:** repair `reducer-shape/selftest.exe` (Bind at the public
  constructor binding). Include that exact legacy assertion in normal
  `src/simp/src/selftest.sml` coverage without migrating legacy clients;
  migrate only branch-specific configured-shape expectations as prescribed.
- **TASK_07:** repair all ten `excl-{rule,solver,looper,split,case}-
  {unmatched,installed}/selftest.exe` targets (`process_tags` HOL_ERR).
  Preserve the real-rewrite/callback preconditions, warning assertions,
  and literal-name semantics when joining normal selftest coverage.
- Keep the separate red fixtures active meanwhile. The runner has no
  expected-failure flag: a repaired `--branch <commit>` must make the
  corresponding unchanged fixtures green. Final paired coverage must pass
  all eleven plus the original suite/control; do not reinterpret exit 1
  as success for a repair gate.
- These tests do not cover configured reducer lifetimes, other literal
  namespaces/history, or fresh-load registration. Those remain assigned
  to subsequent tasks, not deferred TASK_02 work.

Next unblocked task: TASK_03. TASK_04 and TASK_06 are also unblocked.
