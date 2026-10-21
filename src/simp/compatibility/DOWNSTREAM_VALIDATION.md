# TASK_15: downstream consumers and routine validation

**PASS for this gate.** Tested source revision:
`4d7bf126d` (the full pin is in
`results/task15/validation.json`). No implementation, API, assertion or
Holmake rule changed. No integration repair or new selftest was necessary.
The caller's TASK_14 progress commit-ID correction is preserved.

## Fresh execution and provenance

Evidence: [`results/task15/validation.json`](results/task15/validation.json)
and its compressed raw command logs. The manifest records full revision,
initial working-tree status, source/tool/heap hashes, exact argv/cwd,
start times, elapsed times, exit statuses, invalidated product hashes,
raw-output hashes and assertion counts. All listed commands exited **0**;
there are **no failing targets**. ANSI escapes are removed only for counting
`OK` words; retained raw logs are not normalized.

TASK_14 had already landed, and no Holmake/build/selftest process was running
when validation began. Every build command here ran serially in this checkout;
no shared products were used by competing TASK_14 operations.

For each of the eight normal selftests below, delete only its generated
`*-selftest.log`, `selftest.exe`, `.hol/objs/selftest.{uo,ui}` before invoking
Holmake. The manifest identifies every product actually removed. This forces
fresh recipes, executable linking and test execution, rather than accepting
an old successful log. The focused targets are phony and execute afresh.
The fresh-load launcher recipe pair was explicitly regenerated, followed by
removal/relinking of `fresh-load-selftest.exe`, to prevent the previously
observed missing-runtime-recipe problem. No source file was deleted.

From the root, let `HOLDIR=$(pwd)`. Common Holmake arguments are:

```sh
HM="$HOLDIR/bin/Holmake"
# In src/marker, src/simp/src, src/num/{arith,reduce}/src:
"$HM" --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" HOLSELFTESTLEVEL=1 TARGET
# In src/boss, src/integer, src/integer/testing, src/real:
"$HM" --no-project --no-cache -j1 HOLSELFTESTLEVEL=1 TARGET
```

The manifest contains expanded absolute commands, not placeholder commands.
All are normal maintained Holmake execution/log targets, not SML piped into
`bin/hol`. Early directories explicitly use `bin/hol.state0`; later consumers
use their normal heap selection. The normal simplifier test includes both
legacy and explicit extension assertions, not a substituted extension lane.

## Named downstream matrix

Paths in the assertions column are relative to the target directory unless
otherwise stated. Every row passed. Counts are successful `OK` markers,
not claims of exhaustive behavioral coverage.

| Directory | Exact target | OK | Maintained coverage |
| --- | --- | ---: | --- |
| `src/marker` | `marker-selftest.log` | 72 | Legacy marker round trips; distinct ExclX directive; bounded/requirement wrappers; namespace-neutral Split/ExcludeX syntax. |
| `src/simp/src` | `simp-selftest.log` | 630 | Native, configured and child-first traversal; custom reducers; congruences; fragments, exclusions and replay; bounded rewrites; ordinary/full tactics. Details below. |
| `src/num/arith/src` | `arith-selftest.log` | 47 | `selftest.sml:9–54`: REDUCE/SUC_FILTER/ARITH simpsets and ground/empty context; `109–119`: CONJ cache; `167–254`: cached/uncached FULL_SIMP_TAC and assumption regressions. |
| `src/num/reduce/src` | `reduce-selftest.log` | 33 | Numeric ADD/SBC/MUL/DIV/MOD and other direct conversions. These are reduction controls; arithmetic's REDUCE_ss checks provide simplifier integration. |
| `src/boss` | `boss-selftest.log` | 67 | `selftest.sml:201–228`: ordinary simp, exact/qualified rewrite and NUM_ARITH_DP exclusions; `341–374`: fs/gs/rgs/gvs ordering; `431–482`: stored/current simpsets and CONG_TAC clients; `494–513`: local update/restore. |
| `src/integer` | `integer-selftest.log` | 18 | Integer conversions and INTEGER_RULE_00–03 conclusion checks (`selftest.sml:82–99`). |
| `src/integer/testing` | `integer2-selftest.log` | 415 | Omega/Cooper regression corpora, exception outcomes and the non-looping integer simplifier-DP case (`selftest.sml:10–41`). The latter checks successful return, not an independently specified theorem. |
| `src/real` | `real-selftest.log` | 257 | `selftest.sml:24–101`: real reduction through simp; `197–255`: relation normalization; `260–285`: independent NUM_ARITH_DP/REAL_ARITH_DP exclusion and surviving-DP operation; real arithmetic/field/NLA positive and negative tests. |

### Native and opt-in assertions retained

All ranges below refer to `src/simp/src/selftest.sml` at the tested pin:

- **Custom reducers / congruence consumers:** `1035–1150` exercises context
  reducers, residual-condition solvers, congruence facts, restored limits and
  exceptions. `1464–1531` tests `congLib` equality and explicit configured
  subgoaler/solver counts. `120–218` keeps develop's ordinary applied-result
  congruence behavior alongside explicitly threaded rules and replay.
- **Ordinary/full simplification:** `555–618`, `1933–1975`, `2056–2068`
  retain simplification/assumption order, `Excl`, safe/unsafe solvers, looper
  restarts and full/global final steps. Boss and arithmetic add independent
  maintained downstream uses, rather than relying only on core smoke tests.
- **Fragment exclusion/replay:** `395–480`, `1621–1716`, `1755–1791`
  check literal versus extended exclusions, fragment removals, duplicate
  solver replay, strategy fields and filtered rewrites. `4762–4996` tests
  history edits/filtering/bundles without recompilation or refreshed quotas.
- **Bounded controls:** `40–104`, `220–252` test branching, loop-check
  override, decrement timing and joint allowances. `3976–4554` tests
  normalization, failed conditions, source/view identity, suspended siblings
  and replay; this includes ordinary **and child-first** Once/Ntimes checks.
- **Explicit child-first:** `888–1033` asserts visit order, cutoff/budget
  propagation, congruence facts, eta handling and conversion/tactic results.
- **Lifetime/callback contracts:** `5028–5400` retains context reuse and
  factory scheduling, not only final terms. `5799–5904` checks C2 callback
  counts/order and congLib reflexivity/factory exception payloads.
- **Native versus configured projections:** `5907–6300` checks theorem and
  hypothesis agreement, live defaults and exception boundaries; shared
  quotas in both starting orders without compilation; late extraction after
  exhaustion; replayed views; native REDUCER/dproc shape; projection purity;
  omission versus explicit use of configuration, unsafe solvers and custom
  orders; configured fallback collector construction/application counts.

These assertions were executed unchanged. No legacy path was rerouted
through an extension, and no quota/callback check was removed to obtain a
pass. Finite tests still do not establish equivalence for arbitrary callbacks.

## Focused compatibility and clean-load targets

After the normal simplifier target, execute from `src/simp/src`:

```sh
# First regenerate selftest.uo in ../compatibility/probes/fresh-load
# with the same early-heap arguments, then relink the launcher.
"$HM" --no-project --no-cache -j1 \
  --holstate="$HOLDIR/bin/hol.state0" \
  traversal-contracts exclusion-contracts fresh-load-regressions \
  split-registration split-persistence
```

`focused.log.gz` contains fresh output for all targets (**1345 OK**):

- `traversal-contracts`: **47 OK**, native contexts, shared installed quotas,
  collectors/factories, staging, warnings, live defaults and exception IDs.
- `exclusion-contracts`: **929 OK**, all literal prefixes, conversion/rewrite/
  dproc deletion, strict parsing, history/current-theory and Context replay.
- `fresh-load-regressions`: **107 OK**, all six scenarios: control,
  attribute-first, set-first, attribute-after, set-after, syntax-first. Each
  emits `precondition=clean` before dynamic loading. Includes preservation
  of foreign registries, handler identities and syntax.
- `split-registration`: **101 OK**, unowned/owned/foreign initialization,
  Context lifetime, explicit opt-in and pure local splitting.
- `split-persistence`: **161 OK**, parent/child/descendant/owned imports,
  foreign-attribute/foreign-set rejection and actual heap-save/heap-reload.
  The two foreign-owner import errors are asserted expected outcomes, not
  failing targets. The temporary saved heap is removed by the check target.

## Routine build and gate boundary

```sh
bin/build -t --seq=tools/sequences/upto-parallel
```

**Exit 0**, ending `Hol built successfully.` Full fresh command output is
`results/task15/routine.log.gz`; there was no failed attempt or repair.
This is the requested **incremental, selftest-enabled routine sequence**, not
an independent clean build. The driver rebuilds the sigobj inventory and
traverses `kernel` plus `core-theories` (including `base-hol`), ending here in
AI/sml inspection/proof search/machine learning, tactictoe and holyhammer.
Some up-to-date targets are reused normally; the eight named consumer suites
above were independently forced to execute before it. The driver explicitly
skips help documentation for this partial sequence. Integer/real consumers
outside that routine sequence were tested separately above.

Final checks in `results/task15/final-checks.json`: frozen develop-input
hashes, project pedant over simp/marker, changed-text whitespace and
`git diff --check` all pass. No task-created copied tree, cache, downloaded
input or saved heap remains. Task-owned scratch orchestration was removed;
normal checkout products and unrelated artifacts remain.

Handoff to TASK_16/TASK_17: only this report, compact evidence and task
index/progress changed; no repaired-source revision or API decision is
needed. TASK_15 has no remaining blocker. TASK_16 still owns the separate
`bin/build -t -F` full regression gate; TASK_17 owns final acceptance.
Neither full regression nor universal compatibility is claimed here.
