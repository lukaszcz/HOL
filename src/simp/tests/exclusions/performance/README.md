# TASK17 focused ordinary exclusions and replay

**Measurements need an exclusive window.** This suite never runs
implicitly: even its Holmake `all` runs Python synthetic tests only.
No production files or existing runners are modified.

## Offline preparation (no builds or HOL processes)

From repository root:

```sh
python3 -B -m unittest discover \
  -s src/simp/tests/exclusions/performance -p 'test_*.py'
python3 -B src/simp/tests/exclusions/performance/audit_sources.py \
  --output /tmp/task17-source-correspondence.json
```

The source audit reads full bytes from pinned develop
`cccaa27d7099cbadc886983020cbe745db7793f3` and current `simpLib.sml/.sig`.
It fails on *any* difference, with both SHA-256/length seals retained. Whole-file
identity includes the literal parser, the single net filter, the single dproc
filter, unmatched deletion-history recording and replay. This is structural
source evidence, not proof of an identical ambient runtime or timing parity.

## Run commands

Only when **all** builds/other benchmark processes cease, run these commands
**serially** (not in the background). The flag asserts main authorization;
it does not detect other HOL builds. A nonblocking advisory lock on the worktree
Git directory prevents overlapping instances of this runner only, without
leaving a lockfile. Use new output directories and the *same* sealed schedule:

```sh
P=src/simp/tests/exclusions/performance
python3 -B "$P/run_exclusions.py" --authorize-measurements \
  --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/fixed-iterations.json" \
  --output /tmp/task17-exclusion-current
python3 -B "$P/run_exclusions.py" --authorize-measurements \
  --baseline-control --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/fixed-iterations.json" \
  --output /tmp/task17-exclusion-control
python3 -B "$P/summarize.py" \
  --candidate /tmp/task17-exclusion-current \
  --control /tmp/task17-exclusion-control \
  --output /tmp/task17-exclusion-analysis.json
```

Candidate defaults to the working sources, including uncommitted changes;
`--candidate COMMIT` also works. Baseline-control selects pinned develop on
**both** sides. Both private launchers build serially before measurement starts.
Each campaign has >=10 alternating fresh-process AB/BA pairs, >=3 samples and
one fixed-count calibration per workload/process. Every sample and calibration
uses the same count for both sides and all pairs, with no adaptive doubling.
`fixed-iterations.json` is an **uncalibrated initial schedule**; it does not
claim a minimum duration. Inspect all recorded raw batch durations. If batches
are too short, prepare a longer *common* schedule and rerun both full campaigns;
never cherry-pick samples or silently discard the initial run.

## Workload matrix

All eleven workloads run at **0, 10, 1000, 10000** compiled rewrite/dproc
counts (44 keys). Distinct constant keys prevent quadratic input preparation.
Preparation, full GCs and verification are outside each operation timer.

| Label | Timed operation / input |
| --- | --- |
| `empty_list` | `ss -* []`, on n rules + n named dprocs |
| `missing` | nonempty missing literal, on n rules + n dprocs |
| `matching` | first unqualified rule name, same mixed input |
| `batched` | first/middle/last names + missing; duplicates preserved |
| `qualified` | `bool.task17_r0`, same mixed input |
| `partial` | delete `.1`, retain distinct maker-expanded `.2` sibling |
| `literal_namespace` | `task17_ns::` is literal, **not** a namespace selector |
| `literal_exact` | exact `task17_ns::r0`, same n-rule namespace-looking net |
| `dproc_only` | exact dproc-name deletion, no net rules, n named dprocs |
| `mixed` | rule + dproc + missing in one exclusion call |
| `replay` | remove an empty named fragment; replay maker + n rules + missing exclusion |

For `partial`, one parent expands to distinct first/second constant rewrites;
there are still exactly n compiled rewrites. Its `.1` proof becomes reflexive
while the `.2` proof must still rewrite. Zero-size operations intentionally
remain real calls (except the separately labelled empty-list control).

Every timed result escapes through a ref; sink accounting checks each timed
iteration exactly. After every calibration/sample the saved result is consumed
by exact ordered fragment/dproc-name checks and kernel theorem comparisons
(conclusions **and hypothesis sets**) at first, second, middle and last constants,
plus a reflexivity proof even at size zero. Original inputs' proofs/names are
rechecked for persistence. This is focused endpoint coverage, not an assertion
that every net slot is inspected. The dproc-only row also checks unchanged
constant proofs. Proofs use a public traversal-data projection with `dprocs=[]`
so opaque UNCHANGED dprocs cannot mask the net; reducer names are independently
checked in exact order. No opaque reducer implementation is introspected.

Replay validates exactly n maker calls and one collector call per iteration,
including n=0, before untimed proof checks. These callbacks are part of the
replay workload. Exclusion rows require zero maker/collector calls. The replay
history contains a nonempty unmatched literal deletion event; this performance
fixture complements, not replaces, main's theory-change/limit/order semantic
contracts. It does not claim complete replay-control coverage.

## Isolation, evidence and interpretation

Reuses maintained `fragments.run_fragments.snapshot/configure_launcher` and
`compatibility.run_paired` fixture installation, execution, protocol/footer/
exit/path validation and compressed receipts. Sources elaborate in fresh
`hol.state0` processes with private-first paths and one GC thread. Shared heap
and non-simplifier dependencies are sealed: these are **not independent clean
repository builds**. No matched-environment supplements or production flags.

Runner seals sources, fixtures, tools, launcher/private products and loaded
shared products, rechecks them at the end, and records worktree drift. Temporary
source trees/heaps disappear on success and failure; failed runs retain full
compressed receipts and a failing manifest. Existing output directories,
malformed/partial/duplicate schedules, protocol omissions, wrong callbacks,
consumption, timer accounting, exits, footers, or paths fail closed. The
manifest records whole `simpLib.sml/.sig` byte correspondence for each selection.

CPU, non-GC CPU, GC CPU, inclusive user/system CPU and wall remain separate;
GC is not added twice. Raw timer fields and calibration/sample counts remain
in receipts. Summary reparses raw protocols and verifies stored measurements.
It retains all process medians/paired ratios and computes per-workload Student
log-ratio individual/family intervals, plus independent-run control contrasts.
It reuses maintained fragment-summary Student quantiles, generalized to the
actual pair count and 44 workload family. No pooling across workloads, zero
replacement, outlier removal or fixed regression tolerance. A slower interval
remains visible even if control is noisy. An interval spanning one means
**unresolved, not parity**. An exit of zero means complete observations, not
whole-plan performance acceptance. Structural source identity and statistical
uncertainty must be reported separately.

Remove scratch output when finished. No receipt, copied build tree, generated
launcher, heap or cache belongs in this directory or a commit.
