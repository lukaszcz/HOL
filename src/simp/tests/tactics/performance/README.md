# TASK18 ordinary tactic staging performance

**Measured in the parent-authorized exclusive window.** See
`evidence/RESULTS.md`, `evidence/ROWS.md` and `evidence/LOCAL_COSTS.md`.
Two original final 10-pair campaigns and targeted current/control codegen
are retained. The original seven GC family-slower rows and individual CPU
observation are followed up in `evidence/FOLLOWUP.md`: eight focused rows,
16× batches, 10 fresh current/control pairs each, and separate heap traces.
No longer slower interval reproduces; unresolved is still not parity.
No HOL process, launcher build or timing runs implicitly. `Holmake all` only
runs offline Python controls. This subtree owns no production/shared files.

## Offline checks

```sh
P=src/simp/tests/tactics/performance
python3 -B -m unittest discover -s "$P" -p 'test_*.py'
python3 -B "$P/audit_sources.py" --output /tmp/task18-source.json
```

`audit_sources.py` compares **entire bytes**, not selected pretty bodies, of
`simpLib.sml/.sig` against develop `cccaa27d7099cbadc886983020cbe745db7793f3`.
It records lengths/SHA256 and fails on any byte difference. This independently
includes `process_tags`, conversions/rules, ordinary/full/reverse/no-strip
entry points, `global_simp_tac`, `psr` and `allasms`. Source equality is not a
claim that runtime environment, emitted code or finite timings are identical.

## Maintained workload matrix

66 keys: 11 operations × 3 stages × 2 scenarios.

| Operation | Entry point |
| --- | --- |
| simp / asm | `SIMP_TAC` / `ASM_SIMP_TAC` |
| full / rev | `FULL_SIMP_TAC` / `REV_FULL_SIMP_TAC` |
| no_strip_full / no_strip_rev | `NO_STRIP_*FULL_SIMP_TAC` |
| global / global_req | `global_simp_tac`, plain / `ReqD` rewrite |
| conv | `SIMP_CONV` |
| rule / asm_rule | `SIMP_RULE` / `ASM_SIMP_RULE` |

- **construct**: build/save the actual curried public tactic/conversion/rule
  value. Untimed post-batch application and proof verification consume the
  saved closure. `SIMP_CONV ss args` deliberately does not eta-expand/apply
  its term: develop defers `process_tags` until that later stage.
- **reuse**: repeatedly apply one saved value; tactic applications execute
  returned proof validations with genuine kernel residual-goal proofs.
- **complete**: construct, apply, and reconstruct inside the same timer.

Scenario `.0`: no extra assumptions, supplied AND rewrite. Scenario `.8`:
eight extra assumptions and the same rewrite installed before construction.
They are **distinct scenarios**, not a controlled assumption-count slope.
`global_req` explicitly supplies `ReqD rule` in both scenarios, so requirement
wrapper/printing costs cannot hide outside construction/complete timings.
No extension modules, configured entry points or extension markers are used.

Every operation stores its result in an escaping typed ref and updates a
consumption counter. Separate stage counters distinguish construction,
application and reconstruction; parser checks exact counts in every batch.
After each calibration/sample, exact theorem conclusions **and full hypothesis
sets**, ordered residual goals, and absence of oracle tags are verified.
Construction results are exercised outside their timer, whereas complete
and reuse include actual tactic proof reconstruction. Conversion/rule results
are already theorems and their structural checks run outside the timer.
Only the final escaping result is proof-checked per batch, not every iteration.
This small boolean fixture is focused staging coverage, not a replacement for
TASK18's broad staged exception/marker/late-context semantic suite.

## Authorized execution (serial only)

Do not run while any builds/other benchmarks are running. The explicit flag
asserts parent authorization, **not automatic detection** of unrelated builds.
An advisory Git-directory lock only prevents another cooperating runner.
Both private launchers build serially **before** any measurement process.

```sh
P=src/simp/tests/tactics/performance
python3 -B "$P/run_tactics.py" --authorize-measurements \
  --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/final-iterations.json" \
  --output /tmp/task18-tactic-current
python3 -B "$P/run_tactics.py" --authorize-measurements \
  --baseline-control --pairs 10 --samples 3 --timeout 1800 \
  --fixed-iterations "$P/final-iterations.json" \
  --output /tmp/task18-tactic-control
python3 -B "$P/summarize.py" \
  --candidate /tmp/task18-tactic-current \
  --control /tmp/task18-tactic-control \
  --output /tmp/task18-tactic-analysis.json
```

`fixed-iterations.json` retains the initial schedule. `final-iterations.json`
was derived from every initial sample on both sides: multiply each count by
`max(1, ceil(0.12 / minimum_initial_wall_seconds))`. No candidate-specific
schedule or discarded observation. Actual final batches including calibration
span 0.078829–0.828066 s, versus initial sub-millisecond construction batches.
Each fresh process records one same-count calibration plus >=3 samples per
key. Final campaigns require >=10 alternating AB/BA fresh process pairs each,
including baseline control. Durations are observations, not a parity gate.

Reuses `fragments.run_fragments` snapshots/launcher setup and compatibility
paired fixture installation, protocol/path/footer/exit validation and receipt
compaction. No copied infrastructure change or implicit extension promotion.
Private selected sources run on the same sealed `hol.state0` and shared
non-simplifier dependencies, one GC thread; **not independent clean builds**.
Sources (including uncommitted worktree selection), fixture/tool/shared and
private build products are sealed/rechecked. Temporary private trees are
removed on success/failure. Output directories must be new; failures retain
compressed receipts and failed manifests.

CPU, non-GC CPU, GC CPU, user/system inclusive CPU and wall are reported
separately, after timer-accounting checks; GC is not added twice. Summary
reparses receipts, verifies stage counts and alternating pair order, preserves
all process medians/ratios, and uses paired log Student intervals plus separate
baseline-control contrasts. Family intervals cover 66 workloads per metric,
not jointly all metrics. No pooling, outlier removal, fixed regression budget,
zero replacement, or interpretation of uncertainty as parity. A slower
interval remains visible; spanning one is **unresolved**, never a pass.
An exit of zero establishes observations, not task/whole-plan acceptance.

`evidence/receipts.tar.xz` losslessly packs all initial/failure/final/codegen
receipts and full analysis, decompressing their gzip layer for cross-record
compression. `archive-index.json.gz` seals both original and stored bytes;
`recheck.py` recovers identical original compressed receipts in temporary
storage, reparses all 60 timing processes and re-extracts exact native bodies.
`sources.tar.xz` holds 90 unique input/selected-source blobs keyed by SHA256.
No heaps, executables or copied build trees are retained.

```sh
python3 -B "$P/evidence/recheck.py"
python3 -B "$P/evidence/report.py"  # regenerate the 66-row ROWS.md
```

Additional native inspection commands and limitations: `assembly/README.md`.
The source/codegen result recovers local baseline staging work only; it does
not waive unresolved total timings or the observed slower GC rows.

## Focused longer follow-up

`evidence/FOLLOWUP_PLAN.md` predeclares the experiment; `evidence/FOLLOWUP.md`
reports interpretation/limits. `evidence/FOLLOWUP_ROWS.md` preserves all eight
focused rows and all six metrics beside original results. Original all-66-row
reports/archives/checksums are unchanged.

Explicit `--rows key1,key2,...` must use original matrix order, unique known
keys, and a full sealed 66-key schedule. Every selected protocol/proof gate
remains; all scenario fixtures are constructed, but unselected batches are
skipped, changing adaptive heap history. Family inference stays 66 rows.
`--gc-trace` selects separate snapshots/debug diagnostics (>=1 pair), which
`summarize.py` rejects as timing inference. Main timing still requires >=10
pairs. No measurements run implicitly.

The authorized serial commands are retained in `evidence/run_followup.sh`
(outputs must be new). Actual batch walls were roughly 0.93–1.40 seconds,
including calibration. No sample discarded. Runtime diagnostics show adaptive
nursery/GC-frequency variation, comparable rounded collected-nursery volume
(not exact allocation equality), and a small larger candidate live heap.
No stable added ordinary-work signal is demonstrated; universal cost parity
and whole-plan acceptance remain unestablished.

```sh
python3 -B "$P/evidence/followup.py" --archive
python3 -B "$P/evidence/followup_report.py"
```

`followup-receipts.tar.xz` losslessly retains all 48 new timing/diagnostic
processes and their builds/manifests/analysis. Recovery verifies original
compressed hashes, protocols, stage counts, inference and GC trace totals.
`followup-sources.tar.xz` stores only new sealed blobs, reusing original
`sources.tar.xz` for unchanged inputs. No copied heaps/build trees retained.
