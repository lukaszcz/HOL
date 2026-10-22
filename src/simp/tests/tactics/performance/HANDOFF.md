# TASK18 performance evidence handoff

Final bounded decision:
[`../../compatibility/TASK_18_HANDOFF.md`](../../compatibility/TASK_18_HANDOFF.md).
The original bodies and 69 selected native occurrences resolve local staging
costs without added extension dispatch or shifted work. Numerical whole-runtime
parity is **not established** by this experiment. No stable slower interval
survives the predeclared longer repeatability investigation; original intervals,
positive point estimates and limits remain visible, not relabeled parity.

## Executed

- 66 ordinary construction/reuse/complete rows, proof/hypothesis/ordered-goal
  validation and exact stage/consumption guards.
- Initial ten-pair campaign, calibrated common schedule, then ten fresh
  alternating current pairs plus ten independent baseline-control pairs.
- Current/control codegen: 53 named simpLib / 69 total native occurrences
  agree modulo adjacent constant-pool relocation. Five aggregate compiler
  export records retain the actual shared tracking-target difference.
- Seven GC slower rows, three contrasts and individual CPU observation
  investigated with 16x batches, ten current plus ten control pairs, followed
  by two diagnostic GC/heap pairs per selection. No slower interval reproduces;
  intervals still include the old effects. Adaptive nursery differences and
  approximately 27.5 KB larger candidate live heap are explicitly retained.
- 14 harness and three adapter controls, complete raw archive/inference/
  native/GC rechecks and pedant pass.

## Evidence

`evidence/RESULTS.md`, `ROWS.md`, `LOCAL_COSTS.md`, `FOLLOWUP.md`, and
`FOLLOWUP_ROWS.md` contain every result, command, interpretation and limitation.
All raw receipts, initial fixture failures and exact compiler extents survive
lossless compaction. No source tree, heap or executable is retained.

```sh
P=src/simp/tests/tactics/performance
python3 -B "$P/evidence/recheck.py"
python3 -B "$P/evidence/followup.py" --archive
python3 -B -m unittest discover -s "$P" -p 'test_*.py'
python3 -B -m unittest discover -s "$P/assembly" -p 'test_*.py'
(cd "$P/evidence" && sha256sum -c SHA256SUMS &&
  sha256sum -c FOLLOWUP_SHA256SUMS)
```

This final document consolidates the two worker handoffs. Only this
non-measured document's checksum changes; measured inputs, results, archives,
source oracles and all other checksum entries are unchanged. No historical
measurement is attributed to newly edited fixture bytes.
