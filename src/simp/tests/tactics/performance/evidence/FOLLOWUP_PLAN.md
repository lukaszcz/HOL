# TASK18 predeclared focused follow-up

Declared before launching follow-up measurements. Exclusive window remains
parent-authorized; current/control builds and processes run serially.

## Timing design

- Exactly eight keys, in original matrix order:
  `full_complete.0`, `rev_complete.0`, `no_strip_full_complete.0`,
  `simp_complete.8`, `rev_reuse.8`, `no_strip_full_reuse.8`,
  `no_strip_full_complete.8`, `no_strip_rev_reuse.8`.
- Seven original GC family-slower rows plus the individual CPU-slower row.
  No selecting or deleting observations after seeing new results.
- `followup-iterations.json`: multiply these keys' final schedule by **16**;
  retain all other schedule entries unchanged. Same counts for both sides
  and baseline-control. Three samples plus calibration, **10 alternating
  fresh AB/BA pairs current, then 10 baseline-control pairs**.
- Explicit row filter preserves selected order and all selected rows' full
  timer, stage, consumption, proof, hypothesis, residual and oracle checks.
  All workloads for each scenario are still constructed as before; unselected
  batch execution is skipped. Thus retained fixtures are preserved but prior
  adaptive heap history is not the full-matrix campaign history. This is a
  focused replication, not an exact replication of that heap history.
- Existing process-median / paired-log Student intervals; family correction
  stays **66 rows per metric**, not reduced to eight. Independent control
  contrast retained. No outlier removal, zero substitution, budget threshold
  or uncertainty-as-parity. Earlier 66-row results remain unchanged/visible.

## Separate diagnostics and interpretation

After timing, run two fresh AB/BA pairs each current/control with the same
filtered schedule, but GC snapshots outside the timer and private-only
`--debug=gc,heapsize`. These are diagnostics, never mixed into timing inference.
Reuse TASK17's maintained 10-field statistics and cumulative-counter mapping
of GC logs to batch boundaries. Compare collection counts, live heap after
untimed full GC, nursery ranges/adjustments and rounded collected-nursery sums.
`sizeAllocationFree` is GC-updated, **not** cumulative allocation. Rounded
nursery sums omit uncollected tails; never claim exact allocated-byte equality.

Compare signs and individual/family/control-contrast intervals across the
original, longer, and diagnostic campaigns. If slower behavior remains stable,
investigate dynamic collection frequency, heap-policy/live environment and
work/allocation evidence rather than relying on local source identity. Report
remaining uncertainty honestly; no universal parity or task-completion claim.
