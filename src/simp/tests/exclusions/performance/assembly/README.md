# TASK17 delete/replay compiler inspection

`run_assembly.py` adapts the maintained compiled-core compiler-record parser
and fragments private collector, without modifying either. It archives whole
ordinary source bytes, full compiler extent, selected optimized/backend/ICode
records, named native bodies (all repeated occurrences), and exact comparisons.
The trigger reuses the campaign's proof/name/persistence/callback fixture at
sizes 0 and 10; code printing is enabled only around private simpLib source use.

From the repository root, with measurements authorized:

```sh
P=src/simp/tests/exclusions/performance
python3 -B "$P/assembly/run_assembly.py" --output "$P/evidence/codegen-current"
python3 -B "$P/assembly/run_assembly.py" --baseline-control \
  --output "$P/evidence/codegen-control"
```

Required roots: `-*`, `filter_net_by_names`, and `remove_ssfrags`; helpers
include name/dproc filters, replay's `++`, and `mk_named_rewrs`.
`build_from_history` is inlined into the replay caller: its standalone body
is optional, and the caller's exact trees are retained instead. Missing
optional helpers remain explicit, not zero work.
Only adjacent AArch64 ADRP/LDR constant-pool materialization is normalized in
native comparisons; exact raw operands, trees and machine words are retained.
Named pool constants in trees are never silently equated. Valid collection
with differences is successful inspection, not code-equality acceptance.
These are static local bodies, not cumulative allocations, dynamic counts or
timing/parity evidence. See `../evidence/RESULTS.md` for actual outcomes.
