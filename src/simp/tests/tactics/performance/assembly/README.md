# TASK18 targeted ordinary codegen

Explicit authorized native inspection, not timing or closure introspection.
Reuses the maintained TASK16/fragments collector and exact pool-relocation
comparison. Available optimized/backend trees, ICode occurrences and referenced
library specializations are retained; full compiler extents backstop selection.
Local declaration blocks print nested `LAMBDA` backend trees rather than
optimized `fn(...)` trees for the tactic roots. No missing pass is invented.
Full/reverse/no-strip wrappers are source `val` compositions, so inspect their
`GEN_FULL_SIMP_TAC` caller and source spans, not invented standalone bodies.

```sh
P=src/simp/tests/tactics/performance/assembly
python3 -B -m unittest discover -s "$P" -p 'test_*.py'
python3 -B "$P/run_assembly.py" --authorize-measurements \
  --output /tmp/task18-codegen-current
python3 -B "$P/run_assembly.py" --authorize-measurements --baseline-control \
  --output /tmp/task18-codegen-control
```

No code-equality outcome proves dynamic allocation/GC/timing equivalence.
Source/load/fixture failures cannot be promoted as successful inspections.
