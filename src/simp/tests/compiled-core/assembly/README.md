# TASK16 compiler structural inspection

Run from the repository root (AArch64, Poly/ML 5.9.2):

```
python3 src/simp/tests/compiled-core/assembly/run_assembly.py \
  --output src/simp/tests/compiled-core/assembly/evidence/current
python3 src/simp/tests/compiled-core/assembly/run_assembly.py \
  --baseline-control \
  --output src/simp/tests/compiled-core/assembly/evidence/control
python3 -m unittest discover -s src/simp/tests/compiled-core/assembly
```

The private adapter reuses `../../fragments/assembly/run_assembly.py`'s
source snapshot, fresh hol.state0 launcher, load tracing, provenance seals,
assembly parser, narrow pool-relocation normalization and static counters.
Only the private simpLib source use enables compiler printing, with
exception-safe reset. The fixture exercises empty addition/updaters,
rewrite-maker expansion, bounded conversions, keyed and unkeyed user
conversions, and AC compilation. No production sources are edited.

Unlike an equality acceptance test, a valid inspection succeeds with actual
code differences. `strict_equality_accepted` remains false in that case;
`collector_success` and `difference_notice` preserve the original collector's
rejection. Other collector failures cannot be promoted to success.

Evidence includes private source bytes; full compiler extent; all selected
native bodies; selected exact optimized lambdas, backend trees and repeated
ICode passes with stdout ranges and hashes; exact tree diffs and normalized
native diffs. Duplicate named specializations are retained in emission order.
Only adjacent ADRP/LDR constant-pool materialization is normalized in native
comparison; raw machine words and pool operands remain archived. Named pool
constants in optimized trees are not silently identified across processes.

Missing optional functions (including inlined helpers, constructors and
static empty values) are reported, not charged zero work. The full extent
retains anonymous top-level initialization and any unselected compiler
records. This is static *local* emitted work: reservations are not measured
allocations, calls are not dynamic counts, and callees/loops/GC paths are not
cumulative costs. No closure introspection, timings or speed claims.

See `RESULTS.md` for the actual inspection and its limits.
