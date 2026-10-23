# TASK28 review repair — machinery verified

Source identifier: `TASK28-harness-review-repair-v2` (containing commit).
Measured implementation: `c5595b85d7b1f5f7cfe4da6840fba773c166fa54`.
Baseline: `cccaa27d7099cbadc886983020cbe745db7793f3`.
No production SML or benchmark fixture changed during this repair.

`validation.json` pins inputs, commands, actual exits and scope. `replay.json.gz`
contains individual decisions and mutation rejections. The XZ archives are
lossless `evidence_bundle.py` transports, not precomputed acceptance summaries.
`evidence-seal.json` hashes the retained files. The original v1 evidence remains
unchanged historical data; matrix archives without `shared_inputs` deliberately
fail current admission, rather than deriving their inventory from receipts.

## Results

- All six supplied review regressions pass. Maintained checks: 224 Python
  performance tests (two optional tests separately run), 196 compatibility
  tests, 13 runner tests, 9 real client and 23 real runtime tests.
- Six-size storage: 240 timed fresh processes, ten B/B and ten B/C pairs at
  each size, three samples, 0.3s calibration. Point graph increments and all
  20 control/candidate adjacent slopes pass. CPU/wall fail at 10 and 10000;
  other timing/GC results are inconclusive. CLI **1**, not a numerical pass.
- The separate earlier whole 0.1s attempt rejected a short batch at size 1000,
  CLI **2**. Its complete data is retained; no favorable subset was reused.
- Fresh client protocol: two timed processes plus 12 detected executable fault
  controls; not statistical acceptance. All 242 matrix receipts pass strict
  current archive admission, including private-product completeness added after
  measurement. Real source/product/path/tool/options mutations are rejected.
- CongLib loading: 42 processes, inconclusive metrics, CLI **2**. SimpLib smoke:
  six processes, CLI **0**, no performance decision. All 48 positive forced-GC
  controls replay; zero-GC mutations reject all 48. Statistics are recomputed.
- Normal Holmake check passes all 306 fragment-grid and 336 client-stage checks;
  routine selftest build passes with extensions and fresh API audit enabled.

These results complete TASK28 machinery, not TASK29 numerical gates. All
observed failures remain published; no workload is averaged away. Seven
stronger runtime/independent-build prerequisites stay explicit in `matrix.json`.
Only Linux/aarch64 Poly/ML 5.9.2 source isolation has been measured. The routine
build followed measurement, so no final build-product performance gate is
claimed. See `../../../TASK_28_HANDOFF.md` for the complete handoff.

## Offline replay

From repository root; use new output paths. No private build tree is needed:

```sh
P=src/simp/tests/performance
E=$P/evidence/task28/repair
for name in storage client loading-cong loading-simp-smoke; do
  python3 -B "$P/evidence_bundle.py" unpack \
    "$E/$name.json.xz" "/tmp/task28-fresh-$name"
done
python3 -B "$E/replay.py" \
  --storage /tmp/task28-fresh-storage --client /tmp/task28-fresh-client \
  --cong /tmp/task28-fresh-loading-cong \
  --simp /tmp/task28-fresh-loading-simp-smoke \
  --output /tmp/task28-fresh-replay.json
```

Replay checks exact archived manifests, ordered complete observations,
source/product fingerprints, options, runtime telemetry, raw graph arithmetic,
paired statistics and all slope/CLI decisions. It also tests faults on copies
of real receipts/manifests and verifies loading receipt seals/positive GC.
Remove your unpacked temporary folders after inspection.

The original review inputs were caller-owned and are preserved unchanged;
the maintained test suite includes equivalent coverage without requiring them.
