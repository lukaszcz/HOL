# TASK28 loading provenance repair (v3)

Starting/selecting `859be8ed7672d6c319e231d18b3d5cbfcda34b30`;
baseline `cccaa27d7099cbadc886983020cbe745db7793f3`.
Landing: **TASK28-loading-provenance-v3** (containing commit).
See `../../../TASK_28_HANDOFF.md` for completion and scope.

The two review-v2 provenance defects are closed: immutable extraction seals
survive installation/build/actual validation, and actual HOL-linked libraries
are sealed and rediscovered. Maintained tests preserve both failures.
No production SML or extension test changes. The seven explicit matrix
prerequisites still block their later gates; no numerical acceptance is claimed.

## Receipts

- `validation.json`, `evidence-seal.json`: commands, statuses, source/evidence
  identities and numerical limitations.
- `final.json.xz`: lossless transport of all 101 final files: two whole loading
  experiments, build/tool/library/process receipts, and maintained controls/
  fragment/client smoke outputs. Unpack before inspecting. **84 actual fresh
  loading processes**, six linked libraries per experiment. Both CLIs exit 1:
  simpLib CPU/wall/GC fail; congLib CPU/wall fail and GC inconclusive.
  Every final baseline control metric is inconclusive. No observation removed.
- `replay.json`, `roundtrip-check.json`: identical independent statistics,
  immutable Git/product/shared source binding, library/compiler provenance,
  two archive mutations rejected per experiment, all 84 zero-GC substitutions
  rejected. `replay.py` reuses the prior repair's unchanged timer/statistics
  replay, and adds these provenance checks without accessing deleted roots.
- `development.json.xz`: earlier complete 84-process experiment and smoke
  outputs. All candidate metrics were inconclusive, both CLIs exit 2. Before
  final validation, failed-discovery receipt retention was improved, with a
  new regression and v2 report schema. The complete experiment was rerun; no
  favorable subset was selected. Earlier logs are labelled without `final`.
- `review-probe-final.json` / log: unchanged caller-supplied review-v2 probe,
  with only dispatch of new discovery/version commands adapted by
  `review_probe.py`. Unmodified synthetic control accepts 42 observations;
  build-mutated synthetic candidate rejects before any observation. The
  original probe file is caller-owned, unmodified/untracked input, required
  only for reproducing this historical probe. Maintained regressions are
  self-contained and do not depend on caller review files.
- `previous-review.log.gz`: all six prior supplied regressions still pass.
- `holmake-final.log.gz`: 241 Python tests, two optional unchanged runtime/path
  skips; 13 runner tests; complete matrix; real negative controls; 306 fragment
  and 336 client smoke checks. Exit 0.
- `compatibility-tests.log.gz`: 196 pass. The first whole run encountered
  transient ENOSPC; `compatibility-tests-enospc.log.gz` preserves that failure.
  Retrying the whole suite succeeded; no unrelated files were deleted.
- Coverage, immutable-input and pedant logs: exit 0.

## Reproduction

From repository root, stop unrelated builds and measurements. `W` is:

```
sh src/simp/tests/compatibility/evidence/task26/root-wrapper.sh
```

This binds the configured historical root to this exact checkout, not another
build tree. Replace output paths with new ones. Commands and actual fixed
paths are recorded in `validation.json` and the transported reports.

```
python3 -B -m unittest discover -s src/simp/tests/performance \
  -p 'test_loading*.py' -v
W bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate=/home/lukasz/dev/HOL/worktrees/simplifier/bin/hol.state0 \
  -C src/simp/tests/performance -j1 PERFORMANCE_CHECK_OUTPUT=NEW_DIR check
W python3 -B src/simp/tests/performance/loading.py \
  --baseline cccaa27d7099cbadc886983020cbe745db7793f3 \
  --candidate 859be8ed7672d6c319e231d18b3d5cbfcda34b30 \
  --module simpLib --pairs 10 --authorize-measurements \
  --api-audit /home/lukasz/dev/HOL/worktrees/simplifier/src/simp/tests/\
api-audit/evidence/20261023T134511Z-2d38606e/receipt.json --output NEW_DIR
```

Repeat loading with `--module congLib` and a distinct output. The existing
semantic receipt is admitted because the selected candidate Git bytes are
unchanged, not because an old commit label is trusted.

Archive inspection (new unpack/output paths):

```
python3 -B src/simp/tests/performance/evidence_bundle.py unpack \
  src/simp/tests/performance/evidence/task28/loading-repair/final.json.xz \
  /tmp/task28-new-review
W python3 -B src/simp/tests/performance/evidence/task28/loading-repair/\
replay.py /tmp/task28-new-review/simpLib /tmp/task28-new-review/congLib \
  --output /tmp/task28-new-replay.json
```

Remove only the newly unpacked tree after review. All task-owned private
build/source/receipt/roundtrip trees used here have already been removed.
No clean-build, cross-platform, final performance, cumulative HOL allocation,
exact temporary peak or stronger opaque-internal lifetime claim is made.
