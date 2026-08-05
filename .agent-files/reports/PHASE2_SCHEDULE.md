# Phase 2 schedule measurements

Status: TASK_11 preflight P is complete.  Both sampled conditions have 48
cells, the corrected v3 run has no unexplained exporter/prover failures, and
the Phase 1 anchor comparison is mechanically exact.

## Protocol

P used the frozen 253-theory, 24,721-goal corpus and deterministic
`sample = 500` selection (48 goals).  Both conditions used the chainy regime,
`knn1024`, a 30-second wall budget, reconstruction, and `max_proofs = 4`:

| condition | engine | slices | cores | waves |
|---|---|---:|---:|---:|
| S30-v2-fresh | `Sched` | 8 | 8 | 1 |
| S30-v3 | `Sched` | 16 | 16 | 1 |

Every table row has `slice_size = 1`.  `hhSlice.slice_budget` therefore gives
`1 * 30 / ceil(slices / cores) = 30` seconds to every slice in both
conditions.  The `hhSlice` golden selftest fixes the v3 order as the eight
Phase 1 rows followed by these eight Phase 2 rows:

1. Vampire TX0 / `mono_native_fool` / lifting / 96
2. E TX0- / `mono_native_fool` / lifting / 128
3. Zipperposition TH1 / `mono_native_higher_fool` / keep-lams / 128
4. E TH0 / `mono_native_higher` / keep-lams / 512
5. Vampire TH0 / `mono_native_higher` / keep-lams / 512
6. E TX0- / `mono_native_fool` / combs-and-lifting / 1024
7. Vampire TX0 / `mono_native_fool` / combs / 512
8. Zipperposition FOF / legacy / 32

The last row is an additional legacy-format row, so v3 has seven, not eight,
non-FOF slices per goal.

## Run envelope and headers

The host was `ip-172-31-20-100`, with 32 processors, 247 GiB RAM, and no
swap.  The runs were placed in user-systemd services with
`CPUQuota=3200%`, `MemoryHigh=124G` (`133143986176` bytes),
`MemoryMax=128G`, `MemorySwapMax=0`, and `TasksMax=1280`.  Each theory worker
was wrapped in a ten-minute TERM/120-second-KILL recycle boundary.  State and
caches were initially absent and isolated below `/run/user/1003`, a tmpfs;
experiment journals remained under `src/holyhammer/eval/`.

The supervisor checked the absolute path, version, and SHA-256 of every
binary before starting:

| prover | path | version | SHA-256 |
|---|---|---|---|
| E | `/home/lukasz/.local/bin/eprover` | 3.2.5-ho | `3a471eff44535f9ac18f3f80e48fbce7589922d79e493c1baa8545ae449b3ebc` |
| Vampire | `/home/lukasz/.local/bin/vampire` | 5.0.1 | `765c5aa84bf7333e3ed6e7936a5f44eec832777c00ac0ab5ee3b0aadf65c44de` |
| Zipperposition | `/home/lukasz/.local/bin/zipperposition` | 2.1 | `a5962fd8f986ec73cdf2ff80ab5aab7758dd4059464a0d55d57fa2200bd7d7f8` |

Both schema-3 manifests name HOL commit
`8f161f1ff8f7148b98a05f9d7182e6b3e4268bae`, `sample = 500`, the same
ordered corpus, and the triples above.  The accepted headers are:

| experiment | header date | condition |
|---|---|---|
| `phase2-preflight-p-v2-fixed` | Wed Aug 05 12:01:17 2026 | `p-s30-v2-fresh` |
| `phase2-preflight-p-v3-final` | Wed Aug 05 14:02:19 2026 | `p-s30-v3` |

The v2 service used four isolated 8-core state directories.  It started and
completed 254 theory processes (the seed plus the full 253-theory manifest)
without recycling.  The final v3 service used two isolated 16-core states
and started/completed 34 processes (a seed plus the 33 theories containing
the deterministic sample), also without recycling.  The v3 manifest was
consolidated against the same full frozen corpus.  A prior diagnostic run
exercised the recycle path at exactly ten minutes; the final performance fix
made that recovery unnecessary.

The accepted v3 runtime source was pinned by SHA-256, including:

- `hhLamTrans.sml`: `c702e0c868bab3566db274da8ae58565d80385910e1b9c0f972b6e9c49186eaf`
- `hhMonomorph.sml`: `39e9226fca7b822f0cd0bae10b5783c0680af0c60ab1af623e0b3cff177d4a6e`
- `hhTptpProblem.sml`: `cb51a1f7baa7c6034d48de12083390969c114ee85c0c36588b2d6f2c26174ab4`
- `hhProblemGen.sml`: `fdfaa0e0c9747586d92db62b47468a61805529d3992be1ebcb873b4c6d6e75bf`
- `hhSchedule.sml`: `81ec609807ebcf5dfd752b39a1165669a5f00a9ca1a6def773d5824225bd97af`

The v2 run preceded fixes confined to the new exporter and a semantically
transparent per-goal premise-object memo.  The legacy exporter, slice table,
selector, commands, and fact prefixes were unchanged; the artifact-level
anchor audit below also checks the resulting comparison keys.

## Accepted results

| condition | goals | proved | reconstructed | HO proved | HO reconstructed | p50 | p90 | max |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| S30-v2-fresh | 48 | 23 | 21 | 5/18 | 5/18 | 30.67 | 31.31 | 32.34 |
| S30-v3 | 48 | 24 | 21 | 6/18 | 5/18 | 31.81 | 33.00 | 34.05 |

All v3 cells contain a Boolean `ho` field: 18 are `true` and 30 are `false`.
`report.md` renders both HO and non-HO subset rows.  All 48 v3 cells ran all
16 slices; stop reasons were 43 `Timeout` and 5 `MaxProofs`.

The 336 non-FOF attempts were all fresh (`cached = false`) and had these
parsed outcomes: 30 `ContradictoryAxioms`, 9 `CounterSatisfiable`, 82
`GaveUp`, 42 `ResourceOut`, 26 `Theorem`, and 147 `Timeout`.  None was
`RunFailure`, `LoadFailure`, or `Error`.  Thus every new-format row exported,
spawned, and returned a recognized prover status at sample scale.  The
contradictory/counter-satisfiable results are prover SZS answers, not parser
failures; they should be monitored in the full gate but do not indicate a
harness anomaly.

The v2 and v3 journals contain exactly 48 unique cells with 8 and 16 slices
respectively.  Their aggregate journal digests (sorted per-file SHA-256 rows,
then SHA-256 again) are:

- v2: `6798c4dfd7bcc6fe438f2a799ca5e2be06e1762de62721ae19bad4275873381d`
- v3: `edee9243a13f5a6a80d0654c6daf0c4f63b6a60d313fafb1c89bbf5f9eaa893f`

The isolated caches contain 384 v2 and 768 v3 result files.  A read-only host
check after completion found the final service inactive and no surviving E,
Vampire, Zipperposition, or evaluation-worker process.

## Mechanical anchor audit

For every sampled goal, the audit selected the eight v2 FOF rows and the
matching eight v3 anchor rows (all FOF rows except the appended
Zipperposition/32 row).  It normalized each effective command to the pinned
prover executable placeholder and full 30-second argv, and keyed the premise
prefix by `(goal_id, prover, filter, nfacts)`.  Both sorted TSVs contain 384
rows and have identical SHA-256:

`87ee61b068942f57a20abfa4b1be2f46de72b5fe17782b3ab9859b4e4cf7ecaf`

Their `diff -u` is empty (SHA-256 of the empty diff:
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
The source selftest independently fixes the unrotated first-eight order and
checks command equality for all eight anchors.  Journal slice arrays record
completion order, so the TSV comparison deliberately sorts by the stable
slice key rather than treating array position as schedule order.

## Defects found and corrected

Preflight P did its intended job.  Invalid attempts are retained only as
ignored diagnostic artifacts; none contributed cache entries to the final
run.

1. The first v3 attempt left a lambda in first-order output.  Lambda
   traversal was made context-sensitive, nested binders were handled, and
   residual-lambda diagnostics/tests were added.
2. Real new-format smoke then exposed incomplete symbol/type declarations,
   application arities, FOOL Boolean/equality handling, and THF type syntax.
   The exporter now emits typed applications/values, legal proxies, opaque
   monomorphic THF ground sorts, and THF `@` applications.
3. `bag.BAG_DIFF_UNION_eliminate` exposed an illegal `_24ite...` TH1 atom for
   partially applied conditionals.  Such terms now use declared
   `pxy.ite...` symbols; the exact bag cell parses normally.
4. `binary_ieee.float_to_real_eq` initially crossed the ten-minute recycle
   boundary without a checkpoint.  Bounded monomorphization now caps generic
   substitution search, helper instances are generated from helpers alone
   over the already-monomorphized main ground pool, and identical premise
   prefixes are materialized once per goal.  The exact binary cell then
   completed in 109.79 seconds with seven normal new-format outcomes.
5. The first completed-artifact verifier counted all eight appended rows as
   non-FOF.  Correcting the expected count from 384 to 336 made the complete
   schema/cache/anchor verification pass; this was a verifier-only error and
   did not invalidate the experiment data.

## Verification and artifacts

The final source passes:

- HolyHammer `selftest.exe`, including exporter goldens, all eight anchor
  command checks, scheduler/cache tests, and the new lambda/type/proxy tests;
- `bin/build -t --seq=tools/sequences/upto-parallel` with
  `HOL4_HAMMER_DIR` isolated under `/tmp`;
- completed-artifact validation for row counts, schema, `ho`, slice counts,
  new-format statuses, run-header pins, cache writes, and anchor equality.

Raw ignored evidence is under `src/holyhammer/eval/`, principally
`phase2-preflight-p-v2-fixed`, `phase2-preflight-p-v3-final`, the two anchor
TSVs/diff, and `phase2-preflight-p-run.log`.  This report is the durable
version-controlled evidence scaffold for later S30-v2-fresh, S30-v3, and K
gate runs.
