# Phase 3 preflight and anchor derivation

Status date: 2026-09-06. Run P-v12 and Run A-v12 are the only accepted
TASK_10 evidence. Every predecessor is superseded and contributes no row,
result, model, cache, premise list, or mutable support file to these
fresh-empty runs.

## Final source, runtime, and provenance

Both accepted runs bind main commit
`aa669532a0ff8ccb32a3748a73ff8cda38ef2fcc` plus tracked source diff
SHA-256
`2c829ebde7d49e6cf9bd7a5d9961f80fc9aae18080272eea8f749054702dcd26`.
`src/AI/machine_learning` is unchanged. The maintained implementation is
under `src/holyhammer` and `src/holyhammer/tools`; accepted runtime inputs
are immutable copies of tracked files, never implementations under an
ignored work directory.

P-v12's sealed 10,887-file input inventory is
`e8bf287fce2fbd110e04fcb84f3a99608a9ac91cb881bc704858d7fc96701427`.
It contains all 27/27 tracked runtime files, the immutable corpus and
templates, and a complete internal focused-gate support snapshot. Its
runtime-origin inventory is
`481153cfb2f14b547e7d632049bfe5ce1f5402c63d4badfb38b0ec6c3ad058db`.
The final P certificate is
`5785bdac3d5623f68ae980e3a9d089698b9c11b7e5babc90cab9d4e37512c346`.
The production existing-output guard certificate is exactly
`9f761d9f06deb6e3f00f53df095be02d33389e54e11d92b7085225c91cb93575`;
a complete distinct sealed challenger is retained at inventory
`1569e96941ea2ef8bdbd430e36caeb068a9fbf7f258fe5a569d33b6618eae4fc`.

A-v12's sealed 22,098-file input inventory is
`336147f15b76e7f920c287ec0b2721d529498df8a57c78e16e2007966891fe96`.
Its runtime-origin inventory binds all 65/65 tracked runtime files at
`7336eae1ff29d163bf1d0e9ff894955172ebb31f53bc77bda62ace1e71dfabee`;
the theory inventory is
`6f6cdde44670933cc2b0abcaa0a6a8257d3a16c17ea51e4084beeef681cf2506`.
Its internal support inventory is
`2f54d2265f7c828b17e12ab8ef8eb396df86df93342b5690474a0779ea9fed71`;
it snapshots P-v12, mapped smoke-v28, storage-v34, and the exact 27-record
predecessor inventory `b747df6623129d74eaae06c251f8afb592b4b98552f336d8602525574ac5addd`.
External support/history changes after sealing cannot affect verification;
missing or modified internal support fails before mutation.
The canonical Phase 2 gate header and 229-member certificate remain
`d50c414547280480105ea6286e395cc4b4e428885748d866008887c746466b87`
and
`d2b145c9a16710611dcb61acdfc8e0635fd8acc46259e9ac2bddda7ca50c3318`.
The exact mapped historical state is 181 f751 members / 24,353 goals and
48 f258 members / 368 goals, map
`056e9cb65c6792f9d4871ede21dcf182b40bd172c5d2d1ea3dc6d8ddf7ff3f9d`.
Its two closed loaded-state inventories are
`927578faeca4e68c6b4e588d29cef0cbf4b5df6ad4693401555918abc5e0295f`
(f751) and
`65064ffbae3698ccd6f431af2ac817d3b7e4eb8479ab5da49706297c252c3a0c`
(f258). Unknown states and field-wise cross-state mixtures fail closed.

The source makes every stature input explicitly target-scoped over
`Theory.ancestry target @ [target]`: theorem DB rows, user definitions,
type-base updates, and simp deltas are independent of unrelated ambient
theories. Target theorem data uses a bounded one-entry replacement cache
keyed by target and structural inventory, so alternating targets invalidate
the retained model and no obsolete whole inventory remains. Structural goal
hashes use constructor framing, qualified constants and types, de Bruijn
bound variables, explicit free/type variables, and canonical assumptions.
MeSh uses proposition equality, and bounded-best monomorphisation has a
hermetic equivalence/pathological regression.

## Operating envelope and pinned provers

P and A used bounded user-systemd scopes with a 32-core quota,
`MemoryHigh=133143986176` bytes (124 GiB),
`MemoryMax=137438953472` bytes (128 GiB), swap maximum zero, tmpfs scratch,
hard 600-second workers/atoms, atomic durable copy-back, and append-only
resume lineage. P used initially empty private caches. A retained the
required 16 prover-free HOL scheduler workers and limited memory-heavy HOL
atoms to eight kernel advisory-flock slots (64 GiB conservative reservation).
The external-pressure admission formula was
`MemAvailable + scope MemoryCurrent >= 80 GiB`, with a separate 32 GiB
scope-headroom requirement and bounded waits.

| prover | absolute path | version | SHA-256 |
|---|---|---|---|
| E | `/home/lukasz/.local/bin/eprover` | 3.2.5-ho | `3a471eff44535f9ac18f3f80e48fbce7589922d79e493c1baa8545ae449b3ebc` |
| Vampire | `/home/lukasz/.local/bin/vampire` | 5.0.1 | `765c5aa84bf7333e3ed6e7936a5f44eec832777c00ac0ab5ee3b0aadf65c44de` |
| Zipperposition | `/home/lukasz/.local/bin/zipperposition` | 2.1 | `a5962fd8f986ec73cdf2ff80ab5aab7758dd4059464a0d55d57fa2200bd7d7f8` |

Actual successful teardown is: durable copy-back and rehash, durable run
result validation, then accepted tmpfs removal. Independent durable folds
and final certificates run after removal. This order is exercised by fresh,
resume, corrupt-stage, kill-before-commit, and cleanup regressions.

## Run P-v12 schedule and budget

The exact `--sample 500` selection is 48 goals in 33 theories. Schedule TSV
SHA-256 is
`c6a797f0a951f09050f11bbef18f5a74e8b787c41fe0b5a238fd2eb66a20e299`.
All 24 slices are in batch 1 at 30 seconds; one goal is one 24-core wave.

| # | prover | filter | format / type encoding / lambda | facts |
|---:|---|---|---|---:|
| 1 | vampire | knn | fof / legacy | 96 |
| 2 | e | knn | fof / legacy | 128 |
| 3 | zipperposition | knn | fof / legacy | 128 |
| 4 | vampire | knn | fof / legacy | 512 |
| 5 | e | knn | fof / legacy | 512 |
| 6 | vampire | knn | fof / legacy | 32 |
| 7 | zipperposition | knn | fof / legacy | 512 |
| 8 | vampire | knn | fof / legacy | 1024 |
| 9 | vampire | knn | tx0 / mono_native_fool / lifting | 96 |
| 10 | e | knn | tx0- / mono_native_fool / lifting | 128 |
| 11 | zipperposition | knn | th1 / mono_native_higher_fool / keep_lams | 128 |
| 12 | e | knn | th0 / mono_native_higher / keep_lams | 512 |
| 13 | vampire | knn | th0 / mono_native_higher / keep_lams | 512 |
| 14 | e | knn | tx0- / mono_native_fool / combs_and_lifting | 1024 |
| 15 | vampire | knn | tx0 / mono_native_fool / combs | 512 |
| 16 | zipperposition | knn | fof / legacy | 32 |
| 17 | vampire | mesh | fof / legacy | 96 |
| 18 | e | mesh | fof / legacy | 128 |
| 19 | zipperposition | mesh | th1 / mono_native_higher_fool / keep_lams | 128 |
| 20 | vampire | mesh | tx0 / mono_native_fool / lifting | 512 |
| 21 | e | mepo | fof / legacy | 512 |
| 22 | vampire | mepo | fof / legacy | 1024 |
| 23 | e | mash | tx0- / mono_native_fool / lifting | 128 |
| 24 | vampire | mash | fof / legacy | 256 |

## Run P-v12 results

F30 ran from initially empty private state and completed 384/384 cells in
1,090 seconds with zero harness errors. Its run-header, journal, summary,
result, copy-back, volume-result, and cleanup hashes are:

- `8b9b6093e4f083ead809f3b45219474bae4fa911d05a689274c8d74614a15cd5`
- `7131ad85d4a2c75c464b58f05f37a3f7ef361a30cbd7389af47679c742595d0b`
- `1d7ffd9b77870b1b9d0b225982128a184545db7248e7f36be762b43af55ecf18`
- `adeebe7d620b9f7a3b46d999f77d74dd55f6382e75c16a1934d526656564c436`
- `4162f97172c65f47d0e0c5ac7ac2e0be70494a868007d49c4bf1ca8357e805cc`
- `8f2811b0e44cdc22ba2e9d3665ca2636f96184aa2845496d9ce71b2b1f0ea513`
- `98c4108be71404423545fe9e6880d46bbb75c61765818c8fff4601436a1ac68e`

| condition | proved | reconstructed | prover p50 / p90 / max (s) |
|---|---:|---:|---:|
| E knn128 | 9 | 8 | 0.413 / 28.193 / 28.193 |
| E mepo128 | 13 | 11 | 0.127 / 14.410 / 18.353 |
| E mash128 | 13 | 11 | 0.138 / 15.520 / 24.211 |
| E mesh128 | 13 | 11 | 0.156 / 28.216 / 28.239 |
| Vampire knn96 | 15 | 13 | 0.139 / 4.809 / 11.535 |
| Vampire mepo96 | 16 | 14 | 0.177 / 6.343 / 6.902 |
| Vampire mash96 | 16 | 14 | 0.096 / 0.493 / 3.043 |
| Vampire mesh96 | 18 | 15 | 0.178 / 3.113 / 17.184 |

MeSh meets or exceeds every single filter on proved and reconstructed counts
for E/128 and Vampire/96. This is preflight evidence, not the later F30
full-corpus core gate or the revised paired S30-v5 sample.

S30-v5 completed all 48 sampled goals and all 24 requested slices per goal
in 2,601 seconds. It proved 26 and reconstructed 22; bounded no-proof and
reconstruction failures are evaluation outcomes, not harness errors. Its
run-header, journal, summary, result, copy-back, volume-result, and cleanup
hashes are:

- `a1b8dbb49d0f9b1ce87b0f9f397f5e41ff21d552334193ce0bb1c64957904855`
- `f0ce257340e4fe5c4f5313e488ce309c1980b63549cd8e8f60a7be127de0aef1`
- `d3203c097206287c0013efb11048e00d313981244cdf2fe50bf3449926d2585a`
- `8c9c1f4ab1e58be73eb6e3040f6dc3372c4266faa7d97a9287a9e5ba05559173`
- `10fc905e9e89816c113ebcfcaa1fc5e70664b3f50bf610d75e330d4745954b6d`
- `6f00c297f2ad7c24723ef4b22382e112c03d64976247fe6ebaaaf06eb3a0af3e`
- `552f10245e37819c46d3887f0f0b83b3af65e0d7ba8b825a60a08b4670103ed7`

The deterministic durable volume fold discovers exports through validated
experiment metadata and rejects duplicate files, unknown filters, and gaps.
The F30 inventory is
`c7b1e45d746fdf3728d24bb670f73fa6af4ca53c3aef57baddf95de6ce0498ba`
(384 files); S30-v5 is
`647dadc879c5537797360a5abe475211c93ca2e3947485de4b12abf4a2b9f5c2`
(792 files).

| source | filter | exports | bytes |
|---|---|---:|---:|
| F30 | knn | 96 | 11,638,468 |
| F30 | mepo | 96 | 11,922,038 |
| F30 | mash | 96 | 11,163,887 |
| F30 | mesh | 96 | 11,388,266 |
| S30-v5 | knn | 528 | 229,964,568 |
| S30-v5 | mepo | 66 | 52,481,763 |
| S30-v5 | mash | 66 | 17,823,852 |
| S30-v5 | mesh | 132 | 31,212,269 |

Source and durable trees were byte-identical. Durable results were validated
before tmpfs removal;
volume folds and final certificates then consumed durable files only.

### Timing and context probes

The probe covers 24 schedule rows, 192 ranking rows, 33 target contexts, and
33 cleanup rows. Envelope, timing, result, and cleanup hashes are
`1a4d70ff5359db84b67c0e3010243784b563103ec0141f239b9e839a78baa809`,
`a12b45366243bd1ef54e3794a9a06d08f43927b15b12b10ce582f58f79d7dbf2`,
`6a8dbbd15938a92a6d2380f0a70c4e4b74c1919765ae9558945810615c0c6112`,
and
`ea3d5d1efe218d6ea4abea53ecbbed691a8e46195fb670d04c8f4fb310389952`.
Observed P peak memory was 39,459,356,672 bytes, with zero swap.

| filter | rows | mean | p50 | p90 | max | total (s) |
|---|---:|---:|---:|---:|---:|---:|
| knn | 48 | 0.389 | 0.365 | 0.568 | 0.918 | 18.692 |
| mepo | 48 | 0.324 | 0.234 | 0.548 | 2.492 | 15.575 |
| mash | 48 | 0.301 | 0.297 | 0.433 | 0.573 | 14.441 |
| mesh | 48 | 1.127 | 1.070 | 1.553 | 1.827 | 54.119 |

| context stage | rows | mean | p50 | p90 | max | total (s) |
|---|---:|---:|---:|---:|---:|---:|
| theory load | 33 | 1.850 | 0.780 | 4.045 | 7.943 | 61.046 |
| target thmdata | 33 | 3.884 | 4.172 | 5.435 | 7.346 | 128.158 |
| NB + MePo context | 33 | 1.445 | 1.293 | 2.246 | 4.119 | 47.696 |
| cleanup | 33 | 0.000000364 | 0 | 0.000001 | 0.000001 | 0.000012 |

## Run A-v12 derivation and result

Baseline profiles 1--8 run in the exact mapped gate state. Profiles 9--16
use genuine f751 Phase 2 scheduler/exporter behavior with provenance-bound
ranking journals. Current builds its own target-specific model and rankings;
it rejects every baseline model/ranking/premise environment. The independently
derived sides compare premises, profile descriptors, normalized argv,
request keys, and canonical rows.

Current first-eight traversal uses per-theory checkpoint chains in exact
`DB.theorems` creation order. A target model is built once before traversal.
Each atom keeps all eight profiles for a goal together, targets 420 seconds,
and retains the hard 600-second bound. Receipts bind prior/next heap, range,
DB order, model, goal, pool, ranking, row, source, object, runtime, and run
digests. Fold rejects gaps, overlap, branching, duplicates, wrong order,
mixed models, stale/corrupt receipts, and baseline/current cross-feed.
Obsolete heaps and atom payloads are pruned after rehashed durable commit.

The retained final-source storage gate is v34. Its evidence, equivalence,
profile-equivalence, checkpoint, reservation, and cleanup certificates are
respectively
`1ad32d58e21b6b8977db99b9d7194da6d276d67de6776d65e3d805c18cb22a9c`,
`295aacedb619f7f7cb4ba7ae473bc01d2186f19ecfd5ba2df5ca736d33135e97`,
`9cafdd0b7632a7ae5a50ed6d96b9a6bff5f33f50a122d6a9aa20b221852282a2`,
`e37c8fd30bb231d3cc33274f5416066b3655d27d5eff30668bc35ac5796f0574`,
`9ed983087cf232a82d7889ed5feec0b00c6c7df647c7d006ad564ab743a91970`,
and
`b40fe722bd8da13fdbe89c6ed532b6d8f8eed70d08d2ab1f35d09440c66e04bd`.

The retained mapped integration smoke is v28, input seal
`09db202d112ad8b2df8914987c4713562ef5c041a6b1e98e51999188cae186a4`.
It covers complete f751/f258 production paths, including gh224a (54 goals),
gh225a (2), and a 368-goal unequal tail: five members, 426 goals, 6,816 rows,
426 rankings, five chains, and seven atoms. Run, result, baseline, integration,
first8, resume, stale, corrupt, and cleanup hashes are:

- `87996adb1219ae51bfe9a232d63e8f7214e1774322de9777c2578d378492fb65`
- `a934f00aed0e9f30147d08c1a00d54f498444fc50f795baff0b78bf954068bc9`
- `9a6f7ccc070ace0268cdd38cc152b437e910ae3be3e9d4f9ae9d78c7a5bc3562`
- `2cea8d160a6b3197362206a8f35cf3e97621ae4aee762837350664fd451827a7`
- `59e563af0213e126e1c6e00554859e5a3be9c2d6c66d1488661fe379a9c5a121`
- `ca21937cb8c5ab9fd558058e9f165b2e5706f5e44b1532a614fb9259d544aca9`
- `0825acfba446d206bebc7f1e6a4c3ac524f26c7f7f7d03e37823e06a46bf7508`
- `b029007ea963f020c8aa570ed2b1ea560451f55682c28b334b4696bf139a1394`
- `618a946c5cb3f8d6c76deeb4ebe23fb54a821d6faa8af927301ef3b87ae7e9a4`

A-v12 ran from 2026-09-01T14:58:30Z to 2026-09-01T19:08:37Z
(15,007 wall seconds). Run header is
`c51fae74ad1ad831b1c6012c6135cba0044307d6f123174518119a77a485f016`;
baseline validation is
`249d94daedbb1148c2a5fae793ea9645bf28a426b298c6aefebbafd307d25ba1`;
result is
`934b69a7004d91ea639e4ccd25ca5ea7e3b52fb397a963c31676f032cf9086eb`.

Independent fold
`8b2504def61b2395c59870fa600e2d5ea2986e3824fee0263194ba3aa554757a`
validated:

- exactly 229 canonical members, 24,721 goals, 16 slices, and 395,536 rows
  on each side;
- 197,768 historical first-eight rows, with premise, request-key,
  internal-key, and historical prover-spawn counters all zero;
- zero current row mismatches, binding mismatches, and prover spawns;
- 229 gap-free checkpoint chains, 348 receipts/parts, and 24,721 independent
  ranking journals;
- zero partials, failure archives, nonempty mismatch journals, infrastructure
  retries, and computation retries;
- canonical inventory/body digest
  `1a519b8753270358747e9a75075f8d763d942f01d33f199e682a2022b59fe196`,
  canonical sorted body
  `424c40478df3fe96dfca9afc0d5db016a9c0c5126b37e2ecf98f93af0213982d`,
  and selected-premise binding
  `39f0e65f2d726690c709ab36a4d71b571692c08c120ff25f63e6046a52698173`.

Baseline and current model-binding inventories both happened to be
`dd43c86ad38813340ce39262df5c4e953c15c62d40e189e0200e6b3985bff9a5`.
This observed equality is not an input requirement; current derivation never
consumes the baseline model or ranking.

Exact durable-only resume is
`122de9a4ad3ad50d3df2ad3af4eeeccd476ff6fe98027f46da6c90e73ca9c9f9`.
Cleanup
`41db5c3623b13dd0e6059d3ed8b16f6cda51a73831c81bd19834ed0c7245f018`
proves the accepted state root absent before resume. The final-run certificate
is
`4a9f965a6571843a1b36abda51aa973e531ae20ecc42e68eaa9b0e10cf653660`.

A complete distinct challenger is retained at input inventory
`c801c9b0df8def17ef479ac3b496b8cc262e2857befcdacd0d61877ad392f97b`
and tuple header
`b526c74e159345cd5d2ee863475a4c5d031c2f02450f615512fa89ff37319043`.
Both seals were rehashed. Production verification emitted exactly
`task10 tuple mismatch: sealed input does not match accepted run header`
and exited 78. Cross-tuple certificate
`68bda5b156a33ddac3e23643b80cac16394a317195e2679fc374c8d230789c15`
proves the accepted 82,823-file / 18,955,837,315-byte tree, invocation log,
and absent state tree unchanged; its tree digest is
`68a510d49b68836da7de5f0ae993666d0423146bee9b6660bc10d8a2c8b35f6d`.
Final acceptance
`3ddeed2ae8219688e5a59ef66e23c24b5b78aae07beecaf9356fae2e9e3e8313`
rehashes and binds the supplied final-run and cross-tuple certificates and
proves its accepted final-certificate field equals the supplied certificate.

A-v12 peak memory was 106,187,804,672 bytes, with zero swap, high/max events,
OOMs, or OOM kills. All 577 flock acquisitions had matching releases;
maximum concurrency was eight. There were 18 recovered admission waits,
maximum 10 seconds; minimum external availability was 92,578,144 KiB and
minimum scope headroom 34,422,173,696 bytes. There were zero infrastructure
or computation retries; one expected bounded baseline worker recycle was
accepted only after its complete replacement attempt.

## Superseded evidence and final validation

The retained history inventory is
`d8e0e6e1481ed103ee28c7cd708a2fcc22191969005ce18093b9b17553d22aaa`.
It completely inventories 30 retained compact files. The immutable A-v12
predecessor snapshot contains the 27 records that existed when its tuple was
sealed, at
`b747df6623129d74eaae06c251f8afb592b4b98552f336d8602525574ac5addd`.
The external history additionally records A-v11's offline-verifier rejection
and the proactive A-v12-era cleanup manifest/completion. Nested bundles cover
P-v1's volume-fold rejection, P-v2's post-run-stage rejection, and the
A21--A24 compact rejection records. The P-v7/A-v9 cleanup manifest is
`0c147aa0b0263aaea07c65686250a95289b633c542d3677d65d0fca6af831792`;
it removed exactly ten certified paths, 87,651 files, and 20,188,148,367
bytes. The earlier P-v4/A-v6 cleanup record is
`4c6ab6a6138b354721b7e45c1f41e7b2a39b1da9d5919ffdad54048e9889188c`.
This is not a claim that every old A8--A26 or P iteration has its own retained
certificate. Other raw diagnostics were intentionally discarded and cannot
feed fresh-empty output. The proactive cleanup manifest
`af9d166677c7e099b6f24815abff7a917adadf7764c31942e15849b51a9e4420`
removed 104 superseded roots (129,582,469,120 allocated bytes) without
changing any accepted seal; its completion certificate is
`58b640d55586c8be7d40f2cabd8e9c23c249fd60a9fb54d4fb6b82eba1ad3c78`.

The production existing-output guards run before host-memory checks, input
boundary/admission logs, initialization, directory creation, or any mutation.
A distinct tuple returns the stable exit-78 diagnostic while same-tuple
resume proceeds to full fail-closed verification. Missing, corrupt, same,
wrong-diagnostic, unrelated-nonzero, trace-order, and before/after tree/state
cases are covered. P has the analogous ordering and gate.

On the final accepted source:

- target-scope, bounded-cache, goal-structure, MeSh proposition-equality,
  and monomorph equivalence/pathological HolyHammer regressions pass;
- runtime inventory, nonempty provenance, self-contained focused/integration
  support, mapped-state,
  scheduler-digest, large streamed inventory, checkpoint/storage, unequal
  tail, exact resume, stale/corrupt/cross-feed, flock/memory/OOM, teardown,
  tuple-guard, fold-schema, cross-certificate, and final-acceptance tests pass;
- all new shell scripts pass `bash -n`, and long new script lines were wrapped;
- `tools/h4pedant/h4pedant`, `git diff --check`, runtime byte-identity, the
  hermetic HolyHammer selftest, and
  `bin/build -t --seq=tools/sequences/upto-parallel` pass;
- `git diff -- src/AI/machine_learning` is empty;
- all accepted P-v12, A-v12, smoke-v28, and storage-v34 tmpfs roots are absent.

TASK_10's P and A acceptance criteria are therefore evidenced. The sampled
preflight deliberately makes no claim about the later full Phase 3
performance gate.

## Run F30-v6 full-corpus ensemble gate

F30-v6 is the accepted TASK_11 measurement. It ran from
2026-09-02T07:16:27Z until the original fold stopped at
2026-09-04T07:06:27Z (172,200 wall seconds). The run used the TASK_10
envelope: 32 workers, 30-second prover cells, 600-second worker recycling,
124 GiB `MemoryHigh`, 128 GiB `MemoryMax`, and zero swap. Systemd reported a
107.3G peak and zero swap. Its journal contains 26 OOM-killer notifications,
while the captured terminal cgroup `oom_kill` counter is 19; these are kept as
distinct runtime observations. The 3,212 atoms made 10,649 attempts: 7,411
bounded timeout recycles and 26 bounded OOM-related recycles, then all atoms
completed.

The sealed input inventory is
`acd7541e9efa02b114cb0829093ddc6b2caa4e82e61852f9d0c3fa5e9ddd0ea8`;
run-header SHA-256 is
`a9b977d457428440072d65826561c267e3697b26ddffb337bfa2c39fdd78df95`.
The measurement source was main commit
`1ba9e564f4856b3159361d41da90652ad8387b4b` plus tracked
`src/holyhammer` diff
`b4262e2ff6d59da9924577ee3de75fd2c842ae7edb599d08007deac9e842c333`.
E 3.2.5-ho and Vampire 5.0.1 were the pinned binaries recorded above.

### Exact corpus boundary and recovery

The first fold correctly rejected 198,648 rows because five loaded theorem
databases contained 110 post-corpus theorems. There were no missing canonical
goals and no duplicated goal-condition cells. The strict superset consisted
of 2 `finite_map`, 4 `pred_set`, 9 `bisimulation`, 34 `relation`, and 61
`cv_string_fmap` goals, each complete over all eight conditions.

The corrected fold does not infer membership from current `DB.theorems`.
It consumes the exact 24,721-goal inventory extracted from TASK_10 A's
accepted byte-identical baseline/current rows. Its inventory and certificate
SHA-256 values are
`ea11197c9334dc4a3358e914cf815d59ca23d1e5d8df598d3243cfe333ca2c56`
and
`8cbfff0962b4ff8e2456c6f4d72efa8756fa2e8aaecf34ac9206a2b4cd6c5e54`.
The latter binds TASK_10's final acceptance, final certificate, independent
fold, and canonical sorted body
`424c40478df3fe96dfca9afc0d5db016a9c0c5126b37e2ecf98f93af0213982d`.
Every canonical goal has exactly one row for every condition. No prover cell
was rerun, discarded within the canonical set, or tuned.

The raw 3,212-file journal inventory SHA-256 is
`30aa649a1da76d899a8e65ce9d69dc0b2157e76e66f0986e70a92c28cb681d67`;
the excluded-goal inventory is
`18d076852ee08e6f97132758f9fb3392cdec50b7ce405e52c53e94c3acddf3c7`.
The correction, result, shape investigation, and final certificate are:

- `43a98b591568c8967fb13301563874aafac526f71501ccac72bc90f8ad00225e`
- `4e8756211c4fdf8e33fa165c215460cbacaff7d38f25f97445b5e85d21dd719d`
- `295c62f316c154b7c83f5053d5cf14ba3a3ce016b4ff34d648defc8f0a9bd37a`
- `e8bc88e1a2dd6697d33807b34ccf00ead8d747083776c11aa240822051c6f531`

### Full-corpus counts and ensemble gate

| condition | goals | proved | reconstructed |
|---|---:|---:|---:|
| Vampire knn96 | 24,721 | 8,748 | 8,097 |
| Vampire mepo96 | 24,721 | 10,400 | 9,595 |
| Vampire mash96 | 24,721 | 9,599 | 8,902 |
| Vampire mesh96 | 24,721 | 10,870 | 10,083 |
| E knn128 | 24,721 | 7,133 | 6,707 |
| E mepo128 | 24,721 | 7,666 | 7,349 |
| E mash128 | 24,721 | 7,790 | 7,332 |
| E mesh128 | 24,721 | 8,332 | 7,917 |

The P3-5 ensemble gate passes. For Vampire/96, MeSh exceeds each of kNN,
MePo, and MaSh on proved and reconstructed counts. It does the same for
E/128. These values are gate evidence only and were not used to change any
slice identity, fact count, timeout, or ranking constant.

### Seen/fresh shape

The exact subset partition is 4,558 seen and 20,163 fresh goals.

| prover/filter | seen P/R | fresh P/R |
|---|---:|---:|
| Vampire knn96 | 2,569 / 2,354 | 6,179 / 5,743 |
| Vampire mepo96 | 2,834 / 2,624 | 7,566 / 6,971 |
| Vampire mash96 | 2,726 / 2,513 | 6,873 / 6,389 |
| Vampire mesh96 | 2,961 / 2,722 | 7,909 / 7,361 |
| E knn128 | 2,374 / 2,163 | 4,759 / 4,544 |
| E mepo128 | 2,430 / 2,297 | 5,236 / 5,052 |
| E mash128 | 2,548 / 2,317 | 5,242 / 5,015 |
| E mesh128 | 2,612 / 2,396 | 5,720 / 5,521 |

Hard criterion (a) passes for E (`2,548 >= 2,430`) but fails for Vampire
(`2,726 < 2,834`). On the 4,558 paired seen goals, Vampire MePo and MaSh
both prove 2,417, MePo alone proves 417, MaSh alone proves 309, and neither
proves 1,415. Thus the 108-goal deficit is not a coverage, pairing, or fold
artifact. It realizes the plan's recorded Judgment-Day risk that the learner
can lose to MePo for an individual prover. The failure was escalated without
retuning; MeSh still exceeds both single filters. On 2026-09-05 the owner
accepted this explicitly retained criterion-(a) failure because the core F30
MeSh gate passes for both provers; it is not reclassified as a pass.

Direction check (b) passes for both provers. Vampire's MePo/MaSh proved
ratio is `7,566/6,873` on fresh versus `2,834/2,726` on seen; E's is
`5,236/5,242` versus `2,430/2,548`.
The independently regenerated criterion-(b) investigation is SHA-256
`ed0960623f25a846d35a4a3ed7b6cc6f92fa589e8a8ea5ccad0b3d712ce1c3d1`.

### Verification and disk hygiene

Before compaction, the independent verifier rehashed every original atom
tree and matched all journal and atom certificates. The current compaction
certificate
`0a6b2ccbdf347dac2606dfbebb1d1f3483ef3645c98a71f8edf043f043667696`
then removed 3,212 redundant artifact directories, 400,609 files, and
30,875,432,064 bytes, plus 3,212 logs. Canonical journals, atom certificates,
the sealed input tuple, final result, and a self-contained frozen verifier
remain. Its verifier inventory is
`e0a3709335e8316ec07973020f1dcb3dc12d76f63162aeed412909c2776107dc`.
The immutable v3 predecessor lineage is bound by inventory
`cffc56fc60085e9f3c7c5396a506b2fe37119c9afdbebb59f9e7b4ab4e5732ec`.
The compact evidence is 114 MiB.

Durable-only resume certificate
`6ff11bcba285b3c93691d7ef60449daf05f3067938fc6e143e5f0549e0807e8c`
proves the retained 6,463-file, 98,820,416-byte run tree was byte-identical
before and after an independent refold and re-verification, with the tmpfs
state absent throughout.

The completed envelope is
`3ad295ecac4068210f03f6afbfd76fd7b1c74b0a0f18455279a055d9af55ebb0`.
It binds the original running envelope, the result, and terminal service
certificate/log hashes
`3fbfc0174687c4162ddc3b409750689e5481e35bca3198b7b53a8b8e4fb28a38`
and
`047c095eecc9f96c69a9f60c97f77b817f9450d333fc1be31c821ed7e9f05321`.

The maintained harness passes its hermetic fold, duplicate-cell rejection,
sealed-input tamper rejection, atomic pending-artifact recovery,
mutation-free replay, excluded-cell field rejection, and corrupt-certificate
rejection tests. The actual frozen verifier also passes from an arbitrary
mutated working directory without changing the accepted tree, and rejects a
missing or modified frozen dependency. A freshly
sealed disposable tuple verified itself and passed the same harness tests.
The focused HolyHammer selftest, `tools/h4pedant/h4pedant src/holyhammer`,
`git diff --check`, and
`bin/build -t --seq=tools/sequences/upto-parallel` pass. The diff under
`src/AI/machine_learning/` is empty.

## Revised S30-v5 paired sample and K

On 2026-09-05 the owner replaced the projected full-corpus S30-v5 gate with
a bounded paired-sample decision. The service stopped at its next atomic
certificate after about 96,805 seconds; structured systemd records span
96,806.352413 seconds (2026-09-04 16:31:43.796484Z through
2026-09-05 19:25:10.148897Z): 408 fixed-order shards, 3,119 goals, two valid empty
shards, and 410 attempts. `borel-4-of-27` and `borel-14-of-27` each have one
exact restart/resume event with atomic journal continuity. Their causes and
statuses were not retained and are unknown. Systemd
reported 79.2G peak memory, 0B swap, and 2w 19h 21min 38.591s CPU. Journal
and atom-inventory SHA-256 values are `d7715a892b0ccb06e2123855ad57371e3432b0b9d7d13dee05388e66e54ef921`
and `49610a1da885c0c6e842abde204416b714e1031f03ff81044ab931cb2a2a6c44`.

The sample is the 3,000 lowest bytewise `SHA-256(goal_id)` values in that
complete frame. Atom order was fixed at run start; only whole certified atoms
enter the frame; selection reads identity, not outcome or timing, and was
sealed before the Phase 2 join. Thus no fast goal or partial atom can enter
preferentially. Inference is limited to the 3,119-goal frame. Selection,
S30-v3 sample, and S30-v5 sample SHA-256 values are
`9d0783edf3ce42e993b3eba1e0b206475a31cca57f8b89024f23c8076b0530d3`,
`4c0da14d6a7e5054fe6976ba26cdce76244b0e4b28ff990768f55344a3b322a2`,
and `2f729aaed8b1c8055bfcb8ddf94e74d290b3b7fbf9cc88fa52c25a36359fbd34`.

| outcome | S30-v3 | S30-v5 | wins / losses / ties | delta | paired 95% CI |
|---|---:|---:|---:|---:|---:|
| proved | 1,731 | 1,856 | 129 / 4 / 2,867 | +125 (+4.167%) | +3.428% to +4.905% |
| reconstructed | 1,221 | 1,714 | 497 / 4 / 2,499 | +493 (+16.433%) | +15.094% to +17.772% |

The intervals use sample variance of paired binary differences and are wholly
above zero, so neither endpoint has a statistically credible regression.
The exact-full-key paired result and revised sample certificate SHA-256 values
are `f07711939e9f2003804d1a492085cd62f41462b8f1a6a986ff758ae9db23b875`
and `efd116c96f4eec9b2bc78fcccd2f9923b089e3a7948a21d17e4e624823dac38e`.
Every distinct sampled loss was inspected and retained:

| goal | P loss | R loss | S30-v5 observation |
|---|---|---|---|
| `HolSmt.r128` | no | yes | theorem; Metis reconstruction failed |
| `alist.alookup_distinct_reverse` | no | yes | theorem; Metis reconstruction failed |
| `bag.SUB_BAG_UNION_eliminate` | yes | yes | `GaveUp` |
| `bar260.foo_component_equality` | yes | no | `ContradictoryAxioms` |
| `bar260.foo_fupdfupds_comp` | yes | no | `ContradictoryAxioms` |
| `binary_ieee.flags_nchotomy` | no | yes | theorem; Metis reconstruction failed |
| `bitstring.el_field` | yes | no | `ContradictoryAxioms` |

The loss evidence SHA-256 is `6b065371b80406d5c874acd7d1d041dc5a8c791ecb41c0c463c2fa920fd7dfbd`.
No constant, slice, subset, timeout, or schedule was tuned.

### Eight appended slices (sample only)

| # | prover/filter/format/facts | winner P/R | successes | exclusive P/R |
|---:|---|---:|---:|---:|
| 17 | Vampire mesh FOF 96 | 247 / 232 | 1,519 | 77 / 65 |
| 18 | E mesh FOF 128 | 86 / 84 | 1,198 | 30 / 29 |
| 19 | Zipperposition mesh TH1 128 | 24 / 22 | 466 | 4 / 4 |
| 20 | Vampire mesh TX0 512 | 34 / 16 | 353 | 19 / 1 |
| 21 | E mepo FOF 512 | 37 / 35 | 811 | 9 / 9 |
| 22 | Vampire mepo FOF 1024 | 194 / 181 | 1,459 | 60 / 51 |
| 23 | E mash TX0- 128 | 23 / 19 | 364 | 5 / 3 |
| 24 | Vampire mash FOF 256 | 194 / 184 | 1,456 | 42 / 38 |

By filter, mesh supplied 391/354 winner P/R rows, mepo 231/216, and mash
217/203; overlapping success totals were 3,536, 2,270, and 1,820. Exact-full-
key anchor-exclusive slice sums are mesh 130/99, mepo 69/60, and mash 47/41.
Anchor/new identity never uses journal array position, and reversing all 24
slice rows in every sampled goal reproduces the byte-identical semantic fold.
One anchor-failed goal may be attributed to several new slices, including
slices from different filters, so these are overlapping slice-attributed sums,
not distinct-goal counts. These are sampled Phase 8 seeds only.

### K and terminal evidence

K used the first 128 goals of the sealed hash order, subset SHA-256
`a385552c273b1a29e9014f55d199f849ad64c1b9b2a3883874677f0d928aaf79`.
The accepted witness was produced from a genuinely fresh state root. Its
empty-cache seed counted 3,153 spawns: 3,072 slice launches plus three version
queries in each of 27 theory workers. Before either post-seed pass, the
producer proved that the fail-if-existing prime and replay roots were absent;
the state contained only `hammer` and `seed`. In every fresh paired HOL
process it explicitly resolved E, Vampire, and Zipperposition, recorded the
expected 81 version-probe spawns, and only then reset the counter.

The prime cache-check and replay use distinct new journal roots. Each has the
exact same 128 unique goals and all 3,072 slice rows `cached=true` across all
four filters, with measured post-reset spawn totals 0 and 0. The 3,048-file,
296,594-byte real cache was bytewise unchanged; the canonical manifest
captured immediately before prime and after replay has SHA-256
`27bffb4224f2d8821c1b70b71b8545ee0a5d4744bdbab9fd7986ceef2ddc582d`.
Seed, prime, and replay journal SHA-256 values are
`c498ad79576cac1b3d11270348b75f3bf7096a7b281a9f0686dfb3546815a723`,
`e29e9fd51dafaf66768f0cb8687fa550d2b9f72993c748729a8714017752867e`,
and `dd6c3bf9a8a13bfb846f40d0751cca09dbbc9edf36cde0015e11b6349e76f531`.
The fresh-root proof is
`6effd75e9540ac7fd24498bd862c3c00cd76e79582fe12da1003e85c10dff1f8`.

The single producing service invocation
`1d3f9b504d46431fb6ec1b8ff9ad13f0` ran for 6,514.723355 seconds, used
60,462,719,148,000 CPU nanoseconds, peaked at 24,904,933,376 bytes, and used
zero swap. Its complete two-record journal contains no failure record. K and
terminal certificate SHA-256 values are
`2ee1c97097e654caf4511b775ef86e121d90979c118c5a73ebfe68615d86923b`
and `ecee3f43e8d38810a96e40b5bf7e05b049c288e158c38d92c6ce00f461785e02`.

The frozen-verifier inventory is
`cb92e615e9c7b4cb3a75abe60414e62a478d649dc4e66121552c8d9960abcb19`.
The structured endurance journal and terminal certificate are
`5e35c5ebd09c7bd9f484822ba0d172d8dac0434c173933deb987dbf2a4b5d7d5`
and `186a7477550eb0699b11931aa7d680aa97be269b0f0b2356c376370eafa88482`.
Independent semantic recomputation using the real `hhEval.sample_hash`
partition semantics, deterministic atom splitting,
unrelated-directory nonmutation, coherently resealed result/row/schedule/
atom tamper rejection, destructive-path and symlink-escape rejection,
missing-dependency rejection, atomic-copyback, exact resume, and tmpfs
cleanup tests pass. Whole-journal slice-row permutation is accepted with an
identical result, while wrong, duplicate, and missing full schedule keys fail
closed. The maintained extraction reproduces the hard-bound
Phase 2 sample, and clean fold/certification reproduction is byte-identical
to the final sample and evidence tree. The original untracked runner bytes
were compacted and are not falsely claimed. The sealed equivalent bundle
includes an executable reference controller and real HOL worker adapter. It
accepts the target database's deterministic worker order only after checking
exact partition-set equality, binds that order, and atomically publishes
journals and certificates from output-local partials. The dependency closure
checks the exact source commit and explicit empty allowed-diff manifest, HOL
heap and executable, three provers, all 3,023 compiled runtime artifacts, six
artifacts for each of 229 target theories, and 42 host runtime/tool
dependencies. Its shuffled-order bounded fixture passes restart,
set-membership, atomic-copyback, and cleanup checks.
The equivalent-runtime provenance and dependency-certificate SHA-256 values
are `76c0cb9b2b2f5d9ec3909e0c6e8819c5ff7efa64493fafbb8e1e11db540e1702`
and `b57f8e0bfb1c1f95d976a95aebd072af3e4388493f7c8ea6aff56d6e60a3a200`.
Superseded bulk, stale TASK10/TASK11 runtime roots (including all four
`phase3-task10-{anchorcheck,anchorcheck2,anchorcheck3,currentcheck}` roots),
failed TASK12 transient units, and all TASK12 tmpfs children were removed.
After verifying their accepted hashes were preserved in compact certificates
or TASK11's sealed copies, three superseded TASK10 trees totalling about
35.5 GiB were also removed. Compact TASK12 evidence is approximately 58 MB;
an additional exact 224-root `/tmp` manifest (10,255,043,655 apparent bytes)
was proved unreferenced by accepted TASK10--12 evidence and removed, increasing
filesystem free space by 5,532,090,368 bytes after reflink/sparse accounting.
The remaining 551 matching user-owned direct `/tmp` entries were then
classified individually in an exact path/type/size/SHA-256 manifest: 521
regular files and 30 empty regular files, totalling 225,429,428 bytes. The
repository scan found only three references, all in one historical loop log
and none an accepted evidence dependency. Therefore all 551 were deleted;
zero were retained, including `/tmp/task12-keyed-result.json` and the
158,805,751-byte `/tmp/task10-review-repo-basenames.tsv`. A fresh scan finds
no matching entry of any type. Unrelated `/tmp` entries were outside both
explicit manifests and preserved. The direct-file manifest is
`bc7f63b41366adfc9af1f90f30bd62852814ac64d983c2fdd77eca7d281183dd`.
The final cleanup certificate is
`db4f7a3c86aca05a4a27e7e8740290257939af202cc0dec604542f2ce55ef006`;
the combined `/tmp` cleanup certificate is
`729a8fe5c8b8bb94b26f49573d6cd3d58e51e368196abecc8729083376ff98b8`.

Full-corpus S30-v5 totals were not measured and cannot be inferred or
claimed. Historical S30-v3 13,198/11,155 and S30-v2 12,531/10,797 totals are
context only, not sample gates.
