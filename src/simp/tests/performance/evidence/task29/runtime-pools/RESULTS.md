# TASK29A complete post-workload pool attribution — NOT closure

## Scope and retained inputs

Baseline: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Candidate: `441d97888ddcb04a96646c97f1e8f2ee42a94c73`.
Platform: Linux/aarch64, ordinary Poly/ML 5.9.2 native full-64 runtime.
No production source, ordinary fixture, numerical threshold or zero-GC/B/B
rule changed. This is not an independent-build or universal-platform claim.

`record.json.xz` and `collector.json.xz` each retain a fresh B/B and B/C
structural pair: eight final diagnostic workload processes in total. Common
predeclared counts are 33,554,432 for `frag_record/0` and 64 for
`compile_collector/10000`, with the same fixed calibration history and three
samples per process. One structural pair is deliberately NOT a ten-pair gate.

Each archive contains the complete compressed raw stdout, process receipts,
paired manifests, comparison, diagnostic input seals, native build receipt
and exact interposer binary. The interposer is identical across all four
comparisons: SHA-256
`a01959efdd4d9159b22f6f4ceb90ed5da6db709002a64106976e65528e7258ee`,
71,792 bytes. The ordinary runtime/library fingerprints remain bound by the
paired manifests. The ABI source audit is not installed-runtime build lineage.

The native DSO is preloaded only in diagnostic Performance processes; the
ordinary runner's environment sanitization is untouched. After the original
target returns, a separately compiled postlude activates the hook only around
`showSize` of actual `run`, `step`, `measured`, `experiment` roots. Original CODE
printing is retained, then the runtime helper supplies the real pool address,
count and every raw word. Source/proof/runtime admission, extent, owner,
inline equality, split-trailer addresses and shared-pool contents all pass.

**The preload changes process layout, and postlude/FFI/traversal can allocate
or move objects after timing. These are not ordinary measurement-boundary
snapshots. No diagnostic timing is admissible.**

## Omission closed, equality not established

Every final process has 213 distinct split pools, with **1,326 words including
headers**, zero of which were already printed as ordinary objects. Their
storage is reported separately from `showSize`, not silently added to its
footer. Every CODE object has a validated record: 2,566 per fragment process,
2,533 per collector process. No pool slots remain omitted.

Every process has 1,168 adjacent ADRP/LDR64 patterns resolved to actual split
pool slots. The decoder reports zero unresolved patterns and zero unresolved
object/pool pointer slots in these captures. These numbers describe the
supported static patterns only: no disassembler-completeness, dynamic target,
byte-object pointer interpretation or cost-equivalence claim follows. Dummy
split trailers are metadata and are not counted as executed instructions.

Actual `run` callable captures remain two words for fragment, three for
collector. All four roots' native sizes match within every comparison, as do
their immediate-masked instructions. Fragment's captured build code is also
34 words on both sides with matching masked instructions. Raw operands,
code/pool addresses, alignment and decoded targets remain in `attribution.json`
and the archives; names/masked words do not establish target equality.

| Case / comparison | Matched objects | Matched pools | Raw-slot faults | Native-word differences |
| --- | ---: | ---: | ---: | ---: |
| fragment B/B | 33,827 | 2,297 | 1,401 | 30 |
| fragment B/C | 32,509 | 2,023 | 3,268 | 118 |
| collector B/B | 506,053 | 2,500 | 90,813 | 4 |
| collector B/C | 493,675 | 1,949 | 174,026 | 143 |

Correspondence is rooted at actual tuple/closure/raw pool slots, preserves
object and pool aliasing, and reports concrete paths. It is not a solution to
pool permutation: different ordering can cause cascading mismatches. No rows
are removed as noise or relabeled parity. For example, fragment B/C first
diverges at `roots.measured.slot[0].pool[2].pool[4]`, where the actual targets
are `MatrixSupport.fragwork(4)verify(1)` versus
`MatrixSupport.basic(3)(1)`; another slot has the reverse labels. Collector
B/C first diverges below `roots.run.slot[0].pool[2].pool[4]`, with different
actual sizes for two same-named `List.map(2)()` bodies. Repeated names cannot
repair that correspondence. B/B also has faults and large retained-graph
variation. Those are not grounds to waive the candidate gates or infer host
noise caused them.

Original `showSize` totals (separate from split storage):

| Case / comparison | Baseline words / objects | Other words / objects |
| --- | ---: | ---: |
| fragment B/B | 412,600 / 34,858 | 412,600 / 34,858 |
| fragment B/C | 412,600 / 34,858 | 412,599 / 34,858 |
| collector B/B | 2,780,452 / 617,010 | 2,407,845 / 506,211 |
| collector B/C | 2,780,452 / 617,010 | 2,397,860 / 506,216 |

Reachability contains mutable runtime/I/O state and retained construction
results. These are not cumulative allocation, process live-memory or
executed-work measurements. Equal/similar totals are not graph equivalence.

## Executable checks and replay

```sh
python3 -B src/simp/tests/performance/evidence/task29/runtime-pools/replay.py
```

`validation.json` seals diagnostic sources/docs, scripts, check logs,
environment and all three archives. Replay losslessly unpacks each final
archive into a temporary directory, fully re-admits both selections and
regenerates every `attribution.json` summary. It recomputes the environment
counter derivation too. `derived-replay.log` records successful generation;
`final-replay.log` records the independent comparison replay.

- Both real experiments: **14/14 tests pass**, no skips, including actual
  native controls and eleven coherently resealed archive mutations.
- Native controls run ordinary Poly/ML with positive inline/split capture,
  absent extent, non-code root and absent preload. Missing interposition is
  never admitted merely because the library was opened.
- Synthetic controls check signed pages/boundaries, register guards including
  XZR versus SP, shared pools/storage, actual root paths and aliases,
  truncation, empty pools, missing/duplicate/early/wrong-owner records,
  inline disagreements, rejected receipt retention and timing rejection.
- Coherent archive mutations cover comparison, Git source, loader, postlude,
  fixture DSO, process inventory, actual preload, binary, native build recipe,
  build output and proof trace. B/C substituted into the B/B role also rejects.
- Current-tree discovery: **421 performance tests**, seven opt-in skips;
  **196 compatibility tests**, no skips. The maintained runner-only discovery
  additionally passes 13 tests. These are machinery checks, not timing gates.

`development-record.json.xz` preserves the complete earlier four-process
fragment development experiment. Review found insufficient guard coverage
(empty split pools, XZR/SP semantics, early records, native build recipe and
rejected receipt retention). Source/input changes invalidate its admission:
it is not a final archive, not substituted for either final pair, and not
accepted by the current input seals. Final captures were rerun in full after
all source/test corrections. No favorable timing repetition was selected.
All private build trees, unpacked copies and temporary native binaries were
removed after their last use; only sealed, compact unique evidence remains.

## Environment: exclusivity is not verified

`measurement_environment.py` and its 15 passing synthetic tests implement a
read-only two-second environment observation, not a scheduler reservation or
benchmark. `environment.json` records 2026-10-25 10:57:08.907737 through
10:57:10.917732 UTC, with raw visible counters/limits, namespaces,
capabilities/affinity, load and storage. Status is explicitly
`exclusive_not_verified`, `exclusive_verified=false`.

The visible `user.slice` CPU delta minus the enclosing session scope is
**7.891824 CPU-seconds** over that observation. Other overlapping ancestor
residuals are retained, not summed. Counters are sequential rather than
atomic; they are estimates and cannot identify the workload or its timing
effect. Positive activity is observable, but even zero/unavailable residuals
would not certify exclusivity. The sandbox has a separate process namespace,
no effective capabilities, read-only cgroup control and no enforceable
exclusive host reservation. Cooperating advisory locks are not such a
reservation. No quiet-host or host-noise causal claim is made.

## Acceptance remains unsatisfied

No numerical decision is replaced. The historical complete grid remains
**43 failed / 119 inconclusive cells**. The repaired-driver fragment/0 still
fails CPU (CI **[1.014519, 1.032057]**), wall and GC. Collector/10000 CPU
**[0.988111, 1.032104]**, wall and GC remain inconclusive after unchanged
control admission. These values come from the retained ordinary experiments,
not the instrumented diagnostic processes here.

Supplying post-workload pools does not provide ordinary-process boundary
snapshots, executed indirect-target traces, complete generated-work
correspondence or a causal explanation/compatible repair. Diagnosing all
failed/uncertain cells and the entire fresh passing 162-cell repaired-driver
grid with admissible controls remain missing. No unsupported exclusive
full-grid run is presented as acceptance.

The task explicitly also requires an exclusive stable measurement environment
and policy-owner disposition of zero-GC 0/0 and directional B/B upper-CI<=1.
Neither authority is available from this sandbox or supplied by this request.
The unchanged policy makes persistent all-zero GC nonpassing, and precise
B/B intervals straddling equality do not pass or prove host instability.
Those facts cannot be repaired by more identical observations or a tool-only
threshold change. `TASK29A_POLICY_REVIEW.md` remains the explicit review
contract; nothing here authorizes a waiver or alternative.

**TASK29A is NOT complete.** TASK29 remains blocked; TASK29B's allocation
coverage/lineage/matrix is independent and untouched by this diagnostic.
