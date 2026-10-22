# TASK12 structural allocation inspection

This is additional evidence, **not a timing benchmark**. It changes no
production source, existing performance fixture, or existing runner. Run from
repository root (the output directory must not already exist):

```
PYTHONDONTWRITEBYTECODE=1 python3 \
  src/simp/tests/compatibility/task12_allocation.py \
  --output /tmp/task12-allocation
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s src/simp/tests/compatibility -p test_task12_allocation.py
```

The script reuses `run_paired.extract`, `install_fixtures`, `execute`, and
`validate`. Its new Holmake target links only the protocol loader, runs the
maintained SML fixture through `CheckSupport`/`testutils`, and elaborates each
private source selection in a fresh `hol.state0` process with private-first
search paths. It audits the ordered completion protocol, source inventories,
implementation/signature use, exit status, input hashes, and module exclusions.
Temporary source/build trees are removed on success or failure. No SML is
piped into `bin/hol`. This remains mixed-source isolation, not two independent
repository builds. The native allocation-site parser requires AArch64.

## Source correspondence

Default selections are baseline `cccaa27d7099cbadc886983020cbe745db7793f3`
and candidate `HEAD` (run on the TASK12 landing, or pass `--candidate`).
Archived evidence used snapshot `06927a63d9796d33d6cc98f936c2cab27f3b66a5`.
Every extracted candidate implementation/signature must match the worktree.
`audit_task12.structural()` additionally verifies:

- `Cond_rewr.sml` is exactly baseline with the tracking block replaced by
  aliases to `SimpTracking`;
- the direct `COND_REWR_CONV` constructor and all staged bodies are unchanged;
- `SimpTracking.sml` contains exactly the moved baseline tracking block;
- the associated extension/import and single tracking-slot ownership checks.

No source is modified to make the assembly or graph inspection possible.
`Task12AllocationRunner.sml` only enables `PolyML.Compiler.assemblyCode` while
elaborating the private `Cond_rewr.sml` and (candidate) `SimpTracking.sml`.

## Retained graph experiment and result

For each of unconditional, conditional, and genuinely permutative AC rules,
use 0, 1, 8, 64, 256, and 1024 independently named/instantiated source rules.
Keep lists at the constructed, solver-bound, stack-bound, and proof stages.
Check every resulting theorem's full equation and hypothesis set. The AC
input is explicitly selected in the descending ordinary ordering direction.

Each incremental size is

```
objSize (base, results, base) - objSize (base, [], base)
```

`base` roots all inputs, the solver, and prior stages. A separate constant-size
sentinel constructor roots shared matcher/module dependencies even at n=0.
Thus the root tuple and static first-root costs cancel. Lists remain counted:
these are retained graph words per rule, not closure-layout measurements.
All five adjacent finite differences must be constant; no fitted regression
or dropped points. A fresh `ref` per list element is a sensitivity control,
measuring exactly **5n words** in both selections.

Observed slopes (baseline -> candidate), including list storage:

| Incremental stage | Unconditional | Conditional | AC |
|---|---:|---:|---:|
| Constructor | 23 -> 22 | 23 -> 22 | 23 -> 22 |
| Solver-bound | 13 -> 12 | 13 -> 12 | 13 -> 12 |
| Stack-bound | 14 -> 13 | 14 -> 13 | 14 -> 13 |
| Proof results | 3 -> 3 | 32 -> 32 | 3 -> 3 |

All n=0 increments are zero. These exact slopes apply to every interval,
including 0->1. There is **no extra retained per-rule allocation**; each
closure stage retains one word less. The stages are separately anchored,
not three alternative measurements of the same combined root.

## Native compiler inspection and result

Compiler listings support the graph result without any representation casts:

| Generated stage | Baseline reservation | Candidate reservation |
|---|---:|---:|
| Constructor returned closure, `(3)` | 72 bytes | 64 bytes |
| Solver-bound closure, `(3)(1)` | 80 bytes | 72 bytes |
| Stack-bound closure, `(3)(1)(1)` | 88 bytes | 80 bytes |

The native application body `(3)(1)(1)(1)` has **28 reservation sites**, with
identical ordered reservation sizes in both versions, including cold tracking
and exception paths. Its 64 indirect call instructions are also unchanged in
count. The parser checks every generated `COND_REWR_CONV` function: no added
reservation site or larger reservation, and no increased call count.

Crucially, the tracking code is still **inlined into the application body**
across the opaque module boundary. Both listings contain the thread-local
lookup and update sequences there, not an added `note_rewrite` call. The
candidate uses literal-pool loads of the tracking key where baseline uses a
captured environment field (e.g. `[x8,#72]` in this compiler's listing). This
explains the smaller staged closures. The application listing has 842 vs 846
32-bit entries (including metadata/padding); it is **not byte-identical**.
The native closure reservations corroborate the one-word graph reductions.

The full compiler listings and inventories are retained once as compressed
logs in `../evidence/task12-allocation/`; `manifest.json` contains all rows,
finite differences, native reservation offsets/sizes, source/tool seals, and
comparison verdicts. `*-run.json.gz` holds the validated protocol/path audit;
its original stdout hash refers to the corresponding full assembly log.

## Limits

`objSize` measures reachable graph words, not cumulative transient allocation,
RSS, lifetimes, or GC cost. Native reservation sites are a structural check,
not a dynamic path sum or a proof about every external callee. Inspecting the
unchanged application source plus inlined tracking and unchanged reservation
sites closes the specific added-per-rule-allocation concern on this Poly/CPU;
it does not prove instruction-for-instruction equivalence or equal runtime.
In particular this does not resolve the noisy AC timing ratio into either a
speedup or slowdown. No timings were rerun, and no claim about the timing
confidence interval follows from these structural observations.
