# TASK_15 handoff — baseline ordinary fragments

Landing identifier: **TASK_15-fragments-v1** (containing commit).
Start HEAD: `1cb8802770fb9e291951b8a1bd7d4bd1a529bb80`; main worktree clean.
The unrelated nested `.agent-files` state was preserved. Pinned develop:
`cccaa27d7099cbadc886983020cbe745db7793f3`. Production validation snapshot:
`658ebe540693977332e8c08cfc88cd434a0d9d04`. Final production sources are
unchanged from that snapshot. Runtime: Linux/aarch64, Poly/ML 5.9.2;
paired processes use `hol.state0` and one GC thread.

Exact commands, exits, source/tool/input seals and artifact hashes:
[`evidence/task15/validation.json`](evidence/task15/validation.json) and
[`commands.json`](evidence/task15/commands.json).

## Bounded acceptance

**All TASK_15 acceptance criteria are satisfied; no TASK_15 blocker remains.**
This is the fragment representation/construction cutover, **not** a pass of
whole-module loading, compiled storage, or the final default-runtime gates.
In particular, the raw full-module timing measurements below remain visible
and are not represented as recovered default performance.

- Ordinary `ssfrag` is a standalone single-constructor datatype with exactly
  develop's eight fields. Rewrites are `(thname option * thm) list`, AC is
  `(thm * thm) list`, and conversions contain baseline `convdata`, not paired
  closures. No fragment constructor/update/merge allocates a source serial,
  slot, origin, inventory, strategy, configured runner, lazy cell or side table.
- `SSFRAG`, empty/named/anonymous fragments, updates, `add_named_rwt`, AC,
  merging, relsimp, TypeBase, marker-generated Cong/AC and printing use baseline
  construction paths. Named registration remains the ordinary context slot,
  with its original replacement warning and anonymous rejection.
- Paired tests execute **105 behavior/proof checks per side**, at 0, 1, 10,
  100, 1,000 and 10,000 rules/pairs, plus **41 route checks per side**.
  Complete theorem conclusions and hypothesis sets, list/name order,
  duplicates, input persistence, registration and TypeBase failures are checked.
  The **69 route observations match exactly**, including rendering at two
  widths, history extraction, named/anonymous duplicates, exclusions/force-add,
  makers, conversion traces, collectors, malformed tags and exception identity.
- Every one of the **90 incremental retained-graph rows is exactly develop**,
  including intercepts and every adjacent per-input slope. The empty record is
  nine reachable words; anonymous/individually-named rewrite growth is
  six/eight words per rule. No graph increase is tolerated. The fresh-ref positive control is five
  words per element. These are graph words, **not** cumulative bytes or RSS.
  Exact baseline constructor work and emitted reservation sites additionally
  rule out new short-lived fragment bookkeeping hidden by graph subtraction.
- Native/compiler-tree inspection resolves local generated-work uncertainty:
  `ac_ss`, `SSFRAG`, both update/name stages and `rewrites` match after only
  constant-pool relocation normalization. Common named/rewrite helpers match.
  `merge_ss` has one more caller instruction, but its named optimized tree and
  concrete-register ICode establish that `NONE` setup moved out of a removed
  wrapper; the same fold/reducer work remains, bypassing six wrapper fast-path
  instructions. There is no extra local call, reservation or traversal.
  The strict assembly-equality checker **still rejects** 184 versus 185;
  it was not weakened to conceal this real code-generation difference.
- Source-sensitive builders remain in `simpExtLib` only. Its signature/body
  are byte-identical to TASK_14, preserving explicit tracked slots, origins,
  prepared matchers, inventories, actual quotas and shared projections.
  Normal integration freshly executes its **88 + 174** focused checks.
- The still-transitional ordinary compiler consumes the baseline lists using
  installation-local ordinals only. Paired event logs preserve decode-all-tags
  -> AC -> all makers -> conversions -> existing collectors ordering, including
  malformed/throwing earlier stages. The downstream compiler and required
  routine sanity build both pass.

## Files, APIs and ownership

See [`migration/TASK15.md`](migration/TASK15.md) for exact API/removal decisions.

- `simpLib.sml`: restored fragment types/bodies; separate the transitional
  compiled payload as `compiled_convdata`; adapt user conversions only at
  installation, and number rule inputs there rather than storing source slots.
- `simpLib.sig`: remove unused ordinary threaded/strategy/view/bundle fragment
  builders and the dependent bound-bundle tactic. Their explicit extension
  equivalents remain available. No ordinary baseline API needs migration.
- `src/simp/src/Holmakefile`: integrate the private paired fragment/route gate
  at `HOLSELFTESTLEVEL=1`, including cleanup of its normal log.
- `tests/fragments/`: ordinary paired fixtures, fixed-count consumed-result
  timing runner, source/path/protocol validation, graph controls, additional
  routes, native/optimized-tree inspection and per-workload statistical reports.
- `audit_task15.py` / `test_task15.py`: token-level baseline correspondence,
  complete constructor inventory, no hidden allocation/state, installation
  staging and unchanged extension ownership, with fail-closed mutations.
- TASK_13's audit accepts only the exact reviewed TASK_15 ordinary-source seal
  **and** its bounded structural audit. Retired ordinary threaded mutations
  become reintroduction tests; the original extension threaded mutations and
  historical evidence remain intact. No frozen input or assertion ledger was
  regenerated, and `selftest.sml` itself is unchanged.

CUTOVERS ledger: **M3 closed; M4 fragment part closed; M5 fragment part closed**.
M1/M2 and M4/M5 compiled simpset/history/import/strategy remnants retain their
existing **TASK_16** removal owner. Existing ordinary event serials, inventories
and configured companions are still compiler state, not fragment payloads.
No hidden promotion or new transitional dependency was introduced. This task
intentionally does not redesign replay or claim whole-simpset storage recovery.

## Timing experiments and attribution

Maintained inputs, fixed iteration schedule, raw process receipts, all medians,
paired ratios, individual and simultaneous intervals are under
[`../fragments/evidence/task15/`](../fragments/evidence/task15/).
The four final experiments each use **ten fresh AB/BA process pairs**, three
samples per process, all 90 workloads, consumed escaping results and proof
validation after every batch. There were no concurrent builds/benchmarks.
CPU, wall, non-GC, GC, user and system time remain separate; GC is not added
again to inclusive CPU. No workload average or fixed regression tolerance is
used. Baseline-versus-baseline controls use the same fixed schedule.

1. **Default full-module sources and baseline control:** all graph/proof gates
   pass, but timing is **red**, not accepted as final default performance.
   For example, median paired CPU ratios are approximately 1.105 for empty
   merge and 1.046 for 10,000-rule TypeBase construction. Simultaneous red
   rows and their control contrasts remain in `default-summary.json.gz`.
2. **Explicit matched registry/context and 256-MB min/max heap diagnostic:**
   pinned ordinary sources are untouched; both private processes preload the
   same reviewed API-compatible marker/context dependencies. All graph/proof
   gates pass. There are no simultaneous CPU/wall/non-GC red rows or
   reproducible simultaneous red/control contrasts. Individual red rows,
   one raw simultaneous GC red, and zero-GC unresolved intervals are retained:
   the numerical verdict is **inconclusive**, not blanket performance parity.
   `Cond_rewrExt` is deliberately not preloaded into the baseline because its
   required API is incompatible; this is not full environment equivalence.
3. **Local work/layout inspection resolves the fragment-attribution concern:**
   baseline source work, identical fragment graphs and the emitted caller/
   callee evidence above establish no added fragment construction/merge work.
   Together with the diagnostic, they distinguish local fragment restoration
   from the still-mixed module/theory/allocator environment. They do **not**
   waive the default full-module red rows or replace TASK_16/29 numerical gates.

Both timing modes execute unmodified ordinary constructors. Diagnostic flags
are test-runner controls only, never a production fast path, client migration,
metadata promotion or permission to call final default overhead fixed.
`assembly/RESULTS.md` retains the exact code-generation analysis and controls.

## Fresh validation

All mandatory commands below exit **0** on final inputs. Executable launchers
were run; `.uo` generation alone is not counted as a pass.

| Check | Result / evidence |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Complete final routine build; `routine-latest.log.gz` |
| Holmake, `hol.state0`, `--no-project --no-cache`, `-C src/simp/src -j1 HOLSELFTESTLEVEL=1 all` | All normal ordinary/extension suites plus fragment-contracts; `holmake-final.log.gz` |
| `run_prior_native.py --output /tmp/task15-native-final` | 642 native checks, prior traversal/exclusion streams, markers, replay, named registration, fresh loads and persistence scenarios; `native/` |
| `run_paired.py --candidate 658ebe... --candidate-signature pass --public-contracts --prior-contracts --negative-controls ...` | 42 receipts, old signature/nine clients, frozen 73/47/929/six-limit suites and intended fail-closed controls; `paired/` |
| Fragment default/control and diagnostic/control runners | 80 measured fresh processes; all 90 graph rows and consumed-result proof observations complete; timing decisions separate above |
| Supplemental route runner | 41 checks per side, 69 exact observations; `routes/` |
| Python unittest discovery: compatibility / performance / fragments / routes / assembly | **113 / 30 / 36 / 7 / 15**, all pass |
| `audit_task15.py`; coverage ledger; immutable evidence verifier | Baseline routes/allocations, 2,153 source-tied cases and 37 immutable inputs intact |
| `tools/h4pedant/h4pedant ...`; `git diff --check` | Pass |

The final post-measurement change only corrects two synthetic supplement-count
assertions from 14/15 to 12/13 for the documented six-module diagnostic closure.
No runtime driver, SML fixture or production source changed. Original sealed
measurement inputs remain unaltered; all 36 current tests then pass. This is
recorded explicitly rather than rewriting old receipts. Other exploratory
failures and their resolved causes are in `attempt-notes.json`.

## Cleanup and next task

Private source/build trees and heaps are removed by the maintained runners.
Task-created caches, volatile scratch exports, exploratory copies and temporary
logs are removed after archiving their compact unique evidence. No copied build
or generated executable is committed; unrelated caller products are preserved.
No new out-of-scope repair or external worktree edit was needed.

**TASK_16 is next:** remove the ordinary compiled companions/inventories/history
and remaining mixed imports, restore the exact compiler schedule/storage, and
retain these raw full-module timing observations in its performance attribution.
