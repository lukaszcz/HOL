# TASK_09–16 buildable cutovers

This is the bounded implementation/validation plan, **not evidence that these
cutovers have landed**. Final interfaces are in DESIGN.md/Task08API.sml. The
compile-checked plumbing in Task08Cutovers.sml proves the critical intermediate
type routes without permissive engine stubs. `graph.json` records temporary
imports and their mandatory removal owners. Final ordinary code has no extension
imports. Temporary mixed costs are not a performance/compatibility pass.

## Common gate at each landing

1. Build and **execute** the directory's changed selftests and interfaces/check.
   Use `bin/Holmake --holstate="$PWD/bin/hol.state0" -C <dir> -j1 check`
   for interface tests; production uses `HOLSELFTESTLEVEL=1 all` in src/simp/src.
   The core heap choice is mandatory. Execute launchers; `.uo` alone is not a pass.
2. `bin/build -t --seq=tools/sequences/upto-parallel`, then `git diff --check` and
   `tools/h4pedant/h4pedant <changed-source-dirs>`. Follow normal selftest wiring;
   intermediate extension fixtures have explicit runnable targets even before
   TASK_26 finalizes separation. Keep a case-ID/body mapping to TASK_06's ledger.
3. Run the relevant maintained paired runner slices from compatibility/Holmakefile
   on the landing source. Preserve exact immutable baseline inputs. The known
   signature red becomes a **required pass in 11**. The unrelated staging red
   remains diagnosed until 18; never report it as repaired by structural work.
4. Run final-interface positive clients and static-negative reducer/fragment/set
   clients; update actual module imports when prototypes become implementations.
   No catch-all-success stub, assertion removal or disabled feature permits landing.
5. Preserve compact source/input hashes, commands/exits and actual loaded module
   paths. Split focused perf samples from builds; no concurrent benchmarking.
   Targeted measurements below are diagnostics until their full later gates.

Paths/line ranges refer to source HEAD `74ddf80be`; TASK_07's actual consumer tables
bind the unchanged production sources. Assertions, not line numbers, are invariant.

## 09 — additive TraverseExt

- Add the distinct reducer datatype and generalized extension traversal. Keep old
  mixed Traverse intact for one step. Dependencies only point to original/shared
  facilities. Don't copy Trace, stack_limit, Context or tracking state.
- Implement explicit LIFTED handling, integer versus live-depth transport,
  construction-once TRAVERSE and refresh-on-application XTRAVERSE separately.
- Add an extension traversal selftest target outside ordinary fixture imports;
  duplicate assertions temporarily if needed, not ordinary constructors or cells.
- Compile/run lifted ordinary collectors/apply callbacks, initial exception
  contexts and unchanged exception identity. Assert zero callbacks at lift,
  saved-conversion lifetimes, generic solver/binder facts, root/child-first,
  observation/charges, default/configured/live depth and custom order.
- Run TASK_06 traversal contracts and the unchanged native mixed tests. Record
  construction/reuse comparison separately. Original ABI is still an expected
  red until 11; no legacy restoration claim.
- Temporary: old extended Traverse constructors/entry points and dual engine
  bodies. **11 removes them**, including eligibility and projection dispatch.

## 10 — independent simpExtLib relocation and minimum recipes

- Relocate the mixed representation/algorithms to independently sealed extension
  types, change all reducer/solver/config fields to TraverseExt, and use the new
  engine. Allocate a new **simpExtLib.ssfragDB** slot, not a second same-name slot.
- Add pureSimpsExt/boolSimpsExt above the core; construct from theorem/conversion
  ingredients in original order. No simpExtLib -> recipe or congExtLib back edge.
  Provide all fragments needed by currently runnable migrated tests (ETA and
  named/maker/AC/TypeBase/relational fixtures as applicable), not just bool_ss.
- Low-level extraction has not happened yet: the relocated engine still calls
  current `Cond_rewr.COND_REWR_CONVS` until **12**, and current
  `Travrules.mk_threaded_travrules` until **13**. These are existing real
  implementations, not missing Ext modules or stubs. Task08Cutovers elaborates
  their initial signatures as well as the replacement routes. Retarget those
  calls when the primitives move; never duplicate their control/trace state.
- Before 11, retype the **active dependency closure**: native extension fixtures,
  configured congruence fixtures, focused marker/split integration, prepared
  sources/bundles and any in-repo extension factories. Tests can remain interleaved
  temporarily using explicit structure aliases/local scopes. Keep legacy pins
  ordinary; TASK_24/26 later complete catalog/relocation, not first compilation.
- Never forward an ordinary set to simpExtLib. No wrappers in simpLib calling
  simpExtLib, and no source-sensitive tests “fixed” by importing legacy history.
- Execute old ordinary pins and the newly relocated extension cases, including
  partial/exhausted source/view/bundle controls, split opt-in/fresh load, strategy
  SF dispatch and late lookup in **both typed registries**. Build extension recipe
  modules explicitly; run compile-negative constructor/install clients.
- Temporary: ordinary simpLib still owns its old mixed internals and some public
  branch-only exports. Record exact remnants under ledger rows M1–M5. It need not
  meet storage/loading gates yet. No implicit promotion bridge is allowed.

## 11 — exact ordinary Traverse and congLib

- Restore pinned Traverse.sig/datatype/body and ordinary congLib projection,
  eager weakener/congruence factories, reflexivity/error scopes/wrapping. Add
  congExtLib using extension input types. Public CSFRAG may be explicitly lifted;
  opaque congset may not. Convert configured congruence tests as a unit.
- Remove ALL active uses of the two old Traverse constructors/accessors/policies.
  Mixed ordinary simpLib still builds both native runners over its current net:
  ordinary projection uses REDUCER/dprocs unchanged; private configured machinery
  uses TraverseExt.CONFIG_REDUCER plus **explicitly lifted ordinary dprocs**.
  This route is elaborated in Task08Cutovers; it is temporary internal plumbing,
  not a way to promote arbitrary public sets. No ext datatype in ordinary dproc_ss.
- Retype any still-visible branch-only cooperation exports to extension data or
  retire them once their active callers use simpExtLib. They disappear by 16.
  `reducer_config_data` name/printing inspections at simpLib:590,616,3124 become
  ordinary `dest_reducer` inspections. Remove optional ordinary cong fallback.
- Run all seven frozen signatures, ascription/functor/datatype-replication and
  exhaustive-match clients with `--candidate-signature pass`; original complete
  signatures must elaborate unedited. Run 47 traversal contracts and native
  collector/factory/rollback pins. Keep `[1,1,1]` construction-once and `[0,1,2]`
  refreshing assertions separated; do not force unlike-type list pointer equality.
  Extension projections must retain their same extension dproc list; ordinary
  pointer checks stay ordinary. Retain actual-control/callback assertions too.
- Run ordinary and configured cong proof/hypothesis tests, lift callbacks and
  construction/reuse measurements. **11 removes old Traverse/congLib edges**;
  private ordinary simpLib -> TraverseExt remains only until **16**.

## 12 — conditional compiler separation and one tracking slot

- Move paired/configured preparation to Cond_rewrExt. Restore direct pinned
  ordinary COND_REWR_CONV; it must not construct a pair and discard half.
- Extract current ThreadLocal tracking extent to internal SimpTracking, with
  note_rewrite and polymorphic with_tracking. Existing Cond_rewr export aliases
  it; both compilers report to it. Keep the original public signature/control ref
  and Trace identity. No extension import in Cond_rewr itself.
- Retarget simpExtLib and surviving mixed ordinary compiler at simpLib:126 to
  Cond_rewrExt explicitly; **16 removes the latter import**.
- Execute paired matcher tests in both orders, partial/exhausted quotas, late
  extraction without compilation traces, failed conditions/permutations, changed
  stack_limit during a failed candidate, explicit/nested depth and custom order.
  Run tracking across both engines, nesting and exception restoration; check the
  same public stack_limit/Trace refs and exceptions, not equal-value copies.
- Measure ordinary constructor and application separately; document exact direct
  baseline correspondence, including compiler call placement/evaluation order.

## 13 — threaded congruence separation

- Restore pinned Opening.CONGPROC and Travrules factories, moving threaded
  implementations to OpeningExt/TravrulesExt. Return original structural types;
  no generative copies of PREORDER/TRAVRULES or exception constructors.
- Retarget extension compiler/congExtLib; surviving ordinary threaded branch
  at simpLib:1628 may call TravrulesExt until **15/16** deletes it. Do not let
  ordinary Opening/Travrules import extensions.
- Compile structural-identity clients and run ordinary eager/reflexivity/failure
  scopes plus threaded later-premise and rebuilt-RHS-beta proofs (unchanged LHS).
  Test weakener factories/context staging and actual hypotheses/proof validation.
  Exercise standard ordinary and tracked BOOL congruence recipes separately.

## 14 — tracked compiler/projections are authoritative

- Complete extension event/slot/component/conjunct ownership, prepared matchers,
  actual control group binding and internal tracked entries without handles.
  Both extension projections are shallow views of this object, not recompiled
  simpsets or adapters reconstructed from ssfrags_of.
- Keep reset native history replay versus prepared-event replay versus preserving
  replay explicit. Match compatible origins/statements/bounds; zero is a real
  binding. Preserve original callback schedules and no-op identities.
- Run source/view/AC/duplicate occurrence and bundle/conjunct assertions; exhaust
  one projection **before extracting** the other, in both orders. Check maker and
  collector counts and compilation trace silence, surviving bindings after filter
  and preserving replay, and changed-statement invalidation. Source equality
  alone cannot verify control sharing: consume alternately and test exhaustion.
- Include private scope over bounded net entries with no source handle, restoring
  after HOL_ERR, arbitrary exception, interrupt and nested charge cutoffs.
- No new accommodation in ordinary representation. Transitional ordinary mixed
  helpers remain temporary; **16 deletes them**, 19/21/22 extend algorithm gates.

## 15 — ordinary fragments are baseline again

- Restore pinned ssfrag fields and plain rewrite/AC element types in every
  constructor/update/merge/TypeBase/relsimp/named/excluded route. No source slot,
  views/strategy/solver/threaded fields or extension allocator in ordinary frags.
- Adapt the still-mixed compiler **only at installation** if it temporarily needs
  slot wrappers. That private adapter accepts plain rules (Task08Cutovers proves
  the shape), uses a temporary installation-local event/ordinal, not global
  fragment side tables. All source-sensitive public callers have already moved.
  **16 deletes the adapter, mixed event/slot allocation and ordinary inventories**.
- Branch extension fragment APIs are now only in simpExtLib. Mechanically retarget
  ordinary compiler fields, printers, fragment removal/replay and public signature
  enough to build. Do not postpone broken pattern matches to 16.
- Run all constructors/updates including empty/excluded/duplicate/named/AC/
  TypeBase/relsimp, fragment registration/printing and maker staging. Confirm
  ordinary fragment creation has no source allocator call by structural diff;
  measure consumed construction/merge outputs and retained sizes over rule counts.
  Compilation may still carry documented mixed cost until 16; not acceptance.

## 16 — ordinary net/simpset/compiler and load boundary

- Restore pinned net `{thypart,ci}`, simpset/history records, constructors/updaters,
  rewriter, unconditional traversal projection and exact ++ schedule. Remove
  ordinary source inventories, configured companions, strategy fields, paired
  calls, eligibility, temporary slot adapters and private extension helpers.
- Delete all ordinary imports of TraverseExt/Cond_rewrExt/TravrulesExt and all
  simpMarker/split references. Keep ordinary markerLib processing only. Do not
  hide dependencies behind signature removal or unreachable function definitions.
- Adjacent ordinary tactics/exclusions/history need mechanical baseline retyping
  **now**, not uncompilable placeholders until 17/18. Use baseline bodies where
  representation makes this necessary; 17/18 still own full semantic/performance
  closure for those slices. Do not retain extension marker rejection scans in
  ordinary SIMP_CONV/tactics to make an extension test pass: migrate that test.
- Run ++ decoding -> AC derivation -> *all* makers -> conversion construction ->
  original dproc priming probes, including malformed tags, throwing makers,
  empty/excluded additions, replay, printing and supplied rules. Check proofs,
  exact callbacks/exceptions, source signature pass, original selftest and prior
  traversal/exclusion matrix. Keep staging diagnosis honest until 18.
- Fresh-process load only simpLib/boolSimps/congLib, not extension-bearing native
  selftest. Assert no extension module/slot/persistence init dependency. Run the
  literal exclusion smoke tests and source audit before performance diagnostics.
- Measure fragment/merge/compilation/application plus retained graph slope; no
  extension allocation in legacy records. Later gates use the full acceptance
  protocol; reduction of mixed costs alone is not a pass.
- Close every M ledger edge here; **27** independently audits closure and normal
  manifests. No temporary dependency is allowed to survive just because 27 exists.

## Transition ledger (source slices and removal ownership)

| ID | Minimal temporary plumbing | Added/retargeted | Removal owner |
| --- | --- | --- | --- |
| X1 | New simpExtLib initially uses existing Cond_rewr paired API; the new Cond_rewrExt is not needed before its extraction | 10 relocation | **12** retarget to Cond_rewrExt |
| X2 | New simpExtLib initially uses existing Travrules threaded API; Opening/Travrules extension modules arrive in 13 | 10 relocation | **13** retarget to TravrulesExt |
| M0 | Old mixed Traverse alternatives/entry points/eligibility; configured congLib wrapping at 178–205,271–306 | 09 extraction | **11** |
| M1 | Ordinary simpLib configured reducer/config/solver types at 185–238,2059–2150,2346–2422,2925; private bridge uses T types/lift only | 11 retype | **16** |
| M2 | Ordinary paired preparation at simpLib:126 explicitly imports Cond_rewrExt | 12 retarget | **16** |
| M3 | Ordinary threaded factory at simpLib:1628 explicitly imports TravrulesExt | 13 retarget | **15/16**, no later than 16 |
| M4 | Ordinary source slots/inventories/companions/history at 22–45,102–252,1681–1925; installation-local slot adapter after fragment restoration | existing; 15 adapter | fragments **15**, compiled state **16** |
| M5 | Ordinary split/strategy/extended marker helpers at 943–1051,2154–2162,2174–2422 and matching branch-only exports | 10 relocation | fragment fields **15**, remaining imports/code **16** |
| M6 | Interleaved test dependency aliases/local scopes and temporary duplicate assertions | 10/11 minimum migration | final integration **26**; must remain executable throughout |

The graph's introduced-node ledger models the pre-extraction availability:
SimpTracking/Cond_rewrExt arrive in 12, OpeningExt/TravrulesExt in 13. Prior to
those steps the source uses X1/X2 and the existing single local tracking slot;
it must not reference a not-yet-created module. Delete the early-API witness
aliases in Task08Cutovers at 12/13 while moving their assertions to the actual
new modules. Combin/default service modules need not exist before 24.

These are relocation costs only; controls/registries/exceptions are **never**
duplicated temporarily. Earlier task acceptance cannot claim final absence while
an M edge remains. If a step reveals a new dependency, add a named bounded removal
row and recheck the DAG before proceeding, not a permissive fallback.
