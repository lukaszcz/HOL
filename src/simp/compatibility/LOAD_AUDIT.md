# TASK_12 load/registration audit

## Scope and status

Static audit of `c8b193b9871528da14caf05f6492d2ad2ca80f73`
(`[TASK_11] Integrate explicit split persistence`) against pinned
`origin/develop`, `cccaa27d7099cbadc886983020cbe745db7793f3`.
Line references below identify this branch revision, not generated products.

Requirements: `.agent-files/tasks/TASK_12_split_lifecycle_and_load_audit.md`
and `.agent-files/PLAN_compatibility.md:189–243` (Phase 4). The inventory
below describes the base revision, with TASK_12's bounded syntax repair
explicitly identified in S03. Runtime evidence, commands and limitations
are in [SPLIT_LIFECYCLE.md](SPLIT_LIFECYCLE.md) and `results/task12/`.

**Disposition:** persistent `split` registration is explicitly owned and
not an ordinary-load side effect. The one bounded syntax issue found,
A01 (`ExcludeX`'s unqualified mapping), is fixed and regression-tested.
Every relevant production/test registration or syntax delta has a
KEEP/FIX disposition below; no open audit blocker remains.

### Attribution and completeness boundary

Both direct (`git diff origin/develop HEAD`) and branch-introduced
(`git diff origin/develop...HEAD`) changes were inspected. Their merge base
is `92ec5c17ec73938124526a7fa4b3895ff5065233`. Develop advanced independently:
the direct diff also contains datatype/induction, Context/kernel, parser-tool,
and other reversions relative to newer develop. Those are not registrations
introduced by this branch. In particular, the direct diff's `ind_type`
constant/mapping changes and `ind_types` mapping removal are not new
simplifier registrations.

There is **no difference between the merge base and pinned develop** in
`src/1/ThmAttribute.sml`, `src/1/ThmSetData.sml`, `src/marker/`,
`src/postkernel/ThyDataSexp.sml`, or `src/simp/src/`. Thus every relevant
production registration/syntax delta listed here is also a direct delta
against the requested pinned develop, without a baseline substitution.
The full branch-added source inventory is these registry/marker files and
`Cond_rewr`, `Opening`, `Traverse`, `Travrules`, `congLib`, `simpLib`,
`splitLib`, `splitPersistLib`, their signatures, and tests. Added
registrations, top-level mutable allocations, definitions, grammar changes,
and dependency edges were reviewed, not just occurrences of `register`.
Compatibility inputs/results are frozen evidence, not production modules.

## Production dispositions

### R01 — persistent attribute and theorem set `split`: KEEP, explicit only

Locations: `src/simp/src/splitLib.sml:125–190` (handle/initialization),
`:193–222` (removal and queries), `src/simp/src/splitPersistLib.sml:1–7`
(explicit top-level initializer).

- Ordinary `splitLib` loading allocates only its private
  `splitLib.registration` Context slot, initially `NONE` (`:131–134`).
  It neither checks/reserves the public name `split` nor constructs an
  exporter. `simpLib` has no dependency on `splitPersistLib`.
- The actual claim is the call to `enable_split_attribute`, specifically
  `ThmSetData.export_with_ancestry` at `:172–179`. It installs both the
  attribute and theorem-set exporter. These are branch-added registrations,
  but are **not** ordinary top-level initialization.
- Ownership is exact record identity of both handlers (`:136–143`), plus
  the private Context handle. A same-named foreign entry is not adopted.
  Owned reinitialization is a no-op. Unowned initialization checks both
  registries, reserved attributes, abbreviations, and both persistence-hook
  names before constructing the exporter (`:145–171`). Conflicts raise,
  rather than overwrite or suppress a replacement warning.
- Pinned unowned initialization is rejected; an already-owned pin permits
  the no-op. Queries use a single Context snapshot, return `[]` without
  ownership, and never initialize (`:211–222`). `exclude_split` requires
  owned registration and rejects pinned writes (`:193–209`).
- Restoring Context restores the handle and both registry records/data;
  a later foreign replacement invalidates query ownership. This does not
  make deliberate replacement of internal listeners a supported operation.
- `splitPersistLib` intentionally opts in at module load. Its name and
  documented import dependency are the explicit consent boundary. Module
  loading is process-global: after restoring a pre-registration Context,
  call the API again; do not assume loading an already-loaded module reruns
  its initializer. Initialization is serialized theory setup, not concurrent
  proof execution or an arbitrary late/current-segment replay facility.

Indirect names claimed **only by that opt-in**:

| Namespace/name | Installer and owner |
| --- | --- |
| Attribute `split`; exporter settype `split` | Existing `src/1/ThmSetData.sml:261–323`, especially `:308–311`; splitLib owns the returned handler identities. |
| Context `ancestry.split.global`, `ancestry.split.values` | Existing `src/parse/AncestryData.sml:246–269`, invoked for tag `split`. |
| Loadable data `split.deltas`, `split.parents` | Existing `AncestryData.sml:275–284,305–309`, through `ThyDataSexp.new`. |
| Listeners `ThmSetData.onload.split.deltas`, `ThmSetData.onload.split.parents` | `src/postkernel/ThyDataSexp.sml:323–358`; stable routing closures, Context-selected instance hooks (R03). |

Export/load contract: load the opt-in module in the earliest split-bearing
script **and** record `Theory.add_ML_dependency "splitPersistLib"` before
using `[split]`. It must precede that theory's data decoding/replay, not
merely a descendant's declarations. See the concrete client
`probes/split-persistence/splitParentScript.sml:1–7` and
`SPLIT_PERSISTENCE.md`. Ordinary simplifier imports or a non-exported
script-time API call alone do not provide fresh-import initialization.

Private Context/data names are library-owned implementation names, not
public attribute reservations. Collision with deliberately occupied private
slots, corrupt encoded input, allocation failure, or asynchronous exceptions
is not covered by a general transactional rollback promise. The preflight
contract concerns the listed foreign public owners/listeners; do not extend
it to arbitrary exceptions after exporter construction starts.

### R02 — local split fragments and caches: KEEP, no namespace claim

Locations: `src/simp/src/simpLib.sml:929–1012` (local split/TypeBase
integration and `split_ss`), `src/simp/src/splitLib.sml:271–316,350–395`
(caches).

`split_ss` is a named **value**, constructed by `named_merge_ss`, not a
call to `register_frag`, `reserve_word`, or the exporter. Its name `split`
and looper name `splitter` live inside fragment/simpset values. Local
`Split`/`add_split`, TypeBase splitting, and explicit exclusion lookup do
not opt in. Persistent lookup goes through R01's ownership-gated query.

The new process-held `type_split_cache` (`:279–280`) and `case_const_index`
(`:361–363`) start empty. They are memoization, not TypeBase registration:
entries validate the exact tyinfo/table pointer before reuse after Context
changes. They do not write TypeBase, public registries, or grammar. They
may retain prior cached objects across a rewind; no heap-size or universal
lifetime claim is made here.

### R03 — theory-data dispatch: KEEP, intentional shared infrastructure change

Locations: `src/postkernel/ThyDataSexp.sml:309–362,409–410`;
`src/postkernel/ThyDataSexp.sig` exports `check_registration`.

The new top-level Context slot `ThyDataSexp.hooks` (`:314–317`) and empty
process table `dispatchers` (`:318–319`) alone claim no listener name.
Calling `new` now preflights, then routes registration through
`register_data_hook`; the **preexisting** listener spelling
`ThmSetData.onload.<thydataty>` is retained. The old direct registration
at baseline `ThyDataSexp.sml:357` is replaced, not an additional listener.

One permanent process dispatcher per data name selects the actual hook
from the current Context (`:320–343`). Restoring before initialization
makes it a no-op; restoring an initialized Context selects that instance's
UniversalType witness. An existing foreign listener must be pointer-equal
to the stored dispatcher or preflight raises before the registration.
`check_registration` itself only inspects; it does not reserve the name.
Existing owned dispatchers are reused without reordering listeners.

This changes every `ThyDataSexp.new` client, including preexisting clients
loaded transitively. It is not a split-only shim. Stable process routing,
Context-selected hooks, and first-registration listener order are the
contract. Re-elaborating module bodies under the same private slot names
is not the module-loader contract. TASK_12's separate heap-save/reload
processes exercise the restored routing closures, both registry identities,
pre-init/owned/foreign snapshots and real ADD/REMOVE replay.

### R04 — ownership inspection APIs: KEEP, read-only

`src/1/ThmAttribute.sml:87–88` adds `attribute_fns{,_of}`;
`src/1/ThmSetData.sml:114–116` adds `data_exportfns_of` and makes the old
query use it. Corresponding signature additions expose inspection only.
No new registry, reserved word, attribute, abbreviation, or top-level
handler installation is introduced. Existing registration/replacement
policies are not silently tightened by these accessors.

### S01 — marker `$Split` and hidden surface mapping: KEEP

`src/marker/markerScript.sml:115–116` defines `marker$Split`, then removes
**only** that constant's unqualified `Split` overload mapping. This is a
new persistent theory-grammar change, not a removal of every user's
`Split` mapping. Qualified kernel construction remains available.

`src/marker/markerSyntax.sml:10`, `markerLib.sml:77–89,691–738`, and
`simpLib.sml:2153` add ML construction/recognition (`Split_tm`, `Split`,
`destSplit`, `DSplit`). These bind values/functions, not parser/printer
handlers. Ordinary quoted `Split` remains available as a variable in a
clean grammar; `src/marker/selftest.sml:7–11` explicitly tests that case.
No `[simp]` registration is attached to the new definition.

### S02 — OpenTheory name for `$Split`: KEEP, no active map mutation here

`src/marker/markerScript.sml:124–126` adds the explicit
`marker$Split -> (["Unwanted"],"id")` call, paralleling existing `Cong`.
The owner is the qualified marker constant, not the unrelated HOL/ML name
`id`. Importantly, in this checkout
`src/opentheory/OpenTheoryMap.sml:67–72` implements the public mapping
functions as **no-ops**. Do not report this call as a newly installed
reverse mapping, listener, or active namespace overwrite. Changing that
implementation later would require reassessing the call's actual effect.

### S03 — marker `$ExcludeX` and its surface name: FIXED (A01)

`src/marker/markerScript.sml:118` adds the independent qualified constant
and `ExcludeX_def`. `markerLib.sml:97,104,115,696,731–732` and
`simpLib.sml:2156` provide explicit ML `ExclX` construction/recognition.
Those ML additions neither reserve exclusion strings nor register an
attribute. Legacy `Exclude` and its literal string protocol remain
separate. No new OpenTheory call or automatic simp rewrite accompanies it.

At the audited base, unlike `$Split`, this definition retained its default
unqualified mapping. The preexisting `Parse.watch_constants` hook at
`src/parse/Parse.sml:1182–1195` calls `add_const` for each new constant;
`add_const` at `:1011–1015` installs `overload_on(s,c)`. A legacy quotation
using free `ExcludeX` could acquire a constant interpretation/type constraint
without choosing the extension. The qualified definition is intentional;
the unqualified capture is not required by the explicit ML API.

**A01 resolution:** TASK_12 removes just the
`{Name="ExcludeX", Thy="marker"}` mapping immediately after its definition,
mirroring `Split`. The qualified constant/theorem and ML APIs remain.
`src/marker/selftest.sml` now checks variable parsing and qualified access.
The fresh `syntax-first` scenario installs foreign `Split` and `ExcludeX`
overloads *before* ordinary simpLib loading, then checks both foreign
interpretations and both qualified marker constants. It also verifies no
warnings and neither split registry claimed. All checks pass, including
normal marker tests and the routine sanity build (see lifecycle evidence).

### R05 — other new module-level state and extension APIs: KEEP

- `src/simp/src/simpLib.sml:22–23`: `source_serial` and token allocator are
  process-local identity metadata. They claim no named registry; tokens
  need not rewind with Context. Empty/default/strategy fragment values
  (`:279–284,480–495`) do not run user registration callbacks.
- `simpLib.sml:1000–1012`: `cases_simp` derives a theorem and constructs
  `split_ss`; it does not install a rewrite globally.
- Changes to `Cond_rewr`, `Opening`, `Traverse`, `Travrules`, and `congLib`
  introduce functions, reducer constructors/adapters, local traversal
  references, and explicit threaded-congruence/strategy routes, not new
  top-level trace registrations, listeners, syntax, or attribute claims.
  `Opening.sml:356–357` binds the ordinary and explicit threaded factories;
  `Travrules.sml:121–135` is an explicit constructor, not a registry.
- Signature additions and ML aliases are module namespace additions.
  They do not install HOL surface syntax just because a module is loaded.

## Preexisting registrations — do not misattribute

All following registrations exist in both the merge base and pinned
develop. Current line references are supplied because they appear in
ordinary-load/transitive-load searches and can otherwise look new:

| Location | Existing effect / disposition |
| --- | --- |
| `src/simp/src/simpLib.sml:309–335` | `simpLib.ssfragDB` Context slot and explicit `register_frag` replacement warning; unchanged ownership policy. |
| `simpLib.sml:2168–2179` | `SF` can explicitly register an absent named fragment when called; no new top-level invocation for `split_ss`. |
| `src/marker/markerLib.sml:197–200` | Trace `PAT_ABBREV_TAC: match var/const`; not branch-added. |
| `markerLib.sml:590–593,681–687` | Existing hide-printer operations and top-level `markerLib.IgnAsm` user printer; no new branch printer. |
| `markerLib.sml:1123–1137,1200–1214` | Existing `AncestryData.fullmake` stores `suspension.theorems` and `suspension.resumptions`, their slots/data/listeners. Installers unchanged; dispatch mechanics now follow R03. |
| `markerLib.sml:1599–1610` | Existing `markerLib.no_suspended_in_DB` export hook, not a simplifier addition. |
| `src/marker/markerScript.sml:133–138,162–170,180–181` | Existing `:-` syntax, suspended-label notation, and `using`/`usingThm` mapping removals; not new syntax changes. |
| `markerScript.sml:111–114,117,119–123` | Existing AC/Req/Cong/Exclude/ExcludeFrag/FRAG constants and OpenTheory calls. Only Split and ExcludeX are new. |
| `src/1/ThmAttribute.sml:25–38,52–133`; `src/1/ThmSetData.sml:103–112,134–247,261–323` | Existing registry slots and general attribute/exporter installers. New inspection accessors do not auto-install entries. |
| `src/opentheory/OpenTheoryMap.sml:56–64,94` | Existing OpenTheory loadable-data registration and `OpenTheory.onload` hook, not added by the Split mapping call. |

These preexisting facilities are not evidence that all ordinary HOL loading
has no ambient effects. Phase 4's relevant claim is that the branch adds
no unrelated takeover/reservation. R03's impact on their dispatch is
explicitly retained above rather than hidden as unchanged infrastructure.

## Test-only registrations and dependency edges

Disposition for all these additions: **KEEP, explicit isolated test setup**,
not ordinary production imports. Tests intentionally mutate registries and
sometimes provoke existing replacement warnings. They must remain outside
production dependency graphs; executing selftests is not namespace-neutral
library loading.

| Location | Deliberate registration and lifetime |
| --- | --- |
| `src/simp/src/selftest.sml:2726,2898` | Explicit persistent split opt-in for tests; the latter scenario restores Context. |
| `selftest.sml:5175,5186,5528–5538,5679–5685` | Temporary named fragments and callback-time replacements; enclosing tests restore saved Context. |
| `selftest.sml:5251–5253,6066–6080` | Temporary trace listeners; removed via `Portable.finally`. |
| `src/simp/compatibility/probes/support/TraversalContracts.sml:69–71` | Temporary trace listener for ordered observations; final cleanup removes it. |
| `probes/fresh-load/selftest.sml:76–106` | Foreign `split` attribute/exporter installers, selected in distinct fresh scenarios. The executable links only its launcher, not simpLib. |
| `probes/split-registration/selftest.sml:76,111,130,270,274,294–305` | Explicit/repeated/pinned opt-in attempts under saved/restored Contexts. |
| `probes/split-registration/selftest.sml:156,181,206–212` | Deliberate foreign attribute/exporter installs, including mismatched owners, to check rejection/data identity. |
| `probes/split-registration/selftest.sml:255–269` | Temporarily replaces a dispatcher with a foreign hook, checks preflight rejection, then reinstalls the saved exact dispatcher. |
| `probes/split-registration/selftest.sml:276–289` | Deliberately reserves `split` and defines ordinary/cyclic abbreviations in restored fixture Contexts, checking conflict nonmutation. |
| `probes/split-persistence/selftest.sml:28–40` | Scenario-local foreign attribute/exporter; expected opt-in import failure must preserve them. |
| `probes/split-persistence/optIn.ML:1–5`, `verify.ML:23–27` | Explicit opt-in/idempotence controls for dynamic fresh imports, not hidden loader dependencies. |
| TASK_12 `probes/split-persistence/{heapSave,heapVerify}.ML` | Saves pre-init/owned/foreign snapshots, deliberately installs a foreign attribute in an isolated Context, and checks explicit reinitialization/rejection after separate-process heap reload. |
| TASK_12 `probes/fresh-load/selftest.sml` (`syntax-first`) | Installs foreign `Split`/`ExcludeX` overloads only in its isolated executable, before dynamically loading simpLib. |
| `probes/split-persistence/splitParentScript.sml:1–7` | Earliest theory deliberately imports/exports `splitPersistLib`; child/descendant inherit the theory graph. This dependency is essential, not an accidental ambient registration. |

Paths abbreviated to `probes/...` above are relative to this compatibility
directory; `selftest.sml` without that prefix is `src/simp/src/selftest.sml`.
The new marker selftests construct markers but install no new production
printer/handler. Frozen `inputs/` and legacy-support copies retain their
historical setup; they are evidence/test executables, not an initialization
route exported by simpLib.

Build wiring: `src/simp/src/Holmakefile` exposes fresh-load, registration,
and persistence targets under `HOLSELFTESTLEVEL`. The `splitPersistLib.uo`
prerequisite builds the explicit module; it does not execute it as part of
ordinary simpLib loading. The persistence fixture links only the launcher
and runs scenario executables explicitly. TASK_12 adds fresh syntax and
heap save/reload scenarios, optional native-only identity inspection files
(the shared legacy launcher never statically imports the new accessors),
and cleanup for the dynamic fixtures. No new production loading edge is
introduced. New `MANIFEST` descriptions add no loading edge.

## Evidence and coordinating handoff

TASK_10/TASK_11 reports retain their historical scope limits. TASK_12's
new runs, including fresh imports, actual saved-heap reload, normal
selftests and sanity build, are recorded separately in
[SPLIT_LIFECYCLE.md](SPLIT_LIFECYCLE.md) and `results/task12/validation.json`.

For TASK_13 / TASK_17: retain R01's explicit dependency/order and R03's
Context-selected routing. A process-global initialized flag or ordinary
simpLib -> splitPersistLib dependency would violate this contract. Document
qualified marker/ML APIs without promising new unqualified surface syntax.
No universal equivalence, concurrent initialization guarantee, paired run,
or full `-F` gate follows from this bounded audit and lifecycle matrix.

The static inventory used git diff/provenance inspection and source review;
S03's repair and the runtime fixtures were then validated by the coordinator.
Task-owned generated fixture products and temporary heap are cleaned after
use; compact unique evidence remains. Unrelated artifacts are untouched.
