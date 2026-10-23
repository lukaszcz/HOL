# Identity/control/registry ledger

**Final ownership/closure:** [TASK27.md](TASK27.md) publishes the production
module owners and resolves every identity row below to concrete source and
execution evidence. X1/X2 and M0–M6 are closed; M6 closed under TASK26's exact
physical relocation and independent ordinary launchers. Historical graph and
extraction requirements below are retained, not asserted to be pending.

Inventory source `50cfa5d70`; exact files/hashes in manifest.json. These are
identity requirements for the implementation owners. **TASK_08** finalizes them
in [DESIGN.md §5](../interfaces/DESIGN.md), with an acyclic checked graph and
explicit intermediate removal owners. This is not a claim that the final module
graph has already been implemented.
**TASK_27** closes every row's dependency/identity audit.

| Identity / current location | Deliberate sharing or separation | Implementation owner |
| --- | --- | --- |
| `Cond_rewr.stack_limit`, `Cond_rewr.sml:13,188,236` | One existing public `int ref`; both engines read it for live/unconfigured candidate depth. `NONE` stays live, `SOME n` does not sample or mutate the ref. Traversal adapters must not snapshot the default too early | 09/12 |
| `Cond_rewr` thread-local tracking extent, `:24–47`; `simpLib.track = with_tracking` at `simpLib.sml:3082` | One dynamic slot/reporting extent for both engines, nested extent and exception restoration preserved. `note_rewrite` is currently private: extract the single slot/reporter to internal **SimpTracking**, alias the existing public with_tracking and import the same reporter from both compilers; never copy the slot. No per-legacy-rule tracking inventory or global cache | 12 |
| `Trace.action`, `trace_hook`, `trace_level`, `Trace.sml:14–31` | Same action datatype, ref, listener and registered simplifier trace control. Both engines use the existing Trace module; no separate extension trace namespace masquerading as shared | 09/12/13 |
| `BoundedRewrites.control`, `src/1/BoundedRewrites.sml:5–6,27–33`; `simpLib.sml:102–113` | Same datatype and **actual int ref**, not equal-valued counters. Paired runners, views, late extraction and preserving replay share partial and exhausted controls. Ordinary reset replay still creates fresh declared allowance | 12/14/19/21 |
| Private child-first quota scope, `simpLib.sml:2359–2382` | Scope the entire initial tracked net's bounded entries, including entries without public source handles (collectors/supplied/internal conversions). Source inventory alone is incomplete. Restore actual refs after HOL errors, arbitrary exceptions, interrupt/cutoff | 14/22 |
| Source serial/slot/origin, `simpLib.sml:22–45` | Move to extension-owned state only. Preserve duplicate occurrence/event/slot/conjunct identities, proof/statement compatibility and stable comparison. No serial/slot/cache allocation in ordinary constructors | 14–16/21 |
| Named fragment registry `simpLib.ssfragDB`, `simpLib.sml:310–331` | Existing ordinary Context slot/type stays ordinary. Extension fragments have a distinct type: use a deliberately separate typed registry/slot (`simpExtLib.ssfragDB`) and explicit recipe registrations, **not two copies with the same slot name**. Same fragment display names may exist in both typed registries | 08/10/24 |
| `SF` registration `simpLib.sml:2174`; late `DFRAG` lookup `:2238` | FRAG carries a string, not a typed fragment. Each engine resolves its own registry at the original late stage, including replacement and Context rewind. No fallback that recompiles ordinary fragments/sets to invent tracking | 18/20/24 |
| `Context.Data`, `Sref`, TypeBase update/tyinfo identities | Reuse generic modules and context objects, not duplicate registries. Extension default recipe may own its own typed state only on explicit use; ordinary loading/updating must not install extension overhead. Preserve pointer-based invalidation/rewind and factory/collector ordering | 08/23/24 |
| `BasicProvers` srw state/derived registry/update log, `BasicProvers.sml:1150–1522` | Ordinary state and `(simpset -> simpset)` closures are not retrospectively translatable into tracked state. Separate typed extension seed/update path at earliest construction; no generic ThmSetData/postkernel hooks or automatic rebuild in derived getter. Explicit ordered typed recipe/provider boundary finalized in DESIGN.md §6: no arbitrary-state automatic mirroring, getters never build, updates/windows are extension-typed. Recipes/provider by 24, external consumer by 25 | 08/24/25 |
| ThmAttribute attrfuns and Context slots, `src/1/ThmAttribute.sml:25–48,87–88` | One original registry, exact installed record/function identity. Read-only lookups inspect supplied/ambient context without invoking callbacks/mutating. Keep src/1/selftest pins as well as focused first-owner tests | 23 |
| SplitData private witness/tag, ownership/rules slots, attribute handler and TheoryLoaded listener, `SplitData.sml:8–37,86–91,104–177` | One simplifier-owned SplitData instance. Explicit transactional initialize, exact handler/listener pointer/order, retry/rewind/private ordered data replay. No generic split theorem set, namespace interception or ordinary-load ownership claim | 23 |
| `splitLib` TypeBase/case caches, `splitLib.sml:170–205,251–285` | One splitter/cache module reached explicitly by extension use. Invalidate against actual TypeBase/tyinfo identity; do not create a second legacy splitter. Pure splitter loading must not initialize persistence | 23 |
| `simpMarker` constants, `simpMarkerLib.directive`, generic `markerLib.directive` | Single theory/marker module, with simplifier directive explicitly wrapping the same generic directive type. Keep Split/ExcludeX constants qualified, foreign syntax untouched; generic processing remains unchanged | 20/23 |
| `Travrules.preorder/travrules`, `Opening.congproc` | Share structural types where the extension implementation can use them without legacy overhead. Do not generatively replicate datatypes just by compiling a second copy. Threaded factory implementation is extension-only; ordinary congruence factories retain eager/reflexivity staging | 08/13 |
| `Traverse.context = exn`, ordinary `Traverse.reducer` | Ordinary datatype stays baseline; extension datatype is distinct. Explicit lifting carries the **original context exception payload/closure**, no recoding or fake source identity. Engine-private net exceptions can differ only if they never cross the boundary | 08/09/11 |
| `Conv.UNCHANGED`, `Feedback.HOL_ERR`, `Portable.Interrupt`, Basis `Option` and user callback exceptions | Reuse exact constructors; do not catch/rethrow with invented equivalents or change scopes. Preserve foreign exception payload pointer, errors/messages/provenance and interrupt propagation. External typed `searchBudget.LimitReached` remains the same downstream exception | 09/11–13/18/22/25 |

## Ordinary load boundary

Current mixed `simpLib`/`congLib` dependencies reach extension types and marker/
split machinery. The target graph is **extensions → ordinary/shared**, never
ordinary → extension. Shared identities above may live in the existing ordinary
modules or a carefully designed identity-owning helper; they must not be
recreated by compiling two implementations. Extracting tracking reporting needs
special care because the current reporter is private.

TASK_08's acyclic, type-checked graph and compile-checked cutovers are in
[../interfaces](../interfaces/DESIGN.md). TASK_09–16 perform them,
TASK_23 maintains explicit split lifecycle, and TASK_27
checks normal imports/dependencies/control identities. Fresh-load tests in
TASK_06 currently freeze prior foreign-owner/identity behavior, not final absence
of every extension dependency. Update their module-presence contract deliberately
for the new boundary without weakening exact handler/listener assertions.

Neither an optional field in every ordinary node nor a lazily populated global
side table solves these identity/construction requirements. Sharing is explicit
inside tracked objects and shared public controls, not global retention of all
legacy simpsets.
