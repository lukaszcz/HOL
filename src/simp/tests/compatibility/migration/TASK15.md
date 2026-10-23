# TASK_15: ordinary fragment cutover

**Final status:** [TASK27.md](TASK27.md) closes all temporary compiler rows
below; TASK16 removed the installation adapter and mixed compiled state, and
TASK26 closed M6. This supplement retains its historical fragment-only scope,
source seals and explicitly limited cost evidence.

Ordinary clients need no migration. `simpLib.ssfrag` is again a standalone
single-constructor datatype with exactly develop's eight record fields:
`name`, `convs`, `rewrs`, `ac`, `filter`, `dprocs`, `congs`, `relsimps`.
Rewrite elements are `(thname option * thm)`; AC elements are `(thm * thm)`.
Conversion elements are `{thypart : string option, cd : convdata}`. There
are no origin slots, source serials, views, strategy fields, configured
conversion closures, lazy companions, or tracking tables in these values.

The public `SSFRAG` input, ordinary fragment APIs and named registration
remain develop-compatible. Constructors, updates, merging, names, printing,
relsimp and TypeBase paths use baseline bodies. `pureSimps` and `boolSimps`
continue using those unchanged ordinary APIs. In particular, merging and
`ssf_upd_rewrs` do not retokenize rules, nor does `add_named_rwt` copy old
rules into source slots. AC input lists are retained directly.

## Branch-only interfaces

These already-migrated extension builders are removed from ordinary
`simpLib`'s signature and body; use the identically named `simpExtLib` API
with extension-owned fragments/sets:

- `threaded_cong_ss`, `looper_ss`, `solver_ss`, `safe_solver_ss`, `split_ss`;
- `rewrite_views`, `rewrite_bundle`, `prepare_rewrite_bundle`,
  `combine_rewrite_bundles`, `rewrite_bundle_rules`,
  `install_rewrite_bundle`;
- `GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND`, whose parameter is that bundle.

No ordinary-to-extension promotion, history import, or shared insertion
registry replaces them. `simpExtLib.{sig,sml}` is byte-identical to TASK_14,
including its explicit tracked fragment builders, prepared matchers, origins,
inventories, actual controls and both extension-typed projections. Its typed
named-fragment registry remains separate from ordinary named registration.

## Transitional compiler and CUTOVERS ledger

This is the fragment cutover, not the compiled-simpset restoration.

- **M3:** closed here. Ordinary fragments have no threaded congruences;
  ordinary installation uses only `mk_travrules relations congs`. Explicit
  threaded construction remains in the extension module.
- **M4, fragment part:** closed. There is no ordinary `source_slot` type or
  helper. The still-mixed compiler numbers baseline rewrite/AC list inputs
  at installation only. Its existing event serial, compiled source handles,
  inventories, companions and extended history remain **TASK_16** work.
  No tokens or ordinals are retained in a fragment. The unused ordinary
  prepared-bundle construction/install path has been deleted, not adapted.
- **M5, fragment fields/builders:** closed. Fragment strategy/view fields
  and builders are gone. Remaining mixed simpset strategies/marker/tactic
  plumbing and imports remain **TASK_16**, then the separately scheduled
  legacy tactic/exclusion restoration. The removed bound-bundle tactic's
  ordinary unbound path remains the same `NONE` behavior.
- **M1/M2:** existing compiled/configured types and paired compilation remain
  owned by **TASK_16**. Installation adapts baseline user conversion data to
  the old compiled payload, now explicitly named `compiled_convdata`.
  There is no conversion adapter in fragment creation or inspection.

The temporary compiler retains decode-all-ordinary-tags -> derive-AC ->
all-makers -> conversions -> existing-collectors ordering. Its ordinal
adapter is not an extension fragment builder or a promise of retrospective
source tracking for ordinary clients. Source-sensitive clients have already
moved to explicit `simpExtLib` construction. Do not extend the transitional
ordinary source/replay helpers; TASK_16 removes them with compiled storage.

## Evidence scope

See `../TASK_15_HANDOFF.md`. Fragment layout, source work, local emitted work,
proofs, history/printing/exclusion schedules and incremental retained graphs
are tested separately from full-module runtime measurements. Existing mixed
compiled imports still change process/theory/allocator state. Their effects
are not waived or called a final default-performance pass; the full-module
measurements remain visible for the planned TASK_16/29 gates. Matching the
ambient registry/context and heap is an attribution experiment only, never
an API option or a requirement imposed on ordinary clients.
