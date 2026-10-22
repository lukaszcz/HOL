# TASK21: tracked source/view/bundle migration closure

Legacy clients require **no migration**. These branch-only APIs belong to
`simpExtLib`; choose its fragments and simpset **before installation** of any
source-sensitive rule. No import of an arbitrary `simpLib.simpset` exists.
Neither history replay in a getter nor reconstruction from `ssfrags_of` is a
substitute for tracked construction.

## Caller audit

The initial inventory in [CONSUMERS.md](CONSUMERS.md) records historical line
numbers and ownership. The TASK10/14 cutovers already migrated the remaining
in-scope source clients at their construction points; TASK21 verifies them
without changing their assertions or replacing their ledger entries:

| Caller | Earliest explicit tracked construction | Preserved contracts |
| --- | --- | --- |
| `src/selftest.sml`, source/view/suspension/bundle factories | Top-level module aliases to `simpExtLib`, `pureSimpsExt`, `boolSimpsExt`, `TraverseExt`, before all fixtures | Original source/conjunct/AC order, duplicate events and slots, stale/support views, partial/exhausted quotas, opaque contexts, replay and validated proofs |
| Same file, paired/projection blocks | Same aliases before the root sets or conversions are built | Both extraction/use orders, late extraction after exhaustion, no getter compilation or callback work |
| `tests/simp-ext/{selftest,tracked,exclusions,tactics}.sml` | Explicit `simpExtLib` and tracked recipes at every seed | Actual controls across views/projections/filtering/replay, not equal handle labels alone |
| `tests/simp-ext/APIExamples.sml` | Typed extension recipe, directive preparation, bundle preparation, installation | Compile-checked explicit API and module boundary |
| `tests/compatibility/interfaces/Task08Clients.sml` | Typed extension argument and bundle construction | No ordinary-set promotion |
| New `tests/simp-ext/sources.sml` | Explicit tracked seeds before native or prepared installation | Missing intersections and fail-closed legacy-source negative clients |

No new production caller migration was necessary. Standard recipes and the
external consumer retain their independently planned TASK24/TASK25 scopes;
this is not a claim to have integrated that external worktree.

## API/control decisions

- A source origin orders event, slot, AC component and maker conjunct.
  `rewrite_source_compare = EQUAL` is **not** sufficient compatibility:
  `same_rewrite_source` also requires compiled name, alpha-equivalent
  conclusion, complete hypotheses and declared bound. Different proofs of
  the same statement are compatible. Changed hypotheses/bounds are not.
- Inventories prepend new fragment sources and retain maker/conjunct order.
  AC commutativity, associativity and left-commutativity precede ordinary
  rewrites. Installed views enter `rewrite_sources` under their source's
  name, but never create entries in `rewrite_source_handles`.
- Bundle grouping/order follows supplied rules and composition order;
  installation prepends each event, retaining conjunct order within it.
  Composition preserves partial and exhausted actual controls. Nested
  duplicate events and overlapping installations fail before collectors.
- Native conjuncts and every accepted attached view share one actual parent
  control. Prepared projections do too. Preserving replay keeps actual
  partial/zero controls; ordinary replay resets declared groups while still
  sharing between siblings/views. Getters/composition never refresh either.
- Cached successful **and rejected** view matchers replay without compilation.
  Missing/incompatible handles neither bind views nor suspend replacements.
  Source deletion invalidates its views, not surviving sibling sources/views.
- `rewrite_context_changes` reports arbitrary conversion key additions and
  removals, including both keys of a replacement. Keyless or opaque changes
  require rebuilding. It now also detects active view dependency invalidation
  when the view event itself survives suspension/deletion/filtering/removal
  or a changed maker statement. Returning a removed bundle after its old view
  event does not install that view retroactively: dependency observation
  respects installation order, not merely final source membership.
  Alternative installations of one bundle can attach different views even
  with the same event/source/index: compiled view conclusions and hypotheses
  are compared, ignoring proof identity and redundant generalization.
  Compatible view replay and consumption alone are not invalidations. Native rewrite differences remain separately
  inspectable through handles; they are not returned as conversion keys.

The only algorithm change is this extension-only view dependency observation.
No ordinary source, shared control identity, registry, generic marker or
postkernel service changes. There is no new global cache or rebuilding import.

See [TASK21 handoff](../TASK_21_HANDOFF.md) for executable coverage and evidence.
