# TASK17 bounded source / behavior audit

The ordinary `simpLib.{sml,sig}` pair was restored in TASK16. TASK17 deliberately
keeps it byte-identical to develop (`cccaa27d7099cbadc886983020cbe745db7793f3`),
not a wrapper or a second deletion implementation. Whole-file hashes and fresh
compiler correspondence are under `performance/evidence/`. There is no missing
implementation patch hidden in this audit-only landing.

## Literal deletion (pinned source lines 291–342)

- `name_match` uses literal equality, `rewrite:` equality, or the literal
  `rewrite:<base>.` prefix, and optional exact theory equality. No namespace
  resolver, source handle, inventory or extended `ExclX` interpretation.
- `filter_net_by_names` parses all patterns first, then performs exactly one
  `Ho_Net.vfilter` over the **original net**. Dotted parsing preserves numeric
  second components, strict ancestry checking for two-component theory names,
  permissive three-component names, empty fields and too-many-dot errors.
- Decision procedures use exact complete names, not rewrite prefix matching.
  Exactly one `List.filter` sees the original dproc list, after the net filter.
  No extension net discriminator, scan, cache, fast-path or extra inventory.
- Only the **empty list** returns the old simpset. Every nonempty list records a
  reverse-order `DELETE_EVENT`, including missing names and an empty string.
  Surviving conversions retain their closures/live controls. Limits, history,
  maker, traversal rules and excluded set pass through unchanged.

## Replay and fragments (lines 686–758)

- `build_from_history` folds the reversed history from `empty_ss`, calling
  original `++`, `-*`, or `add_weakener` in that order. A DELETE_EVENT stores
  strings, not previously parsed patterns: reparsing asks the **current**
  theory. Replaying unmatched deletions is observable even with an empty net.
- `remove_ssfrags` removes every matching ADDFRAG (including duplicate names
  and empty-name anonymous matches), preserving other events. No match raises
  `UNCHANGED` **without callbacks**. A match replays, then restores limit and
  excluded state. Maker changes and opaque collector callbacks rerun at their
  historical stages; declared rewrite bounds reset on recompilation.
- `exclude_ssfrags` unions excluded names, filters against the union and always
  replays, even for `[]` or absent names. It restores the original limit and
  resulting excluded set. This is not control-preserving extension replay.
- `force_add` clears only the named fragment's excluded entry, then uses `++`.
  Baseline nuance preserved: `exclude_ssfrags [""]` removes existing anonymous
  fragments, but `is_excluded` does not suppress future anonymous additions;
  anonymous force-add is still an ordinary anonymous addition.

## Marker routes (lines 838–908, ordinary tactics below)

`DExcl` gathers literal strings in argument order. `process_tags` performs
fragment removals, Cong/AC addition, forced named-fragment additions, then
ordinary `-*`. Conversions/rules and the ordinary tactics use this same path.
No marker is changed into ExclX and no generic marker implementation changes.
TASK17's saved tactic tests execute both returned validations and check exact
conclusions and hypothesis sets. TASK18 separately owns its broader staging
contract; nothing in TASK17's exclusion path is left for that task to repair.

## Evidence interpretation

The immutable prior 929 exclusion checks retain exact warnings, errors,
callback and parser/theory streams. The new 42 checks independently pin
missing-empty-net history across real theory changes, ADDWEAKENER/delete/maker
replay order, counts, limits, excluded state, live quota survival and declared
quota reset, plus literal conversion/tactic routes and validations.

The 44-row, four-size cost matrix consumes results and checks proofs, ordered
dproc names and replay maker/collector counts. Fresh AB/BA and baseline-control
campaigns remove the reported ~3x cost: total-CPU point ratios span
0.972–1.020, with source and local native delete/replay work identical to
develop. This is a **bounded algorithm-cost conclusion**, not statistical proof
of equality. Numerical parity remains unresolved; initial GC-only slower rows
are retained, investigated with longer batches/counters and not reproducible
as a stable four-row slowdown. See `performance/evidence/GC_FOLLOWUP.md`.
No arbitrary slowdown allowance or averaging of workloads is used. Whole-plan
final runtime/independent-build gates are not TASK17's bounded acceptance.
