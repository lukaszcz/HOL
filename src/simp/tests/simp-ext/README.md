# Focused simpExtLib contracts (TASK_10)

Run from the repository root, once `simpExtLib` is available:

```
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/simp-ext -j1 check
```

`check` builds **and executes** `selftest.exe`. Building `.uo` files alone
is not validation. This target does not modify the production Holmakefile or
ordinary `../../src/selftest.sml`. The production `simp-ext` target runs it
at `HOLSELFTESTLEVEL=1`. Expected Poly/ML type-error diagnostics
from `negative/*.ML` are normal successful test output.

## Construction and compiled clients

`../../src/pureSimpsExt.{sig,sml}` and
`../../src/boolSimpsExt.{sig,sml}` mechanically reproduce the ordinary
recipes using extension constructors, in the original order. The full BOOL
catalog is available, including optional ETA, ordinary versus explicitly
threaded congruences, conversions, and named fragments. Inputs are immutable
theorems/conversions; no ordinary fragment/set is promoted, inspected, or
reconstructed via `ssfrags_of`. BOOL retains the ordered recipe
`PURE -> BOOL -> NOT -> CONG -> UNWIND`; ETA is opt-in.

`APIExamples.sml` elaborates clients against the actual sealed production
modules. It checks the complete recipe catalog, explicit ordinary-reducer
lifting, configured reducers, both **extension-typed** projections, argument
preparation, bundle installation, and immutable AC/TypeBase/relational/threaded
factory inputs, plus explicit public congruence-fragment lifting and typed
congruence construction. No fake implementation or legacy projection adapter
is used.

## Semantic checks

- BOOL beta/boolean rewrites and contextual COND congruences; opt-in ETA and
  logical-binder exclusions.
- Saved live conditional depth observes changes to the shared
  `Cond_rewr.stack_limit` in both directions; explicit zero/40 overrides it
  without mutating it. Recursive conditional proofs compare conclusions and
  complete hypothesis sets; recursive side-condition rewrites are not tracked.
- Explicit opaque lifting preserves collector/application payload identity and
  relation/reflexivity callbacks, creates no source inventory, and distinguishes
  construction-once default collection from per-application configured refresh.
- Late projection extraction after exhaustion, in both orders; original/view
  quota sharing, source identity/order, partial/exhausted preserving replay,
  explicit reset replay, preserving filtering and source suspension. No getter
  compilation, maker callback or compilation trace is allowed.
- Prepared bundle combination retains bindings and partially spent actual
  controls; duplicate bindings fail rather than refreshing allowances.
- Parent/child-first overlapping rewrites, charging, argument-only root
  preservation, reusable private normalization with exhausted native quotas,
  and restoration on success and observer exceptions with exact payloads.
- Same-name ordinary/extension typed registries remain independent. Saved SF
  tactics resolve late, follow replacement/Context rewind, and fail when absent.
  SF's shared string-marker syntax does not permit cross-registry fallback.
- One Trace listener and one tracking extent observe both engines. Nesting in
  both directions isolates inner reports and restores outer tracking, including
  a foreign exception leaving the nested extent.
- Eight real Poly/ML negative clients reject reducer, set-consumer, fragment
  installation and compiled congruence-set crossings in **both directions**. The harness follows
  `../traverse-ext`: only `Fail "Static Errors"` counts as rejection; accepted
  code, missing files and other exceptions fail closed.

Closed rewrite fixtures check both sides of each conversion theorem and empty
hypotheses, not just the resulting term. Open conditional fixtures compare the
complete expected theorem/hypothesis set. Saved-tactic checks run through
`VALID`. Context snapshots, listeners and the global depth control are restored.

## Additive provenance

These tests add separate-type assertions; they do not move or weaken original
cases or alter the sealed TASK_06 coverage ledger. Comment anchors map to the
existing original contracts as follows:

| New block | Original semantic provenance |
| --- | --- |
| `The standard recipe order` | ordinary PURE/BOOL construction recipes |
| `A saved NONE stays live` | main selftest configured depth surface; TraverseExt live-depth contracts |
| `Lift construction and projection` | TraverseExt lifting and construction/reuse contracts |
| `Exhaust before extracting` / `Getter/source extraction` | main selftest compiled projection/source lifetime contracts |
| `Prepared bundles retain` | main selftest `combined_bundle_fixture` |
| `Child-first changes overlap` | main selftest `prepared_normalization_fixture`, observer/child-first contracts |
| `Two typed Context slots` | main selftest R4 late FRAG lookup and Context restoration |
| `One tracking slot` | TASK_08 singleton tracking/control ownership contract |

This focused suite is a relocation smoke/contract gate, not full TASK_14 quota
revalidation, TASK_26 normal-suite migration, or a performance acceptance claim.
