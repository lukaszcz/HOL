# Focused TraverseExt contracts (TASK_09)

Run from the repository root, with the core heap:

```
bin/Holmake --holstate="$PWD/bin/hol.state0" --no-project --no-cache \
  -C src/simp/tests/traverse-ext -j1 check
```

`check` builds **and executes** `selftest.exe`. Building `.uo` files alone
is not validation. No `bin/hol` input pipelines or mixed simpset adapters are
used. `SignatureWitness.sml` applies TASK_08's complete traversal signature
to the actual `TraverseExt` structure. `selftest.sml` also instantiates its
signature-parameterized test body with that actual structure.

Coverage:

- Explicit ordinary lifting, inert lifting/record views, explicit collector
  counts, context exception payload identity, solver/conv/stack/relation/refl
  forwarding, native integer/option record adapters.
- All three reducer constructors: saved TRAVERSE construction-once versus
  per-application XTRAVERSE, explicit-context, root and observer entry points;
  collector/fact ordering, empty context and reuse.
- NONE reaches each native candidate inside one reducer's FIRST_CONV, even
  after an earlier candidate changes the shared `Cond_rewr.stack_limit`;
  SOME zero/one stay explicit, saved NONE stays live, CONTEXT samples at its
  callback, and custom order controls a native permutative rewrite.
- Generic subgoaler/solver fact and stack order, recursive prepend versus
  solver-only append, separation from reducer collection, and capture-safe
  binder traversal without a generic solver provider.
- One-step root rewriting with no child descent, full recursive proving of
  root side conditions, parent/child-first visitation and overlap proofs.
- Eta head preservation, selected abstraction retention, logical-binder
  exclusions, abstraction-body normalization and exact normalization charges.
- Failed side-condition observation with exact observer/reducer/solver/charge
  counts; observer and charge HOL_ERR, foreign payload and Interrupt identity,
  including callback errors passing through conditional-rewrite wrappers.
- Default eager factory schedules compared with ordinary traversal for high,
  low and aborting reducers; reuse, lazy extended/root factories, rejected
  factories, initial collector exception stages, shared Trace listener.
- Failed recursive proofs restore traversal limits, preserve exact callback
  order, and transport rewritten-condition proofs through ordered solvers.
- Real Poly/ML static rejection of reducers crossing the boundary in both
  directions, from the two deliberately ill-typed `negative/*.ML` clients.
  A missing file or exception other than `Fail "Static Errors"` fails closed.
  Expected compiler diagnostics from these clients are normal test output.

The lifetime/collector/default/factory observations derive from
`../contracts/TraversalContracts.sml`; extension assertions also correspond
to the mixed `../../src/selftest.sml` extended-traversal block, R2 lifetime
and P1 generic-context contracts. These are additive tests: no existing
contract body, ordinary test, or source is replaced. TASK_11 still owns
removal of the mixed legacy constructors; this suite uses none of them.

Successful execution prints `TraverseExt focused checks: 131` and exits zero.
The counter includes `convtest` assertions and the two negative clients.
The parent `../../src/Holmakefile` runs this separate target at selftest level 1;
ordinary `selftest.sml` does not import the new engine.

## Additive coverage map

These anchors identify duplicated invariants, **not relocated original cases**.
All 2,153 TASK_06 IDs/bodies remain at their original sealed destinations and
are checked by `../compatibility/coverage_ledger.py`. The new tests add explicit
lifting and apply the same contracts to the separate type/engine.

| New selftest block (exact comment anchor) | TASK_06 case/body provenance |
| --- | --- |
| `Lifting and both record views are inert` / `Native adapter views` | New explicit boundary; TASK_08 adapter contracts |
| `The lifted callbacks also receive` | `traversal:0001-0009` private recursive contexts; explicit stack/relation checks added |
| `Atomic terms isolate initial collection` | `native:0503,0512,0514,0518-0520`; `traversal:0001-0009` |
| `NONE must reach the native candidate` | `traversal:0029-0032`; `native:0612-0613,0617-0630` live/configured controls |
| `Generic solver facts must not leak` | `native:0607-0610` binder/fact-order assertions |
| `Root selection applies only outside` | `native:0554`; original root/child-first blocks at selftest:730-1533,3446 |
| `Eta preservation is policy-selected` / `Observer failure must survive` | `native:0491-0502` child-first composite assertions, selftest:3871-5019 |
| `Failed recursive proofs restore` | `limits:0001-0005` (explicitly lifted); pipeline proof transport is additional |
| `Construction and factory exception scopes` | `traversal:0011-0028`; `native:0548-0555` factory schedules |

Original assertions are not weakened or replaced by this subset map. Fresh native
receipts compare the entire original ordered streams; paired receipts compare
all 47 traversal checks/273 OBS events (plus original/exclusion/limit suites).

## Separate construction/reuse diagnostic

Build `diagnostics.exe` with the same Holmake flags, then, **after builds finish**:

```
(cd src/simp/tests/traverse-ext && ./diagnostics.exe)
```

This retains/exercises 20,000 constructed conversions separately from saved
conversion reuse, for ordinary default, extended default, old mixed refresh and
separate refresh. Every result's conclusion/hypotheses and exact callback counts
are consumed. CPU and wall displays are single-process diagnostics only, not
calibrated performance acceptance, independent builds or a legacy cost claim.
