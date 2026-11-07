# Frozen public source contracts

Baseline: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Expected-red candidate pin: `8b1e8c69f5dd819d1fbe8b75cf5755f21b450499`.
The production source diff from reviewed `cf1f863b4` to this candidate is empty.
In expected-red mode this is a **coverage gate**, not restoration or a
compatibility pass; the restoration gate selects `--candidate-signature pass`.

## Complete inventory and mapping

The whole-tree `git diff <baseline> HEAD -- '*.sig'` finds six changed
baseline-existing signatures. `public_contracts.inventory` refuses any changed
baseline signature without a reference/client, including outside `src/simp`.
The manifests retain the actual diffs and inventory for BOTH selected revisions.
[`public/surface.json`](public/surface.json) enumerates all original declared
values, types and constructors and maps each to its full-ascription clients.

All seven original signatures are real, byte-identical SML in
[`inputs/develop/`](inputs/develop/). `public/references.json` pins revision,
Git blob, SHA-256 and byte count; the runner compares them to Git before every
build. No dependency, field, constructor or original export is rewritten.
Private `Legacy*.sig` files change **only the signature declaration name**;
empty companion `.sml` files make these signature-only modules loadable.

Counts exclude the aliases inherited through `include Abbrev`:

| Public signature | Old values/types/datatypes/constructors | Reviewed-candidate change | Client (under `public/`) |
| --- | --- | --- | --- |
| `src/1/ThmAttribute.sig` | 12/4/0/0 | 2 added values | `PublicThmAttribute.sml` |
| `src/simp/src/Cond_rewr.sig` | 7/1/0/0 | 4 added values | `PublicCond_rewr.sml` |
| `src/simp/src/Opening.sig` | 5/1/0/0 | 1 added value | `PublicOpening.sml` |
| `src/simp/src/Travrules.sig` | 9/0/2/2 | 1 added value | `PublicTravrules.sml` |
| `src/simp/src/simpLib.sig` | 67/9/0/0 | 49 added values, 4 types | `PublicSimpLib.sml` |
| `src/simp/src/Traverse.sig` | 3/2/1/1 | 11 added values, 7 types, 1 datatype, **2 extra reducer constructors** | `PublicTraverseAscription.sml`, `PublicTraverseFunctor.sml`, `PublicTraverseClient.sml` |
| `src/simp/src/congLib.sig` | 13/1/1/1 | **unchanged**, changed dependencies | `PublicCongLib.sml`, `PublicTraverseClient.sml` |

Thus every original explicit value (116), ordinary type (18), datatype (4)
and constructor (4) has executed signature matching. All 15 original `Abbrev`
aliases are also checked by each of the six including signatures: `thm`, `term`,
`hol_type`, `conv`, `rule`, `goal`, `validation`, `tactic`, `list_validation`,
`list_tactic`, `gentactic`, `thm_tactic`, `thm_tactical`, `quotation`, `subst`.
`Abbrev.sig` itself is unchanged. These are **static contracts for every
export**, not claims that every operation's runtime semantics were exercised.

The complete signatures cover operator types (`++`, `-*`, `&&`), polymorphic
tracking, printers, all tactic variants, registrations, record aliases and
abstract types, not just the handful of operations in the smoke assertions.
`where type` constraints and cross-module assignments explicitly retain
`ssfrag`, `simpset`, `congset`, controlled-theorem and reducer type identities.

Additional runtime/type checks:

- `PublicThmAttribute`: every original export is called; all original record
  fields, local/stored callbacks, registration, parsing, formatting and
  abbreviation lifecycle are exercised.
- `PublicCond_rewr`: controlled-theorem identity, all three canonicalizers,
  curried rewrite construction/application, order and polymorphic tracking;
  `stack_limit` remains an `int ref` (no configured-depth import).
- `PublicOpening`: original `congproc` continuation record, ordinary
  construction, relation/condition inspection and equality opening.
- `PublicTravrules`: replication of BOTH original datatypes, exact constructor
  payloads, relation lookup, merging and construction with `Opening.congproc`.
- `PublicSimpLib`: every original record alias, complete `SSFRAG` record,
  ordinary tactic construction, projection and proof-producing simplification.
- `PublicCongLib`: complete datatype ascription/replication, every `CSFRAG`
  field, original opaque `congset` and ordinary `simpLib.simpset` interoperability.
- `PublicTraverseClient`: replicated `reducer` is assigned in BOTH directions;
  the original constructor-only function remains unchanged and has no wildcard.
  All four outer fields (`name`, `initial`, `addcontext`, `apply`) and all five
  callback fields (`solver`, `conv`, `context`, `stack`, `relation`) are used.
  The callback's relation pair, exception-context identity, collector and both
  continuations execute. All five `traverse_data` fields are constructed and
  deconstructed. Original reducers pass through `dproc_ss`, `weakener_data`,
  projection and `congLib.CSFRAG` without extension types or imports.

These new clients were developed against the baseline, then sealed in
`public/clients.json` after a successful baseline execution. Do not edit them
(or their seal) to accept a candidate API. Add further clients alongside them.
The immutable review `abicheck.sml` and original `Traverse.sig` are untouched;
that earlier complete-ascription control also still executes independently.

## Expected outcomes and non-breaks

| Contract | Baseline | Reviewed candidate |
| --- | --- | --- |
| Six non-Traverse full signatures, including unchanged `congLib` | pass | pass |
| Complete original `Traverse` structure ascription | pass | **exit 1**, both unexpected constructors |
| Complete original `Traverse` functor parameter/application | pass | **exit 1**, both unexpected constructors |
| Datatype replication and every original reducer/record field | pass | executes successfully, same original type identities |
| Original exhaustive constructor-only match | exhaustive | **nonexhaustive warning**, exit 0, not a compatibility pass |
| Ordinary cross-module smoke clients | pass | pass, no extension imports |

Replication alone is not red: SML replicates the *current* constructor set.
The unchanged original match then loses exhaustiveness. The runner requires
exactly one warning attributed to `PublicTraverseClient.sml`; a warning in an
unrelated loaded source is not evidence. The two static failures require both
specific constructor diagnostics, the correct failing source, exit 1, zero
checks and a complete error footer. Arbitrary static errors are rejected.

`Traverse` additions are NOT harmless merely because `REDUCER` kept its old
record shape. Its constructor set participates in datatype signature matching.
No original field/type was removed from the other signatures. Their new value
and type components are additive for these qualified baseline **consumers**;
`simpset` declaration movement and `ssf_upd_rewrs` reformatting are harmless.
This does not promise universal safety for unqualified `open` name collisions
or hand-written providers implementing today's expanded named signatures.
Runtime, scheduling, allocation and loading equivalence are outside this gate.

Branch-only `SplitData.sig`, `simpMarkerLib.sig` and `splitLib.sig` have no
baseline consumers to freeze. The added `inputs/develop/Traverse.sig` is a test
input, not another public production API. This gate neither imports nor alters
their contracts.

## Execution and isolation

Use the paired runner (`run_paired.py`), which builds deferred `.uo`
dependencies and then really executes every client in its own fresh process.
Explicit Holmake dependencies are essential: its scanner misses some names used only in module ascriptions.
The validator requires completed elaboration of each entire `Legacy*.sig`,
not just building a `.ui`/`.uo` or seeing a check string.

`ThmAttribute` is already in `hol.state0`; reloading it would collide with its
Context slots. Its dedicated launcher instead uses **`hol.state.min` on both
sides**. The bootstrap imports no `HolKernel`/`testutils` before activating
private-first paths and tracing. `CheckSupport.sml` then installs the ordinary
`testutils` reporter. Exact selected `ThmAttribute.{sig,sml}` must be freshly
elaborated; preloading or loading the shared copy is rejected. No source
renaming, slot-name rewriting, duplicate registry trick or production edit is
used. Other fixtures retain `hol.state0` and normal preloaded dependencies.
Each manifest records both launchers and their exact Holmake inputs/options.

```sh
# From repository root; choose NEW output paths (never overwrite evidence).
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/public-current public-contracts

bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/public-baseline public-baseline-control
```

These targets run 23 Python controls, 22 independent normal fixture launches
and 12 rejected executable negative controls per comparison. The ordinary
signature/staging fixtures and failure controls remain active.
For a restoration gate explicitly choose `--candidate-signature pass` (and
`--candidate-behavior baseline` when staging is repaired): expected-red modes
must never stand in for restored compatibility.

These runs are mixed-source isolation, not independent clean builds or
platform-wide proof.
