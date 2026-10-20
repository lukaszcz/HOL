# TASK_06: extended-exclusion marker boundary

## Finalized API decision (before implementation)

Use `markerLib.ExclX : string -> thm`, recognizer
`markerLib.destExclX : thm -> string option`, and directive
`markerLib.DExclX of string`. The distinct theory constant is
`marker$ExcludeX`, defined by `ExcludeX (x:'a) = T` in
`markerTheory.ExcludeX_def`. No evidenced constraint requires departing
from the plan's proposed public spelling.

Follow the existing `Excl`/`ExclSF` named-marker convention: store the
unchanged ML string as a variable name, not a HOL string, prefix encoding
or sentinel. Keep the term constant private to markerLib, like those of
Excl/ExclSF/FRAG; markerSyntax needs no additions.

This task supplies only the marker/API boundary. TASK_07 must expose the
simpLib alias, implement extended exclusion routing and restore literal
legacy Excl routing. Until then simpLib explicitly rejects ExclX rather
than accidentally treating it as a rewrite or silently accepting it.
No persistent split registration is added or changed.

## Implementation and consumer audit

Entry revision: `3a1f4de0d` (TASK_05). Existing branch `simplifier` was
retained; no new branch/reset/merge was needed. A pre-existing PROGRESS.md
TASK_05 handoff edit was preserved and is not part of this task's changes.
Landing identifier: `[TASK_06] Add a distinct extended exclusion marker`.

Changed compiled sources:

- `src/marker/markerScript.sml`: new independent `ExcludeX` definition.
- `src/marker/markerLib.{sig,sml}`: constructor/recognizer, public `DExclX`
  and `dest_directive` classification; existing marker APIs unchanged.
- `src/marker/selftest.sml`: new directive row plus eight focused checks.
- `src/simp/src/simpLib.sml`: the only external exhaustive directive match,
  `process_tags0`, explicitly rejects the new unsupported directive. It
  also rejects bounded ExclX: bounds live in hypotheses, leaving the head
  available to `destExclX`. Existing bounded markers still pass through.
- `src/simp/src/selftest.sml`: twelve temporary boundary assertions for
  SIMP_CONV, `&&` and SIMP_TAC, including Once/Ntimes and requirements.

The other directive consumers are intentionally selective/wildcard:
`strip_wrappers` stops at a named marker, `dest_tacmarked` forwards simpset
markers, and GEN_GLOBAL_SIMP_TAC's assumption-control filter selects only
NoAsms/IgnAsm. They need no new branch. `strategy_free` remains proof-free
and unchanged: unsupported ExclX errors are deferred to normal processing.
Repository searches found no other compiled exhaustive matches. Historical
artifacts/frozen inputs were not edited. No markerSyntax changes are needed:
Excl/ExclSF/FRAG likewise have no term-level named-marker API there.

Documentation: new `help/Docfiles/markerLib.ExclX.smd`, a transitional note
in `help/Docfiles/simpLib.Excl.smd`, and signature comments. Task/index/
progress handoffs name the finalized API and distinguish TASK_07 semantics.

## Validation

Receipts, source hashes and compact test output:
[`results/task06/`](results/task06/). All final commands exited 0:

```sh
bin/Holmake --no-project --no-cache -j1 -C src/marker \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
bin/Holmake --no-project --no-cache -j1 -C src/simp/src \
  --holstate="$PWD/bin/hol.state0" HOLSELFTESTLEVEL=1
bin/build -t --seq=tools/sequences/upto-parallel
tools/h4pedant/h4pedant src/marker src/simp/src
git diff --check
(cd src/simp/compatibility && sha256sum -c inputs/SHA256SUMS)
```

- Marker normal target: **70 OK** (61 existing + 9 new), no failures.
  Tests preserve empty strings, all five namespace-like prefixes, dotted/
  dollar names, whitespace/quotes/backslashes, Unicode, every byte alone
  and a combined 256-byte name. All legacy named marker round trips and
  directive identities stay literal and disjoint. Malformed/non-variable
  arguments and same-named variable heads are rejected. Requirements and
  bounds retain precedence, stripped conclusions and empty hypotheses.
- Simplifier normal target: **444 OK**, including all five existing
  availability-guarded datatype checks and twelve new rejection assertions.
  Traversal-contracts normal target: **47 OK**. Existing exclusion and
  other directive assertions were not changed, migrated or weakened.
- Routine sanity build: exit 0, `Hol built successfully.` It refreshed
  downstream theory identities and built affected consumers through the
  requested sequence. A final incremental rerun also exited 0. This is
  not the full `-F` gate, a paired differential run or a helpdocs build.
- Style and frozen input checks: exit 0. New sources have no tabs/trailing
  whitespace; h4pedant passes both affected source directories.

Initial attempts were not counted as passes: the new malformed-marker
fixture needed ISPEC rather than SPEC for a polymorphic argument, and an
initial per-directory simplifier run encountered stale combinTheory parent
identity after markerTheory regenerated. The routine build resolved that
normal dependency refresh; final targets were forced to rerun by touching
selftest source mtimes only. During the early routine pass the simplifier
suite had 439 OK before later datatype products were available; the final
normal target ran all 444 OK. No existing test guards were changed.

Temporary logs under `/tmp/hol-task06-logs` were reduced to compact receipts
and unique marker/boundary output, then removed. Normal build products and
unrelated/caller-owned historical artifacts were left intact.

## Acceptance and TASK_07 handoff

All TASK_06 criteria are satisfied; no TASK_06 validation blocker remains.
The finalized public names are **ExclX / destExclX / DExclX**, backed by
**marker$ExcludeX / ExcludeX_def**. TASK_07 must add `simpLib.ExclX`, route
DExclX to the extended resolver, restore strict literal DExcl behavior,
replace the temporary `unsupported_exclx` branch and rejection assertions
with routing assertions, and update the transitional signature/doc prose.
Remember the DBounded ExclX case when supplying routing. Bounds and
requirements must keep their established classification precedence.

The ten legacy prefix failures remain assigned to TASK_07, split/case
history repair to TASK_08, and persistent split registration to TASK_10+.
No legacy Excl string was re-encoded, and no complete extended exclusion
feature or whole-plan compatibility is claimed here.
