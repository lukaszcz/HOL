# Legacy tactic staging and proof contracts

This suite gates the ordinary path against the original sealed develop
expectations; expected-red observations below are not an accepted outcome.
`staging/Staging.sml` is independent of the historical compact reproducer.
It runs 43 saved-tactic scenarios plus a negative-bound argument probe and
three validator controls. The exact ordered expectations are sealed in
`staging/references.json`; do not regenerate them to accommodate a candidate.

Reference: develop `cccaa27d7099cbadc886983020cbe745db7793f3`.
Expected-red pins (diagnostic mode only): reviewed
`cf1f863b4e5a9712ce1b179f18274eb3451f3954` and
`54c4882ba04dd788bc6fee104e68b2f5c0335ce2` (same production sources).
These are mixed-source isolation experiments on the same
shared Poly/ML runtime/dependencies, not independent clean repository builds.

## Stages and proof contract

Arguments (`Req0`, `ReqD`, bounds, `Abbr`, label references, `FRAG`) are built
**before** the construction meter. The separate negative-bound probe measures
argument construction itself. Construction means obtaining a saved tactic from
`global_simp_tac cfg ss args`; first and second application reuse that value.
All use the legacy, strategy-free entry point and the same config. Hooks
changing the grammar, live context, printer, registry or goal run outside meters.

Each measured construction/application/reconstruction reports primitive
inference deltas and an ordered callback log. Exceptions report HOL provenance
and captured message, or the actual `PrinterFailure` constructor and payload
reference identity, or the exact Basis `Option` constructor. Exceptions caught
by a scenario do not count as a successful application or proof. Construction
failure explicitly makes both uses unavailable; it is not retried.

Every successful application records **ordered goals and assumptions**, then
constructs genuine kernel proofs of the residual goals from their own
assumptions, and **calls its returned validation**, even for zero subgoals.
Proof construction is outside the reconstruction meter. A separate measured
reconstruction reports its inference/callback counts, checks the original
conclusion, requires every hypothesis to belong to the original assumptions,
and rejects oracle tags other than normal `DISK_THM` dependencies. The full
reconstructed hypotheses/conclusion and oracle tags are recorded. Type-aware
structural encodings do not call printers or depend on grammar/pretty names.

Develop executes **57 validations / 60 checks / 726 ordered observations**;
reviewed/current execute **54 / 57 / 718**. The three lost validations are
`throw_after` first/second and `throw_second` second. Real kernel proof checks
and the final executed-validation counter are mandatory. Controls reject wrong
conclusions, foreign hypotheses and a deliberately oracle-tagged theorem.
`VALID` is deliberately not used to merge application and proof stages or to
replace genuine residual proofs with its synthetic oracle proofs.

## Executed develop stage matrix

`C/U1/U2` are primitive counts; `V1/V2` are reconstruction counts. `-` means
there is no returned tactic/validation, **not** a skipped validator. Ordinary
returned residual goals reconstruct the original goal with a subset of its
hypotheses. Exact ordered terms, hypothesis sets and exception messages are
in `staging/baseline.json`, not inferred from this abbreviated table.

| Scenario | C/U1/U2 | V1/V2 | Application/proof outcome |
| --- | --- | --- | --- |
| empty | 0/13/13 | 0/0 | Unchanged, real residual proofs |
| unmarked | 0/14/14 | 1/1 | `p /\ T` becomes `p` |
| req0 | 2/14/14 | 1/1 | Requirement succeeds |
| reqD | 2/14/14 | 1/1 | Requirement succeeds |
| req0_reqD | 4/14/14 | 1/1 | Both wrappers succeed |
| reqD_req0 | 4/14/14 | 1/1 | Same wrapper semantics |
| req0_failure | 2/23/23 | -/- | `REQUIRE0_TAC`, zero bound leaves LHS |
| reqD_failure | 2/13/13 | -/- | `REQUIRE_DECREASE_TAC`, zero-to-zero |
| both_failure | 4/23/23 | -/- | Inner `REQUIRE0_TAC` raises first |
| reqD_then_plain | 2/13/13 | 0/0 | Requirement dropped; unchanged proof |
| plain_then_reqD | 2/13/13 | -/- | Last requirement fails |
| req0_then_reqD | 4/14/14 | -/- | Only last check survives; fails |
| reqD_then_req0 | 4/14/14 | 1/1 | Only last check survives; succeeds |
| req0_then_plain | 2/23/23 | 0/0 | Zero-bound requirement dropped |
| bound0 | 0/23/23 | 0/0 | No rewriting on either use |
| bound1 | 0/24/24 | 1/1 | Supplied allowance fresh each use |
| bound2 | 0/24/24 | 1/1 | Supplied allowance fresh each use |
| bound1_two_redex | 0/26/26 | 1/1 | One occurrence remains each use |
| bound2_two_redex | 0/27/27 | 1/1 | Both occurrences removed each use |
| req0_bound1_two_redex | 2/26/26 | -/- | `REQUIRE0_TAC`, residual occurrence |
| installed_bound1 | 0/14/13 | 1/0 | First spends installed quota; second cannot |
| reqD_bound1 | 2/24/24 | 1/1 | Wrapper around bound |
| bound1_reqD | 2/24/24 | 1/1 | Bound around wrapper |
| malformed_bound | 0/10/10 | -/- | Exact `Option`, only at application |
| reqD_malformed_bound | 2/10/10 | -/- | Early wrapper, late exact `Option` |
| ordered_subgoals | 0/13/13 | 1/1 | Two goals `p;q`, then `q;p`; both validated |
| hyp_rule | 2/14/14 | 1/1 | Reconstructed proof retains hypothesis `r` |
| closed | 2/3/3 | 0/0 | No subgoals; validation called with `[]` |
| grammar_context | 2/13/13 | -/- | Diagnostic retains construction grammar/context |
| throw_construct | 2/-/- | -/- | Exact printer exception during construction |
| throw_after | 2/14/14 | 1/1 | Saved tactic valid despite now-throwing printer |
| throw_second | 2/14/14 | 1/1 | Printer starts throwing only before reuse |
| throw_discarded | 2/-/- | -/- | Even discarded wrapper prints/throws early |
| late_fragment | 0/0/14 | -/1 | Missing first; register; same tactic succeeds |
| replaced_fragment | 0/14/13 | 1/0 | Registry replacement affects second use |
| rewound_fragment | 0/13/0 | 0/- | Context rewind makes fragment missing |
| missing_fragment | 0/0/0 | -/- | `simpLib.process_tags`, both uses, not construction |
| late_label | 0/13/49 | 0/9 | Missing label omitted; next goal supplies rewrite |
| label_order | 0/76/76 | 11/11 | Duplicate-label assumption order yields `p`, then `q` |
| label_reference_order | 0/76/76 | 11/11 | Distinct refs follow assumptions, yielding `q`, then `p` |
| late_abbr | 0/25/6 | 8/- | Expands in first goal; missing abbreviation fails second |
| reqD_then_abbr | 2/25/25 | 8/8 | Trailing `Abbr` drops requirement; expansion succeeds |
| reqD_after_abbr | 2/25/6 | -/- | First requirement fails; second missing abbreviation |

The separate negative-bound argument probe has zero primitive inferences and
raises `HOL_ERR(BoundedRewrites.MK_BOUNDED:negative bound)` before any tactic
construction. A malformed encoded bound is different: the tactic constructs
successfully and application raises Basis `Option`. Do not normalize or move it.

## Explicit early and late obligations

- Develop's `global_simp_tac` composes `mk_require_tac` and `ABBRS_THEN` early.
  Each requirement wrapper strips its marker and constructs a diagnostic then:
  **one printer call and two primitive inferences per wrapper**. Both wrappers
  on one theorem construct twice, independent of their tagging order.
- `mk_require_tac` restarts from its **original** tactic for each list item.
  Only the final item's checks survive, but all earlier wrappers still strip,
  print, infer and can throw. Within one item `Req0` is processed before `ReqD`;
  `ReqD` surrounds it, and a failing inner `Req0` raises first. This suite
  deliberately preserves these quirks; it does not repair generic markers.
- Requirements inspect subgoal conclusions, not assumptions. `closed` exercises
  vacuous success with no remaining goals; its proof has no hypotheses.
- `ABBRS_THEN` partitions/name-extracts at construction, but `UNABBREV_TAC`
  expansion and missing-abbreviation errors remain goal-dependent and late.
  An early wrapper can count the original abbreviated goal before expansion.
- Label resolution remains late. The `LLABEL_RES_THEN` path silently omits
  missing references (unlike some other marker APIs). Both duplicate-label
  selection and distinct-reference ordering follow the **assumption list**.
- `FRAG`, not the eager registering helper `SF`, exercises late registry lookup,
  replacement and context rewind. Missing fragments must not break construction.
- Supplied bounded rules compile on each application; installed bounded rules
  retain their spent quota. Neither may be moved indiscriminately to construction.
- Grammar replacement and a context-backed printer slot change `A/A` to `B/B`
  between construction and use. Develop's failing requirement retains `A/A`;
  the candidate incorrectly captures `B/B`. Context/grammar restoration before
  reuse restores `A/A`, but must not trigger a new develop callback.

## Expected-red diagnostics

`staging/reviewed.json` holds the expected-red (diagnostic) behavior. All
requirement construction counts become zero; their callbacks and two/four
inferences move to **each application**. Plain/empty, late lookup and
nonthrowing proof outcomes otherwise match develop on this fixture. Exception
stages do not:

- A printer already throwing makes develop construction fail, but candidate
  construction returns and each use raises the identical exception instead.
- `throw_after` and the second use of `throw_second` reconstruct valid develop
  proofs but raise on candidate. Their missing proof results are expected-red
  evidence, never successful validations.
- The discarded-wrapper printer has the same wrong exception stage.
- Changed grammar/context changes the candidate's captured requirement message.

The exact expected-red stream is checked, not merely accepted because it differs
from develop. Extra exceptions, static errors, missing proofs/uses, reversed
subgoals, changed hypotheses, failed processes, wrong paths or truncated streams
are failures. Python controls mutate these observations independently of the
historical reproducer. A standalone strict baseline-contract run executes only
`Staging` and passes develop; it exits 1 on a candidate that regresses the
staging contracts.

## Reproduction

Use fresh output paths. From the repository root:

```sh
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/staging-current staging-contracts
bin/Holmake --no-project --no-cache --no_prereqs \
  --holstate="$PWD/bin/hol.state0" \
  -C src/simp/tests/compatibility -j1 \
  PAIRED_OUTPUT=/tmp/staging-control staging-baseline-control
```

The first command runs the new and original probes plus six executable negative
controls per selection. The second runs just the new suite baseline/baseline.
To run the strict gate **without executing either old reproducer**:

```sh
python3 -B src/simp/tests/compatibility/run_paired.py \
  --staging-contracts --staging-only --candidate HEAD \
  --candidate-signature pass --candidate-behavior baseline \
  --output /tmp/staging-strict
```

That command must exit **0** on restored sources and exits **1** on a candidate
that regresses the staging contracts. The `staging-contracts` target explicitly
selects baseline behavior and a passing signature too. Diagnostic
`--candidate-behavior reviewed` is the expected-red mode, not a compatibility
pass. Rechecking the reviewed pin
`cf1f863b4e5a9712ce1b179f18274eb3451f3954` (`--candidate` with that revision)
needs a checkout of that revision, because the pin no longer builds against
the current tree. `--staging-only` intentionally excludes old
signature/behavior probes and cannot combine with performance, public
clients or old negative controls.
