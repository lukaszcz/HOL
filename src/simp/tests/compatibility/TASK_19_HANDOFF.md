# TASK19 — extension exclusions and control-preserving replay

Landing identifier: **TASK19-extension-exclusions-v1** (containing commit).
Starting HEAD: `5784ccf89fdb3251226eb1e2133808ad4c346366`.
Develop: `cccaa27d7099cbadc886983020cbe745db7793f3`.
Linux/aarch64, Poly/ML 5.9.2; shared `hol.state0`, one GC thread in
isolated paired processes. Main checkout initially clean; unrelated nested
`.agent-files` changes preserved.

## Completion and implementation

**All bounded TASK19 acceptance criteria are satisfied. No blocker remains.**
The tracked representation and exclusion/replay implementation were already
separate after TASK10/14/16. This task audits their behavior, adds missing
intersection tests without weakening originals, and repairs one real namespace
collision. It does not claim whole-plan performance or independent-clean-build
acceptance.

`looper_tac` previously applied split/case suppression displays to **every**
looper. Consequently `ExclX "case:bool"` also disabled an ordinary user looper
literally named `split.case bool`; the same predicate also covered colliding
local split displays. The extension dispatcher now tests suppression only for split loopers.
Ordinary loopers remain independently removable through `looper:`. The new
regression failed before the fix and passes directly, after later additions,
and after preserving replay. The signature documents the namespace boundary.

No other exclusion/replay algorithm needed replacement:

- Extension-owned net entries, source inventories and native handles are
  filtered consistently. Surviving native/default/configured runners and views
  retain their actual controls. No identity is inferred from ordinary history.
- Literal Excl/operator deletion remains strict, silent when unmatched, and
  records nonempty unmatched history. Strict history reparses at replay.
  Extended names retain rule/dproc priority, explicit namespaces, relaxed
  qualified rule resolution, ambiguity/error/warning contracts and resolved
  replay. Pending batched deletions mask subsequent resolution.
- Ordinary replay explicitly resets declared allowances; preserving removal,
  filtering and argument preparation retain compatible surviving controls,
  including exhausted controls. Prepared shapes retain their cached matchers;
  projection extraction neither recompiles nor invokes makers/collectors.
- Private history event order, named prohibition, force-add, duplicate
  occurrences, limits, split/case suppression of later additions and opaque
  context payload identity remain intact. A failed extended request does not
  install a deletion in its input object. This does not promise rollback of
  external side effects from callbacks already scheduled during preparation.

Only `simpExtLib.sml`'s looper enable predicate changes executable production
code. Ordinary `simpLib.sml` and `.sig` remain **entirely byte-identical** to
develop, with SHA256s `ee324439ac66cd14858d6ea5dc45a867d44fa6762298f1cf7df45b13aed6c3cd`
and `d1979668da105341e6e97e900848a2d382eaac3a50650c89bbdeae8ee3689666`.
Thus ordinary exclusions still perform only the original net/dproc filtering;
they import, allocate and scan no extension inventory/suppression state.
Fresh-load tests independently retain the ordinary dependency boundary.

## Tests and retained original assertions

New `tests/simp-ext/exclusions.sml` executes **159 checks**:

- Both projection extraction/application orders, native plus prepared sources,
  literal plus resolved deletions, shared conjunct/view counters, independent
  unrelated counters, surviving origin/statement/order, partially spent and
  exhausted controls, preserving removal and genuinely changing filtering.
  Old saved conversions observe new consumption, not just equal handle labels.
- Failed/unmatched requests and duplicate pending extended targets, physical
  inventory retention, unmatched literal history reviving versus suppressing
  compiler-dropped rules, strict/resolved theory rewind and failed preserving
  reconstruction without quota refresh.
- Named fragment prohibition, no-op pointer/UNCHANGED contracts, force-add and
  independent duplicates, ordinary reset versus preserving replay, exact
  maker/collector order, limit/prohibition retention and opaque payload identity.
- Explicit split/case versus ordinary-looper display collisions, later split
  additions, resolved suppression replay, repeated ambient case exclusion and
  the distinct unmatched-after-removal local-split error contract. Tactic
  validations are actually called; conversion checks compare full conclusions
  and complete hypothesis sets, not just printed endpoints.

The original native fixture is unchanged: **642 checks**, including original
strict/relaxed parser, warnings, ambiguity, strategy namespace, split/case
suppression, source/view, replay, callback-count and failure assertions.
The coverage ledger still verifies **2,153 original source-tied cases**.
Existing separate extension suites retain **88 focused + 174 tracked checks**.
No lowered count, relaxed predicate, rewritten oracle or ordinary-history
promotion is used. The additive coverage map is in
[`../simp-ext/README.md`](../simp-ext/README.md).

## Fresh final validation

Exact source/input/tool/runtime hashes, command exits, loaded paths and
receipts: [`evidence/task19/validation.json`](evidence/task19/validation.json).
All final driver commands below exit **0**; injected negative controls are
correctly rejected, not counted as ordinary successful executions.

| Command | Observation / evidence |
| --- | --- |
| `bin/build -t --seq=tools/sequences/upto-parallel` | Full final routine build; integrated new suite executes; `routine-final.log.gz` |
| `run_prior_native.py --output /tmp/task19/native-final` | 14 receipts; explicit integrated Holmake `HOLSELFTESTLEVEL=1 all`, then actual 642/47/929/native/focused/fresh-load launchers and fresh split exports/heap lifecycle; `native/` |
| `run_paired.py --candidate HEAD --candidate-signature pass --candidate-behavior baseline --prior-contracts --negative-controls --output /tmp/task19/paired` | 24 receipts; baseline/current legacy 73/47/929/6 suites and ABI/callback probes, rejection controls; `paired/` |
| `cd src/simp/tests/simp-ext && ./exclusions.exe` | Final explicit launcher, 159 checks; `exclusions-final.log.gz` |
| `coverage_ledger.py`; `verify_evidence.py`; `audit_task14.py` | 2,153 original cases, 37 immutable inputs, inert getters/actual controls/cached matcher structural audit intact |
| `tools/h4pedant/h4pedant src/simp/tests/simp-ext` | Pass, including line lengths |
| `tools/h4pedant/h4pedant --nolinelen src/simp/src`; `git diff --check` | Pass |

The paired runner selects committed HEAD `5784ccf89`, whose **legacy** inputs
are identical to this final working tree. Its isolated selection does not
include the extension-only edit; it is legacy evidence, not a claimed test of
that edit. The final native driver seals and executes the actual working-tree
extension sources/new fixture. Its receipt includes all three extension-suite
completion counts. No historical result substitutes for final validation.

Two fixture-only exploratory corrections preceded acceptance: prepared bundle
rules are anonymous, so the mixed test now deletes a named native conjunct
while retaining a prepared unrelated source; SML assignment precedence needed
parentheses. Repeated exclusion of a removed local split correctly fails,
unlike an ambient case target that remains resolvable. Expectations retain that
existing distinction. An initial native run detected a fixture edit during
execution and **failed source sealing**; it is not accepted. Final routine,
full native and paired runs were rerun with stable inputs. Compact red/dropped
attempt evidence is explicitly labeled under `attempts/`.

## Changed files, boundaries and cleanup

- `src/simp/src/simpExtLib.sml`: split-only suppression predicate.
- `src/simp/src/simpExtLib.sig`: clarify namespace isolation; no type/API change.
- `tests/simp-ext/{exclusions.sml,Holmakefile,README.md}`: new maintained
  executable regression and coverage/contract map.
- `src/simp/src/Holmakefile`: clean the new launcher; existing `simp-ext` at
  selftest level 1 automatically runs it, outside legacy selftest imports.
- This handoff, compact source-tied evidence and actual progress status.

No ordinary source/signature, generic marker/postkernel service, registry,
public control identity, external consumer, or original fixture changes.
Exhaustive dependent-view invalidation and persistence lifecycle remain their
pre-existing TASK21/TASK23 scope, not newly deferred repairs. No new out-of-scope
repair was discovered. TASK20 is next.

Runners remove their private source/build trees and temporary persistence heap.
Only compact receipts/logs/hashes are retained; no copied tree, binary or heap
is committed. Task-owned scratch evidence and the new launcher/dependency/cache
products are removed after recording. Pre-existing products/caches and unrelated
nested-repository changes are not deleted.
