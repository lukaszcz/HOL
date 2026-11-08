# Standalone API/runtime audit

This fixture owns no production code. It uses `testutils` with fail-fast
executable launchers, not SML piped into `hol`.

From the repository root (no routine/full build is requested):

```sh
bin/Holmake -C src/simp/tests/api-audit check
```

Receipts are written outside the repository, below `API_AUDIT_OUTPUT`, which
must be an **absolute** path (`run.py` refuses one inside the repository).
Without it (or if it is empty) `check` writes the receipts to a temporary
directory and removes it when the audit finishes, pass or fail; set
`API_AUDIT_OUTPUT` to keep them. Run `python3 run.py --output DIR` directly to
choose the directory (without `--output`, `run.py` makes a directory with
`mkdtemp` and prints its path). If the
checkout is mounted at a different root than the one the build was
configured with, run the command through
`src/simp/tests/compatibility/tools/root-wrapper.sh`.

`check` compiles `Documentation.sml` against the real sealed signatures but
**does not link it into the launcher**. `run.py` starts eight fresh processes:
`simpLib` then `congLib`, or the reverse, each with a foreign split attribute
or exporter owner installed before or after the ordinary imports. Exporters
install their own attribute dispatcher, so the two foreign owners are tested
in separate processes, not registered over each other.

## Executed contracts

- Entry, each ordinary import and ordinary recipes check loaded modules,
  global structure bindings, actual used files and the loader's file map.
  Extension modules, private splitter/marker modules, `combinSimpsExt` and
  `trackedSimpDefaults` are forbidden. Actual requested, used and loaded
  paths are printed separately; this is not a dependency-name-only scan.
- Attribute/exporter record pointers, foreign theorem data and callback
  behavior survive ordinary and explicit extension imports. Imports/proofs
  invoke no foreign attribute/exporter initialization callbacks. Existing
  Theory listener function pointers/order are retained; ordinary additions
  must be the exact legacy list. Extension imports/use add no listeners and
  never initialize split persistence or import the tracked default provider.
- Original `Cond_rewr.stack_limit`, `Trace.trace_level` and `Trace.trace_hook`
  are captured before extension import. Saved ordinary and extension
  conversions see live shared depth changes; explicit extension depths are
  local. Proofs compare complete conclusions and hypotheses.
- Feedback's `simplifier` trace knob and the original trace ref work in both
  directions. One original Trace listener observes actual rewrites by both
  engines. Nested tracking in both directions, exceptional restoration and
  empty-scope cleanup use real kernel rewrite proofs.
- Two **single-sided** names test independent fragment registries. Opposite
  lookup is absent and opposite SF tactic consumption must raise the specific
  missing-fragment error. Own-registry tactics work; failures do not populate
  the other registry. Context is restored afterwards.
- `Documentation.sml` gives typed tracked construction, both traversal
  projections, explicit one-way ordinary reducer/public congruence-fragment
  lifts, prepared bundles and source views. Its executable examples prove
  the lifts work and that bundle/view aliases share remaining/exhausted
  actual controls. No opaque simpset or congset promotion is offered.

Each invocation writes a unique `<UTC>-<nonce>/` receipt directory with source
hashes, exact executable commands/environment, compressed complete logs,
observed paths and hashes of existing observed files. Failed invocations
remain failures. These bounded checks are not a routine/full build,
performance comparison, saved-heap/persistence audit or cross-platform claim.
