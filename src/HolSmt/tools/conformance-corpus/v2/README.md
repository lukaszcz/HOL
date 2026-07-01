# HolSmt Conformance Corpus v2

This directory is the SMT-LIB complete conformance corpus skeleton for
HolSmt.  It is intentionally separate from `v1`: v2 is the strict,
initially-red corpus used by later generators, auditors, runners, and Z3
version checks.

`manifest.json` is the stable metadata entry point and must validate against
`manifest.schema.json`.  The seed manifest is valid with an empty `cases`
array so that later tasks can add generated command, theory, logic, proof-rule,
soundness, and external benchmark cases incrementally.

Each case entry has these required fields:

- `id`: stable evidence ID used by reports, auditors, and red summaries.
- `file`: SMT-LIB script path relative to this directory.
- `logic`: expected `set-logic` name, or the explicit logic context for
  command/proof cases.
- `standard`: one of `SMT-LIB-2.7`, `SMT-LIB-3`, or `Z3-extension`.
- `class`: one of `command`, `theory`, `logic`, `proof-rule`,
  `soundness-audit`, or `external-benchmark`.
- `features`: exact command, operator, theory, logic, proof-rule, or audit
  feature IDs covered by the case.
- `modes`: required execution modes, such as `parser-only`, `typecheck-only`,
  `z3-oracle`, `proof-parse`, `proof-replay`, and `z3-tac`.
- `versions`: required Z3 versions for the case.
- `expected`: per-mode expected results.  Each result status is exactly
  `pass`, `fail`, or `red`; negative and red rows may also carry diagnostic
  substrings, theorem-shape predicates, and proof-rule histogram constraints.
- `implementation_obligation`: `null` for non-red rows; non-null for red rows,
  naming likely implementation files, the missing feature, failing test IDs,
  and the failure phase.
- `source`: the official SMT-LIB reference, Z3 extension/proof source,
  external benchmark source, or HolSmt-internal source for the case.

Strict mode treats `red` as a failing expected result.  A `red` row is an
implementation obligation, not a completed coverage claim.  Similarly,
`unsupported`, `parse_only`, and `not_applicable` are current-state labels only:
they must not be counted as complete conformance.

Generated and imported SMT-LIB scripts are organized under:

- `cases/commands/` for command parser, state, solver, and replay behavior.
- `cases/theories/` for official SMT-LIB theory and Z3 extension operators.
- `cases/logics/` for per-logic SAT, UNSAT proof, malformed, type-error,
  fragment, and boundary packets.
- `cases/proof_rules/` for Z3 proof-rule trigger cases.
- `cases/soundness/` for theorem-shape, oracle-tag, axiom, assumption, and
  semantic soundness audits.
- `cases/external/` for pinned reduced external benchmarks.

`generate_complete_corpus.py` is the shared generator framework for the v2
corpus.  With no subcommand it performs a deterministic dry run and prints a
sample manifest containing one red seed row for each class:

```sh
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py
```

Focused dry-run subcommands are available for the planned domains:

```sh
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py commands
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py theories
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py logics
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py proof-rules
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py soundness
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py external
```

Use `--write` with `samples` or a focused subcommand to update
`manifest.json` and write the generated SMT-LIB scripts.  The write path is
idempotent: generated case IDs are replaced deterministically and unrelated
manifest entries are preserved.

```sh
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py samples --write
```

Use audit-only mode in CI when the checked-in manifest should be validated
without writing files:

```sh
python3 src/HolSmt/tools/conformance-corpus/v2/generate_complete_corpus.py audit
```

The generator centralizes the supported Z3 versions:

- `2.19.1`
- `4.11.2`
- `4.12.4`
- `4.13.0`
- `4.14.1`
- `4.15.3`

Validate the seed manifest with the locally available JSON schema validator:

```sh
python3 -m jsonschema \
  src/HolSmt/tools/conformance-corpus/v2/manifest.schema.json \
  -i src/HolSmt/tools/conformance-corpus/v2/manifest.json
```

If the `jsonschema` module is unavailable in another environment, install it
for the active Python environment or run an equivalent Draft 2020-12 JSON
Schema validator against the same schema and manifest files.

Run the complete conformance foundation auditor with:

```sh
python3 src/HolSmt/tools/audit_complete_conformance.py \
  --json-output complete-conformance-audit.json
```

The auditor validates this v2 manifest, extracts accepted logic names from
`src/HolSmt/SmtLib_Logics.sml`, reads the current coverage rows when present,
and reports missing complete evidence as failures.  Exit code `1` means the
corpus is still red or incomplete; exit code `2` means an infrastructure error
such as malformed JSON or invalid manifest structure.

The complete conformance runner is also part of the mandatory local HolSmt
test path:

```sh
src/HolSmt/tools/run_holsmt_tests.sh
```

That integrated path writes the complete suite report directory under
`.holsmt-ci/complete-conformance` by default.  Use
`src/HolSmt/tools/run_holsmt_tests.sh --out-dir DIR` to put both the existing
HolSmt conformance reports and the complete suite reports under another
directory.  The complete suite intentionally exits nonzero while red
implementation obligations remain; inspect these files first:

- `DIR/complete-conformance/complete-conformance.json`
- `DIR/complete-conformance/COMPLETE_CONFORMANCE.md`
- `DIR/complete-conformance/red-obligations.json`
- `DIR/complete-conformance/RED_OBLIGATIONS.md`

The main runner does not provide a bypass for complete conformance.  Existing
HolSmt test failures and complete-suite red obligations are collected in the
same invocation, then the script exits nonzero if any mandatory step failed.
