# HolSmt Coverage Manifest Audit

The manifest in `coverage_manifest.json` is the evidence checklist for rows in
`smtlib_coverage.json`. It is intentionally small at first; later coverage
tasks should add rows as executable evidence is created.

Run the report-only audit with:

```sh
python3 src/HolSmt/tools/coverage/audit_coverage_manifest.py
```

The default mode validates the manifest, checks evidence that is available in
the checkout, and prints missing row-level obligations without failing CI. Use
`--enforce` only after a later task deliberately turns missing obligations into
a gate.

Add one manifest entry per coverage row, using the exact `section`, `item`, and
`class` values from `smtlib_coverage.json`. Put the covered status columns in
`phases`, and set `expected_status` to the status those phases must have. Use:

- `positive_tests` for implemented behavior that should pass.
- `negative_tests` for unsupported behavior that must produce an exact
  diagnostic.
- `z3_versions` for proof-corpus rows that must be supported by specific Z3
  versions.
- `artifacts` for source files, checked-in reports, parse-only justifications,
  or not-applicable explanations.

The audit understands `source`, `conformance_result`, `proof_rule`,
`proof_version`, and `manual` evidence kinds. Source evidence checks that the
path exists and, when `match` is present, that the text appears in the file.
Conformance and proof evidence is checked only when report paths are supplied
with `--conformance-report` or `--proof-report`.
