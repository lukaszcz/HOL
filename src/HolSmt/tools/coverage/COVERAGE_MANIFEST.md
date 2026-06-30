# HolSmt Coverage Manifest Audit

The manifest in `coverage_manifest.json` is the evidence checklist for rows in
`smtlib_coverage.json`. It is intentionally small at first; later coverage
tasks should add rows as executable evidence is created.

Run the enforcing audit with:

```sh
python3 src/HolSmt/tools/coverage/audit_coverage_manifest.py --enforce
```

The default mode still validates the manifest and prints missing row-level
obligations without failing, but CI always uses `--enforce`. Enforcing mode
rejects unresolved `unknown` or `untested` rows, implemented rows without
positive executable evidence, unsupported-diagnostic rows without negative
diagnostic evidence, and stale or missing proof-version evidence. The
checked-in supported-version proof summary is loaded as a default
`--proof-report`; pass additional `--proof-report` paths when auditing freshly
recorded Z3 proof-corpus runs.

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
with `--conformance-report` or `--proof-report`. The `holsmt-contract` CI
workflow uploads conformance summaries from the parser, Z3 oracle/proof,
typecheck-only, and checked `Z3_TAC` slices, then runs a final enforced manifest
audit against those summaries.
