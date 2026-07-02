# HolSmt Complete SMT-LIB Conformance

- Status: `red-obligations`
- Red obligations: 1406
- Unexpected regressions: 0
- Infrastructure errors: 0
- Nonzero exit reasons: red-obligations
- Steps: 29

## Artifacts

- `complete-conformance.json`
- `RED_OBLIGATIONS.md` and `red-obligations.json`
- `conformance/<mode>/conformance-<mode>.json`
- `external/<mode>/external-<mode>.json`
- `proofs/z3-<version>/summary.json` or `proof-version-report.json`
- `minimized-repros/`

## Step Status

| Step | Kind | Status | Exit |
| --- | --- | --- | ---: |
| `build-holsmt-drivers` | `build` | `pass` | 0 |
| `generate-v2-commands` | `generation` | `pass` | 0 |
| `generate-v2-theories` | `generation` | `pass` | 0 |
| `generate-v2-logics` | `generation` | `pass` | 0 |
| `generate-v2-proof-rules` | `generation` | `pass` | 0 |
| `generate-v2-soundness` | `generation` | `pass` | 0 |
| `generate-v2-external` | `generation` | `pass` | 0 |
| `import-external-benchmarks` | `external-import` | `pass` | 0 |
| `validate-v2-manifest` | `validation` | `pass` | 0 |
| `conformance-parser-only` | `conformance` | `pass` | 0 |
| `conformance-typecheck-only` | `conformance` | `pass` | 0 |
| `conformance-z3-oracle` | `conformance` | `pass` | 0 |
| `conformance-proof-parse` | `conformance` | `pass` | 0 |
| `conformance-proof-replay` | `conformance` | `pass` | 0 |
| `conformance-z3-tac` | `conformance` | `pass` | 0 |
| `external-parser-only` | `external-conformance` | `pass` | 0 |
| `external-typecheck-only` | `external-conformance` | `pass` | 0 |
| `external-z3-oracle` | `external-conformance` | `pass` | 0 |
| `external-proof-parse` | `external-conformance` | `pass` | 0 |
| `external-proof-replay` | `external-conformance` | `pass` | 0 |
| `external-z3-tac` | `external-conformance` | `pass` | 0 |
| `proof-z3-2.19.1` | `proof-version` | `skipped` | 0 |
| `proof-z3-4.11.2` | `proof-version` | `pass` | 0 |
| `proof-z3-4.12.4` | `proof-version` | `pass` | 0 |
| `proof-z3-4.13.0` | `proof-version` | `pass` | 0 |
| `proof-z3-4.14.1` | `proof-version` | `pass` | 0 |
| `proof-z3-4.15.3` | `proof-version` | `pass` | 0 |
| `audit-complete-conformance` | `audit` | `fail` | 1 |
| `audit-proof-completeness` | `audit` | `fail` | 1 |
