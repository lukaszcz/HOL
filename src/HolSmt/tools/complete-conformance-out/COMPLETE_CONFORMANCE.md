# HolSmt Complete SMT-LIB Conformance

- Status: `red-obligations`
- Red obligations: 1381
- Unexpected regressions: 32
- Infrastructure errors: 0
- Nonzero exit reasons: red-obligations, unexpected-regressions
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
| `conformance-z3-tac` | `conformance` | `fail` | 1 |
| `external-parser-only` | `external-conformance` | `pass` | 0 |
| `external-typecheck-only` | `external-conformance` | `fail` | 1 |
| `external-z3-oracle` | `external-conformance` | `pass` | 0 |
| `external-proof-parse` | `external-conformance` | `pass` | 0 |
| `external-proof-replay` | `external-conformance` | `pass` | 0 |
| `external-z3-tac` | `external-conformance` | `fail` | 1 |
| `proof-z3-2.19.1` | `proof-version` | `skipped` | 0 |
| `proof-z3-4.11.2` | `proof-version` | `pass` | 0 |
| `proof-z3-4.12.4` | `proof-version` | `pass` | 0 |
| `proof-z3-4.13.0` | `proof-version` | `pass` | 0 |
| `proof-z3-4.14.1` | `proof-version` | `pass` | 0 |
| `proof-z3-4.15.3` | `proof-version` | `pass` | 0 |
| `audit-complete-conformance` | `audit` | `fail` | 1 |
| `audit-proof-completeness` | `audit` | `fail` | 1 |

## Unexpected Regressions

| Report | Case | Mode | Detail |
| --- | --- | --- | --- |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Core:distinct:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:abs:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:div:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:divisible:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:ge:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:gt:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:int:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:le:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:lt:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:mod:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:neg:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:plus:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:pow:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:sub:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Ints:times:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:decimal:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:div:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:ge:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:gt:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:le:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:lt:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:neg:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:plus:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:real:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:sub:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals:times:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals_Ints:is-int:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals_Ints:to-int:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/conformance/z3-tac/conformance-z3-tac.json` | `theory:Reals_Ints:to-real:sat` | `z3-tac` | z3-tac command timed out after 30s |
| `src/HolSmt/tools/complete-conformance-out/external/typecheck-only/external-typecheck-only.json` | `strings-qf_s_concat` | `typecheck-only` | typecheck-only command succeeded |
| `src/HolSmt/tools/complete-conformance-out/external/z3-tac/external-z3-tac.json` | `arrays-qf_auflia_select_store` | `z3-tac` | checked Z3_TAC theorem proved |
| `src/HolSmt/tools/complete-conformance-out/external/z3-tac/external-z3-tac.json` | `strings-qf_s_concat` | `z3-tac` | checked Z3_TAC solver result sat |
