# HolSmt Complete SMT-LIB Conformance

- Status: `unexpected-regression`
- Red obligations: 1341
- Unexpected regressions: 908
- Infrastructure errors: 0
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
| `conformance-parser-only` | `conformance` | `fail` | 1 |
| `conformance-typecheck-only` | `conformance` | `fail` | 1 |
| `conformance-z3-oracle` | `conformance` | `fail` | 1 |
| `conformance-proof-parse` | `conformance` | `pass` | 0 |
| `conformance-proof-replay` | `conformance` | `pass` | 0 |
| `conformance-z3-tac` | `conformance` | `fail` | 1 |
| `external-parser-only` | `external-conformance` | `pass` | 0 |
| `external-typecheck-only` | `external-conformance` | `fail` | 1 |
| `external-z3-oracle` | `external-conformance` | `pass` | 0 |
| `external-proof-parse` | `external-conformance` | `fail` | 1 |
| `external-proof-replay` | `external-conformance` | `fail` | 1 |
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
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:check-sat:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:define-fun-rec-define-funs-rec:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:echo:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:exit:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:get-info-get-option:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:get-model-get-value-get-assignment-get-assertions:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:reset-reset-assertions:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `command:set-info:negative` | `parser-only` | SMT-LIB S-expression parse succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:ALIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:ALIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:ANIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:ANIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:AUFLIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:AUFLIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:AUFNIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:BV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:LIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:LRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:NIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:NRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_ABV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_ALIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_ALRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_ANIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_ANRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_AUFBV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_AUFLIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_AUFLIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_AUFNIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_AUFNIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_AX:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_BV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_BVFP:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_FP:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_FPBV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_IDL:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_LIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_LIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_LRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_NIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_NIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_NRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_RDL:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_S:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_SLIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_SNIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UF:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFBV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFBVFP:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFFP:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFIDL:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFLIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFLIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFLRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFNIRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:QF_UFNRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UF:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UFBV:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UFIDL:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UFLIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UFLRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UFNIA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/parser-only/conformance-parser-only.json` | `logic:UFNRA:malformed` | `parser-only` | missing ')' |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:assert:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:check-sat-assuming:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-const` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-const:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-datatype-declare-datatypes:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-datatype-declare-datatypes:state` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-fun:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-fun:state` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-sort:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:define-const:negative` | `typecheck-only` | typecheck-only command succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:define-fun-rec-define-funs-rec` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:define-fun-rec-define-funs-rec:state` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:define-fun:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:define-sort` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:define-sort:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:push-pop:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:reset-reset-assertions` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:set-logic:negative` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:set-option:negative` | `typecheck-only` | typecheck-only command succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:ALIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:ALIRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:ANIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:ANIRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:AUFLIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:AUFLIRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:AUFNIRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:BV:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:LIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:LRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:NIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:NRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:QF_ABV:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:QF_ALIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:QF_ALRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:QF_ANIA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:QF_ANRA:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `logic:QF_AUFBV:type-error` | `typecheck-only` | typecheck-only command failed |
