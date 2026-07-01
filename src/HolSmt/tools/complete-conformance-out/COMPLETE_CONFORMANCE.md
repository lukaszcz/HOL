# HolSmt Complete SMT-LIB Conformance

- Status: `unexpected-regression`
- Red obligations: 1338
- Unexpected regressions: 776
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
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `command:declare-fun:state` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:array:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:extensionality:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:mixed-index-value-sorts:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:read-over-write:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:select:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:store:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:ArraysEx:write-over-write:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:and:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:bool:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:distinct:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:eq:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:false:type-error` | `typecheck-only` | typecheck-only command succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:implies:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:ite:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:not:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:or:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:true:type-error` | `typecheck-only` | typecheck-only command succeeded |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Core:xor:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:binary-hex-literal:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bitvec:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvadd:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvand:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvashr:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvcomp:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvlshr:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvmul:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvnand:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvneg:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvnego:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvnor:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvnot:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvor:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvsaddo:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvsdiv:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvsdivo:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvsge:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvsgt:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvshl:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvsle:type-error` | `typecheck-only` | typecheck-only command failed |
| `src/HolSmt/tools/complete-conformance-out/conformance/typecheck-only/conformance-typecheck-only.json` | `theory:Fixed_Size_BitVectors:bvslt:type-error` | `typecheck-only` | typecheck-only command failed |
