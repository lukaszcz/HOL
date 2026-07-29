This file provides guidance to coding agents when working with
HolSmt code in this repository.

This directory is **HolSmt**: the HOL4 library integrating SMT solvers (Z3,
cvc5, Yices) with checked proof reconstruction.

## Soundness invariants (non-negotiable)

- **No oracles in checked replay, ever.**  `Z3_TAC`/`CVC_TAC` must return
  `UNSAT (SOME thm)` after full proof replay; `UNSAT NONE` is a failure for
  them.  Oracle results belong only to `Z3_ORACLE_TAC`/`CVC_ORACLE_TAC`.
- **No short-circuit / local-solve.**  `Z3.Z3_SMT_Prover` invokes the external
  solver directly — never a local TAUT/EVAL/ARITH ladder that decides the goal
  before or instead of the solver.  A checked tactic proves theorems; it does
  not produce models or SAT witnesses.
- **Re-prove in HOL, else fail loudly.**  Solver proof steps without a usable
  certificate (th-lemmas) are re-proved by independent HOL decision
  procedures.  Where no HOL procedure can close a step, replay fails with a
  structured unsupported diagnostic — never a silent skip, never an oracle
  fallback.  Prefer fixing the root cause (translation, invocation, prover)
  over any workaround that papers over a failure, and prefer a principled,
  general fix that closes a whole class of cases over a per-term special case.
- Every accepted theorem passes `Library.check_oracle_tags`; an unexpected
  oracle or axiom tag on a checked-tactic output is a test failure.

## Build

```sh
cd src/HolSmt
Holmake <module>.uo    # compile one changed module, e.g. Z3_ProofReplay.uo
Holmake                # full library + smtheap + selftest.exe + drivers
```

Plain `Holmake` works here (no `--holstate` needed).  `Holmake` also builds
the `smtheap` HOL heap and the conformance driver wrappers `holsmt-typecheck`,
`holsmt-z3-tac`, and `holsmt-cvc-cpc-tac` (shell scripts wrapping
`*_driver.sml` via `bin/hol run`).  Style: `tools/h4pedant` from the repo root
(no tabs, no trailing whitespace, < 80 columns).

Solver selection is via `HOL4_Z3_EXECUTABLE`, `HOL4_CVC_EXECUTABLE`,
`HOL4_YICES_EXECUTABLE`, and `HOL4_CSDP_EXECUTABLE` (CSDP is the untrusted
SOS-certificate finder for nonlinear real replay; HOL checks every
certificate it returns).

## Testing — pick the lowest gate that covers the change

Validation assets (corpora, coverage, runner scripts) live in the separate
`holsmt-validation` checkout pointed to by `$HOLSMT_VALIDATION_DIR` (see
`README`).

- **G0** every edit: `Holmake` + `tools/h4pedant`.
- **G1** any runtime-behaviour change (translation, preprocessing, replay):
  `$HOLSMT_VALIDATION_DIR/tools/run_selftest.sh --keep-going` — the sharded
  functional selftest.  **Never run `selftest.exe` directly/unsharded**: a
  single process exceeds 200 GB RSS and gets OOM-killed.  Deterministic
  no-solver regressions go in `Unittest.sml`; solver-backed goals in
  `selftest.sml` (testutils conventions).
- **G2** when the *emitted SMT-LIB* changes:
  `run_conformance_suite.py` with the relevant `--mode` flags.
- **G3** closing a large piece of work: full selftest with both solvers +
  `run_complete_smtlib_conformance.sh` + `bin/build -t
  --seq=tools/sequences/upto-parallel`.
- **G4** merge/release only: `run_holsmt_tests.sh` (the whole local CI
  contract) and `verify_z3_versions.sh` (the multi-version Z3 matrix) —
  never after an ordinary task.

## Architecture

Entry point: `HolSmtLib.GENERIC_SMT_TAC` applies a `goal -> SolverSpec.result`
prover as a tactic.  `SolverSpec.result` is `SAT | UNSAT of thm option |
UNKNOWN`; `SolverSpec` also owns external-process invocation and the fail-fast
solver timeout.  `Z3_TAC` = `GENERIC_SMT_TAC Z3.Z3_SMT_Prover`; `CVC_TAC` =
`GENERIC_SMT_TAC CVC.CVC_SMT_Prover`.

**HOL → SMT-LIB translation (solver-neutral, shared by all solvers):**

- `SmtLib.sml` — translates goals to SMT-LIB 2.7, infers the logic, records
  emitted symbols and HOL theory encodings.  `num` embeds as SMT `Int` via a
  proved preprocessing transfer pass (`0 <= v` relativization of `num`
  variables and binders; no recursive num↔Int bridge axioms).
- Two translation regimes, selected by the goal's features: the first-order,
  arity-keyed encoding for FO logics (HO constructs in FO input are a
  typecheck error), and a native higher-order regime (`->` sorts, `lambda`,
  partial application) for HO logics.  HO emission is dual-dialect: standard
  SMT-LIB 2.7 for cvc5, and a Z3 lowering (`->` → nested `Array`,
  application → `select`).  There is no lambda-lifting bridge between
  regimes.
- Theory models: datatypes via `TypeBase` (HOL→SMT) and genuine `Datatype`
  definitions (SMT→HOL); SMT strings as Unicode code-point sequences with a
  RegLan regex datatype; FloatingPoint on `binary_ieee` with an explicit
  NaN-quotient layer for SMT value semantics; Z3's Seq/Set/Bag extensions
  modelled as `list` / `pred_set` / `bag` (with finiteness and
  non-negativity side conditions at the bridges).
- `SmtLib_Theories.sml` / `SmtLib_Logics.sml` — per-theory and per-logic
  parsing dictionaries, fragment checks, and metadata for all official logics.
- `SmtLib_Parser.sml` — SMT-LIB → HOL parser/typechecker (used by benchmark
  drivers and conformance).  Datatype elaboration to genuine HOL `Datatype`
  definitions is behind `elaborate_datatypes` (default **false** for library
  users; drivers enable it).  `SmtLib_Datatypes.sml` does the elaboration.
  `define-fun-rec` elaborates to a fresh uninterpreted function plus its
  defining equation as a quantified hypothesis (no termination proofs).

**Z3 checked replay:** `Z3.sml` (invoke, parse only `unsat`, check oracle
tags) → `Z3_ProofParser.sml` (untrusted proof text through the version-gated
rule registry) → `Z3_Proof.sml` (proofterm type, `proof_rule_registry`,
`resolve_version`: unknown Z3 versions resolve to the nearest tested anchor
with a warning, never a rejection) → `Z3_ProofReplay.sml` (per-rule handlers
and th-lemma dispatch) + `Z3_ProformaThms.sml`.

**cvc5 checked replay (CPC is the sole checked format,
`--proof-granularity=dsl-rewrite`):** `CVC.sml` (invoke, validate the
reconstructed theorem against the original goal) → `CPC_ProofParser.sml` →
`CPC_Proof.sml` (version-gated CPC rule registry, `resolve_version`) →
`CPC_ProofReplay.sml`.

**Theory re-provers (shared by both replay engines):** arithmetic th-lemmas
go through the `arith_prove` ladder (linear deciders, then the nonlinear SOS
ladder in `Library.nla_prove`, with CSDP probed at runtime); arrays through
`SmtArrayProve`; datatypes through `SmtDatatypeProve` (harvests
distinctness/injectivity/exhaustiveness facts from `TypeBase` at replay
time); bit-vectors through `blastLib` bit-blasting; strings/regex through
the string prover over the code-point theory; FP th-lemmas rewrite through
proved `binary_ieee`↔word-circuit correspondence lemmas and discharge with
the bit-vector machinery — FP steps exceeding the fixed time/term-size
budget fail with a structured resource-gated diagnostic.  `Library.sml`
holds tracing and `check_oracle_tags`; `HolSmtScript.sml` the supporting
theorems.

Adding a Z3 proof rule touches, in order: corpus evidence
(`record_z3_proof_corpus.py`), `Z3_Proof.sml` registry, `Z3_ProofParser.sml`
(only for new premise shapes), `Z3_ProofReplay.sml` handler, `Unittest.sml`
coverage, then the coverage manifest — the full checklist is in `README`.

## Support contract

`README` in this directory is the user-facing support contract (support
matrix, trusted-code-base boundary, Z3/cvc5 version anchors, CI commands) and
**must be kept in agreement** with any change to the supported surface.  The
generated coverage report in the `holsmt-validation` checkout is the source
of truth for per-logic/per-theory status — never claim more support than it
records, and surface every unsupported case as an enumerated diagnostic row,
never a silent skip.

## Instructions

- ALL code should be the SIMPLEST design required to adhere to the SIMPLEST POSSIBLE INTERPRETATION OF THE INTENT, but preserving correctness and efficiency
