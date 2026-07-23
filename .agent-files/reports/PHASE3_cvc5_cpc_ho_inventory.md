# Phase 3 cvc5 CPC higher-order corpus and replay inventory

## Baseline

- Recorder: `tools/record_cvc5_cpc_corpus.py` from the HolSmt validation
  repository.
- Solver: cvc5 1.3.4 (`f3b21c4`).
- Proof mode: CPC, `--proof-granularity=dsl-rewrite`.
- Native corpus: 9/9 unsatisfiable queries exported a CPC proof; 155 proof
  steps total.
- Checked matrix: 9/9 queries report `CVC_CPC_TAC_PASS`.
- Frozen evidence and the re-verification manifest:
  `tools/cpc-ho-corpus/cvc5-1.3.4/` and
  `tools/cpc-ho-corpus/inputs.txt` in the validation repository.

The native slice covers `@` application, curried and partially applied
functions, lambda identity/equality, beta, eta/extensionality, and a lambda
below a quantifier.  The D3 Z3-lowered cases remain in the complete
conformance corpus and are checked after the HOL driver translates them
through the cvc5 Standard27 boundary.  The checked selftest band additionally
covers first-class lambda arguments, alpha-equivalent lambda equality, eta,
rank-2 partial application, and the guarded pair-lambda case.

## Frozen rule histogram

| CPC rule | Count | HOL replay |
| --- | ---: | --- |
| `aci_norm` | 1 | existing checked normalization |
| `alpha_equiv` | 2 | `Thm.ALPHA`, extended to HOL abstractions |
| `beta-reduce` | 3 | `TOP_DEPTH_CONV BETA_CONV` |
| `bool-double-not-elim` | 2 | existing propositional rewrite |
| `bool-not-eq-elim1` | 1 | checked propositional equality |
| `chain_m_resolution` | 4 | existing checked resolution; eta-normalizes complementary literals |
| `cong` | 28 | existing context congruence |
| `distinct-elim` | 4 | `ALL_DISTINCT` simplification |
| `distinct-false` | 5 | `ALL_DISTINCT` simplification |
| `eq-ite-lift` | 1 | conditional cases |
| `eq-refl` | 5 | kernel reflexivity |
| `eq-symm` | 6 | existing checked rewrite |
| `eq_resolve` | 14 | existing equality resolution |
| `evaluate` | 6 | kernel evaluation |
| `exists-elim` | 1 | existing quantified rewrite |
| `ho_cong` | 2 | `Thm.MK_COMB` on function and argument equalities |
| `implies_elim` | 2 | existing propositional elimination |
| `instantiate` | 1 | kernel specialization |
| `ite-neg-branch` | 1 | checked consequence of complementary branches |
| `lambda-elim` | 2 | `TOP_DEPTH_CONV ETA_CONV` |
| `nary_cong` | 3 | existing context congruence |
| `process_scope` | 2 | existing checked scope processing |
| `refl` | 13 | kernel reflexivity |
| `skolem_intro` | 3 | existing choice-based replay |
| `skolemize` | 1 | existing choice-based replay |
| `symm` | 1 | kernel symmetry |
| `trans` | 32 | kernel transitivity |
| `true_elim` | 6 | kernel equality elimination |
| `true_intro` | 1 | kernel equality introduction |
| `trust` | 2 | existing handler independently reproves the explicit proposition |

All 30 inventoried names are registered for the measured cvc5 1.3.4
dialect.  There are no residual `proof-rule:*` obligations.  In particular,
the two cvc5-exported `trust` nodes are not accepted as oracles: their
propositions are reconstructed by the existing HOL prover rung, and every
final `thm_CVCp` theorem passes `Library.check_oracle_tags`.

## Parser evidence

Deterministic `Unittest.sml` captures cover:

- inline `(@var "b0" Bool)` binders;
- CPC lambda terms and alpha-renaming;
- CPC `_` partial application in proof output;
- beta, eta/`lambda-elim`, `ho_cong`, the conditional rewrites, and both
  `distinct` rewrites.

The live rank-2 case also records why cvc5 1.3.4 needs a boundary-local logic
policy: it treats lambda binders as quantifiers for logic checking and rejects
them under `HO_QF_*`.  `CVC.sml` widens only such cvc5 HO queries to the
corresponding non-QF `HO_*` logic.  Shared inference remains unchanged.

## Solver-neutrality audit

`git diff -- src/HolSmt/SmtLib*.sml` is empty, so this task introduced no
solver name, cvc5 spelling, or CPC rule into shared SMT-LIB translation.
The cvc5 logic workaround and `@` selection remain in `CVC.sml`; CPC syntax
and rules remain in `CPC_Proof*`.  Existing `Z3LambdaArray` support in shared
code is an explicit dialect abstraction from the earlier Z3 workstream, not
a new dependency of the Standard27 or CPC paths.

## Verification

- All eight sharded `selftest.exe` runs pass with live cvc5 1.3.4 checked
  proofs.
- The frozen CPC gate replays all 9/9 queries.
- Complete SMT-LIB conformance reports 0 unexpected regressions: 41 accepted,
  1,202 expected implementation gaps, and 4,071 matched cases.
- The external benchmark manifest refresh succeeds with network access; its
  initial failure in the full run was limited to sandbox DNS.
- The validation assets are committed as `7d813fc` in the isolated
  `holsmt-validation` task worktree, pending integration into its default
  branch.
