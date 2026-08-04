# Phase 2 progress

## Task status

- TASK_01 `hhTptpProblem` AST + printers — done
- TASK_02 `hhTypeEnc` — done
- TASK_03 `hhLamTrans` — done
- TASK_04 `hhMonomorph` — done
- TASK_05 `hhProblemGen` passes 1–5 — done
- TASK_06 `hhProblemGen` passes 6–8 — done
- TASK_07 `hhProblemGen` passes 9–11 — done
- TASK_08 Wiring + `hhTptp` deletion — done
- TASK_09 `hhEval` journal v3 + HO classifier — done
- TASK_10 Slice tables + smoke + soundness — done
- TASK_11 Preflight P — unblocked (needs 10)
- TASK_12 S30-v2-fresh baseline — blocked (needs 11)
- TASK_13 Gate S30-v3 + K + reports — blocked (needs 12)

## Next unblocked task

TASK_10 (`TASK_10_slices_smoke.md`)

## Completion log

- 2026-08-04 TASK_01 — Added the shared TPTP AST/printers, format goldens, and hermetic printer selftests; build and h4pedant pass.
- 2026-08-04 TASK_02 — Added type-encoding grammar/adjustment, infinity oracle, and monotonicity calculus; hermetic selftests, build, and h4pedant pass.
- 2026-08-04 TASK_03 — Added all four lambda-translation modes, parser-safe runtime combinators, grammar-pollution regression coverage, selftests, build, and h4pedant pass.
- 2026-08-04 TASK_04 — Added bounded term-level monomorphization with round/cap/determinism tests; hermetic selftests, build, and h4pedant pass.
- 2026-08-04 TASK_05 — Added hhProblemGen front passes 1–5, compositional IR, proxy tracking, and hermetic unit tests; build and h4pedant pass.
- 2026-08-04 TASK_06 — Added firstorderization, app/pp operators, monotonicity scanning, native/mangled/guard encodings, declarations, and hermetic encoding tests; build and h4pedant pass.
- 2026-08-04 TASK_07 — Completed helper translation through the full pipeline, final-symbol-table naming, eight format/encoding/mode goldens, memoization, and export-linked parse-back coverage; hermetic selftests, build, and h4pedant pass.
- 2026-08-04 TASK_08 — Threaded format triples through prover, slices, schedule, and config; preserved legacy byte identity, added dispatch/re-key tests, deleted `hhTptp`, and passed build and h4pedant.
- 2026-08-04 TASK_09 — Added the HO classifier, v3 journal `ho` field with v1/v2 compatibility, mixed-journal resume, HO subset metrics, and slice-contribution reports; selftests, build, and h4pedant pass.
- 2026-08-04 TASK_10 — Froze the 16-slice schedule and rotation, added
  pinned-prover format/reconstruction smoke and cardinality soundness cases
  for every Phase 2 encoding row, and recorded parser-equivalence
  substitutions: Vampire TF1/poly-native → TH0/mono-native-higher, E
  TF0/mono-native/combs-and-lifting → TX0-/mono-native-fool/
  combs-and-lifting, and Zipperposition FOF/mono-guards?? → legacy FOF.
  Versioned TSTP recordings, hermetic replay/golden tests, full build, and
  h4pedant pass.
