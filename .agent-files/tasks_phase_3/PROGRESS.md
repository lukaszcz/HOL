# Phase 3 progress (HolSmt higher-order redesign)

Keep this file concise: exactly the three sections below.  When a
task lands, update its status line, recompute "Next unblocked
task", and append ONE line to the completion log — one line per
task, no more.

## 1. Task status

- TASK_01 (golden FO byte-identity test) — unblocked (not started)
- TASK_02 (C1 HO proof corpus) — complete
- TASK_03 (D3 red-first corpus) — unblocked (not started)
- TASK_04 (D4 coverage rows) — blocked (03)
- TASK_05 (A1 lambda terms) — unblocked (not started)
- TASK_06 (A2 apply operators) — blocked (05)
- TASK_07 (A3 partial application) — blocked (06)
- TASK_08 (A4+A5 fragment + hygiene) — blocked (07)
- TASK_09 (D1 HO_ logic packets) — blocked (08)
- TASK_10 (B1 regime + trigger) — blocked (01)
- TASK_11 (B2+B4 HO core + Z3 lowering) — blocked (10)
- TASK_12 (B3+B5 Standard27 + features) — blocked (09, 11)
- TASK_13 (B6+B7 dicts + docs) — blocked (11, 12)
- TASK_14 (C2 proof-parser lambdas) — unblocked (not started)
- TASK_15 (C3 replay capability) — blocked (14)
- TASK_16 (C4 wiring + flips) — blocked (12, 13, 15)
- TASK_17 (D2 suite band + cvc5-oracle) — blocked (03, 08, 09)
- TASK_18 (D5 external benchmarks) — blocked (17)
- TASK_19 (E cvc5 CPC HO replay) — blocked (12, 16, 17)
- TASK_20 (phase closure) — blocked (all)

## 2. Next unblocked task

TASK_01 — it gates all encoder (B) work.  (TASK_03, TASK_05, and TASK_14
are also unblocked and parallelizable.)

## 3. Completion log

(one line per task as it lands)
- 2026-07-18 — TASK_02: recorded the six-case HO proof-shape corpus across five Z3 versions and pinned the case-specific boundaries.
