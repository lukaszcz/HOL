## 1. Task status for each task

- TASK_01: done — acceptance verified; paired harness rerun passed.
- TASK_02: done — acceptance verified; all eleven failures reproduced.
- TASK_03: done — acceptance verified; ten fresh scenarios reproduced.
- TASK_04: done — public legacy projection restored; focused/sanity green.
- TASK_05: unblocked (not started).
- TASK_06: unblocked (not started).
- TASK_07: blocked — needs 05, 06.
- TASK_08: blocked — needs 07.
- TASK_09: blocked — needs 08.
- TASK_10: unblocked (not started).
- TASK_11: blocked — needs 10.
- TASK_12: blocked — needs 09, 11.
- TASK_13: blocked — needs 05, 09, 12.
- TASK_14: blocked — needs 13.
- TASK_15: blocked — needs 13.
- TASK_16: blocked — needs 14, 15.
- TASK_17: blocked — needs 16.

## 2. Next unblocked task

`.agent-files/tasks/TASK_05_traversal_lifetime_contracts.md` — validate
projection staging, lifetimes, and shared controls.

## 3. Completion log

Requirement: **ONE line per task as each task lands**, with landing ID
and evidence pointer.

- TASK_01 — `2ef0942dd`; evidence: `src/simp/compatibility/BASELINE.md` and `src/simp/compatibility/results/task01/`.
- TASK_02 — `ac0c5a1a5`; evidence: `src/simp/compatibility/LEGACY_FAILURES.md` and `src/simp/compatibility/results/task02/`.
- TASK_03 — `a5ec9cbe9`; evidence: `src/simp/compatibility/FRESH_LOAD.md` and `src/simp/compatibility/results/task03/`.
- TASK_04 — `[TASK_04] Restore the public legacy traversal projection` (commit subject); evidence: `src/simp/compatibility/TRAVERSAL_PROJECTION.md` and `src/simp/compatibility/results/task04/`.
