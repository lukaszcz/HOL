## 1. Task status for each task

- TASK_01: done — acceptance verified; paired harness rerun passed.
- TASK_02: done — acceptance verified; all eleven failures reproduced.
- TASK_03: done — acceptance verified; ten fresh scenarios reproduced.
- TASK_04: done — acceptance verified; focused tests and sanity rerun pass.
- TASK_05: done — acceptance verified; differential/native/sanity reruns pass.
- TASK_06: done — acceptance verified; marker/native/sanity reruns pass.
- TASK_07: done — literal/extended routing, native/paired/sanity checks pass.
- TASK_08: unblocked (not started).
- TASK_09: blocked — needs 08.
- TASK_10: unblocked (not started).
- TASK_11: blocked — needs 10.
- TASK_12: blocked — needs 09, 11.
- TASK_13: blocked — needs 09, 12.
- TASK_14: blocked — needs 13.
- TASK_15: blocked — needs 13.
- TASK_16: blocked — needs 14, 15.
- TASK_17: blocked — needs 16.

## 2. Next unblocked task

`.agent-files/tasks/TASK_08_exclusion_history_replay.md` — preserve
extended split/case exclusion state through history replay.

## 3. Completion log

Requirement: **ONE line per task as each task lands**, with landing ID
and evidence pointer.

- TASK_01 — `2ef0942dd`; evidence: `src/simp/compatibility/BASELINE.md` and `src/simp/compatibility/results/task01/`.
- TASK_02 — `ac0c5a1a5`; evidence: `src/simp/compatibility/LEGACY_FAILURES.md` and `src/simp/compatibility/results/task02/`.
- TASK_03 — `a5ec9cbe9`; evidence: `src/simp/compatibility/FRESH_LOAD.md` and `src/simp/compatibility/results/task03/`.
- TASK_04 — `667320e9b`; evidence: `src/simp/compatibility/TRAVERSAL_PROJECTION.md` and `src/simp/compatibility/results/task04/`.
- TASK_05 — `3a1f4de0d`; evidence: `src/simp/compatibility/TRAVERSAL_LIFETIMES.md` and `src/simp/compatibility/results/task05/`.
- TASK_06 — `d536a8893`; evidence: `src/simp/compatibility/EXTENDED_EXCLUSION_MARKER.md` and `src/simp/compatibility/results/task06/`.
- TASK_07 — `[TASK_07] Separate literal and extended exclusion routes` (commit subject); evidence: `src/simp/compatibility/EXCLUSION_ROUTES.md` and `src/simp/compatibility/results/task07/`.
