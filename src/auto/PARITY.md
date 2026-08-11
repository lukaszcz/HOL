# Isabelle-method parity

Generated deterministically from the Phase-8 benchmark modules. The pinned Isabelle mirror is `f7e02b7e`; the per-goal budget is 30 seconds and the measurement date is 2026-08-11.

This report covers the exhaustive 874-goal executable corpus. The pinned source contributes 1,061 accounted outcomes after nine documented HOL4 `aconv` collapses; eleven additional goals come from HOL4's integer regression suite. Translation gaps remain explicit shortfalls.

The shortfall column is `accepted/engine/translation/under-iteration`. Battery columns are recorded observations and do not gate the build.

| Family | Goals | Gated solved | L1 slice | Shortfalls | AUTO | BLAST | AESOP |
|---|---:|---:|---:|---:|---:|---:|---:|
| Classical | 25 | 25 | 4 | 0/0/0/0 | 15 | 0 | 6 |
| Sets | 349 | 226 | 4 | 0/123/4/0 | 0 | 99 | 249 |
| List/map | 413 | 154 | 5 | 0/259/191/0 | 123 | 0 | 90 |
| Linarith | 46 | 46 | 4 | 0/0/0/0 | 29 | 0 | 22 |
| Presburger | 34 | 33 | 8 | 0/1/0/0 | 10 | 0 | 8 |
| Algebra | 7 | 6 | 3 | 1/0/3/0 | 1 | 0 | 1 |

The seed inversion audit currently requires no waivers. Corpus provenance is carried by each benchmark entry and points to the pinned files under `src/HOL/`.
