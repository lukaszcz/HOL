# TASK29A fail attribution (diagnostic, not a grid decision)

Predeclared runs on the four cells that failed the equivalence-policy grid
(`../grid-partial`). The plan was written before each run: `PLAN.md` (R1–R3
first, R4 appended before R4 started). Every run is `task29a_grid.py run
--only ...` with 20 pairs, 5 samples and policy version 2. Logs are in
`run.log`. Ratios are candidate/develop CPU per operation.

| Run | Candidate | Layout | Counts | create/10000 | named/10000 | named_rules/1 | named_rules/10 |
|---|---|---|---|---|---|---|---|
| R1 | 6f62229c0 | fixed | predeclared | fail 1.086–1.122 | fail 1.089–1.118 | fail 1.052–1.067 | fail 1.063–1.082 |
| R2 | probe 8d4a84417 | fixed | predeclared | fail 1.174–1.202 | fail 1.230–1.260 | pass 0.997–1.009 | pass 1.006–1.022 |
| R3 | 6f62229c0 | fixed | half | — | — | protocol failure | fail 1.051–1.076 |
| R4 | 6f62229c0 | seed `task29a-r4` | predeclared | inconclusive 0.956–1.052 | inconclusive 0.952–1.069 | pass 1.004–1.016 | pass 0.985–1.015 |

R4 also ran `frag_record/0`, which passed in the pilot, as a sanity cell. It
passes again at 0.993–1.013. Under randomized layout the B/B controls of the
two size-10000 cells are 0.977–1.060 and 0.965–1.071, outside the window, so
those cells cannot be decided at 20 pairs.

- **Probe** (`8d4a84417`, local branch `task29a/probe-develop-tracking`).
  `Cond_rewr.sml` is develop's byte for byte, and the candidate's ordinary
  loaded sources equal develop's except `Cond_rewr.sig`. Two cells start
  passing and two fail by a larger margin. The executed ordinary path is
  identical in the two size-10000 cells (production `simpLib` is
  byte-identical, and the fragment constructors never call `Cond_rewr`).
  User time per operation still differs by 36% there, while system time
  and GC are equal.
- **Code-area size.** `sizeCode` at batch start tracks speed. In R1/R2
  every develop process but one has 1032192 bytes. The odd one is
  1036288, and that develop process is also an outlier, fast in one
  experiment and slow in the other. Candidates have 1040384 (R1) and
  1036288 (R2).
- **Counts.** R3 used the historical half counts (`iterations-half.json`).
  `frag_named_rules/10` still fails, so count does not explain the fail.
  `frag_named_rules/1` stopped with "fixed calibration too short", the
  protocol's refusal at that count. R3 is outside the predeclared counts and
  `replay` rejects it by design ("changed predeclared counts").
- **Randomization.** In R4 the per-process spread is about 8% in the
  size-10000 cells and 1–2% in the others. Develop processes given the same
  padding count in the control and candidate experiments mostly run within
  1–2% of each other: layout, not the host, sets most of a process's speed.

Conclusion: the four fixed-layout fails are code-layout artefacts, not an
ordinary-path cost of the candidate. Under randomized layout, two of them
pass and two need more pairs. This motivated the layout seed and the
predeclared second stage (`PROTOCOL.md`). `task29a_grid.py replay --partial
--output R1` (also R2 and R4) recomputes every cell.
