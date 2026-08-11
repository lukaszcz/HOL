# Automation benchmark results

## What this report measures

Each benchmark entry contains a HOL4 theorem statement, the Isabelle method used for the corresponding source result, and the HOL4 tactic chosen as that method's closest counterpart. This report calls that HOL4 tactic the **assigned tactic**.

The comparison data was mined from Isabelle/HOL commit `f7e02b7e`. Each in-repository benchmark entry records its source file, line, method, and commit. The report was generated on 2026-08-11 with a 30-second limit for each tactic attempt.

## Source accounting

Source mining identified 1,070 relevant Isabelle results. Nine pairs translated to the same HOL4 statement except for bound variable names, so they are tested once. This leaves 1,061 distinct source-derived results. Eleven existing HOL4 integer regression goals are also included, giving 1,072 accounted results in total:

- 874 are executable HOL4 benchmark goals.
- 198 could not be translated faithfully and are listed by identifier and reason in the benchmark files.
- 0 source results are missing from both groups.

The selftest checks this accounting in both directions. An unexpected failure is an error, but so is an expected failure that starts succeeding without its record being updated.

## Results from the assigned tactics

**Executable goals** is the number of runnable HOL4 statements. **Solved by assigned tactic** counts statements proved by the HOL4 counterpart selected for their Isabelle method. **Routine selftest goals** is a fixed, explicitly marked subset run when `HOLSELFTESTLEVEL=1`; it is not a random sample. At level 2 or higher, all executable goals run.

A **family** is a subject-area group:

- **Classical** contains propositional and first-order logic.
- **Sets** contains set and relation reasoning.
- **List/map** contains lists, finite maps, options, strings, and product types.
- **Linarith** contains linear arithmetic over natural numbers, integers, real numbers, and rational numbers.
- **Presburger** contains quantified additive arithmetic over natural numbers and integers.
- **Algebra** contains polynomial, ring, and field identities.

| Family | Executable goals | Solved by assigned tactic | Routine selftest goals |
|---|---:|---:|---:|
| Classical | 25 | 25 | 4 |
| Sets | 349 | 226 | 4 |
| List/map | 413 | 154 | 5 |
| Linarith | 46 | 46 | 4 |
| Presburger | 34 | 33 | 8 |
| Algebra | 7 | 6 | 3 |
| **Total** | **874** | **490** | **28** |

## Documented results not solved by the assigned tactic

- **Accepted scope exclusions** are executable goals deliberately outside the supported tactic scope, with a recorded reason.
- **Assigned-tactic limitations** are executable goals for which the assigned tactic failed or exceeded 30 seconds.
- **Unavailable translations** are source results that could not be represented faithfully as HOL4 goals. They are not included in the executable-goal count.
- **Unaccounted source results** would be source results that are neither executable nor documented as unavailable. This number must remain zero.

| Family | Accepted scope exclusions | Assigned-tactic limitations | Unavailable translations | Unaccounted source results |
|---|---:|---:|---:|---:|
| Classical | 0 | 0 | 0 | 0 |
| Sets | 0 | 123 | 4 | 0 |
| List/map | 0 | 259 | 191 | 0 |
| Linarith | 0 | 0 | 0 | 0 |
| Presburger | 0 | 1 | 0 | 0 |
| Algebra | 1 | 0 | 3 | 0 |
| **Total** | **1** | **383** | **198** | **0** |

For every family, executable goals equal assigned-tactic solutions plus accepted scope exclusions plus assigned-tactic limitations.

## Additional tactic observations

For context, the exhaustive run also tries three general-purpose HOL4 tactics when they are not already the assigned tactic. The numbers below count these additional solutions. They do not affect whether the benchmark selftest passes and are not total strength scores for the tactics.

| Family | Additional `AUTO_TAC` solutions | Additional `BLAST_TAC` solutions | Additional `AESOP_TAC` solutions |
|---|---:|---:|---:|
| Classical | 15 | 0 | 6 |
| Sets | 0 | 99 | 249 |
| List/map | 123 | 0 | 90 |
| Linarith | 29 | 0 | 22 |
| Presburger | 10 | 0 | 8 |
| Algebra | 1 | 0 | 1 |
| **Total** | **178** | **99** | **376** |

## Seed-rule safety check

A rule is classified as **safe** when applying it cannot discard a possible proof of the goal. The automated seed-rule check proves the required reverse direction for every such rule. It currently passes with no exceptions.

## Reproducing the report

From `src/auto/benchmarks/`:

```sh
Holmake
./selftest.exe
HOLSELFTESTLEVEL=2 ./selftest.exe
./genparity.exe
```

The first selftest command runs the fixed routine subset. The second runs every executable goal and the additional tactic observations. The final command regenerates `../PARITY.md`.
