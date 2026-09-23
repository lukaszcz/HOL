# Automation generalization evidence

The local selftests exercise the public tactic paths as well as the
underlying engine cursors. This table names representative independent
checks; it is not a solved-goal score.

| Scenario | Regression observation |
| --- | --- |
| Bound-name and carrier changes | `rules/selftest.sml` checks a rename/carrier matrix, fixed support, and two schematic citations. |
| Redundant forward candidates | `aesop/selftest.sml` puts a useful consequence after more than 200 redundant candidates, then compares small resumed scans with one funded run. |
| New applications and contexts | `classical/selftest.sml` checks membership/application crossings, interleaved explicit contexts, and interrupted replay. |
| Normalization bridges | `clasimp/selftest.sml` uses independently defined predicates for a tagged rule whose premise changes normal form, and reports a typed limit for cyclic rewrites. |
| Head preservation and seeds | `seeds/selftest.sml` uses eta-expanded interval terms and an independently defined `INJ` client predicate; a separate client datatype and relation exercise temporary declarations. |
| Bounded FORCE turns | `clasimp/selftest.sml` compares the admitted first-best expansions under one-unit and large slices on the same partial-map proof. `classical/selftest.sml` resumes depth search and pending kernel replay under one budget. |

The following temporary source ablations were run, then removed:

| Removed mechanism | Designated public failure |
| --- | --- |
| Certified transport of unsafe tagged rules | `certified tagged rule view crosses an invocation normal form` failed in clasimp. |
| Currying a normalized conjunctive premise | `an INJ client rule survives the seed's definition normal form` failed in seeds. |
| Retaining FORCE's first-best session after a turn | `FORCE preserves first-best expansions across small turns` failed in clasimp. |

The restored rules, classical, clasimp and seeds local selftests pass.
`bin/build -F -t` passed after the simplifier edit, and the ordered
`upto-auto` gate passed after depth sessions and budgeted fact views were
added. The final full-build result predates those later auto-only changes.

Tableau currently has a charged, reported restart adapter when a bounded
turn cuts off; it does not retain its mutable search frontier. Persistent
and safe tagged rule transport, and a theorem-kit proof on an independent
arithmetic carrier, remain for the final generalization audit.
