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
| Renamed arithmetic declarations | `linarith/instances/selftest.sml` registers fresh names for integer addition and order, derives their laws from the existing theorem kit, and closes an additive inequality the ordinary instance declines. |
| Safe tagged rule transport | `clasimp/selftest.sml` derives a safe introduction rule whose conclusion reaches the goal only after an invocation rewrite changes its normal form. |

The following temporary source ablations were run, then removed:

| Removed mechanism | Designated public failure |
| --- | --- |
| Certified transport of unsafe tagged rules | `certified tagged rule view crosses an invocation normal form` failed in clasimp. |
| Currying a normalized conjunctive premise | `an INJ client rule survives the seed's definition normal form` failed in seeds. |
| Retaining FORCE's first-best session after a turn | `FORCE preserves first-best expansions across small turns` failed in clasimp. |
| Transporting safe tagged rules | `safe tagged introduction retains its role after transport` failed in clasimp when safe transport was disabled. |

The restored rules, classical, clasimp, linarith instances and seeds local
selftests pass.
`bin/build -F -t` passed after the simplifier edit, and the ordered
`upto-auto` gate passed after safe rule transport and the renamed arithmetic
test. A subsequent application charge for installing a derived rule passed
the local clasimp selftest. The full-build result predates these later
auto-only changes.

Tableau currently has a charged, reported restart adapter when a bounded
turn cuts off; it does not retain its mutable search frontier. Invocation
safe rule transport retains its declared role only when its safe class is
unchanged and no new theorem hypothesis is introduced. Persistent tagged
rule transport and a proof on an independent arithmetic carrier remain
for the final generalization audit.
