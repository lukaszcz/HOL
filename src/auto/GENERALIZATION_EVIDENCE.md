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
| Resumed tableau turns | `blast/selftest.sml` compares small application slices with one funded fixed-depth run, interleaves another search while a live owned trail is suspended, rejects the first proof to force backtracking, and validates a resumed theorem in an explicit context. |
| Renamed arithmetic declarations | `linarith/instances/selftest.sml` registers fresh names for integer addition and order, derives their laws from the existing theorem kit, and closes an additive inequality the ordinary instance declines. |
| Safe tagged rule transport | `clasimp/selftest.sml` derives a safe introduction rule whose conclusion reaches the goal only after an invocation rewrite changes its normal form. |
| Persistent claset transport | `clasimp/selftest.sml` uses an explicit base-claset destruction rule through `CS_AUTO_TAC` and scoped public `AUTO_TAC`, and a safe introduction rule through `CS_CLARSIMP_TAC`. Each needs a supplied rewrite before the rule view reaches the goal; a polymorphic rule is checked at both `num` and `bool`. |
| Reloaded persistent transport | `clasimp/theory_tests/transportPersistentBaseScript.sml` declares a safe destruction rule; its child theory closes the differently spelled goal with public `AUTO_TAC` and a supplied bridge rewrite. |

The following temporary source ablations were run, then removed:

| Removed mechanism | Designated public failure |
| --- | --- |
| Certified transport of unsafe tagged rules | `certified tagged rule view crosses an invocation normal form` failed in clasimp. |
| Currying a normalized conjunctive premise | `an INJ client rule survives the seed's definition normal form` failed in seeds. |
| Retaining FORCE's first-best session after a turn | `FORCE preserves first-best expansions across small turns` failed in clasimp. |
| Transporting safe tagged rules | `safe tagged introduction retains its role after transport` failed in clasimp when safe transport was disabled. |
| Retaining the tableau continuation | `resumed tableau retains its fixed-depth work and proof` failed when yielded turns restarted the fixed-depth run. |
| Selecting persistent claset rules for transport | `persistent destruction rule crosses a supplied normal form` failed through public `AUTO_TAC` when only invocation markers were selected; the invocation tagged-rule control still passed. |

The restored rules, classical, clasimp, linarith instances and seeds local
selftests pass. The ordered `upto-auto` gate passed after the persistent
rule-view change, including benchmarks and the reloaded-rule theory test.
The `bin/build -F -t` result predates these later auto-only changes.

Tableau now retains its mutable search frontier at bounded turns. A cutoff
during initial translation restarts that preparation, and a cutoff within
one search step can replay charged work inside that step. Invocation safe
rule transport retains its declared role only when its safe class is
unchanged and no new theorem hypothesis is introduced. Persistent claset
rules now use the same certified view checks when a tactic leaves work open;
the direct contextual FORCE path and a proof on an independent arithmetic
carrier remain for the final generalization audit.
