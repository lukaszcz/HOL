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
| Child-first migration | `clasimp/selftest.sml` runs the same subject rewrite with plain `[iff]` and `[iff_bottom_up]` declarations under the opt-in policy; both close after the child rewrite. The ordinary simplifier test still distinguishes their priorities. |
| Head preservation and seeds | `seeds/selftest.sml` uses eta-expanded interval terms and an independently defined `INJ` client predicate; a separate client datatype and relation exercise temporary declarations. |
| Bounded FORCE turns | `clasimp/selftest.sml` compares the admitted first-best expansions under one-unit and large slices on the same partial-map proof. `classical/selftest.sml` resumes depth search and pending kernel replay under one budget. |
| FORCE scheduling | `clasimp/selftest.sml` drives the production round-robin loop with scripted yielding, proving and exhausting engines; each engine is the sole finisher in one case, and a shared three-application limit reaches all three before propagation. |
| Resumed tableau turns | `blast/selftest.sml` compares small application slices with one funded fixed-depth run, interleaves another search while a live owned trail is suspended, rejects the first proof to force backtracking, and validates a resumed theorem in an explicit context. |
| Renamed arithmetic declarations | `linarith/instances/selftest.sml` registers fresh names for integer addition and order, derives their laws from the existing theorem kit, and closes an additive inequality the ordinary instance declines. |
| Independent arithmetic carrier | `linarith/instances/selftest.sml` defines a fresh `client_integer` datatype, proves its addition and order kit from integer laws, and closes an additive inequality only after registering that instance. Its AC fallback also checks certified cancellation replay. |
| Safe tagged rule transport | `clasimp/selftest.sml` derives a safe introduction rule whose conclusion reaches the goal only after an invocation rewrite changes its normal form. |
| Persistent claset transport | `clasimp/selftest.sml` uses an explicit base-claset destruction rule through `CS_AUTO_TAC` and scoped public `AUTO_TAC`, and a safe introduction rule through `CS_CLARSIMP_TAC`. Each needs a supplied rewrite before the rule view reaches the goal; a polymorphic rule is checked at both `num` and `bool`. |
| Reloaded persistent transport | `clasimp/theory_tests/transportPersistentBaseScript.sml` declares a safe destruction rule; its child theory closes the differently spelled goal with public `AUTO_TAC` and a supplied bridge rewrite. |
| Contextual FORCE transport | `clasimp/selftest.sml` keeps only FORCE's best-first leg and closes a rule/goal spelling mismatch after the ordinary search exhausts. |

The following temporary source ablations were run, then removed:

| Removed mechanism | Designated public failure |
| --- | --- |
| Fresh specialization before fixed-variable classification | `bound-variable spelling preserves fact type instances` failed in rules when specialization reused binder names and the resulting variables were classified as fixed. The rename/carrier matrix passed after restoration. |
| Safe consumers retain a literal implication | `the conditional citation does not add unsafe CLARSIMP search` failed when `SafeFacts` compiled the implication as a search rule and withheld its assumption. |
| Unbounded raw forward enumeration | `forward search reaches useful candidates through known results` failed when the shared forward cursor stopped after 200 raw candidates. A cap after duplicate filtering left that public proof green but broke `budgeted Aesop resumes a safe forward candidate scan`; it was not counted as evidence for E3. |
| Certified transport of unsafe tagged rules | `certified tagged rule view crosses an invocation normal form` failed in clasimp. |
| Currying a normalized conjunctive premise | `an INJ client rule survives the seed's definition normal form` failed in seeds. |
| Retaining FORCE's first-best session after a turn | `FORCE preserves first-best expansions across small turns` failed in clasimp. |
| Advancing after a yielded FORCE turn | `FORCE scheduler gives yielding engines one turn per round` failed when a yield immediately retried the same engine. |
| Transporting safe tagged rules | `safe tagged introduction retains its role after transport` failed in clasimp when safe transport was disabled. |
| Retaining the tableau continuation | `resumed tableau retains its fixed-depth work and proof` failed when yielded turns restarted the fixed-depth run. |
| Selecting persistent claset rules for transport | `persistent destruction rule crosses a supplied normal form` failed through public `AUTO_TAC` when only invocation markers were selected; the invocation tagged-rule control still passed. |
| Contextual FORCE's view fallback | `contextual FORCE uses a persistent rule's certified view` failed when that entry point passed no persistent candidates to the shared fallback. |
| Certified AC fallback reflexivity | `a new arithmetic carrier uses its registered theorem kit` failed with `EQT_ELIM` when the shared fallback left equal canonical forms as an unevaluated equality. |

The restored rules, classical, clasimp, linarith instances and seeds local
selftests pass. The ordered `upto-auto` gate passed after the FORCE
scheduler extraction and sole-finisher tests; the preceding gate ran
benchmarks on the same production scheduler. `bin/build -F -t` passed at
`22b8e0c53`, including the full distribution and generated documentation.

Tableau now retains its mutable search frontier at bounded turns. A cutoff
during initial translation restarts that preparation, and a cutoff within
one search step can replay charged work inside that step. Invocation safe
rule transport retains its declared role only when its safe class is
unchanged and no new theorem hypothesis is introduced. Persistent claset
rules now use the same certified view checks when a tactic leaves work open.
The independent arithmetic carrier uses its own type and operations; its
laws are proved from integer arithmetic, then consumed through the public
instance registry and tactic without generic dispatch on its names.
