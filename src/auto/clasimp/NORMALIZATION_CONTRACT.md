# Automation normalization: G4 inventory and proposed contract

This records the G4 passes and their migration status. The owner approved
D2's opt-in child-first traversal and D5's abstraction policy.
Ordinary HOL4 simplification retains its existing traversal.

## Current passes

| Pass | Input and output | Traversal, context and progress | Consumers |
| --- | --- | --- | --- |
| Opt-in child-first traversal (`Traverse`, `simpLib`) | A goal, invocation simpset and rewrite arguments become a goal simplified with local assumptions and selected invocation rules. | Congruences control descent and context. A certified eta contraction preserves function-argument heads before permitted children are visited; logical binders are excluded. Parent rewrites follow child descent, and the simplifier's assumption/conclusion fixpoint remains in use. This replaces the former `context_first` and `refining` outer pass in clasimp. The traversal accepts a normalization charge callback shared by each public tactic’s mutual simplification and search wrappers. | `asm_full_simp`, `safe_asm_full_simp`, then AUTO, FORCE, CLARSIMP and their search wrappers. |
| Conditional witness subgoaler | A residual side condition and simplifier context theorems become a proved equality to `T`, or the traversal's unchanged reduction. | It recursively simplifies the condition, reverses existential miniscoping, then matches each condition against context assumptions while holding the condition's other variables and types fixed. It constructs the proof from those context theorems without taking an ambient context snapshot. Public tactics charge each candidate match and proof work to their invocation budget. It runs only in conditional rewriting. | The derived clasimp simpset, including tactics built on it. |
| Conditional congruence | A conditional's condition and branches become a simplified conditional. | The weak congruence simplifies the condition but leaves both branches alone to avoid recursive unfolding inside an inactive branch. The split fragment handles branch reasoning later. | Every tactic using the derived clasimp simpset. |
| `permutation_instances` | A supplied permutative theorem and current goal assumptions become bounded contextual rewrite instances. | Before the main simplification pass, it matches a redex in the current goal, discharges every condition from exact assumptions, checks support rigidity and term order, then bounds each rewrite by its redex occurrences. | Unsafe `asm_full_simp` and its AUTO/FORCE/search wrappers. |
| `iff_bottom_up`, `simp_bottom_up` and invocation subject reducer | Named declarations or invocation rewrites become higher-order root reductions. | A reducer is reached after higher-priority ordinary rewrites at a node. The persistent reducer reads the declaration table when called; the invocation reducer closes over its own rules. Neither is a general child-first traversal. | The derived simpset; `[iff_bottom_up]` also seeds claset rules. |
| `membership_heads`, `pointwise` and `extensional_normalize` | A function equality becomes an applied or membership equivalence with a kernel conversion. | `membership_heads` scans rewrite heads once per tactic construction. The conversion acts at the goal boundary under leading universal quantifiers and implications; it stands down when a supplied rewrite states the reading. It does not recurse through arbitrary nested equalities. Each pointwise step removes one function arrow. | AUTO, FORCE, FASTFORCE and terminal `with_extensionality`; safe-only methods do not add the unsafe extensional step. |
| `GEN_GLOBAL_SIMP_TAC` mutual fixpoint | Goal assumptions and conclusion become simplified goals plus kernel validation. | It scans assumptions in configured order, simplifies the conclusion, and repeats after actual changes or structural decomposition. Root implication rewriting and rebuild are separate flags. `cascade_safe_simp` disables implication rebuild to avoid a safe-step cycle. | Context, ambient and cascade simplification in clasimp; Aesop's normalization rule also calls safe simplification. |
| Fact and rule views | The invocation's original theorems become literal assumptions, schematic simplifier views, and compiled search rules. | `clasetFacts` owns original theorem, support, fixed parameters and source ID. Safe consumers insert literal facts without compiling an unsafe rule. Search consumers compile eligible implications from lazy schematic views and insert the others, avoiding duplicate assumption expansion. Search canonicalization instantiates the rule view at use sites. Clasimp derives certified child-first normalized views of supplied search facts against the invocation simpset; it then curries conjunctive antecedents so separately simplified assumptions remain usable. If the ordinary tactic leaves work open, clasimp derives rule views of persistent and invocation declarations and retries on the original goal. The originals remain installed, and transported rules retain their declared role. Safe consumers transport only safe declarations; every derived rule must preserve its safe classification and theorem support. BLAST offers a safe introduction view for plain facts with loose type variables. Aesop selects equational normalization views, including equational conjuncts, before freshening; derived views retain their source and support while propositional facts remain available to forward rules. Order tactics match theorem views at relation sites, and the order reducer matches directly supplied schematic citations at an atom while keeping assumptions fixed. Literal insertion still specializes against the current goal as a compatibility route. | Classical, BLAST, clasimp, Aesop and order; linarith still inserts literal facts. |

The ordinary `Traverse.TRAVERSE_IN_CONTEXT` still tries high-priority
rewriters at a node before descending through congruences. The opt-in
child-first path contracts an eta function argument first when possible,
then descends and offers rewrites and reducers at that node. Its callback
charges head preservation, traversal and reducer attempts; the existing
`limit` counts successful reducer calls. Public clasimp tactics share an
invocation normalization budget across their mutual fixpoint, search
wrappers, initial FORCE simplification, extensional conversions and target
transport.

## Proposed automation contract

1. Congruence controls which children may be visited and which local
   assumptions they receive. Weak conditional congruence leaves branches
   untouched until the split stage licenses them.
2. For an automation traversal, visit permitted children before ordinary
   parent rewrites, then revisit a changed parent under the invocation's
   normalization budget. At a redex, local and ambient rules have one
   deterministic precedence independent of registration name. A
   congruence's explicit behavior takes priority over this default order.
3. Conditional rewriting may match a witness against the invocation fact
   environment and local context. Fixed parameters and theorem hypotheses
   remain support; no unsupported witness is guessed. Replay uses the
   tactic's explicit context and discharges that support.
4. Permutative rewrites follow the configured term order. A grounded
   contextual instance may use a justified orientation only when its
   premises have been discharged and its support fixes the matched terms.
5. Assumption and conclusion normalization form one mutual fixpoint.
   Before simplifying a context fact, dependents can read its original
   view; a fact cannot justify rewriting itself away. Context generations
   invalidate derived views when the available assumptions change.
6. Extensionality remains a certified inference at a documented goal
   boundary. It does not expand nested equations by default or enter a
   safe-only tactic as an unsafe step. Membership and application views
   must reconstruct the caller's exact target.
7. Cyclic user rules terminate with a typed normalization-limit outcome.
   Built-in rules receive either a decreasing measure or an explicit
   repeat guard. An exhausted budget never reports saturation.

The approved D2 API is an opt-in traversal policy in `simp`. It preserves
eta function-argument heads with a certified conversion, then selects
child-first order under congruence and takes a normalization charge
callback. The default traversal stays as it is. `context_first` and
overlap-specific deferral were removed after local overlap and
recursive-equation tests. The seed and benchmark gates now pass, including
the `GENLIST` interval case that initially exposed the abstraction-head
problem. The bottom-up reducer remains until paired tests show the policy
subsumes its cases. The existing context fixpoint and conditional subgoaler
remain reusable. Certified rule-view transport now covers persistent claset
rules in AUTO and the direct contextual AUTO, FORCE, FASTFORCE, SLOWSIMP,
BESTSIMP and CLARSIMP entry points. The ordinary tactic runs first, and a
certified derived view is tried when it leaves work open. Candidates share
a nonlogical head with the goal, a residual goal from the first attempt,
or a head reachable through chains of the supplied simpset's direct
rewrite-head bridges; this bounds conversion work without
assuming that the rule and goal use identical heads. The original
declaration and role are retained. A synthetic pair of cyclic rules
exercises the typed
normalization-limit outcome through `CLARSIMP_TAC_BUDGETED`.
