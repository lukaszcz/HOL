# Automation seeds

This directory contains optional automation rules built after `src/boss`.
Each source theory has its own `*AutoSeed` theory; `autoSeed` imports all of
them.  A child theory inherits the rules of every seed theory in its
ancestry.  Loading a seed does not change HOL4's default simplifier rules.

`seedAudit` checks every rule classified as safe by proving the reverse
direction required to show that applying the rule cannot lose solutions.
The named `algebra_simps` and `field_simps` collections are exposed by
`seedCollections` as optional simplifier fragments (`simpLib.ssfrag`
values).

Declarations are grouped by the job they do, rather than by the theory
in which their theorem was first proved:

- Structural normalization uses `[simp]`, `[iff]`, or the subject-last
  `[simp_bottom_up]` and `[iff_bottom_up]` views. These read
  constructors, membership, list operators and quantifier bodies into
  forms other rules can match. The bottom-up views are for rules such
  as option non-`NONE` and miniscoping laws whose subject must be
  simplified first.
- Contextual simplification uses `[simp]` rules with premises and the
  explicit `algebra_simps` and `field_simps` collections. Assumptions
  discharge rewrite conditions; algebraic expansion and field rewrites
  remain opt-in where they may enlarge terms.
- Safe decomposition uses `[sintro]`, `[selim]` and `[sdest]` to expose
  all branches or premises without committing to a witness or losing
  solutions. `seedAudit` checks the declared safe direction.
- Search choices use `[intro]`, `[elim]` and `[dest]` to offer witnesses,
  case splits and consequences only to unsafe search. Universe
  membership and transitive-closure steps should not fire in every
  safe pass.
- Bridges use dual declarations such as `[simp, dest]` for order
  components and `[simp, intro]` for well-founded inverse images. They
  make a fact available both at a rewrite side condition and at a
  search rule premise, where rewriting the goal alone cannot reach it.

`[iff]` also supplies classical views of an equivalence. The rule's
actual safe or unsafe claset role is determined by the derived direction,
not by the fact that it is an equivalence. Split declarations are kept
for constructor-sensitive branching rather than treated as rewrite laws.

`INJ_DEF_AUTO` currently unfolds an `INJ` head in the simplifier. That
helps goals which need the defining obligations, but can hide the head
from a client rule stated over `INJ`. Its replacement needs either
specific laws that preserve the head or certified transport between
the client's and goal's normalized forms. Until that choice is made,
the unfolding remains in place and the interaction is an open audit
item. Safe-rule inversion does not establish rewrite termination or
search completeness; those properties need separate normalization and
consumer tests.

For the complete seeded state, make `autoSeed` an ancestor of a theory (or
`open autoSeedTheory` in an ML consumer).  A smaller consumer can depend on
one per-theory seed such as `listAutoSeed` instead.  The numeric collections
remain explicit:

```sml
SIMP_TAC (srw_ss() ++ seedCollections.algebra_ss ()) []
SIMP_TAC (srw_ss() ++ seedCollections.field_ss ()) []
```

Use `remove_algebra_simps` and `remove_field_simps` with persistent theorem
names when a descendant theory needs to retract an inherited member.
