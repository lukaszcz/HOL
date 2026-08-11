# Automation seeds

This post-boss directory contains the opt-in, promotion-ready rule corpus
for the automation layer.  Each source theory has its own `*AutoSeed`
theory; `autoSeed` is the complete umbrella.  Loading a seed changes only
the theory-ancestry-backed automation databases and does not alter a
distribution simpset.

`seedAudit` checks every safe rule's inversion obligation.  The named
`algebra_simps` and `field_simps` collections are exposed by
`seedCollections` as stateful ssfrags and are likewise opt-in.

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
