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
