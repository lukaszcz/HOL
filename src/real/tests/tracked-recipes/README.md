# Logged real recipes

`realSimpsExt` exports only REAL_REDUCE, RMULCANON and RMULRELNORM,
matching the ordinary real log's append order. It reconstructs the ordered
literal theorem ingredients and shares only the public conversions
`elim_common_factor`, `REALMULCANON` and `mulrelnorm`. No ordinary fragment,
compiled simpset, registry recipe, log replay or `dest_ssfrag` is imported.
There are no default-simpset or global compute-set updates.

The ceiling specialisation uses tracked boolean/numeral rewriting; it does
not need the ordinary pair fragment or arithmetic decision procedure.
Every resulting rewrite is checked against the ordinary ordered ingredients,
including its complete conclusion and exact hypothesis set.

From the repository root:

```sh
bin/Holmake -C src/real/tests/tracked-recipes check
```

The check prints `REAL_RECIPE_CHECKS=<n>` on success.
Ordinary `realSimps.{sig,sml}` and the existing `src/real/Holmakefile`
are unchanged. The standalone Holmakefile is new, not a build integration.

Coverage includes rational arithmetic, all four common-factor patterns,
comparison/equality, min/max/abs, powers, floor/ceiling, multiplication
canonicalisation, equality and signed inequality cancellation, retained
side-condition hypotheses, unknown-sign refusal and non-matching terms.
Each example compares whole ordinary/tracked/configured-traversal theorem
conclusions and hypothesis sets and checks an independently stated result.
Ceiling supplies LET_THM explicitly because the minimal base lacks LET_ss.

Metadata/control checks cover append order, anonymous native source names,
conversion-only source absence, extension catalog isolation, all six isolated
equality keys and their original exclusion names, other conversion names,
fragment removal/prohibition, zero/one traversal limits, native Once quotas,
and source identity/quota preservation across fragment removal.

The historical dotted conversion name `realSimps.elim_common_factor` is
preserved. Ordinary strict `-*` interprets it as theory-qualified and rejects
`realSimps` (a structure, not a theory); tracked behavior must agree. Removing
the REAL_REDUCE fragment disables the conversion instead.

Only these logged recipes are supplied: REAL_ARITH, RADDCANON, real_SS,
real_ac_SS, full real simpsets and computation sets remain out of scope.
