# Tracked numeral default recipes

`../../src/numSimpsExt.{sig,sml}` exports only the actual logged numeral
fragments. Loading it does not install defaults or use ordinary fragments,
simpsets, update logs, or replay. Ordinary `numSimps` is unchanged.

## Exact order and dependencies

`numSimps.sml` logs under `{thyname = "numeral"}`:

1. `add_frags [REDUCE_ss, ARITH_RWTS_ss]`
2. Later, `add_frags [MOD_ss]`

The append/application order is therefore **REDUCE, ARITH_RWTS, MOD**.
`ssfrags_of`/`ssfrag_names_of` show newest first: **MOD, ARITH_RWTS,
REDUCE**. The selftest checks the public ordinary
`BasicProvers.apply_logged_updates` result as well as this explicit recipe
list. No `ARITH_DP`, `ARITH_NORM`, `SUC_FILTER`, or `ARITH` is a dependency
or an implicit extra default.

- **REDUCE:** the original five unary and thirteen binary conversion keys,
  in their original order, and the small private numeral/SUC argument
  guard; evaluation uses public `reduceLib.REDUCE_CONV`. There are no
  native rewrite sources.
- **ARITH_RWTS:** the original 70 theory-named and 27 locally named theorem
  ingredients, in order, including derived theorem names and symmetric
  variants. Public `Arith.ARITH_CONV` derives the local arithmetic facts.
  These are native tracked equality sources, with their original names.
- **MOD:** a theorem-only `relsimp_ss` recipe with `MODEQ_REFL`,
  `MODEQ_TRANS`, weakening `[MODEQ_INTRO_CONG]`, no subsets, and relational
  rewrites `[MODEQ_NUMERAL, MODEQ_MOD, MODEQ_0]`; followed by congruences
  `[MODEQ_PLUS_CONG, MODEQ_MULT_CONG, MODEQ_SUC_CONG, MODEQ_EXP_CONG]`.
  `simpExtLib.relsimp_ss` builds the relational reducer from those inputs;
  its implementation explicitly lifts the opaque ordinary reducer using
  `TraverseExt.lift`. No ordinary `MOD_ss` or large decision-procedure
  implementation is copied. Relational rewrites are not represented as
  native equality-source handles.

The fragment recipes need `simpExtLib`, the arithmetic/prim_rec theorems,
`numSyntax`, `reduceLib`, `Arith`, and ordinary kernel/theorem construction
helpers. No additional exported dependency fragment is needed. The test
installs the recipes over corresponding ordinary/tracked boolean bases;
MOD uses the installed reducer/arithmetic rules to discharge side
conditions, including symbolic positive-modulus assumptions.

## Running

From the repository root, use the configured-path wrapper (it need not be
executable):

```sh
sh src/simp/tests/compatibility/tools/root-wrapper.sh \
  sh -c 'cd src/num/arith/tests/tracked-recipes && Holmake check'
```

The standalone test Holmakefile is opt-in; existing Holmakefiles and main
wiring are untouched. The test compares complete theorems (conclusion and
hypothesis set), names, ingredient order, all reduction keys, modular
congruences including exponentiation, exclusions, traversal limits,
fragment prohibition, bounded-rule spending, and native source identities
across control-preserving removal.

The check prints `NUMERAL_RECIPE_CHECKS=<n>` on success.  Also run
`bin/build -t --seq=tools/sequences/upto-parallel` and `h4pedant -q` on the
arithmetic source directory and this test directory.
