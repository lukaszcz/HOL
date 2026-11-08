# Tracked integer logged recipes (TASK24)

Opt-in exports, with no default installation or main wiring:

- `../../intReduceExt.{sig,sml}`: `INT_REDUCE_ss`, named `INT_REDUCE`,
  logged by ordinary `intReduce` under theory `integer`. Original ordered
  keys: exponent, ABS negative, ABS nonnegative, then addition, subtraction,
  multiplication, division, modulus, equality, less, less/equal, greater,
  greater/equal, divides, remainder, quotient, minimum, maximum. The original
  literal/numeral argument guard delegates to public `intReduce.REDUCE_CONV`.
  All conversions retain the name `Integer calculation` and trace level 2.
- `../../integer_wordLibExt.{sig,sml}`: `INT_SIZES_ss`, named `int sizes`,
  logged under `integer_word`. Original ordered patterns are integer
  `INT_MIN`, `INT_MAX`, `UINT_MAX`, with conversion name `INT_SIZES_CONV`.
  Public `integer_wordLib.INT_SIZES_CONV` is exposed, so no word evaluator
  implementation or extra fragment recipe is needed. Its existing
  `integer_wordLib`/`wordsLib` dependencies suffice.

Both recipes register only in the extension catalog and construct tracked
fragments directly from immutable patterns/public conversions. Neither uses
ordinary fragments, simpsets, logs, or replay. Neither has native equality
rewrite sources. Existing ordinary sources and Holmakefiles are unchanged.

The standalone test compares ordinary, tracked and configured traversal
proofs, including complete hypothesis sets. It checks all keys, signs,
nesting, symbolic refusal, wrong heads, numeric word sizes 1/8/32, combined
recipes, exact fragment/conversion names, exclusions, removal/prohibition,
limits, installed Once spending, and source identity/quota preservation when
removing both conversions. The ordinary word fragment is signature-hidden;
**the test only** obtains the real ordinary fragment from the public logged
updates, rather than testing against a guessed reconstruction.

Run from the repository root:

```sh
sh src/simp/tests/compatibility/tools/root-wrapper.sh \
  sh -c 'cd src/integer/tests/tracked-recipes && Holmake check'
```

The check prints `INTEGER_RECIPE_CHECKS=<n>` on success.  Also run
`bin/build -t --seq=tools/sequences/upto-parallel` and
`tools/h4pedant/h4pedant -q src/integer`.
