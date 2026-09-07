# Automation benchmark results

## What this report measures

Each benchmark entry contains a HOL4 theorem statement, the Isabelle method used for the corresponding source result, and the HOL4 tactic chosen as that method's closest counterpart. This report calls that HOL4 tactic the **assigned tactic**.

The assigned tactic and its arguments are derived from the recorded Isabelle method string rather than authored per goal, so a goal cannot be handed a fact its source proof did not name. One context is added on top of that: every equational definition the translation introduces, as a rewrite, identically for every goal, and only to the methods that consult a simpset. This stands in for the ambient simpset an Isabelle method reads without naming it. It is more generous than Isabelle in one direction -- Isabelle adds a `fun` definition to its simpset by default but not a plain `definition` -- and the numbers below should be read with that in mind.

The comparison data was mined from Isabelle/HOL commit `f7e02b7e`. Each in-repository benchmark entry records its source file, line, method, and commit. The report was generated on 2026-08-28 with a 30-second limit for each tactic attempt. The limit is an asynchronous interrupt, so a goal can overrun it by the time its search takes to reach an interruptible point; the times below are wall-clock and record the overrun where it happened.

## Scope

The corpus covers six Isabelle theories at one commit -- `Set.thy`, `List.thy`, `Product_Type.thy`, `Map.thy`, `Option.thy` and `String.thy` -- plus a handful of `ex/` files. That is Isabelle's base library, not Isabelle/HOL. What follows says what these HOL4 tactics do on those goals at that budget. It is not a claim about Isabelle automation in general, and it is not a claim about goals outside the six theories.

## Facts the measurement withheld

Two distinct Isabelle facts can translate onto one HOL4 theorem, and a proof citing one of them then reads as if it assumed what it proves. The citation is dropped rather than the goal, so HOL4 is asked to close the goal without a fact the Isabelle proof had. That can only under-credit HOL4, and it is named here rather than left for the reader to discover.

- `set_L105_set_eq_iff (pred_set$EXTENSION)`
- `set_L563_empty_def (pred_set$EMPTY_DEF)`
- `set_L595_UNIV_def (pred_set$UNIV_DEF)`
- `list_L1921_in_set_conv_nth (parityTranslation$source_set_conv_nth)`
- `list_L8167_list_all_iff (list$EVERY_MEM)`
- `list_L8660_card_set (list$CARD_LIST_TO_SET_EQN[symmetric])`
- `list_L6444_stable_sort_key_sort_key (parityTranslation$source_sort_key_stable)`
- `list_L6690_distinct_if_distinct_map (list$ALL_DISTINCT_MAP)`
- `list_L6761_anon_L6761 (parityTranslation$source_strict_sorted_equal_unique)`
- `list_L8683_can_select_set_list_ex1 (parityTranslation$source_list_ex1_def)`
- `list_L7775_in_measures_2 (parityTranslation$source_measures_def)`
- `string_L728_anon_L728 (source_Literal_prime_def)`
- `product_type_L785_curry_conv (pair$CURRY_DEF)`

## Facts the translation does not render

An Isabelle proof can name a fact HOL4 states nowhere -- neither in a library nor in the translation theory.  The recipe has nothing to supply for such a citation, so the goal below is measured without it. As above, that can only under-credit HOL4, and the goals are named rather than left implicit in a shortfall count.

- `set_L651_Pow_not_empty (Pow_top)`
- `list_L1838_partition_filter_conv (partition_filter2[symmetric], partition_filter1[symmetric])`
- `list_L9013_list_all_transfer (list.pred_transfer)`
- `list_L5409_nths_drop (drop_eq_nths, nths_nths, atLeastLessThan_iff[symmetric])`
- `list_L6487_nth_nth_transpose_sorted (filter_equals_takeWhile_sorted_rev[OF sorted, of i])`
- `list_L6669_sorted_key_list_of_set_eq_Nil_iff (fold_insort_key.remove)`
- `list_L6770_sorted_key_list_of_set_unique (idem_if_sorted_distinct)`
- `list_L6873_nth_sorted_list_of_set_greaterThanAtMost (nth_sorted_list_of_set_greaterThanLessThan[of n "Suc j" i], greaterThanLessThan_eq)`
- `list_L7823_append_listrel1I (append_eq_appendI)`
- `list_L7922_wf_listrel1_iff (lists_accD, lists_accI[THEN Cons_in_lists_iff[THEN iffD1, THEN conjunct1]])`
- `list_L7256_lenlex_conv (lex_prod_def, inv_image_def)`
- `list_L7570_asym_lenlex (asym_inv_image, asym_less_than, asym_lex)`
- `list_L8999_set_Cons_transfer (rel_set_def)`
- `map_L308_dom_map_option_comp (dom_map_option[of "\<lambda>_. g" m])`
- `map_L810_graph_map_add (map_add_comm)`
- `map_L816_fst_graph_eq_dom (graph_eq_to_snd_dom)`
- `map_L828_finite_graph_map_of (finite_dom_map_of, graph_eq_to_snd_dom)`
- `string_L60_char_of_take_bit_eq (bit_take_bit_iff)`
- `string_L135_char_of_nat (drop_bit_of_nat, bit_simps, possible_bit_def)`
- `string_L344_char_of_integer_code (bit_iff_odd_drop_bit, drop_bit_eq_div)`
- `product_type_L1226_inj_apfst (inj_on_apfst[of f UNIV])`
- `product_type_L1232_inj_apsnd (inj_on_apsnd[of f UNIV])`

## Source accounting

Source mining identified 1,070 relevant Isabelle results. Nine pairs translated to the same HOL4 statement except for bound variable names, so they are tested once. This leaves 1,061 distinct source-derived results. Eleven existing HOL4 integer regression goals are also included, giving 1,072 accounted results in total:

- 1070 are executable HOL4 benchmark goals.
- 2 could not be translated faithfully and are listed by identifier and reason in the benchmark files.
- 0 source results are missing from both groups.

The selftest checks this accounting in both directions. An unexpected failure is an error, but so is an expected failure that starts succeeding without its record being updated.

## Results from the assigned tactics

**Executable goals** is the number of runnable HOL4 statements. **Solved by assigned tactic** counts statements proved by the HOL4 counterpart selected for their Isabelle method, with the ambient context described above. **Solved under Isabelle's own ambient set** is the same measurement with that context cut back to the definitions Isabelle would have made ambient by itself. Isabelle puts a `fun` definition in the default simpset and a plain `definition` not, and the corpus does not record which of the two introduced each constant, so recursion stands in for the distinction: a definition whose right-hand side mentions the constant it defines is one no plain `definition` could have made. The proxy errs strict, which is the direction that cannot flatter HOL4. Both numbers are given because choosing one would mean guessing which side of that distinction each constant fell on. **Routine selftest goals** is a fixed, explicitly marked subset run when `HOLSELFTESTLEVEL=1`; it is not a random sample. At level 2 or higher, all executable goals run.

A **family** is a subject-area group:

- **Classical** contains propositional and first-order logic.
- **Sets** contains set and relation reasoning.
- **List/map** contains lists, finite maps, options, strings, and product types.
- **Linarith** contains linear arithmetic over natural numbers, integers, real numbers, and rational numbers.
- **Presburger** contains quantified additive arithmetic over natural numbers and integers.
- **Algebra** contains polynomial, ring, and field identities.

| Family | Executable goals | Solved by assigned tactic | Solved under Isabelle's own ambient set | Routine selftest goals |
|---|---:|---:|---:|---:|
| Classical | 25 | 25 | 25 | 4 |
| Sets | 353 | 334 | 333 | 4 |
| List/map | 602 | 453 | 402 | 5 |
| Linarith | 46 | 46 | 46 | 4 |
| Presburger | 34 | 34 | 34 | 8 |
| Algebra | 10 | 8 | 8 | 3 |
| **Total** | **1070** | **900** | **848** | **28** |

## Cost of the solutions

A solve at 28 seconds is not the same result as a solve in milliseconds, and the count above cannot tell them apart. The columns below split the solved goals by elapsed time and report the search work the engines metered while solving them: node expansions, tableau branches, inferences and rule applications, summed. Zero search work means the goal was closed by rewriting rather than by search. Goals that overran the budget are counted as limitations, not here, so this distribution is bounded by the budget by construction.

| Family | Solved | < 0.1 s | 0.1-1 s | 1-10 s | > 10 s | Slowest | Median search work | Largest search work |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Classical | 25 | 6 | 19 | 0 | 0 | 0.9 | 39 | 516 |
| Sets | 334 | 86 | 243 | 5 | 0 | 3.0 | 3 | 2430 |
| List/map | 453 | 4 | 438 | 11 | 0 | 2.3 | 0 | 1868 |
| Linarith | 46 | 44 | 2 | 0 | 0 | 0.2 | 0 | 0 |
| Presburger | 34 | 31 | 2 | 1 | 0 | 1.4 | 0 | 0 |
| Algebra | 8 | 7 | 1 | 0 | 0 | 0.9 | 0 | 0 |
| **Total** | **900** | **178** | **705** | **17** | **0** | **3.0** | **0** | **2430** |

## Documented results not solved by the assigned tactic

- **Accepted scope exclusions** are executable goals deliberately outside the supported tactic scope, with a recorded reason.
- **Assigned-tactic limitations** are executable goals for which the assigned tactic failed or exceeded 30 seconds. Each one has a dated record naming its root cause, in `benchmarks/benchSetShortfalls.sml`, `benchmarks/benchLibraryShortfalls.sml` or `benchmarks/benchAlgebra.sml`.
- **Unavailable translations** are source results that could not be represented faithfully as HOL4 goals. They are not included in the executable-goal count.
- **Unaccounted source results** would be source results that are neither executable nor documented as unavailable. This number must remain zero.

| Family | Accepted scope exclusions | Assigned-tactic limitations | Unavailable translations | Unaccounted source results |
|---|---:|---:|---:|---:|
| Classical | 0 | 0 | 0 | 0 |
| Sets | 0 | 19 | 0 | 0 |
| List/map | 0 | 149 | 2 | 0 |
| Linarith | 0 | 0 | 0 | 0 |
| Presburger | 0 | 0 | 0 | 0 |
| Algebra | 0 | 2 | 0 | 0 |
| **Total** | **0** | **170** | **2** | **0** |

For every family, executable goals equal assigned-tactic solutions plus accepted scope exclusions plus assigned-tactic limitations.

## Goals another tactic would have closed

The exhaustive run also tries three general-purpose HOL4 tactics on every goal whose recipe does not already use them. A goal is counted below when that tactic closed it and the assigned tactic did not, so each column measures what the method-to-tactic mapping cost rather than what HOL4 cannot do. The columns overlap one another and are disjoint from the solved count. They are not strength scores: a tactic is never counted on a goal it was assigned. They do not affect whether the benchmark selftest passes.

| Family | `AUTO_TAC` | `BLAST_TAC` | `AESOP_TAC` |
|---|---:|---:|---:|
| Classical | 0 | 0 | 0 |
| Sets | 0 | 2 | 5 |
| List/map | 14 | 0 | 10 |
| Linarith | 0 | 0 | 0 |
| Presburger | 0 | 0 | 0 |
| Algebra | 0 | 0 | 0 |
| **Total** | **14** | **2** | **15** |

## Seed-rule safety check

A rule is classified as **safe** when applying it cannot discard a possible proof of the goal. The automated seed-rule check proves the required reverse direction for every such rule. It currently passes with no exceptions.

## Reproducing the report

From `src/auto/benchmarks/`:

```sh
Holmake
./selftest.exe
HOLSELFTESTLEVEL=2 ./selftest.exe
./genparity.exe
```

The first selftest command runs the fixed routine subset. The second runs every executable goal and the other-tactic observations. The final command regenerates `../PARITY.md`.
