open HolKernel Parse boolLib bossLib sortingTheory relationTheory

val _ = new_theory "parityTranslation"

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:399-442.  A source linorder is represented by its
   explicit weak ordering relation.  Isabelle's strict operation is
   HOL4's STRORD construction on that relation. *)
Definition source_sorted_def:
  source_sorted le (xs : 'a list) = sorting$SORTED le xs
End

Definition source_strict_sorted_def:
  source_strict_sorted le (xs : 'a list) =
    sorting$SORTED (relation$STRORD le) xs
End

(* Isabelle/HOL src/HOL/List.thy:5911-5974.  Unlike HOL4's adjacent
   SORTED predicate, sorted_wrt relates every earlier element to every
   later element. *)
Definition source_sorted_wrt_def:
  (source_sorted_wrt relation ([] : 'a list) <=> T) /\
  (source_sorted_wrt relation (head::tail) <=>
     (!item. MEM item tail ==> relation head item) /\
     source_sorted_wrt relation tail)
End

Theorem source_sorted_bridge:
  !le xs : 'a list.
    source_sorted le xs <=> sorting$SORTED le xs
Proof
  simp[source_sorted_def]
QED

Theorem source_strict_sorted_bridge:
  !le xs : 'a list.
    source_strict_sorted le xs <=>
    sorting$SORTED (relation$STRORD le) xs
Proof
  simp[source_strict_sorted_def]
QED

Theorem source_sorted_wrt_bridge:
  !relation xs.
    relation$transitive relation ==>
    (source_sorted_wrt relation xs <=>
     sorting$SORTED relation xs)
Proof
  gen_tac
  >> Induct
  >- simp[source_sorted_wrt_def]
  >> simp[source_sorted_wrt_def, sortingTheory.SORTED_EQ,
          CONJ_COMM]
QED

Theorem source_sorted_wrt_nth_less:
  !relation xs.
    source_sorted_wrt relation xs <=>
    !left right.
      left < right /\ right < LENGTH xs ==>
      relation (EL left xs) (EL right xs)
Proof
  gen_tac
  >> Induct
  >- simp[source_sorted_wrt_def]
  >> simp[source_sorted_wrt_def, listTheory.MEM_EL]
  >> gen_tac
  >> eq_tac
  >- (strip_tac
      >> rpt gen_tac
      >> strip_tac
      >> Cases_on `left`
      >> Cases_on `right`
      >> fs[]
      >> metis_tac[])
  >> strip_tac
  >> conj_tac
  >- (rpt gen_tac
      >> strip_tac
      >> fs[]
      >> qpat_x_assum `!left right. _`
           (qspecl_then [`0`, `SUC n`] mp_tac)
      >> simp[])
  >> rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `!left right. _`
       (qspecl_then [`SUC left`, `SUC right`] mp_tac)
  >> simp[]
QED

Theorem source_sorted_wrt_not_adjacent:
  sorting$SORTED
    (\left right : num. right = SUC left) [0; 1; 2] /\
  ~source_sorted_wrt
    (\left right : num. right = SUC left) [0; 1; 2]
Proof
  simp[source_sorted_wrt_def]
QED

Theorem source_weak_linear_transitive:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==> relation$transitive le
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder]
QED

Theorem source_weak_linear_reflexive:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==> relation$reflexive le
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder]
QED

Theorem source_weak_linear_antisymmetric:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    relation$antisymmetric le
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder]
QED

Theorem source_weak_linear_refl:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==> !value. le value value
Proof
  rpt strip_tac
  >> drule source_weak_linear_reflexive
  >> simp[relationTheory.reflexive_def]
QED

Theorem source_sorted_map_bridge:
  !le function xs.
    source_sorted le (MAP function xs) <=>
    source_sorted (\left right. le (function left) (function right)) xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def]
  >> Cases_on `xs`
  >- simp[source_sorted_def]
  >> rw[source_sorted_def]
  >> fs[source_sorted_def]
  >> Cases_on `t`
  >> fs[]
QED

Theorem source_sorted_length01:
  !le xs : 'a list.
    LENGTH xs <= 1 ==> source_sorted le xs
Proof
  rpt strip_tac
  >> Cases_on `xs`
  >- simp[source_sorted_def]
  >> Cases_on `t`
  >> fs[source_sorted_def]
QED

Theorem source_sorted_front:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      source_sorted le xs ==>
      source_sorted le (FRONT xs)
Proof
  rpt strip_tac
  >> Cases_on `xs`
  >- simp[source_sorted_def]
  >> `FRONT (h::t) ++ [LAST (h::t)] = h::t` by
       simp[listTheory.APPEND_FRONT_LAST]
  >> fs[source_sorted_def]
  >> metis_tac[sortingTheory.SORTED_APPEND,
               source_weak_linear_transitive]
QED

Theorem source_sorted_dropwhile:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !predicate xs.
      source_sorted le xs ==>
      source_sorted le (dropWhile predicate xs)
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def]
  >> simp[source_sorted_def, listTheory.dropWhile_def]
  >> Cases_on `predicate h`
  >> fs[source_sorted_def]
  >> metis_tac[sortingTheory.SORTED_TL]
QED

Theorem source_sorted_wrt_dropWhile:
  !relation predicate xs.
    source_sorted_wrt relation xs ==>
    source_sorted_wrt relation (dropWhile predicate xs)
Proof
  Induct_on `xs`
  >- simp[source_sorted_wrt_def, listTheory.dropWhile_def]
  >> rpt gen_tac
  >> Cases_on `predicate h`
  >- simp[source_sorted_wrt_def, listTheory.dropWhile_def]
  >> simp[source_sorted_wrt_def, listTheory.dropWhile_def]
QED

Theorem source_sorted_wrt_length01:
  !relation xs.
    LENGTH xs <= 1 ==> source_sorted_wrt relation xs
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >- simp[source_sorted_wrt_def]
  >> Cases_on `t`
  >> simp[source_sorted_wrt_def]
QED

Theorem source_sorted_same:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      source_sorted le (FILTER (\item. item = value) xs)
Proof
  rpt strip_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def]
  >> simp[]
  >> Cases_on `h = value`
  >> fs[source_sorted_def, sortingTheory.SORTED_EQ,
        source_weak_linear_transitive]
  >> rw[]
  >> fs[listTheory.MEM_FILTER]
  >> metis_tac[source_weak_linear_refl]
QED

Theorem source_genlist_el_take:
  !xs count.
    count <= LENGTH xs ==>
    GENLIST (\index. EL index xs) count = TAKE count xs
Proof
  rw[listTheory.LIST_EQ_REWRITE, listTheory.EL_GENLIST,
     listTheory.EL_TAKE]
QED

Theorem source_strord_transitive:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    relation$transitive (relation$STRORD le)
Proof
  rpt strip_tac
  >> `relation$WeakOrder le` by
       fs[relationTheory.WeakLinearOrder]
  >> `relation$Order le` by
       metis_tac[relationTheory.WeakOrd_Ord]
  >> `relation$StrongOrder (relation$STRORD le)` by
       metis_tac[relationTheory.STRORD_Strong]
  >> fs[relationTheory.StrongOrder]
QED

Theorem source_strord_subset:
  !le (x : 'a) y. relation$STRORD le x y ==> le x y
Proof
  simp[relationTheory.STRORD]
QED

Theorem source_strict_sorted_iff:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      (source_strict_sorted le xs <=>
       source_sorted le xs /\ ALL_DISTINCT xs)
Proof
  rpt strip_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def, source_strict_sorted_def]
  >> simp[source_sorted_def, source_strict_sorted_def,
          sortingTheory.SORTED_EQ,
          source_weak_linear_transitive,
          source_strord_transitive,
          relationTheory.STRORD,
          boolTheory.FORALL_AND_THM]
  >> fs[source_sorted_def, source_strict_sorted_def]
  >> metis_tac[]
QED

Theorem source_strict_sorted_equal_unique:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !domain xs ys.
      source_strict_sorted le xs /\
      LIST_TO_SET xs = domain /\
      source_strict_sorted le ys /\
      LIST_TO_SET ys = domain ==>
      xs = ys
Proof
  metis_tac[source_strict_sorted_iff, source_sorted_def,
            source_weak_linear_transitive,
            source_weak_linear_antisymmetric,
            sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ]
QED

(* Isabelle/HOL src/HOL/List.thy:6222-6400.  The source insertion
   sort is parameterized here by its weak linear order. *)
Definition source_insort_key_def:
  (source_insort_key le function value [] = [value]) /\
  (source_insort_key le function value (head::tail) =
     if le (function value) (function head) then
       value::head::tail
     else
       head::source_insort_key le function value tail)
End

Definition source_insort_def:
  source_insort le value xs =
    source_insort_key le I value xs
End

Definition source_sort_key_def:
  (source_sort_key le function [] = []) /\
  (source_sort_key le function (head::tail) =
     source_insort_key le function head
       (source_sort_key le function tail))
End

Definition source_sort_def:
  source_sort le xs = source_sort_key le I xs
End

Definition source_insort_insert_key_def:
  source_insort_insert_key le function value xs =
    if function value IN IMAGE function (LIST_TO_SET xs) then xs
    else source_insort_key le function value xs
End

Definition source_insort_insert_def:
  source_insort_insert le value xs =
    source_insort_insert_key le I value xs
End

Theorem source_set_insort_key:
  !le function value xs.
    LIST_TO_SET (source_insort_key le function value xs) =
    value INSERT LIST_TO_SET xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_insort_key_def]
  >> gen_tac
  >> IF_CASES_TAC
  >> simp[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_map_insort_key:
  !le function value xs.
    MAP function (source_insort_key le function value xs) =
    source_insort le (function value) (MAP function xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_insort_def, source_insort_key_def,
          combinTheory.I_THM]
  >> Cases_on `le (function value) (function h)`
  >> simp[source_insort_def, source_insort_key_def,
          combinTheory.I_THM]
QED

Theorem source_set_insort:
  !le value xs.
    LIST_TO_SET (source_insort le value xs) =
    value INSERT LIST_TO_SET xs
Proof
  simp[source_insort_def, source_set_insort_key]
QED

Theorem source_sorted_insort_identity:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      (source_sorted le
         (source_insort_key le I value xs) <=>
       source_sorted le xs)
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def, source_insort_key_def]
  >> rw[source_insort_key_def]
  >> fs[source_sorted_def, sortingTheory.SORTED_EQ,
        source_set_insort_key, combinTheory.I_THM,
        relationTheory.WeakLinearOrder_dichotomy,
        relationTheory.WeakOrder]
  >> metis_tac[]
QED

Theorem source_sorted_insort:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      (source_sorted le (source_insort le value xs) <=>
       source_sorted le xs)
Proof
  simp[source_insort_def, source_sorted_insort_identity]
QED

Theorem source_sorted_insort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs.
      (source_sorted le
         (MAP function
           (source_insort_key le function value xs)) <=>
       source_sorted le (MAP function xs))
Proof
  simp[source_map_insort_key, source_sorted_insort]
QED

Theorem source_sorted_sort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs.
      source_sorted le (MAP function
        (source_sort_key le function xs))
Proof
  rpt strip_tac
  >> Induct_on `xs`
  >- simp[source_sort_key_def, source_sorted_def]
  >> simp[source_sort_key_def, source_sorted_insort_key]
QED

Theorem source_sorted_sort:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs. source_sorted le (source_sort le xs)
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> simp[source_sort_def]
  >> drule source_sorted_sort_key
  >> strip_tac
  >> first_x_assum (qspecl_then [`I`, `xs`] mp_tac)
  >> simp[]
QED

Theorem source_insort_key_is_cons:
  !le function value xs.
    (!item.
       MEM item xs ==>
       le (function value) (function item)) ==>
    source_insort_key le function value xs = value::xs
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> simp[source_insort_key_def]
QED

Theorem source_sort_key_id_if_sorted:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs.
      source_sorted le (MAP function xs) ==>
      source_sort_key le function xs = xs
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sort_key_def]
  >> rpt strip_tac
  >> `source_sorted le (MAP function xs)` by
       (fs[source_sorted_def]
        >> metis_tac[sortingTheory.SORTED_TL])
  >> `source_sort_key le function xs = xs` by metis_tac[]
  >> `!mapped.
        MEM mapped (MAP function xs) ==>
        le (function h) mapped` by
       (fs[source_sorted_def]
        >> `relation$transitive le` by
             metis_tac[source_weak_linear_transitive]
        >> imp_res_tac sortingTheory.SORTED_EQ)
  >> simp[source_sort_key_def]
  >> irule source_insort_key_is_cons
  >> rpt strip_tac
  >> qpat_x_assum
       `!mapped.
          MEM mapped (MAP function xs) ==>
          le (function h) mapped`
       (qspec_then `function item` mp_tac)
  >> disch_then match_mp_tac
  >> simp[listTheory.MEM_MAP]
  >> qexists_tac `item`
  >> simp[]
QED

Theorem source_sorted_sort_id:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !xs.
      source_sorted le xs ==>
      source_sort le xs = xs
Proof
  simp[source_sort_def]
  >> metis_tac[source_sort_key_id_if_sorted,
               listTheory.MAP_ID]
QED

Theorem source_sorted_replicate:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !n value.
      source_sorted le (REPLICATE n value)
Proof
  gen_tac
  >> strip_tac
  >> drule source_sorted_same
  >> strip_tac
  >> rpt gen_tac
  >> `FILTER (\item. item = value) (REPLICATE n value) =
      REPLICATE n value` by
       (Induct_on `n` >> simp[])
  >> first_x_assum
       (qspecl_then [`value`, `REPLICATE n value`] mp_tac)
  >> simp[]
QED

Theorem source_sort_replicate:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !count value.
      source_sort le (REPLICATE count value) =
      REPLICATE count value
Proof
  metis_tac[source_sorted_sort_id,
            source_sorted_replicate]
QED

Theorem source_insort_insert_key_triv:
  !le function value xs.
    function value IN IMAGE function (LIST_TO_SET xs) ==>
    source_insort_insert_key le function value xs = xs
Proof
  simp[source_insort_insert_key_def]
  >> metis_tac[]
QED

Theorem source_insort_insert_triv:
  !le value xs.
    value IN LIST_TO_SET xs ==>
    source_insort_insert le value xs = xs
Proof
  simp[source_insort_insert_def,
       source_insort_insert_key_def]
QED

Theorem source_insort_insert_insort_key:
  !le function value xs.
    function value NOTIN IMAGE function (LIST_TO_SET xs) ==>
    source_insort_insert_key le function value xs =
    source_insort_key le function value xs
Proof
  simp[source_insort_insert_key_def]
  >> metis_tac[]
QED

Theorem source_insort_insert_insort:
  !le value xs.
    value NOTIN LIST_TO_SET xs ==>
    source_insort_insert le value xs =
    source_insort le value xs
Proof
  simp[source_insort_insert_def,
       source_insort_insert_key_def,
       source_insort_def]
  >> metis_tac[]
QED

Theorem source_set_insort_insert:
  !le value xs.
    LIST_TO_SET (source_insort_insert le value xs) =
    value INSERT LIST_TO_SET xs
Proof
  rpt gen_tac
  >> Cases_on `value IN LIST_TO_SET xs`
  >> simp[source_insort_insert_def,
          source_insort_insert_key_def,
          source_set_insort_key,
          pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_sorted_insort_insert_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs.
      source_sorted le (MAP function xs) ==>
      source_sorted le
        (MAP function
          (source_insort_insert_key le function value xs))
Proof
  simp[source_insort_insert_key_def]
  >> metis_tac[source_sorted_insort_key]
QED

Theorem source_sorted_insort_insert:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      source_sorted le xs ==>
      source_sorted le (source_insort_insert le value xs)
Proof
  simp[source_insort_insert_def,
       source_insort_insert_key_def,
       source_insort_def]
  >> metis_tac[source_sorted_insort_identity]
QED

Definition source_stable_sort_key_def:
  source_stable_sort_key le sorter <=>
    !function xs key.
      FILTER (\value. function value = key)
        (sorter le function xs) =
      FILTER (\value. function value = key) xs
End

Theorem source_filter_insort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function value xs key.
      FILTER (\item. function item = key)
        (source_insort_key le function value xs) =
      if function value = key then
        value::FILTER (\item. function item = key) xs
      else
        FILTER (\item. function item = key) xs
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_insort_key_def]
  >> rpt gen_tac
  >> rw[source_insort_key_def]
  >> Cases_on `function value = key`
  >> Cases_on `function h = key`
  >> fs[]
  >> metis_tac[source_weak_linear_refl]
QED

Theorem source_sort_key_stable:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs key.
      FILTER (\value. function value = key)
        (source_sort_key le function xs) =
      FILTER (\value. function value = key) xs
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sort_key_def]
  >> gen_tac
  >> simp[source_sort_key_def, source_filter_insort_key]
QED

Theorem source_stable_sort_key_sort_key:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    source_stable_sort_key le source_sort_key
Proof
  simp[source_stable_sort_key_def, source_sort_key_stable]
QED

Definition source_transpose_def:
  source_transpose rows =
    GENLIST
      (\index.
         MAP (\row. EL index row)
           (FILTER (\row. index < LENGTH row) rows))
      (rich_list$MAX_LIST (MAP LENGTH rows))
End

Theorem source_sorted_transpose:
  !rows : 'a list list.
    source_sorted ($<=)
      (REVERSE (MAP LENGTH (source_transpose rows)))
Proof
  gen_tac
  >> simp[source_sorted_def, sortingTheory.SORTED_EL_LESS,
          relationTheory.transitive_def]
  >> rpt strip_tac
  >> simp[source_transpose_def, listTheory.MAP_GENLIST,
          listTheory.EL_REVERSE]
  >> fs[source_transpose_def]
  >> simp[listTheory.EL_REVERSE]
  >> irule listTheory.LENGTH_FILTER_LEQ_MONO
  >> simp[]
  >> decide_tac
QED

Theorem source_sorted_reverse_lengths_mono:
  !rows : 'a list list.
    source_sorted ($<=) (REVERSE (MAP LENGTH rows)) ==>
    !left right.
      left < right ==>
      right < LENGTH rows ==>
      LENGTH (EL right rows) <= LENGTH (EL left rows)
Proof
  rpt strip_tac
  >> fs[source_sorted_def,
        sortingTheory.SORTED_EL_LESS,
        relationTheory.transitive_def]
  >> first_x_assum
       (qspecl_then
          [`PRE (LENGTH rows - right)`,
           `PRE (LENGTH rows - left)`]
          mp_tac)
  >> simp[listTheory.EL_REVERSE]
  >> `PRE (LENGTH rows - PRE (LENGTH rows - right)) = right` by
       decide_tac
  >> `PRE (LENGTH rows - PRE (LENGTH rows - left)) = left` by
       decide_tac
  >> simp[listTheory.EL_MAP]
  >> qsuff_tac
       `PRE (LENGTH rows - right) < PRE (LENGTH rows - left)`
  >- simp[]
  >> decide_tac
QED

Theorem source_el_filter_prefix:
  !predicate (xs : 'a list) index.
    (!left right.
       left < right ==>
       right < LENGTH xs ==>
       predicate (EL right xs) ==>
       predicate (EL left xs)) ==>
    index < LENGTH (FILTER predicate xs) ==>
    EL index (FILTER predicate xs) = EL index xs
Proof
  gen_tac
  >> Induct_on `xs`
  >- simp[]
  >> gen_tac
  >> rpt strip_tac
  >> Cases_on `predicate h`
  >- (Cases_on `index`
      >- simp[]
      >> simp[]
      >> first_x_assum irule
      >> rpt strip_tac
      >> first_x_assum
           (qspecl_then [`SUC left`, `SUC right`] mp_tac)
      >> simp[]
      >> strip_tac
      >> fs[])
  >> `FILTER predicate xs = []` by
       (simp[listTheory.FILTER_EQ_NIL,
             listTheory.EVERY_MEM]
        >> rpt strip_tac
        >> `?offset. offset < LENGTH xs /\ EL offset xs = x` by
             metis_tac[listTheory.MEM_EL]
        >> first_x_assum
             (qspecl_then [`0`, `SUC offset`] mp_tac)
        >> simp[])
  >> fs[]
QED

Theorem source_nth_nth_transpose_sorted:
  !rows : 'a list list.
    source_sorted ($<=) (REVERSE (MAP LENGTH rows)) ==>
    !column row.
      column < LENGTH (source_transpose rows) ==>
      row < LENGTH
        (FILTER (\items. column < LENGTH items) rows) ==>
      EL row (EL column (source_transpose rows)) =
      EL column (EL row rows)
Proof
  rpt strip_tac
  >> simp[source_transpose_def]
  >> fs[source_transpose_def]
  >> simp[listTheory.EL_GENLIST, listTheory.EL_MAP]
  >> qsuff_tac
       `EL row
          (FILTER (\items. column < LENGTH items) rows) =
        EL row rows`
  >- simp[]
  >> irule source_el_filter_prefix
  >> conj_tac
  >- (rpt strip_tac
      >> drule source_sorted_reverse_lengths_mono
      >> strip_tac
      >> fs[]
      >> first_x_assum
           (qspecl_then [`left`, `right`] mp_tac)
      >> decide_tac)
  >> simp[]
QED

Theorem source_length_insort_key:
  !le function value xs.
    LENGTH (source_insort_key le function value xs) =
    SUC (LENGTH xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_insort_key_def]
  >> Cases_on `le (function value) (function h)`
  >> simp[]
QED

Theorem source_set_sort_key:
  !le function xs.
    LIST_TO_SET (source_sort_key le function xs) =
    LIST_TO_SET xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_sort_key_def, source_set_insort_key]
QED

Theorem source_length_sort_key:
  !le function xs.
    LENGTH (source_sort_key le function xs) = LENGTH xs
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_sort_key_def, source_length_insort_key]
QED

Theorem source_all_distinct_insort_key:
  !le function value xs.
    (ALL_DISTINCT (source_insort_key le function value xs) <=>
     value NOTIN LIST_TO_SET xs /\ ALL_DISTINCT xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >- simp[source_insort_key_def]
  >> rw[source_insort_key_def]
  >> simp[source_set_insort_key]
  >> metis_tac[]
QED

Theorem source_all_distinct_sort_key:
  !le function xs.
    (ALL_DISTINCT (source_sort_key le function xs) <=>
     ALL_DISTINCT xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >> simp[source_sort_key_def,
          source_all_distinct_insort_key,
          source_set_sort_key]
QED

Theorem source_insort_key_not_nil:
  !le function value xs.
    source_insort_key le function value xs <> []
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >- simp[source_insort_key_def]
  >> (simp[source_insort_key_def]
      THEN IF_CASES_TAC
      THEN simp[])
QED

Theorem source_sort_key_eq_nil:
  !le function xs.
    (source_sort_key le function xs = [] <=> xs = [])
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >> simp[source_sort_key_def, source_insort_key_not_nil]
QED

Definition source_sorted_key_list_of_set_def:
  source_sorted_key_list_of_set le function domain =
    source_sort_key le function (SET_TO_LIST domain)
End

Definition source_sorted_list_of_set_def:
  source_sorted_list_of_set le domain =
    source_sort le (SET_TO_LIST domain)
End

Theorem source_set_sorted_key_list_of_set:
  !le function domain.
    FINITE domain ==>
    LIST_TO_SET
      (source_sorted_key_list_of_set le function domain) = domain
Proof
  simp[source_sorted_key_list_of_set_def,
       source_set_sort_key, listTheory.SET_TO_LIST_INV]
QED

Theorem source_length_sorted_key_list_of_set:
  !le function domain.
    FINITE domain ==>
    LENGTH (source_sorted_key_list_of_set le function domain) =
    CARD domain
Proof
  simp[source_sorted_key_list_of_set_def,
       source_length_sort_key, listTheory.SET_TO_LIST_CARD]
QED

Theorem source_all_distinct_sorted_key_list_of_set:
  !le function domain.
    FINITE domain ==>
    ALL_DISTINCT
      (source_sorted_key_list_of_set le function domain)
Proof
  simp[source_sorted_key_list_of_set_def,
       source_all_distinct_sort_key,
       listTheory.ALL_DISTINCT_SET_TO_LIST]
QED

Theorem source_sorted_sorted_key_list_of_set:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function domain.
      source_sorted le
        (MAP function
          (source_sorted_key_list_of_set le function domain))
Proof
  simp[source_sorted_key_list_of_set_def,
       source_sorted_sort_key]
QED

Theorem source_set_sorted_list_of_set:
  !le domain.
    FINITE domain ==>
    LIST_TO_SET (source_sorted_list_of_set le domain) = domain
Proof
  simp[source_sorted_list_of_set_def, source_sort_def,
       source_set_sort_key, listTheory.SET_TO_LIST_INV]
QED

Theorem source_length_sorted_list_of_set:
  !le domain.
    FINITE domain ==>
    LENGTH (source_sorted_list_of_set le domain) = CARD domain
Proof
  simp[source_sorted_list_of_set_def, source_sort_def,
       source_length_sort_key, listTheory.SET_TO_LIST_CARD]
QED

Theorem source_all_distinct_sorted_list_of_set:
  !le domain.
    FINITE domain ==>
    ALL_DISTINCT (source_sorted_list_of_set le domain)
Proof
  simp[source_sorted_list_of_set_def, source_sort_def,
       source_all_distinct_sort_key,
       listTheory.ALL_DISTINCT_SET_TO_LIST]
QED

Theorem source_sorted_sorted_list_of_set:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !domain. source_sorted le (source_sorted_list_of_set le domain)
Proof
  simp[source_sorted_list_of_set_def, source_sorted_sort]
QED

Theorem source_sorted_list_of_set_unique:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !domain target.
      FINITE domain ==>
      source_sorted le target ==>
      ALL_DISTINCT target ==>
      LIST_TO_SET target = domain ==>
      source_sorted_list_of_set le domain = target
Proof
  metis_tac[source_sorted_def,
            source_weak_linear_transitive,
            source_weak_linear_antisymmetric,
            source_sorted_sorted_list_of_set,
            source_all_distinct_sorted_list_of_set,
            source_set_sorted_list_of_set,
            sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ]
QED

Theorem source_sorted_key_list_of_set_eq_nil:
  !le function domain.
    FINITE domain ==>
    (source_sorted_key_list_of_set le function domain = [] <=>
     domain = EMPTY)
Proof
  simp[source_sorted_key_list_of_set_def,
       source_sort_key_eq_nil,
       listTheory.SET_TO_LIST_EMPTY_IFF]
QED

Definition source_minimum_def:
  source_minimum le domain =
    HD (source_sorted_list_of_set le domain)
End

Theorem source_sorted_list_of_set_nonempty:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !items.
      FINITE items ==>
      items <> EMPTY ==>
      source_sorted_list_of_set le items =
      source_minimum le items ::
        source_sorted_list_of_set le
          (items DELETE source_minimum le items)
Proof
  rpt strip_tac
  >> qabbrev_tac `xs = source_sorted_list_of_set le items`
  >> Cases_on `xs`
  >- metis_tac[source_sorted_key_list_of_set_eq_nil,
                source_sorted_list_of_set_def,
                source_sort_def,
                source_sorted_key_list_of_set_def]
  >> `source_minimum le items = h` by
       simp[source_minimum_def]
  >> simp[]
  >> qsuff_tac
       `source_sorted_list_of_set le (items DELETE h) = t`
  >- simp[]
  >> irule source_sorted_list_of_set_unique
  >> fs[source_sorted_def]
  >> `ALL_DISTINCT (h::t)` by
       metis_tac[source_all_distinct_sorted_list_of_set]
  >> `LIST_TO_SET (h::t) = items` by
       metis_tac[source_set_sorted_list_of_set]
  >> `source_sorted le (h::t)` by
       metis_tac[source_sorted_sorted_list_of_set]
  >> fs[source_sorted_def]
  >> conj_tac
  >- (rw[pred_setTheory.EXTENSION] >> metis_tac[])
  >> metis_tac[sortingTheory.SORTED_TL]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:3581-3700.  Isabelle's internal numeral type
   denotes positive numerals; SUC is its total HOL4 representation.
   The inclusive integer interval is kept benchmark-local. *)
Definition source_numeral_def:
  source_numeral n = SUC n
End

Theorem source_numeral_bridge:
  !m. 0 < m <=> ?n. m = source_numeral n
Proof
  Cases
  >> simp[source_numeral_def]
QED

Definition source_upto_def:
  source_upto (i : int) j =
    if j < i then [] else i :: source_upto (i + 1) j
Termination
  WF_REL_TAC `measure (\(i,j). Num (j - i + 1))`
  >> simp[]
  >> intLib.ARITH_TAC
End

Theorem source_upto_empty:
  !i j. j < i ==> source_upto i j = []
Proof
  rpt strip_tac
  >> rw[Once source_upto_def]
  >> intLib.ARITH_TAC
QED

Theorem source_upto_single:
  !i. source_upto i i = [i]
Proof
  rw[Once source_upto_def]
  >> simp[source_upto_empty]
QED

Theorem source_upto_nil:
  !i j. source_upto i j = [] <=> j < i
Proof
  rw[Once source_upto_def]
QED

Theorem source_upto_rec1:
  !i j. i <= j ==>
    source_upto i j = i :: source_upto (i + 1) j
Proof
  rpt strip_tac
  >> rw[Once source_upto_def]
  >> intLib.ARITH_TAC
QED

Theorem source_upto_rec2:
  !i j. i <= j ==>
    source_upto i j = source_upto i (j - 1) ++ [j]
Proof
  ho_match_mp_tac source_upto_ind
  >> rw[Once source_upto_def]
  >- (`i = j` by intLib.ARITH_TAC
      >> `source_upto i (j - 1) = []` by
           (irule source_upto_empty >> intLib.ARITH_TAC)
      >> fs[source_upto_single])
  >> `i + 1 <= j` by intLib.ARITH_TAC
  >> `~(j < i)` by intLib.ARITH_TAC
  >> `source_upto i (j - 1) =
      i :: source_upto (i + 1) (j - 1)` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> rw[Once source_upto_rec1]
  >> fs[]
  >> rw[Once source_upto_rec1]
  >> fs[]
QED

Theorem source_num_step:
  !i j : int. i < j ==>
    Num (j - i) = SUC (Num (j - (i + 1)))
Proof
  rpt strip_tac
  >> `0 <= j - i` by intLib.ARITH_TAC
  >> `0 <= j - (i + 1)` by intLib.ARITH_TAC
  >> `&(Num (j - i)) = j - i` by
       simp[integerTheory.INT_OF_NUM]
  >> `&(Num (j - (i + 1))) = j - (i + 1)` by
       simp[integerTheory.INT_OF_NUM]
  >> intLib.ARITH_TAC
QED

Theorem source_int_genlist_cons:
  !i : int. !n.
    GENLIST (\k. i + &k) (SUC n) =
    i :: GENLIST (\k. i + 1 + &k) n
Proof
  rw[listTheory.GENLIST_CONS, combinTheory.o_DEF]
  >> rw[listTheory.GENLIST_FUN_EQ]
  >> intLib.ARITH_TAC
QED

Theorem source_int_lt_add1:
  !x y : int. x < y + 1 <=> x <= y
Proof
  intLib.ARITH_TAC
QED

Theorem source_int_le_antisym_imp:
  !x y : int. x <= y ==> y <= x ==> x = y
Proof
  intLib.ARITH_TAC
QED

Theorem source_int_le_cases:
  !x y : int. x <= y ==> x = y \/ x + 1 <= y
Proof
  intLib.ARITH_TAC
QED

Theorem source_upto_closed:
  !i j.
    source_upto i j =
    if j < i then []
    else GENLIST (\n. i + &n) (SUC (Num (j - i)))
Proof
  ho_match_mp_tac source_upto_ind
  >> rw[Once source_upto_def]
  >> TRY (qpat_x_assum `j < i` mp_tac
          >> simp[source_upto_empty])
  >> TRY (`i = j` by intLib.ARITH_TAC
          >> fs[source_upto_single, listTheory.GENLIST_CONS])
  >> `i < j` by intLib.ARITH_TAC
  >> `Num (j - i) = SUC (Num (j - (i + 1)))` by
       metis_tac[source_num_step]
  >> `i + 1 <= j` by intLib.ARITH_TAC
  >> fs[listTheory.GENLIST_CONS, combinTheory.o_DEF]
  >> `source_upto (i + 1) j =
      (i + 1) :: source_upto (i + 1 + 1) j` by
       metis_tac[source_upto_rec1]
  >> `source_upto i j = i :: source_upto (i + 1) j` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> fs[]
  >> rw[listTheory.GENLIST_FUN_EQ]
  >> intLib.ARITH_TAC
QED

Theorem source_upto_split1:
  !i j. !k. i <= j ==> j <= k ==>
    source_upto i k =
    source_upto i (j - 1) ++ source_upto j k
Proof
  ho_match_mp_tac source_upto_ind
  >> rw[]
  >> Cases_on `i = j`
  >- (`source_upto i (j - 1) = []` by
        (irule source_upto_empty >> intLib.ARITH_TAC)
      >> fs[])
  >> `i + 1 <= j` by intLib.ARITH_TAC
  >> `~(j < i)` by intLib.ARITH_TAC
  >> `source_upto i k = i :: source_upto (i + 1) k` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> `source_upto i (j - 1) =
      i :: source_upto (i + 1) (j - 1)` by
       (irule source_upto_rec1 >> intLib.ARITH_TAC)
  >> `source_upto (i + 1) k =
      source_upto (i + 1) (j - 1) ++ source_upto j k` by
       metis_tac[]
  >> metis_tac[listTheory.APPEND]
QED

(* An explicit name for the predecessor lets the classical rule matcher
   choose a split point before integer normalization discharges the side
   equation. *)
Theorem source_upto_split_boundary:
  !i left pivot k : int.
    i <= pivot ==> pivot <= k ==> left = pivot - 1 ==>
    source_upto i k =
    source_upto i left ++ source_upto pivot k
Proof
  metis_tac[source_upto_split1]
QED

Theorem source_append_cons_cut:
  !whole prefix tail head rest.
    whole = prefix ++ tail ==>
    tail = head::rest ==>
    whole = prefix ++ [head] ++ rest
Proof
  simp[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:4241-4252 and 4314-4451. *)
Definition source_successively_def:
  source_successively relation xs =
    !left right. adjacent xs left right ==> relation left right
End

Definition source_distinct_adj_def:
  source_distinct_adj xs =
    source_successively (\left right. left <> right) xs
End

Definition source_inj_on_def:
  source_inj_on function set =
    !left right.
      left IN set ==> right IN set ==>
      function left = function right ==> left = right
End

Theorem source_inj_on_bridge:
  !function set.
    source_inj_on function set <=>
    !left right.
      left IN set ==> right IN set ==>
      function left = function right ==> left = right
Proof
  simp[source_inj_on_def]
QED

Theorem source_all_distinct_map_sorted_key_list_of_set:
  !le function source domain.
    source_inj_on function source ==>
    domain SUBSET source ==>
    FINITE domain ==>
    ALL_DISTINCT
      (MAP function
        (source_sorted_key_list_of_set le function domain))
Proof
  rpt strip_tac
  >> irule listTheory.ALL_DISTINCT_MAP_INJ
  >> conj_tac
  >- (rpt strip_tac
      >> fs[source_inj_on_def]
      >> first_x_assum irule
      >> fs[pred_setTheory.SUBSET_DEF]
      >> metis_tac[source_set_sorted_key_list_of_set])
  >> simp[source_all_distinct_sorted_key_list_of_set]
QED

Theorem source_map_sorted_distinct_set_unique:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !function xs ys.
      source_inj_on function
        (LIST_TO_SET xs UNION LIST_TO_SET ys) ==>
      source_sorted le (MAP function xs) ==>
      ALL_DISTINCT (MAP function xs) ==>
      source_sorted le (MAP function ys) ==>
      ALL_DISTINCT (MAP function ys) ==>
      LIST_TO_SET xs = LIST_TO_SET ys ==>
      xs = ys
Proof
  rpt strip_tac
  >> irule listTheory.INJ_MAP_EQ
  >> qexists_tac `function`
  >> conj_tac
  >- (irule sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ
      >> simp[listTheory.LIST_TO_SET_MAP]
      >> qexists_tac `le`
      >> fs[source_sorted_def,
            source_weak_linear_transitive,
            source_weak_linear_antisymmetric])
  >> fs[pred_setTheory.INJ_DEF, source_inj_on_def]
QED

Theorem source_inj_on_union_subset:
  !function source left right.
    source_inj_on function source ==>
    left SUBSET source ==>
    right SUBSET source ==>
    source_inj_on function (left UNION right)
Proof
  simp[source_inj_on_def, pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_sorted_key_list_of_set_eq:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !source function domain target.
      source_inj_on function source ==>
      domain SUBSET source ==>
      FINITE domain ==>
      source_sorted le (MAP function target) ==>
      ALL_DISTINCT (MAP function target) ==>
      LIST_TO_SET target = domain ==>
      source_sorted_key_list_of_set le function domain = target
Proof
  rpt strip_tac
  >> irule source_map_sorted_distinct_set_unique
  >> conj_tac
  >- metis_tac[source_set_sorted_key_list_of_set]
  >> qexists_tac `function`
  >> qexists_tac `le`
  >> metis_tac[source_inj_on_union_subset,
                source_all_distinct_map_sorted_key_list_of_set,
                source_sorted_sorted_key_list_of_set,
                source_set_sorted_key_list_of_set]
QED

Theorem source_sorted_key_list_of_set_unique:
  !le : 'b -> 'b -> bool.
    relation$WeakLinearOrder le ==>
    !source function domain target.
      source_inj_on function source ==>
      domain SUBSET source ==>
      FINITE domain ==>
      (source_strict_sorted le (MAP function target) /\
       LIST_TO_SET target = domain /\
       LENGTH target = CARD domain <=>
       source_sorted_key_list_of_set le function domain = target)
Proof
  rpt strip_tac
  >> eq_tac
  >- (strip_tac
      >> metis_tac[source_strict_sorted_iff,
                    source_sorted_key_list_of_set_eq])
  >> strip_tac
  >> fs[]
  >> metis_tac[source_strict_sorted_iff,
                source_all_distinct_map_sorted_key_list_of_set,
                source_sorted_sorted_key_list_of_set,
                source_set_sorted_key_list_of_set,
                source_length_sorted_key_list_of_set]
QED

Theorem source_successively_bridge:
  !relation xs.
    source_successively relation xs <=>
    !left right. adjacent xs left right ==> relation left right
Proof
  simp[source_successively_def]
QED

Theorem source_successively_nil:
  !relation. source_successively relation []
Proof
  simp[source_successively_def]
QED

Theorem source_successively_singleton:
  !relation x. source_successively relation [x]
Proof
  simp[source_successively_def]
QED

Theorem source_successively_cons_cons:
  !relation x y xs.
    source_successively relation (x::y::xs) <=>
    relation x y /\ source_successively relation (y::xs)
Proof
  simp[source_successively_def, listTheory.adjacent_iff]
  >> metis_tac[]
QED

Theorem source_successively_conv_nth:
  !relation xs.
    source_successively relation xs <=>
    !i. i + 1 < LENGTH xs ==>
      relation (EL i xs) (EL (i + 1) xs)
Proof
  simp[source_successively_def, listTheory.adjacent_EL]
  >> metis_tac[]
QED

Theorem source_adjacent_append:
  !xs ys left right.
    adjacent (xs ++ ys) left right <=>
    adjacent xs left right \/ adjacent ys left right \/
    (xs <> [] /\ ys <> [] /\
     left = LAST xs /\ right = HD ys)
Proof
  Induct
  >- simp[]
  >> Cases_on `xs`
  >- (Cases_on `ys`
      >> simp[listTheory.adjacent_iff]
      >> metis_tac[])
  >> simp[listTheory.adjacent_iff]
  >> rpt gen_tac
  >> first_x_assum
       (qspecl_then [`ys`, `left`, `right`] mp_tac)
  >> simp[]
  >> metis_tac[]
QED

Theorem source_successively_append_iff:
  !relation xs ys.
    source_successively relation (xs ++ ys) <=>
    source_successively relation xs /\
    source_successively relation ys /\
    (xs = [] \/ ys = [] \/ relation (LAST xs) (HD ys))
Proof
  simp[source_successively_def, source_adjacent_append]
  >> metis_tac[]
QED

Theorem source_successively_map:
  !relation function xs.
    source_successively relation (MAP function xs) <=>
    !left right. adjacent xs left right ==>
      relation (function left) (function right)
Proof
  simp[source_successively_def, listTheory.adjacent_MAP]
  >> metis_tac[]
QED

Theorem source_distinct_adj_mapI:
  !function xs.
    source_distinct_adj xs ==>
    source_inj_on function (LIST_TO_SET xs) ==>
    source_distinct_adj (MAP function xs)
Proof
  simp[source_distinct_adj_def, source_successively_map,
       source_successively_def, source_inj_on_def]
  >> metis_tac[listTheory.adjacent_MEM]
QED

Theorem source_distinct_adj_mapD:
  !function xs.
    source_distinct_adj (MAP function xs) ==>
    source_distinct_adj xs
Proof
  simp[source_distinct_adj_def, source_successively_map,
       source_successively_def]
  >> metis_tac[]
QED

Theorem source_distinct_adj_conv_nth:
  !xs.
    source_distinct_adj xs <=>
    !i. i + 1 < LENGTH xs ==> EL i xs <> EL (i + 1) xs
Proof
  simp[source_distinct_adj_def, source_successively_conv_nth]
QED

Theorem source_distinct_adj_append_iff:
  !xs ys.
    source_distinct_adj (xs ++ ys) <=>
    source_distinct_adj xs /\ source_distinct_adj ys /\
    (xs = [] \/ ys = [] \/ LAST xs <> HD ys)
Proof
  simp[source_distinct_adj_def, source_successively_append_iff]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:233-245 and 4654-4858. *)
Definition source_remove1_def:
  (source_remove1 value [] = []) /\
  (source_remove1 value (head::tail) =
     if value = head then tail
     else head::source_remove1 value tail)
End

Definition source_removeAll_def:
  (source_removeAll value [] = []) /\
  (source_removeAll value (head::tail) =
     if value = head then source_removeAll value tail
     else head::source_removeAll value tail)
End

Theorem source_removeAll_bridge:
  !value xs.
    source_removeAll value xs =
    rich_list$DELETE_ELEMENT value xs
Proof
  Induct_on `xs`
  >> simp[source_removeAll_def, rich_listTheory.DELETE_ELEMENT]
QED

Theorem source_remove1_mem:
  !removed xs value.
    MEM value (source_remove1 removed xs) ==>
    MEM value xs
Proof
  Induct_on `xs`
  >- simp[source_remove1_def]
  >> simp[source_remove1_def]
  >> rpt gen_tac
  >> Cases_on `removed = h`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_removeAll_filter:
  !value xs.
    source_removeAll value xs = FILTER ((<>) value) xs
Proof
  simp[source_removeAll_bridge,
       rich_listTheory.DELETE_ELEMENT_FILTER]
QED

Theorem source_remove1_commute:
  !left right xs.
    source_remove1 left (source_remove1 right xs) =
    source_remove1 right (source_remove1 left xs)
Proof
  Induct_on `xs`
  >> rw[source_remove1_def]
  >> metis_tac[]
QED

Theorem source_removeAll_commute:
  !left right xs.
    source_removeAll left (source_removeAll right xs) =
    source_removeAll right (source_removeAll left xs)
Proof
  Induct_on `xs`
  >> rw[source_removeAll_def]
  >> metis_tac[]
QED

Definition source_foldr_def:
  source_foldr operation xs initial = FOLDR operation initial xs
End

Definition source_fold_def:
  source_fold operation xs initial =
    FOLDL (\current element. operation element current) initial xs
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:3400-3438. *)
Theorem source_foldr_conv_fold:
  !operation xs initial.
    FOLDR operation initial xs =
    source_fold operation (REVERSE xs) initial
Proof
  simp[source_fold_def,
       rich_listTheory.FOLDR_FOLDL_REVERSE]
QED

Theorem source_foldl_conv_fold:
  !operation xs initial.
    FOLDL operation initial xs =
    source_fold
      (\value current. operation current value) xs initial
Proof
  rpt gen_tac
  >> rw[source_fold_def]
  >> `(\current value. operation current value) = operation` by
       simp[FUN_EQ_THM]
  >> simp[]
QED

Theorem source_fold_eta:
  !operation xs initial.
    source_fold
      (\value current. operation value current) xs initial =
    source_fold operation xs initial
Proof
  rpt gen_tac
  >> `(\value current. operation value current) = operation` by
       simp[FUN_EQ_THM]
  >> simp[]
QED

Theorem source_fold_append:
  !operation xs ys initial.
    source_fold operation (xs ++ ys) initial =
    source_fold operation ys (source_fold operation xs initial)
Proof
  simp[source_fold_def, rich_listTheory.FOLDL_APPEND]
QED

(* src/HOL/List.thy:3283-3287, fold_Cons_rev. *)
Theorem source_fold_Cons_rev:
  !xs initial.
    source_fold CONS xs initial = REVERSE xs ++ initial
Proof
  `(\element current. element::current) = CONS` by
    simp[FUN_EQ_THM]
  >> simp[source_fold_def,
          rich_listTheory.FOLDL_FOLDR_REVERSE,
          rich_listTheory.APPEND_FOLDR]
QED

Theorem source_fold_filter:
  !operation predicate xs initial.
    source_fold operation (FILTER predicate xs) initial =
    source_fold
      (\value current.
         if predicate value then operation value current else current)
      xs initial
Proof
  simp[source_fold_def, rich_listTheory.FOLDL_FILTER]
QED

Theorem source_fold_map_eta:
  !operation function xs initial.
    source_fold
      (\value current. operation (function value) current) xs initial =
    source_fold (\value. operation (function value)) xs initial
Proof
  rpt gen_tac
  >> `(\value current. operation (function value) current) =
      (\value. operation (function value))` by
       simp[FUN_EQ_THM]
  >> simp[]
QED

Theorem source_fold_filter_eta:
  !operation predicate xs initial.
    source_fold
      (\value current.
         if predicate value then operation value current else current)
      xs initial =
    source_fold
      (\value. if predicate value then operation value else I)
      xs initial
Proof
  rpt gen_tac
  >> `(\value current.
         if predicate value then operation value current else current) =
      (\value. if predicate value then operation value else I)` by
       (rw[FUN_EQ_THM]
        >> Cases_on `predicate value`
        >> simp[])
  >> simp[]
QED

Theorem source_fold_cong:
  !left right xs initial.
    (!current value.
       MEM value xs ==>
       left value current = right value current) ==>
    source_fold left xs initial = source_fold right xs initial
Proof
  rpt strip_tac
  >> rw[source_fold_def]
  >> irule listTheory.FOLDL_CONG
  >> simp[]
QED

Theorem source_fold_append_concat_rev:
  !xss.
    FLAT xss = source_fold APPEND (REVERSE xss) []
Proof
  Induct
  >- simp[source_fold_def]
  >> simp[source_fold_def, listTheory.REVERSE_DEF,
          rich_listTheory.FOLDL_APPEND]
QED

Definition source_INF_def:
  source_INF aggregate function domain =
    aggregate (IMAGE function domain)
End

Definition source_SUP_def:
  source_SUP aggregate function domain =
    aggregate (IMAGE function domain)
End

Theorem source_fold_map:
  !operation function xs initial.
    source_fold operation (MAP function xs) initial =
    source_fold
      (\value current. operation (function value) current)
      xs initial
Proof
  simp[source_fold_def, rich_listTheory.FOLDL_MAP]
QED

Theorem source_INF_set_fold:
  !aggregate operation top function xs.
    (!ys.
       aggregate (LIST_TO_SET ys) =
       source_fold operation ys top) ==>
    source_INF aggregate function (LIST_TO_SET xs) =
    source_fold
      (\value current. operation (function value) current)
      xs top
Proof
  rpt strip_tac
  >> first_x_assum (qspec_then `MAP function xs` mp_tac)
  >> simp[source_INF_def, listTheory.LIST_TO_SET_MAP,
          source_fold_map]
QED

Theorem source_SUP_set_fold:
  !aggregate operation bottom function xs.
    (!ys.
       aggregate (LIST_TO_SET ys) =
       source_fold operation ys bottom) ==>
    source_SUP aggregate function (LIST_TO_SET xs) =
    source_fold
      (\value current. operation (function value) current)
      xs bottom
Proof
  rpt strip_tac
  >> first_x_assum (qspec_then `MAP function xs` mp_tac)
  >> simp[source_SUP_def, listTheory.LIST_TO_SET_MAP,
          source_fold_map]
QED

Theorem source_fold_commute:
  !operation.
    (!left right current.
       operation left (operation right current) =
       operation right (operation left current)) ==>
    !xs value current.
      source_fold operation xs (operation value current) =
      operation value (source_fold operation xs current)
Proof
  gen_tac
  >> strip_tac
  >> Induct
  >> simp[source_fold_def]
  >> rpt gen_tac
  >> fs[source_fold_def]
QED

Theorem source_foldr_fold:
  !operation.
    (!left right current.
       operation left (operation right current) =
       operation right (operation left current)) ==>
    source_foldr operation = source_fold operation
Proof
  gen_tac
  >> strip_tac
  >> rw[FUN_EQ_THM]
  >> Induct_on `x`
  >> simp[source_foldr_def, source_fold_def]
  >> rpt gen_tac
  >> fs[source_foldr_def, source_fold_def]
  >> once_rewrite_tac[GSYM source_fold_def]
  >> irule EQ_SYM
  >> irule source_fold_commute
  >> simp[]
QED

Definition source_minus_list_mset_def:
  source_minus_list_mset xs ys =
    source_foldr source_remove1 ys xs
End

Definition source_minus_list_set_def:
  source_minus_list_set xs ys =
    source_foldr source_removeAll ys xs
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:226-231 and 4626-4650.  SPLITP is the HOL4
   representation of the source takeWhile/dropWhile decomposition. *)
Definition source_extract_def:
  source_extract predicate xs =
    case SND (rich_list$SPLITP predicate xs) of
      [] => NONE
    | head::tail =>
        SOME (FST (rich_list$SPLITP predicate xs), head, tail)
End

Theorem source_extract_splitp_bridge:
  !predicate xs prefix rest.
    rich_list$SPLITP predicate xs = (prefix, rest) ==>
    (source_extract predicate xs =
     case rest of
       [] => NONE
     | head::tail => SOME (prefix, head, tail))
Proof
  simp[source_extract_def]
QED

Theorem source_extract_rec:
  (source_extract predicate [] = NONE) /\
  (!head tail.
    source_extract predicate (head::tail) =
    if predicate head then SOME ([], head, tail)
    else
      case source_extract predicate tail of
        NONE => NONE
      | SOME (prefix, value, suffix) =>
          SOME (head::prefix, value, suffix))
Proof
  conj_tac
  >- simp[source_extract_def, rich_listTheory.SPLITP]
  >> rpt gen_tac
  >> rw[source_extract_def, rich_listTheory.SPLITP]
  >> Cases_on `rich_list$SPLITP predicate tail`
  >> Cases_on `r`
  >> simp[source_extract_def]
QED

Theorem source_extract_none_splitp:
  !predicate xs.
    (source_extract predicate xs = NONE <=>
     SND (rich_list$SPLITP predicate xs) = [])
Proof
  simp[source_extract_def]
  >> Cases_on `SND (rich_list$SPLITP predicate xs)`
  >> simp[]
QED

Theorem source_extract_some_splitp:
  !predicate xs prefix value suffix.
    (source_extract predicate xs = SOME (prefix, value, suffix) <=>
     rich_list$SPLITP predicate xs =
       (prefix, value::suffix))
Proof
  rpt gen_tac
  >> Cases_on `rich_list$SPLITP predicate xs`
  >> Cases_on `r`
  >> simp[source_extract_def]
QED

Theorem source_splitp_none:
  !predicate xs.
    (SND (rich_list$SPLITP predicate xs) = [] <=>
     ~(?value. MEM value xs /\ predicate value))
Proof
  Induct_on `xs`
  >> rw[rich_listTheory.SPLITP]
  >> Cases_on `rich_list$SPLITP predicate xs`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_splitp_first:
  !predicate prefix value suffix.
    predicate value ==>
    ~(?item. MEM item prefix /\ predicate item) ==>
    rich_list$SPLITP predicate (prefix ++ value::suffix) =
      (prefix, value::suffix)
Proof
  rpt strip_tac
  >> `EVERY ($~ o predicate) prefix` by
       (rw[listTheory.EVERY_MEM, combinTheory.o_DEF]
        >> metis_tac[])
  >> `rich_list$SPLITP predicate prefix = (prefix, [])` by
       simp[rich_listTheory.SPLITP_NIL_SND_EVERY]
  >> simp[rich_listTheory.SPLITP_APPEND,
          listTheory.EXISTS_MEM, rich_listTheory.SPLITP]
QED

Theorem source_splitp_someD:
  !predicate xs prefix value suffix.
    rich_list$SPLITP predicate xs =
      (prefix, value::suffix) ==>
    xs = prefix ++ value::suffix /\ predicate value /\
    ~(?item. MEM item prefix /\ predicate item)
Proof
  rpt gen_tac
  >> disch_tac
  >> imp_res_tac rich_listTheory.SPLITP_JOIN
  >> imp_res_tac rich_listTheory.SPLITP_IMP
  >> conj_tac
  >- fs[]
  >> conj_tac
  >- fs[]
  >> rw[]
  >> qpat_x_assum `EVERY _ prefix` mp_tac
  >> simp[listTheory.EVERY_MEM, combinTheory.o_DEF]
  >> metis_tac[]
QED

Theorem source_splitp_some:
  !predicate xs prefix value suffix.
    (rich_list$SPLITP predicate xs =
       (prefix, value::suffix) <=>
     xs = prefix ++ value::suffix /\ predicate value /\
     ~(?item. MEM item prefix /\ predicate item))
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[source_splitp_someD]
  >> rpt strip_tac
  >> qpat_x_assum `xs = _` SUBST1_TAC
  >> irule source_splitp_first
  >> simp[]
  >> metis_tac[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:247-248 and 5125-5182. *)
Definition source_indexed_from_def:
  (source_indexed_from (start : num) [] = []) /\
  (source_indexed_from (start : num) (head::tail) =
     (start, head)::source_indexed_from (start + 1) tail)
End

Theorem source_indexed_from_bridge:
  !start xs.
    source_indexed_from start xs =
    ZIP (GENLIST (\offset. start + offset) (LENGTH xs), xs)
Proof
  Induct_on `xs`
  >> simp[source_indexed_from_def, listTheory.GENLIST_CONS,
          combinTheory.o_DEF]
  >> gen_tac
  >> AP_TERM_TAC
  >> simp[]
  >> rw[listTheory.GENLIST_FUN_EQ]
  >> decide_tac
QED

Theorem source_indexed_from_append_bridge:
  !start xs ys.
    source_indexed_from start (xs ++ ys) =
    source_indexed_from start xs ++
    source_indexed_from (start + LENGTH xs) ys
Proof
  Induct_on `xs`
  >- simp[source_indexed_from_def]
  >> rpt gen_tac
  >> simp_tac bool_ss
       [listTheory.APPEND, source_indexed_from_def, listTheory.LENGTH]
  >> asm_rewrite_tac[]
  >> ntac 2 AP_TERM_TAC
  >> AP_THM_TAC
  >> AP_TERM_TAC
  >> decide_tac
QED

Theorem source_num_genlist_append:
  !start left right.
    GENLIST (\offset. start + offset) (left + right) =
    GENLIST (\offset. start + offset) left ++
    GENLIST (\offset. start + left + offset) right
Proof
  rpt gen_tac
  >> SUBST1_TAC
       (SPECL [``left : num``, ``right : num``]
          arithmeticTheory.ADD_COMM)
  >> rw[listTheory.GENLIST_APPEND, listTheory.GENLIST_FUN_EQ]
QED

Theorem source_num_genlist_distinct:
  !start count.
    ALL_DISTINCT (GENLIST (\offset. start + offset) count)
Proof
  simp[listTheory.ALL_DISTINCT_GENLIST]
  >> decide_tac
QED

Theorem source_num_genlist_zip_distinct:
  !start xs.
    ALL_DISTINCT
      (ZIP (GENLIST (\offset. start + offset) (LENGTH xs), xs))
Proof
  rpt gen_tac
  >> irule listTheory.ALL_DISTINCT_ZIP
  >> simp[source_num_genlist_distinct]
QED

Theorem source_zip_append1:
  !xs ys us vs.
    LENGTH xs = LENGTH us ==>
    ZIP (xs ++ ys, us ++ vs) = ZIP (xs, us) ++ ZIP (ys, vs)
Proof
  Induct_on `xs`
  >- (Cases_on `us` >> simp[listTheory.ZIP_def])
  >> Cases_on `us`
  >> simp[listTheory.ZIP_def]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/List.thy:2794-2804.  The following zip-map lemmas use this
   independently proved, more general result through a `using` fact. *)
Theorem source_zip_map_map:
  !xs ys f g.
    ZIP (MAP f xs, MAP g ys) =
    MAP (\pair. (f (FST pair), g (SND pair))) (ZIP (xs, ys))
Proof
  Induct_on `xs`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_map1:
  !xs ys f.
    ZIP (MAP f xs, ys) =
    MAP (UNCURRY (\x y. (f x, y))) (ZIP (xs, ys))
Proof
  Induct_on `xs`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_map2:
  !xs ys f.
    ZIP (xs, MAP f ys) =
    MAP (UNCURRY (\x y. (x, f y))) (ZIP (xs, ys))
Proof
  Induct_on `xs`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `ys`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_zip_rev:
  !xs ys.
    LENGTH xs = LENGTH ys ==>
    ZIP (REVERSE xs, REVERSE ys) = REVERSE (ZIP (xs, ys))
Proof
  metis_tac[rich_listTheory.REVERSE_ZIP]
QED

Theorem source_el_zip_min:
  !xs ys index.
    index < MIN (LENGTH xs) (LENGTH ys) ==>
    EL index (ZIP (xs, ys)) = (EL index xs, EL index ys)
Proof
  Induct_on `xs`
  >- simp[]
  >> Cases_on `ys`
  >- simp[]
  >> Cases_on `index`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_fst_el_zip_min:
  !xs ys index.
    index < LENGTH xs /\ index < LENGTH ys ==>
    FST (EL index (ZIP (xs, ys))) = EL index xs
Proof
  rpt strip_tac
  >> `index < MIN (LENGTH xs) (LENGTH ys)` by simp[]
  >> simp[source_el_zip_min]
QED

Theorem source_snd_el_zip_min:
  !xs ys index.
    index < LENGTH xs /\ index < LENGTH ys ==>
    SND (EL index (ZIP (xs, ys))) = EL index ys
Proof
  rpt strip_tac
  >> `index < MIN (LENGTH xs) (LENGTH ys)` by simp[]
  >> simp[source_el_zip_min]
QED

Theorem source_set_conv_nth:
  !xs value.
    LIST_TO_SET xs value <=>
    ?index. value = EL index xs /\ index < LENGTH xs
Proof
  ACCEPT_TAC
    (PURE_ONCE_REWRITE_RULE [boolTheory.CONJ_COMM]
       (SIMP_RULE bool_ss [pred_setTheory.IN_APP]
       listTheory.MEM_EL))
QED

Theorem source_update_zip:
  !xs ys index pair.
    LUPDATE pair index (ZIP (xs, ys)) =
    ZIP (LUPDATE (FST pair) index xs,
         LUPDATE (SND pair) index ys)
Proof
  Induct_on `ys`
  >> Cases_on `xs`
  >> Cases_on `index`
  >> Cases_on `pair`
  >> simp[listTheory.ZIP_def, listTheory.LUPDATE_def]
QED

Theorem source_set_zip_leftD:
  !xs ys left right.
    (left, right) IN LIST_TO_SET (ZIP (xs, ys)) ==>
    left IN LIST_TO_SET xs
Proof
  simp[pred_setTheory.IN_APP, source_set_conv_nth]
  >> rpt gen_tac
  >> strip_tac
  >> qexists_tac `index`
  >> fs[]
  >> `EL index (ZIP (xs, ys)) =
      (EL index xs, EL index ys)` by
       (irule source_el_zip_min >> simp[])
  >> fs[]
QED

Theorem source_set_zip_rightD:
  !xs ys left right.
    (left, right) IN LIST_TO_SET (ZIP (xs, ys)) ==>
    right IN LIST_TO_SET ys
Proof
  simp[pred_setTheory.IN_APP, source_set_conv_nth]
  >> rpt gen_tac
  >> strip_tac
  >> qexists_tac `index`
  >> fs[]
  >> `EL index (ZIP (xs, ys)) =
      (EL index xs, EL index ys)` by
       (irule source_el_zip_min >> simp[])
  >> fs[]
QED

Theorem source_inj_on_nth:
  !xs.
    ALL_DISTINCT xs ==>
    INJ (\index. EL index xs) (count (LENGTH xs)) UNIV
Proof
  simp[pred_setTheory.INJ_DEF, pred_setTheory.IN_COUNT]
  >> metis_tac[listTheory.ALL_DISTINCT_EL_IMP]
QED

Theorem source_nth_eq_iff_index_eq:
  !xs first second.
    ALL_DISTINCT xs ==>
    first < LENGTH xs ==>
    second < LENGTH xs ==>
    (EL first xs = EL second xs <=> first = second)
Proof
  metis_tac[listTheory.ALL_DISTINCT_EL_IMP]
QED

Theorem source_set_update_subset_insert:
  !xs index replacement value.
    value IN LIST_TO_SET (LUPDATE replacement index xs) ==>
    value = replacement \/ value IN LIST_TO_SET xs
Proof
  metis_tac[listTheory.MEM_LUPDATE_E]
QED

Theorem source_subsetD:
  !source target value.
    source SUBSET target ==>
    value IN source ==>
    value IN target
Proof
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem source_sorted_remove1:
  !le : 'a -> 'a -> bool.
    relation$WeakLinearOrder le ==>
    !value xs.
      source_sorted le xs ==>
      source_sorted le (source_remove1 value xs)
Proof
  gen_tac
  >> strip_tac
  >> gen_tac
  >> Induct_on `xs`
  >- simp[source_sorted_def, source_remove1_def]
  >> simp[source_remove1_def]
  >> Cases_on `value = h`
  >> fs[source_sorted_def, sortingTheory.SORTED_EQ,
        source_weak_linear_transitive]
  >> metis_tac[source_remove1_mem]
QED

Theorem source_sorted_indexed_from:
  !start xs.
    source_sorted ($<=)
      (MAP FST (source_indexed_from start xs))
Proof
  rpt gen_tac
  >> rw[source_indexed_from_bridge]
  >> simp[source_sorted_def, listTheory.MAP_ZIP]
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[]
  >> `(\offset. offset + start) = $+ start` by
       simp[FUN_EQ_THM, arithmeticTheory.ADD_COMM]
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

(* Isabelle/HOL src/HOL/List.thy:6208-6212. *)
Definition source_num_upto_def:
  source_num_upto lower upper =
    if upper < lower then []
    else GENLIST ($+ lower) (SUC (upper - lower))
End

Theorem source_sorted_num_upto:
  !lower upper.
    source_sorted ($<=) (source_num_upto lower upper)
Proof
  rw[source_num_upto_def, source_sorted_def]
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

Theorem source_sorted_upt_weaken:
  !relation.
    (!left right : num. left < right ==> relation left right) ==>
    !start length.
      sorting$SORTED relation
        (GENLIST (\offset. start + offset) length)
Proof
  rpt strip_tac
  >> `sorting$SORTED ($<)
        (GENLIST (\offset. start + offset) length)` by
       (`(\offset. start + offset) = $+ start` by
          simp[FUN_EQ_THM]
        >> simp[sortingTheory.SORTED_GENLIST_PLUS])
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[]
QED

Theorem source_sorted_upt:
  !start length.
    sorting$SORTED (\left right : num. left <= right)
      (GENLIST (\offset. start + offset) length)
Proof
  rpt gen_tac
  >> irule source_sorted_upt_weaken
  >> simp[]
QED

Theorem source_sorted_wrt_upt:
  !start length.
    source_sorted_wrt (\left right : num. left <= right)
      (GENLIST (\offset. start + offset) length)
Proof
  rpt gen_tac
  >> `relation$transitive
        (\left right : num. left <= right)` by
       simp[relationTheory.transitive_def]
  >> metis_tac[source_sorted_wrt_bridge, source_sorted_upt]
QED

(* Isabelle/HOL src/HOL/List.thy:5185-5327. *)
Definition source_rotate1_def:
  (source_rotate1 ([] : 'a list) = []) /\
  (source_rotate1 (head::tail) = tail ++ [head])
End

Definition source_rotate_def:
  source_rotate count (xs : 'a list) =
    FUNPOW source_rotate1 count xs
End

Theorem source_rotate1_length:
  !xs. LENGTH (source_rotate1 xs) = LENGTH xs
Proof
  Cases
  >> simp[source_rotate1_def]
QED

Theorem source_rotate1_drop_take_bridge:
  !xs.
    source_rotate1 xs = DROP 1 xs ++ TAKE 1 xs
Proof
  Cases
  >> simp[source_rotate1_def]
QED

Theorem source_tail_snoc_el:
  !head tail index.
    index < LENGTH (head::tail) ==>
    EL index (tail ++ [head]) =
    EL (SUC index MOD LENGTH (head::tail)) (head::tail)
Proof
  rpt strip_tac
  >> Cases_on `index < LENGTH tail`
  >- simp[listTheory.EL_APPEND_EQN]
  >> fs[]
  >> `index = LENGTH tail` by decide_tac
  >> simp[listTheory.EL_APPEND_EQN]
QED

Theorem source_drop1_take1_el:
  !xs index.
    index < LENGTH xs ==>
    EL index (DROP 1 xs ++ TAKE 1 xs) =
    EL (SUC index MOD LENGTH xs) xs
Proof
  Cases_on `xs`
  >> simp[source_tail_snoc_el]
QED

Theorem source_rotate_length:
  !count xs. LENGTH (source_rotate count xs) = LENGTH xs
Proof
  Induct
  >- simp[source_rotate_def]
  >> gen_tac
  >> rw[source_rotate_def, arithmeticTheory.FUNPOW_SUC,
        source_rotate1_length]
  >> rw[GSYM source_rotate_def]
QED

Theorem source_rotate1_map:
  !function xs.
    source_rotate1 (MAP function xs) =
    MAP function (source_rotate1 xs)
Proof
  Cases_on `xs`
  >> simp[source_rotate1_def]
QED

Theorem source_funpow_rotate1_map:
  !count function xs.
    FUNPOW source_rotate1 count (MAP function xs) =
    MAP function (FUNPOW source_rotate1 count xs)
Proof
  Induct
  >> simp[arithmeticTheory.FUNPOW_SUC, source_rotate1_map]
QED

Theorem source_funpow_rotate1_swap:
  !count xs.
    source_rotate1 (FUNPOW source_rotate1 count xs) =
    FUNPOW source_rotate1 count (source_rotate1 xs)
Proof
  Induct
  >> simp[arithmeticTheory.FUNPOW_SUC]
QED

Theorem source_rotate_split_period:
  !left right.
    source_rotate (LENGTH left) (left ++ right) = right ++ left
Proof
  Induct
  >- simp[source_rotate_def]
  >> rpt gen_tac
  >> simp[source_rotate_def, arithmeticTheory.FUNPOW_SUC,
          source_funpow_rotate1_swap, source_rotate1_def]
  >> first_x_assum
       (qspec_then `right ++ [h]` mp_tac)
  >> simp[source_rotate_def, listTheory.APPEND_ASSOC]
QED

Theorem source_rotate_period:
  !xs. source_rotate (LENGTH xs) xs = xs
Proof
  gen_tac
  >> qspecl_then [`xs`, `[]`] mp_tac source_rotate_split_period
  >> simp[]
QED

Theorem source_rotate_conv_mod:
  !count xs.
    source_rotate count xs =
    source_rotate (count MOD LENGTH xs) xs
Proof
  rpt gen_tac
  >> Cases_on `xs`
  >- simp[source_rotate_def, source_rotate1_def]
  >> fs[source_rotate_def]
  >> irule numberTheory.FUNPOW_MOD
  >> conj_tac
  >- simp[]
  >> qspec_then `h::t` mp_tac source_rotate_period
  >> simp[source_rotate_def]
QED

Theorem source_rotate_map_bridge:
  !count function xs.
    source_rotate count (MAP function xs) =
    MAP function (source_rotate count xs)
Proof
  simp[source_rotate_def, source_funpow_rotate1_map]
QED

Definition source_unrotate1_def:
  source_unrotate1 (xs : 'a list) =
    if NULL xs then [] else LAST xs :: FRONT xs
End

Theorem source_rotate1_inverse:
  !xs.
    source_rotate1 (source_unrotate1 xs) = xs /\
    source_unrotate1 (source_rotate1 xs) = xs
Proof
  Cases
  >> simp[source_rotate1_def, source_unrotate1_def,
          listTheory.APPEND_FRONT_LAST,
          GSYM listTheory.SNOC_APPEND]
QED

Theorem source_rotate1_inj:
  !xs ys. source_rotate1 xs = source_rotate1 ys ==> xs = ys
Proof
  metis_tac[source_rotate1_inverse]
QED

Theorem source_rotate1_surj:
  !ys. ?xs. source_rotate1 xs = ys
Proof
  metis_tac[source_rotate1_inverse]
QED

(* Isabelle/HOL src/HOL/List.thy:5329-5411. *)
Definition source_nths_def:
  (source_nths ([] : 'a list) (indices : num set) = []) /\
  (source_nths (head::tail) indices =
     (if 0 IN indices then [head] else []) ++
     source_nths tail {index | SUC index IN indices})
End

Theorem source_map_el_suc:
  !head tail indices.
    MAP (\index. EL index (head::tail)) (MAP SUC indices) =
    MAP (\index. EL index tail) indices
Proof
  Induct_on `indices`
  >> simp[listTheory.EL]
QED

Theorem source_nths_filter_bridge:
  !xs indices.
    source_nths xs indices =
    MAP (\index. EL index xs)
      (FILTER (\index. index IN indices)
        (rich_list$COUNT_LIST (LENGTH xs)))
Proof
  Induct_on `xs`
  >- simp[source_nths_def, rich_listTheory.COUNT_LIST_def]
  >> rpt gen_tac
  >> Cases_on `0 IN indices`
  >> simp[source_nths_def, rich_listTheory.COUNT_LIST_def,
          rich_listTheory.FILTER_MAP, listTheory.MAP_MAP_o,
          combinTheory.o_DEF, listTheory.EL,
          source_map_el_suc]
QED

Theorem source_nths_set_subset:
  !xs indices value.
    MEM value (source_nths xs indices) ==> MEM value xs
Proof
  Induct_on `xs`
  >- simp[source_nths_def]
  >> rpt gen_tac
  >> rw[source_nths_def]
  >> first_x_assum drule
  >> simp[]
QED

Theorem source_map_el_filter_count_mem:
  !xs predicate value.
    MEM value
      (MAP (\index. EL index xs)
        (FILTER predicate
          (rich_list$COUNT_LIST (LENGTH xs)))) ==>
    MEM value xs
Proof
  simp[listTheory.MEM_MAP, listTheory.MEM_FILTER,
       rich_listTheory.MEM_COUNT_LIST]
  >> metis_tac[listTheory.EL_MEM]
QED

Theorem source_nths_length_bridge:
  !xs indices.
    LENGTH (source_nths xs indices) =
    CARD {index | index < LENGTH xs /\ index IN indices}
Proof
  rpt gen_tac
  >> rw[source_nths_filter_bridge]
  >> qabbrev_tac
       `selected =
          FILTER (\index. index IN indices)
            (rich_list$COUNT_LIST (LENGTH xs))`
  >> `ALL_DISTINCT selected`
       by simp[Abbr `selected`, listTheory.FILTER_ALL_DISTINCT,
               rich_listTheory.all_distinct_count_list]
  >> drule listTheory.ALL_DISTINCT_CARD_LIST_TO_SET
  >> strip_tac
  >> fs[Abbr `selected`, listTheory.LIST_TO_SET_FILTER,
        rich_listTheory.COUNT_LIST_COUNT]
  >> `indices INTER count (LENGTH xs) =
      {index | index < LENGTH xs /\ index IN indices}`
       by (rw[pred_setTheory.EXTENSION, pred_setTheory.IN_COUNT]
           >> metis_tac[])
  >> fs[]
QED

Theorem source_length_filter_count:
  !predicate size.
    LENGTH
      (FILTER predicate (rich_list$COUNT_LIST size)) =
    CARD {index | index < size /\ predicate index}
Proof
  rpt gen_tac
  >> qabbrev_tac
       `selected = FILTER predicate (rich_list$COUNT_LIST size)`
  >> `ALL_DISTINCT selected`
       by simp[Abbr `selected`, listTheory.FILTER_ALL_DISTINCT,
               rich_listTheory.all_distinct_count_list]
  >> drule listTheory.ALL_DISTINCT_CARD_LIST_TO_SET
  >> strip_tac
  >> fs[Abbr `selected`, listTheory.LIST_TO_SET_FILTER,
        rich_listTheory.COUNT_LIST_COUNT]
  >> `{index | predicate index} INTER count size =
      {index | index < size /\ predicate index}`
       by (rw[pred_setTheory.EXTENSION, pred_setTheory.IN_COUNT]
           >> metis_tac[])
  >> fs[]
QED

Theorem source_shift_image:
  !count indices.
    {index |
       SUC index IN
       IMAGE (\value. SUC count + value) indices} =
    IMAGE (\value. count + value) indices
Proof
  rw[pred_setTheory.EXTENSION]
  >> eq_tac
  >> rw[]
  >- (qexists_tac `value`
      >> fs[]
      >> decide_tac)
  >> qexists_tac `value`
  >> fs[]
  >> decide_tac
QED

Theorem source_nths_drop:
  !count xs indices.
    source_nths (DROP count xs) indices =
    source_nths xs (IMAGE (\index. count + index) indices)
Proof
  Induct
  >- simp[source_nths_def, pred_setTheory.EXTENSION]
  >> Cases_on `xs`
  >> simp[source_nths_def, source_shift_image]
QED

(* Isabelle/HOL src/HOL/List.thy:8287-8321. *)
Definition source_atMost_def:
  source_atMost le bound = {value | le value bound}
End

Definition source_lessThan_def:
  source_lessThan lt bound = {value | lt value bound}
End

Definition source_atLeast_def:
  source_atLeast le bound = {value | le bound value}
End

Definition source_greaterThan_def:
  source_greaterThan lt bound = {value | lt bound value}
End

Definition source_atLeastAtMost_def:
  source_atLeastAtMost le lower upper =
    {value | le lower value /\ le value upper}
End

Definition source_greaterThanAtMost_def:
  source_greaterThanAtMost le lt lower upper =
    {value | lt lower value /\ le value upper}
End

Definition source_atLeastLessThan_def:
  source_atLeastLessThan le lt lower upper =
    {value | le lower value /\ lt value upper}
End

Theorem source_interval_membership:
  (!le bound value.
     value IN source_atMost le bound <=> le value bound) /\
  (!lt bound value.
     value IN source_lessThan lt bound <=> lt value bound) /\
  (!le bound value.
     value IN source_atLeast le bound <=> le bound value) /\
  (!lt bound value.
     value IN source_greaterThan lt bound <=> lt bound value)
Proof
  simp[source_atMost_def, source_lessThan_def,
       source_atLeast_def, source_greaterThan_def]
QED

Theorem source_bounded_interval_membership:
  (!le lower upper value.
     value IN source_atLeastAtMost le lower upper <=>
     le lower value /\ le value upper) /\
  (!le lt lower upper value.
     value IN source_greaterThanAtMost le lt lower upper <=>
     lt lower value /\ le value upper) /\
  (!le lt lower upper value.
     value IN source_atLeastLessThan le lt lower upper <=>
     le lower value /\ lt value upper)
Proof
  simp[source_atLeastAtMost_def, source_greaterThanAtMost_def,
       source_atLeastLessThan_def]
QED

Theorem source_num_weak_linear_order:
  relation$WeakLinearOrder ($<= : num -> num -> bool)
Proof
  simp[relationTheory.WeakLinearOrder,
       relationTheory.WeakOrder,
       relationTheory.reflexive_def,
       relationTheory.transitive_def,
       relationTheory.antisymmetric_def,
       relationTheory.trichotomous]
QED

Theorem source_less_than_count:
  !bound.
    source_lessThan ($<) bound = pred_set$count bound
Proof
  simp[source_lessThan_def, pred_setTheory.count_def,
       pred_setTheory.EXTENSION]
QED

Theorem source_at_most_count:
  !bound.
    source_atMost ($<=) bound = pred_set$count (SUC bound)
Proof
  simp[source_atMost_def, pred_setTheory.count_def,
       pred_setTheory.EXTENSION]
QED

Theorem source_sorted_list_of_count:
  !bound.
    source_sorted_list_of_set ($<=) (pred_set$count bound) =
    rich_list$COUNT_LIST bound
Proof
  gen_tac
  >> irule source_sorted_list_of_set_unique
  >> simp[source_num_weak_linear_order,
          source_sorted_def,
          sortingTheory.sorted_count_list,
          rich_listTheory.all_distinct_count_list,
          rich_listTheory.COUNT_LIST_COUNT]
QED

Theorem source_sorted_list_of_set_less_than_suc:
  !bound.
    source_sorted_list_of_set ($<=)
      (source_lessThan ($<) (SUC bound)) =
    source_sorted_list_of_set ($<=)
      (source_lessThan ($<) bound) ++ [bound]
Proof
  simp[source_less_than_count,
       source_sorted_list_of_count,
       rich_listTheory.COUNT_LIST_SNOC,
       listTheory.SNOC_APPEND]
QED

Theorem source_sorted_list_of_set_at_most_suc:
  !bound.
    source_sorted_list_of_set ($<=)
      (source_atMost ($<=) (SUC bound)) =
    source_sorted_list_of_set ($<=)
      (source_atMost ($<=) bound) ++ [SUC bound]
Proof
  simp[source_at_most_count,
       source_sorted_list_of_count,
       rich_listTheory.COUNT_LIST_SNOC,
       listTheory.SNOC_APPEND]
QED

Theorem source_sorted_list_of_set_greater_than_at_most:
  !lower upper.
    lower < upper ==>
    source_sorted_list_of_set ($<=)
      (source_greaterThanAtMost ($<=) ($<) lower upper) =
    GENLIST ($+ (SUC lower)) (upper - lower)
Proof
  rpt strip_tac
  >> irule source_sorted_list_of_set_unique
  >> simp[source_num_weak_linear_order,
          source_sorted_def,
          sortingTheory.SORTED_GENLIST_PLUS,
          listTheory.ALL_DISTINCT_GENLIST,
          listTheory.LIST_TO_SET_GENLIST,
          source_greaterThanAtMost_def,
          pred_setTheory.EXTENSION,
          pred_setTheory.FINITE_COUNT,
          pred_setTheory.SUBSET_DEF]
  >> conj_tac
  >- (irule pred_setTheory.SUBSET_FINITE
      >> qexists_tac `pred_set$count (SUC upper)`
      >> simp[pred_setTheory.SUBSET_DEF,
              pred_setTheory.count_def])
  >> conj_tac
  >- (gen_tac
      >> eq_tac
      >- (strip_tac >> decide_tac)
      >> strip_tac
      >> qexists_tac `x - SUC lower`
      >> decide_tac)
  >> irule sortingTheory.SORTED_weaken
  >> qexists_tac `$<`
  >> simp[sortingTheory.SORTED_GENLIST_PLUS]
QED

Theorem source_nth_sorted_list_of_set_greater_than_at_most:
  !index lower upper.
    index < upper - lower ==>
    EL index
      (source_sorted_list_of_set ($<=)
        (source_greaterThanAtMost ($<=) ($<) lower upper)) =
    SUC (lower + index)
Proof
  rpt strip_tac
  >> `lower < upper` by decide_tac
  >> simp[source_sorted_list_of_set_greater_than_at_most,
          listTheory.EL_GENLIST]
QED

(* Isabelle/HOL src/HOL/List.thy:8527-8548. *)
Definition source_map_filter_def:
  source_map_filter function xs =
    MAP (THE o function)
      (FILTER (\value. function value <> NONE) xs)
End

Theorem source_map_filter_bridge:
  (!function. source_map_filter function [] = []) /\
  (!function head tail.
     source_map_filter function (head::tail) =
     case function head of
       NONE => source_map_filter function tail
     | SOME value => value::source_map_filter function tail)
Proof
  conj_tac
  >- simp[source_map_filter_def, combinTheory.o_DEF]
  >> rpt gen_tac
  >> Cases_on `function head`
  >> simp[source_map_filter_def, combinTheory.o_DEF]
QED

Theorem source_map_filter_some_filter:
  !function predicate xs.
    MAP
      (\value.
         THE
           (if predicate value then SOME (function value) else NONE))
      (FILTER predicate xs) =
    MAP function (FILTER predicate xs)
Proof
  rpt gen_tac
  >> Induct_on `xs`
  >- simp[combinTheory.o_DEF]
  >> gen_tac
  >> Cases_on `predicate h`
  >> fs[combinTheory.o_DEF]
QED

(* Isabelle/HOL src/HOL/List.thy:8199-8206, 8673-8694. *)
Definition source_can_select_def:
  source_can_select predicate domain <=>
    ?value.
      value IN domain /\ predicate value /\
      !other.
        other IN domain /\ predicate other ==> other = value
End

Definition source_list_ex1_def:
  source_list_ex1 predicate xs <=>
    source_can_select predicate (LIST_TO_SET xs)
End

Definition source_list_all_def:
  source_list_all predicate xs <=> EVERY predicate xs
End

Definition source_these_def:
  source_these domain = {value | SOME value IN domain}
End

Theorem source_these_list_to_set:
  !xs.
    source_these (LIST_TO_SET xs) =
    LIST_TO_SET (source_map_filter I xs)
Proof
  Induct
  >- simp[source_these_def, source_map_filter_def]
  >> Cases_on `h`
  >> fs[source_these_def, source_map_filter_def,
        combinTheory.o_DEF, pred_setTheory.EXTENSION]
QED

Definition source_Id_on_def:
  source_Id_on domain =
    {pair | ?value. value IN domain /\ pair = (value, value)}
End

(* Isabelle/HOL src/HOL/List.thy:7790-7870.  A set of pairs is
   represented as its curried membership predicate. *)
Definition source_listrel1_def:
  source_listrel1 relation xs ys <=>
    ?prefix left right suffix.
      xs = prefix ++ left::suffix /\
      relation left right /\
      ys = prefix ++ right::suffix
End

Theorem source_listrel1_append_suffix:
  !relation xs ys suffix.
    source_listrel1 relation xs ys ==>
    source_listrel1 relation (xs ++ suffix) (ys ++ suffix)
Proof
  rpt strip_tac
  >> fs[source_listrel1_def]
  >> metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem source_listrel1_append_prefix:
  !relation prefix xs ys.
    source_listrel1 relation xs ys ==>
    source_listrel1 relation (prefix ++ xs) (prefix ++ ys)
Proof
  rpt strip_tac
  >> fs[source_listrel1_def]
  >> metis_tac[listTheory.APPEND_ASSOC]
QED

Theorem source_shortlex_not_less_equal:
  !relation xs ys.
    list$SHORTLEX relation xs ys ==>
    ~(LENGTH xs < LENGTH ys) ==>
    LENGTH xs = LENGTH ys
Proof
  metis_tac[listTheory.SHORTLEX_LENGTH_LE,
            arithmeticTheory.NOT_LESS,
            arithmeticTheory.LESS_EQUAL_ANTISYM]
QED

Theorem source_shortlex_append_change:
  !relation prefix left right suffix.
    relation left right ==>
    list$SHORTLEX relation
      (prefix ++ [left] ++ suffix)
      (prefix ++ [right] ++ suffix)
Proof
  gen_tac
  >> Induct
  >> simp[listTheory.SHORTLEX_THM]
QED

Theorem source_listrel1_shortlex:
  !relation xs ys.
    source_listrel1 relation xs ys ==>
    list$SHORTLEX relation xs ys
Proof
  rpt gen_tac
  >> strip_tac
  >> fs[source_listrel1_def]
  >> mp_tac
       (Q.SPECL [`relation`, `prefix`, `left`, `right`, `suffix`]
          source_shortlex_append_change)
  >> simp[]
QED

Theorem source_listrel1_singleton:
  !relation left right.
    source_listrel1 relation [left] [right] <=>
    relation left right
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> fs[source_listrel1_def]
      >> Cases_on `prefix`
      >> fs[])
  >> strip_tac
  >> simp[source_listrel1_def]
  >> map_every qexists_tac [`[]`, `left`, `right`, `[]`]
  >> simp[]
QED

Theorem source_wf_listrel1_iff:
  !relation.
    relation$WF (source_listrel1 relation) <=>
    relation$WF relation
Proof
  gen_tac
  >> eq_tac
  >- (strip_tac
      >> irule relationTheory.WF_SUBSET
      >> qexists_tac
           `relation$inv_image
              (source_listrel1 relation) (\value. [value])`
      >> conj_tac
      >- simp[relationTheory.inv_image_def,
              source_listrel1_singleton]
      >> irule relationTheory.WF_inv_image
      >> simp[])
  >> strip_tac
  >> irule relationTheory.WF_SUBSET
  >> qexists_tac `list$SHORTLEX relation`
  >> simp[source_listrel1_shortlex,
          listTheory.WF_SHORTLEX]
QED

(* Isabelle/HOL src/HOL/List.thy:7770-7788. *)
Definition source_measures_def:
  (source_measures [] left right <=> F) /\
  (source_measures ((function : 'a -> num)::functions) left right <=>
     function left < function right \/
     (function left = function right /\
      source_measures functions left right))
End

Theorem source_measures_WF:
  !functions. relation$WF (source_measures functions)
Proof
  Induct
  >- simp[source_measures_def, relationTheory.WF_DEF]
  >> gen_tac
  >> `source_measures (h::functions) =
      relation$inv_image
        (pair$LEX (($<) : num -> num -> bool)
           (source_measures functions))
        (\value. (h value, value))` by
       simp[boolTheory.FUN_EQ_THM, source_measures_def,
            relationTheory.inv_image_def, pairTheory.LEX_DEF]
  >> pop_assum SUBST1_TAC
  >> irule relationTheory.WF_inv_image
  >> irule pairTheory.WF_LEX
  >> simp[prim_recTheory.WF_LESS]
QED

(* Isabelle/HOL src/HOL/List.thy:7247-7760.  Isabelle's [lex] is
   equal-length lexicographic order, [lenlex] is shortlex, and
   [lexord] is the prefix-aware lexicographic order. *)
Definition source_lex_def:
  source_lex relation xs ys <=>
    LENGTH xs = LENGTH ys /\ list$LLEX relation xs ys
End

Definition source_lenlex_def:
  source_lenlex relation xs ys <=> list$SHORTLEX relation xs ys
End

Definition source_lexord_def:
  source_lexord relation xs ys <=> list$LLEX relation xs ys
End

Theorem source_lexord_partial_trans:
  !relation xs ys zs.
    source_lexord relation xs ys ==>
    source_lexord relation ys zs ==>
    relation$transitive relation ==>
    source_lexord relation xs zs
Proof
  metis_tac[source_lexord_def, listTheory.LLEX_transitive,
            relationTheory.transitive_def]
QED

Definition source_lexordp_def:
  source_lexordp relation xs ys <=> source_lexord relation xs ys
End

Definition source_lexordp_eq_def:
  source_lexordp_eq relation xs ys <=>
    xs = ys \/ source_lexordp relation xs ys
End

Theorem source_lex_conv:
  !relation xs ys.
    source_lex relation xs ys <=>
    LENGTH xs = LENGTH ys /\
    ?prefix left right xs' ys'.
      xs = prefix ++ (left::xs') /\
      ys = prefix ++ (right::ys') /\
      relation left right
Proof
  rpt gen_tac
  >> eq_tac
  >- (rw[source_lex_def, listTheory.LLEX_EL_THM]
      >> `n < LENGTH xs` by fs[]
      >> map_every qexists_tac
           [`TAKE n xs`, `EL n xs`, `EL n ys`,
            `DROP (SUC n) xs`, `DROP (SUC n) ys`]
      >> simp[rich_listTheory.TAKE_DROP_SUC])
  >> rw[source_lex_def, listTheory.LLEX_EL_THM]
  >> qexists_tac `LENGTH prefix`
  >> simp[listTheory.EL_APPEND_EQN,
          rich_listTheory.TAKE_APPEND1,
          rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem source_shortlex_equal_length:
  !relation xs ys.
    LENGTH xs = LENGTH ys ==>
    (list$SHORTLEX relation xs ys <=> list$LLEX relation xs ys)
Proof
  gen_tac
  >> Induct
  >> Cases_on `ys`
  >> simp[listTheory.SHORTLEX_def, listTheory.LLEX_def]
  >> metis_tac[]
QED

Theorem source_lenlex_conv:
  !relation xs ys.
    source_lenlex relation xs ys <=>
    LENGTH xs < LENGTH ys \/
    (LENGTH xs = LENGTH ys /\ source_lex relation xs ys)
Proof
  simp[source_lenlex_def, source_lex_def]
  >> metis_tac[source_shortlex_equal_length,
                listTheory.LENGTH_LT_SHORTLEX,
                listTheory.SHORTLEX_LENGTH_LE,
                arithmeticTheory.LESS_OR_EQ]
QED

Definition source_asym_def:
  source_asym relation <=>
    !left right. relation left right ==> ~relation right left
End

Theorem source_asym_lenlex:
  !relation.
    source_asym relation ==>
    source_asym (source_lenlex relation)
Proof
  simp[source_asym_def, source_lenlex_def]
  >> gen_tac
  >> strip_tac
  >> Induct_on `left`
  >> Cases_on `right`
  >> simp[listTheory.SHORTLEX_def]
  >> rpt strip_tac
  >> TRY decide_tac
  >> metis_tac[]
QED

Theorem source_lex_append_right:
  !relation xs ys.
    source_lex relation xs ys ==>
    !us vs.
      LENGTH us = LENGTH vs ==>
      source_lex relation (xs ++ us) (ys ++ vs)
Proof
  rpt strip_tac
  >> fs[source_lex_def, listTheory.LLEX_EL_THM]
  >> qexists_tac `n`
  >> simp[listTheory.TAKE_APPEND1,
          listTheory.EL_APPEND_EQN]
QED

Theorem source_lexord_append_leftI:
  !relation xs ys.
    source_lexord relation xs ys ==>
    !prefix.
      source_lexord relation (prefix ++ xs) (prefix ++ ys)
Proof
  rpt strip_tac
  >> Induct_on `prefix`
  >> fs[source_lexord_def, listTheory.LLEX_def]
QED

Theorem source_lexord_append_left_rightI:
  !relation left right.
    relation left right ==>
    !prefix xs ys.
      source_lexord relation
        (prefix ++ left::xs) (prefix ++ right::ys)
Proof
  rpt strip_tac
  >> Induct_on `prefix`
  >> fs[source_lexord_def, listTheory.LLEX_def]
QED

Theorem source_lexord_append_prefix_iff:
  !relation.
    relation$irreflexive relation ==>
    !prefix xs ys.
      (source_lexord relation
         (prefix ++ xs) (prefix ++ ys) <=>
       source_lexord relation xs ys)
Proof
  simp[relationTheory.irreflexive_def]
  >> rpt strip_tac
  >> Induct_on `prefix`
  >> fs[source_lexord_def, listTheory.LLEX_def]
QED

Theorem source_lexord_irreflexive:
  !relation.
    relation$irreflexive relation ==>
    relation$irreflexive (source_lexord relation)
Proof
  simp[relationTheory.irreflexive_def, source_lexord_def]
  >> rpt strip_tac
  >> Induct_on `x`
  >> simp[listTheory.LLEX_def]
QED

(* Isabelle/HOL src/HOL/List.thy:7954-8275. *)
Definition source_rel_image_def:
  source_rel_image relation domain =
    {right | ?left. left IN domain /\ relation left right}
End

Definition source_set_Cons_def:
  source_set_Cons heads tails =
    {result |
       ?head tail.
         head IN heads /\ tail IN tails /\ result = head::tail}
End

Definition source_superset_def:
  source_superset xs ys <=>
    LIST_TO_SET ys SUBSET LIST_TO_SET xs
End

Definition source_listrel1p_def:
  source_listrel1p relation xs ys <=>
    source_listrel1 relation xs ys
End

Definition source_lexordp_code_def:
  source_lexordp_code relation xs ys <=>
    source_lexord relation xs ys
End

Theorem source_listrel1_subset_LIST_REL:
  !left_relation right_relation xs ys.
    (!left right.
       left_relation left right ==> right_relation left right) ==>
    relation$reflexive right_relation ==>
    source_listrel1 left_relation xs ys ==>
    LIST_REL right_relation xs ys
Proof
  rpt strip_tac
  >> fs[source_listrel1_def]
  >> irule listTheory.LIST_REL_APPEND_suff
  >> conj_tac
  >- (irule listTheory.LIST_REL_APPEND_suff
      >> conj_tac
      >- (irule listTheory.LIST_REL_refl
          >> fs[relationTheory.reflexive_def])
      >> simp[])
  >> irule listTheory.LIST_REL_refl
  >> fs[relationTheory.reflexive_def]
QED

(* Isabelle/HOL src/HOL/List.thy:7995-7996. *)
Definition source_refl_on_def:
  source_refl_on domain relation <=>
    (!value. value IN domain ==> relation value value) /\
    (!left right.
       relation left right ==>
       left IN domain /\ right IN domain)
End

Definition source_equiv_def:
  source_equiv domain relation <=>
    source_refl_on domain relation /\
    relation$symmetric relation /\
    relation$transitive relation
End

Definition source_lists_def:
  source_lists domain =
    {xs | EVERY (\value. value IN domain) xs}
End

Theorem source_mono_lists:
  !left right.
    left SUBSET right ==>
    source_lists left SUBSET source_lists right
Proof
  simp[source_lists_def, pred_setTheory.SUBSET_DEF,
       listTheory.EVERY_MEM]
  >> metis_tac[]
QED

Theorem source_LIST_REL_in_lists:
  !carrier relation xs ys.
    (!left right.
       relation left right ==>
       left IN carrier /\ right IN carrier) ==>
    LIST_REL relation xs ys ==>
    source_lists carrier xs /\ source_lists carrier ys
Proof
  simp[source_lists_def, listTheory.LIST_REL_EL_EQN,
       listTheory.EVERY_EL]
  >> metis_tac[]
QED

Theorem source_LIST_REL_refl_on:
  !carrier relation xs.
    (!value. value IN carrier ==> relation value value) ==>
    xs IN source_lists carrier ==>
    LIST_REL relation xs xs
Proof
  rpt gen_tac
  >> strip_tac
  >> Induct_on `xs`
  >> simp[source_lists_def]
QED

Theorem source_equiv_LIST_REL:
  !carrier relation.
    source_equiv carrier relation ==>
    source_equiv (source_lists carrier) (LIST_REL relation)
Proof
  rpt gen_tac
  >> strip_tac
  >> fs[source_equiv_def, source_refl_on_def]
  >> rw[source_equiv_def, source_refl_on_def]
      >- (irule
        (Q.SPECL [`carrier`, `relation`, `value`]
           source_LIST_REL_refl_on)
      >> qexists_tac `carrier`
      >> fs[source_lists_def])
  >- (qspecl_then [`carrier`, `relation`, `left`, `right`]
        mp_tac source_LIST_REL_in_lists
      >> simp[source_lists_def]
      >> metis_tac[])
  >- (qspecl_then [`carrier`, `relation`, `left`, `right`]
        mp_tac source_LIST_REL_in_lists
      >> simp[source_lists_def]
      >> metis_tac[])
  >- (fs[relationTheory.symmetric_def]
      >> rw[relationTheory.symmetric_def]
      >> eq_tac
      >> metis_tac[listTheory.LIST_REL_sym])
  >> fs[relationTheory.transitive_def]
  >> rw[relationTheory.transitive_def]
  >> irule listTheory.LIST_REL_trans_same
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:8999-9003. *)
Theorem source_set_Cons_transfer:
  !relation.
    (list$SET_REL relation ===>
      list$SET_REL (LIST_REL relation) ===>
      list$SET_REL (LIST_REL relation))
      source_set_Cons source_set_Cons
Proof
  simp[transferTheory.FUN_REL_def, listTheory.SET_REL_THM,
       source_set_Cons_def]
  >> rpt strip_tac
  >> metis_tac[listTheory.LIST_REL_CONS1]
QED

(* Isabelle/HOL src/HOL/List.thy:8709-8711. *)
Theorem source_wf_list_set:
  !pairs.
    relation$WF
      (set_relation$reln_to_rel (LIST_TO_SET pairs)) <=>
    set_relation$acyclic (LIST_TO_SET pairs)
Proof
  gen_tac
  >> eq_tac
  >- metis_tac[set_relationTheory.WF_acyclic]
  >> strip_tac
  >> irule set_relationTheory.acyclic_WF
  >> conj_tac
  >- simp[]
  >> qexists_tac
       `IMAGE FST (LIST_TO_SET pairs) UNION
        IMAGE SND (LIST_TO_SET pairs)`
  >> simp[set_relationTheory.domain_def,
          set_relationTheory.range_def,
          pred_setTheory.SUBSET_DEF]
  >> conj_tac
  >- (rpt strip_tac
      >> disj1_tac
      >> qexists_tac `(x,y)`
      >> simp[])
  >> rpt strip_tac
  >> disj2_tac
  >> qexists_tac `(x',x)`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/List.thy:7052-7055. *)
Definition source_trans_list_step_def:
  source_trans_list_step pairs =
    FLAT
      (MAP
        (\left.
           MAP (\right. (FST left, SND right))
             (FILTER (\right. SND left = FST right) pairs))
        pairs)
End

Theorem source_trans_list_step_subset_tc:
  !pairs.
    LIST_TO_SET (source_trans_list_step pairs) SUBSET
    set_relation$transitive_closure (LIST_TO_SET pairs)
Proof
  simp[source_trans_list_step_def, pred_setTheory.SUBSET_DEF,
       listTheory.MEM_FLAT, listTheory.MEM_MAP,
       listTheory.MEM_FILTER, PULL_EXISTS]
  >> rpt strip_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> fs[]
  >> metis_tac[set_relationTheory.tc_rules]
QED

(* Isabelle/HOL src/HOL/List.thy:5482-5536. *)
Inductive source_shuffle:
  source_shuffle [] [] [] /\
  (!left xs ys zs.
     source_shuffle xs ys zs ==>
     source_shuffle (left::xs) ys (left::zs)) /\
  (!right xs ys zs.
     source_shuffle xs ys zs ==>
     source_shuffle xs (right::ys) (right::zs))
End

Definition source_shuffles_def:
  source_shuffles xs ys = {zs | source_shuffle xs ys zs}
End

Theorem source_nil_in_shuffles:
  !xs ys.
    xs = [] ==> ys = [] ==> [] IN source_shuffles xs ys
Proof
  simp[source_shuffles_def, source_shuffle_rules]
QED

(* Isabelle/HOL src/HOL/List.thy:5415-5480. *)
Definition source_subseqs_def:
  (source_subseqs ([] : 'a list) = [[]]) /\
  (source_subseqs (head::tail) =
     source_subseqs tail ++
     MAP (CONS head) (source_subseqs tail))
End

Theorem source_subseqs_member_subset:
  !xs ys.
    MEM ys (source_subseqs xs) ==>
    LIST_TO_SET ys SUBSET LIST_TO_SET xs
Proof
  Induct
  >> simp[source_subseqs_def, pred_setTheory.SUBSET_DEF,
          listTheory.MEM_MAP]
  >> rpt strip_tac
  >> Cases_on `ys`
  >> fs[]
  >> first_x_assum drule
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_subset_subseqs:
  !xs subset.
    subset SUBSET LIST_TO_SET xs ==>
    subset IN IMAGE LIST_TO_SET (LIST_TO_SET (source_subseqs xs))
Proof
  Induct
  >- simp[source_subseqs_def, pred_setTheory.SUBSET_EMPTY]
  >> rpt strip_tac
  >> Cases_on `h IN subset`
  >- (qpat_x_assum `subset SUBSET LIST_TO_SET (h::xs)`
        mp_tac
      >> simp[pred_setTheory.SUBSET_DEF]
      >> strip_tac
      >> `subset DELETE h SUBSET LIST_TO_SET xs` by
           (rw[pred_setTheory.SUBSET_DEF,
               pred_setTheory.IN_DELETE]
            >> metis_tac[])
      >> qpat_x_assum
           `!candidate. candidate SUBSET LIST_TO_SET xs ==> _`
           (qspec_then `subset DELETE h` mp_tac)
      >> simp[]
      >> strip_tac
      >> qexists_tac `h::x`
      >> simp[source_subseqs_def, listTheory.MEM_MAP,
              pred_setTheory.EXTENSION]
      >> gen_tac
      >> eq_tac
      >> strip_tac
      >> fs[pred_setTheory.EXTENSION,
            pred_setTheory.IN_DELETE]
      >> metis_tac[])
  >> `subset SUBSET LIST_TO_SET xs` by
       (rw[pred_setTheory.SUBSET_DEF]
        >> fs[pred_setTheory.SUBSET_DEF]
        >> metis_tac[])
  >> first_x_assum drule
  >> simp[source_subseqs_def]
  >> metis_tac[]
QED

Theorem source_all_distinct_subseq_sets:
  !xs.
    ALL_DISTINCT xs ==>
    ALL_DISTINCT (MAP LIST_TO_SET (source_subseqs xs))
Proof
  Induct
  >- simp[source_subseqs_def]
  >> simp[source_subseqs_def]
  >> rpt strip_tac
  >> simp[listTheory.ALL_DISTINCT_APPEND]
  >> conj_tac
  >- (`MAP LIST_TO_SET
         (MAP (CONS h) (source_subseqs xs)) =
       MAP (pred_set$INSERT h)
         (MAP LIST_TO_SET (source_subseqs xs))` by
        simp[listTheory.MAP_MAP_o, combinTheory.o_DEF]
      >> pop_assum SUBST1_TAC
      >> irule listTheory.ALL_DISTINCT_MAP_INJ
      >> conj_tac
      >- (rpt strip_tac
          >> fs[listTheory.MEM_MAP]
          >> `h NOTIN x /\ h NOTIN y` by
               metis_tac[source_subseqs_member_subset,
                          pred_setTheory.SUBSET_DEF]
          >> fs[pred_setTheory.EXTENSION]
          >> metis_tac[])
      >> metis_tac[])
  >> simp[listTheory.MEM_MAP]
  >> rpt strip_tac
  >> `h NOTIN LIST_TO_SET y` by
       metis_tac[source_subseqs_member_subset,
                  pred_setTheory.SUBSET_DEF]
  >> fs[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_upto_split2:
  !i j k. i <= j ==> j <= k ==>
    source_upto i k =
    source_upto i j ++ source_upto (j + 1) k
Proof
  rpt strip_tac
  >> Cases_on `j = k`
  >- (`source_upto (j + 1) k = []` by
        (irule source_upto_empty >> intLib.ARITH_TAC)
      >> fs[])
  >> `i <= j + 1` by intLib.ARITH_TAC
  >> `j + 1 <= k` by intLib.ARITH_TAC
  >> `j + 1 - 1 = j` by intLib.ARITH_TAC
  >> metis_tac[source_upto_split1]
QED

Theorem source_upto_split3:
  !i j k. i <= j ==> j <= k ==>
    source_upto i k =
    source_upto i (j - 1) ++ j :: source_upto (j + 1) k
Proof
  rpt strip_tac
  >> `source_upto i k =
      source_upto i (j - 1) ++ source_upto j k` by
       metis_tac[source_upto_split1]
  >> `source_upto j k = j :: source_upto (j + 1) k` by
       metis_tac[source_upto_rec1]
  >> metis_tac[]
QED

Definition source_upto_aux_def:
  source_upto_aux i j js = source_upto i j ++ js
End

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Product_Type.thy:135-147.  HOL4 deliberately has no global
   order instance for unit; these operations are the benchmark-local
   interpretation of that source instance. *)
Definition source_unit_le_def:
  source_unit_le (_ : unit) (_ : unit) = T
End

Definition source_unit_lt_def:
  source_unit_lt (_ : unit) (_ : unit) = F
End

Theorem source_unit_le_bridge:
  !u v : unit. source_unit_le u v <=> T
Proof
  simp[source_unit_le_def]
QED

Theorem source_unit_lt_bridge:
  !u v : unit. source_unit_lt u v <=> F
Proof
  simp[source_unit_lt_def]
QED

Theorem source_unit_le_unique:
  !relation : unit -> unit -> bool.
    (!u. relation u u) ==> relation = source_unit_le
Proof
  simp[FUN_EQ_THM, oneTheory.FORALL_ONE, source_unit_le_def]
QED

Theorem source_unit_lt_unique:
  !relation : unit -> unit -> bool.
    (!u. ~relation u u) ==> relation = source_unit_lt
Proof
  simp[FUN_EQ_THM, oneTheory.FORALL_ONE, source_unit_lt_def]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Set.thy:456-473 and 967-975.  Isabelle's [=simp=>]
   connective has ordinary implication as its logical content.  Its
   operational congruence role is represented by invocation-local Cong
   recipe arguments, not by an additional Boolean connective. *)
Definition source_ball_def:
  source_ball (set : 'a set) predicate =
    !x. x IN set ==> predicate x
End

Definition source_bex_def:
  source_bex (set : 'a set) predicate =
    ?x. x IN set /\ predicate x
End

Definition source_image_def:
  source_image (function : 'a -> 'b) set = IMAGE function set
End

(* Isabelle/HOL src/HOL/Set.thy:883-884.  Isabelle's image definition
   exposes the bounded-domain premise before the value equality. *)
Theorem source_image_expansion:
  !function set.
    IMAGE function set =
    (\value. ?argument. argument IN set /\ value = function argument)
Proof
  simp[pred_setTheory.EXTENSION, pred_setTheory.IN_IMAGE,
       boolTheory.CONJ_COMM]
QED

Theorem source_ball_bridge:
  !set predicate.
    source_ball set predicate <=>
    !x. x IN set ==> predicate x
Proof
  simp[source_ball_def]
QED

Theorem source_bex_bridge:
  !set predicate.
    source_bex set predicate <=>
    ?x. x IN set /\ predicate x
Proof
  rw[source_bex_def]
  >> metis_tac[]
QED

Theorem source_image_bridge:
  !function set. source_image function set = IMAGE function set
Proof
  simp[source_image_def]
QED

Theorem source_ball_cong_simp:
  !left right predicate predicate'.
    left = right ==>
    (!x. x IN right ==> (predicate x <=> predicate' x)) ==>
    (source_ball left predicate <=> source_ball right predicate')
Proof
  simp[source_ball_def]
QED

Theorem source_bex_cong_simp:
  !left right predicate predicate'.
    left = right ==>
    (!x. x IN right ==> (predicate x <=> predicate' x)) ==>
    (source_bex left predicate <=> source_bex right predicate')
Proof
  rw[source_bex_def]
  >> metis_tac[]
QED

Theorem source_image_cong_simp:
  !left right function function'.
    left = right ==>
    (!x. x IN right ==> function x = function' x) ==>
    source_image function left = source_image function' right
Proof
  rw[source_image_def]
  >> irule pred_setTheory.IMAGE_CONG
  >> simp[]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/Set.thy:994-995.  The source comm_monoid_add constraint is
   interpreted by HOL4's explicit AbelianMonoid record. *)
Definition source_add_image_def:
  source_add_image (g : 'a monoid) set =
    IMAGE (g.op g.id) set
End

Theorem source_add_image_bridge:
  !g set.
    source_add_image g set =
    IMAGE (g.op g.id) set
Proof
  simp[source_add_image_def]
QED

Theorem source_add_image_preimage:
  !g : 'a monoid.
    Monoid g ==>
    !set. set SUBSET g.carrier ==>
    !x. x IN set ==>
      ?y. x = g.op g.id y /\ y IN set
Proof
  rpt strip_tac
  >> qexists_tac `x`
  >> metis_tac[monoidTheory.monoid_lid,
               pred_setTheory.SUBSET_DEF]
QED

Theorem source_abelian_monoid_is_monoid:
  !g : 'a monoid. AbelianMonoid g ==> Monoid g
Proof
  simp[monoidTheory.AbelianMonoid_def]
QED

Theorem source_image_add_zero:
  !g : 'a monoid.
    AbelianMonoid g ==>
    !set. set SUBSET g.carrier ==>
      source_add_image g set = set
Proof
  rw[source_add_image_def, pred_setTheory.EXTENSION,
     pred_setTheory.IN_IMAGE]
  >> metis_tac[monoidTheory.AbelianMonoid_def,
               monoidTheory.monoid_lid,
               pred_setTheory.SUBSET_DEF]
QED

(* Isabelle/HOL f7e02b7e1f311d9c41ee075d22ff788b3e0de6db,
   src/HOL/String.thy:24-137 and 366-730.  Isabelle's char is an
   eight-bit datatype.  HOL4's char is the isomorphic subtype of
   naturals below 256, so the source operations stay local to this
   translation boundary. *)
Definition source_bool_num_def:
  source_bool_num bit : num = if bit then 1 else 0
End

Definition source_horner8_def:
  source_horner8 b0 b1 b2 b3 b4 b5 b6 b7 =
    source_bool_num b0 +
    2 * (source_bool_num b1 +
    2 * (source_bool_num b2 +
    2 * (source_bool_num b3 +
    2 * (source_bool_num b4 +
    2 * (source_bool_num b5 +
    2 * (source_bool_num b6 +
    2 * source_bool_num b7))))))
End

Theorem source_horner8_bound:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    source_horner8 b0 b1 b2 b3 b4 b5 b6 b7 < 256
Proof
  rpt Cases
  >> simp[source_horner8_def, source_bool_num_def]
QED

Theorem source_horner7_bound:
  !b0 b1 b2 b3 b4 b5 b6.
    source_horner8 b0 b1 b2 b3 b4 b5 b6 F < 128
Proof
  rpt Cases
  >> simp[source_horner8_def, source_bool_num_def]
QED

Definition source_Char_def:
  source_Char b0 b1 b2 b3 b4 b5 b6 b7 =
    CHR (source_horner8 b0 b1 b2 b3 b4 b5 b6 b7)
End

Theorem source_Char_ascii_bound:
  !b0 b1 b2 b3 b4 b5 b6.
    ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F) < 128
Proof
  rpt Cases
  >> simp[source_Char_def, source_horner8_def,
          source_bool_num_def, stringTheory.ORD_CHR_RWT]
QED

Definition source_of_char_def:
  source_of_char (character : char) = ORD character
End

Definition source_char_of_def:
  source_char_of number = CHR (number MOD 256)
End

Definition source_take_bit_def:
  source_take_bit width number = number MOD (2 ** width)
End

Definition source_ascii_of_def:
  source_ascii_of character = CHR (ORD character MOD 128)
End

Theorem source_of_char_Char:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    source_of_char (source_Char b0 b1 b2 b3 b4 b5 b6 b7) =
    source_horner8 b0 b1 b2 b3 b4 b5 b6 b7
Proof
  simp[source_of_char_def, source_Char_def, source_horner8_bound]
QED

Theorem source_char_roundtrip:
  !character. source_char_of (source_of_char character) = character
Proof
  simp[source_char_of_def, source_of_char_def,
       arithmeticTheory.LESS_MOD, stringTheory.ORD_BOUND]
QED

Theorem source_code_roundtrip:
  !number. source_of_char (source_char_of number) = number MOD 256
Proof
  simp[source_char_of_def, source_of_char_def,
       stringTheory.ORD_CHR_RWT, arithmeticTheory.MOD_LESS]
QED

Theorem source_char_of_take_bit_eq:
  !width number.
    8 <= width ==>
    source_char_of (source_take_bit width number) =
    source_char_of number
Proof
  rw[source_char_of_def, source_take_bit_def]
  >> fs[arithmeticTheory.LESS_EQ_EXISTS]
  >> simp[arithmeticTheory.EXP_ADD, arithmeticTheory.MOD_MULT_MOD]
QED

Theorem source_take_bit_mod_256:
  !width number.
    8 <= width ==>
    source_take_bit width number MOD 256 = number MOD 256
Proof
  rw[source_take_bit_def]
  >> fs[arithmeticTheory.LESS_EQ_EXISTS]
  >> simp[arithmeticTheory.EXP_ADD, arithmeticTheory.MOD_MULT_MOD]
QED

Theorem source_char_of_comp_of_char:
  source_char_of o source_of_char = I
Proof
  simp[FUN_EQ_THM, source_char_roundtrip]
QED

Theorem source_of_char_eqI:
  !left right.
    source_of_char left = source_of_char right ==> left = right
Proof
  simp[source_of_char_def, stringTheory.ORD_11]
QED

Theorem source_char_eq_by_ord:
  !left right : char. ORD left = ORD right ==> left = right
Proof
  simp[stringTheory.ORD_11]
QED

Theorem source_of_char_eq_iff:
  !left right.
    source_of_char left = source_of_char right <=> left = right
Proof
  simp[source_of_char_def, stringTheory.ORD_11]
QED

Theorem source_char_of_eq_iff:
  !number character.
    source_char_of number = character <=>
    source_take_bit 8 number = source_of_char character
Proof
  simp[source_char_of_def, source_take_bit_def, source_of_char_def,
       GSYM stringTheory.ORD_11, stringTheory.ORD_CHR_RWT,
       arithmeticTheory.MOD_LESS]
QED

Definition source_of_nat_def:
  source_of_nat number = number
End

Theorem source_char_of_nat:
  !number.
    source_char_of (source_of_nat number) = source_char_of number
Proof
  simp[source_of_nat_def]
QED

Theorem source_ascii_of_bound:
  !character. ORD (source_ascii_of character) < 128
Proof
  gen_tac
  >> `ORD character MOD 128 < 128`
       by simp[arithmeticTheory.MOD_LESS]
  >> `ORD character MOD 128 < 256` by decide_tac
  >> simp[source_ascii_of_def, stringTheory.ORD_CHR_RWT]
QED

Theorem source_ascii_of_idem:
  !character.
    ORD character < 128 ==> source_ascii_of character = character
Proof
  simp[source_ascii_of_def, arithmeticTheory.LESS_MOD,
       stringTheory.CHR_ORD]
QED

Definition source_literal_valid_def:
  source_literal_valid characters =
    EVERY (\character. ORD character < 128) characters
End

val source_literal_tydef = new_type_definition
  ("source_literal",
   prove(``?characters : char list. source_literal_valid characters``,
         qexists_tac `[]` >> simp[source_literal_valid_def]))

val source_literal_bij = define_new_type_bijections
  {ABS = "source_literal_abs", REP = "source_literal_explode",
   name = "source_literal_bij", tyax = source_literal_tydef}

Theorem source_literal_explode_valid:
  !literal. source_literal_valid (source_literal_explode literal)
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_abs_explode:
  !literal.
    source_literal_abs (source_literal_explode literal) = literal
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_explode_abs:
  !characters.
    source_literal_valid characters ==>
    source_literal_explode (source_literal_abs characters) = characters
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_abs_11:
  !left right.
    source_literal_valid left /\ source_literal_valid right ==>
    (source_literal_abs left = source_literal_abs right <=> left = right)
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_explode_11:
  !left right.
    (source_literal_explode left = source_literal_explode right <=>
     left = right)
Proof
  metis_tac[source_literal_bij]
QED

Theorem source_literal_eq_iff_explode:
  !left right.
    (left = right <=>
     source_literal_explode left = source_literal_explode right)
Proof
  simp[source_literal_explode_11]
QED

Definition source_literal_implode_def:
  source_literal_implode characters =
    source_literal_abs (MAP source_ascii_of characters)
End

Theorem source_literal_implode_valid:
  !characters.
    source_literal_valid (MAP source_ascii_of characters)
Proof
  simp[source_literal_valid_def, listTheory.EVERY_MAP,
       source_ascii_of_bound]
QED

Theorem source_ascii_map_id:
  !characters.
    source_literal_valid characters ==>
    MAP source_ascii_of characters = characters
Proof
  Induct_on `characters`
  >> simp[source_literal_valid_def, source_ascii_of_idem]
QED

Theorem source_literal_implode_explode:
  !literal.
    source_literal_implode (source_literal_explode literal) = literal
Proof
  rw[source_literal_implode_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `source_literal_abs (source_literal_explode literal)`
  >> conj_tac
  >- simp[source_ascii_map_id, source_literal_explode_valid]
  >> simp[source_literal_abs_explode]
QED

Theorem source_literal_explode_implode:
  !characters.
    source_literal_explode (source_literal_implode characters) =
    MAP source_ascii_of characters
Proof
  simp[source_literal_implode_def, source_literal_explode_abs,
       source_literal_implode_valid]
QED

Definition source_literal_empty_def:
  source_literal_empty = source_literal_abs []
End

Definition source_Literal_def:
  source_Literal b0 b1 b2 b3 b4 b5 b6 literal =
    source_literal_abs
      (source_Char b0 b1 b2 b3 b4 b5 b6 F ::
       source_literal_explode literal)
End

Theorem source_Literal_valid:
  !b0 b1 b2 b3 b4 b5 b6 literal.
    source_literal_valid
      (source_Char b0 b1 b2 b3 b4 b5 b6 F ::
       source_literal_explode literal)
Proof
  rpt gen_tac
  >> rw[source_literal_valid_def]
  >- simp[source_Char_ascii_bound]
  >> mp_tac (SPEC ``literal : source_literal``
       source_literal_explode_valid)
  >> simp[source_literal_valid_def]
QED

Theorem source_Char_ascii_bits:
  !b0 b1 b2 b3 b4 b5 b6.
    (BIT 0 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b0) /\
    (BIT 1 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b1) /\
    (BIT 2 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b2) /\
    (BIT 3 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b3) /\
    (BIT 4 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b4) /\
    (BIT 5 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b5) /\
    (BIT 6 (ORD (source_Char b0 b1 b2 b3 b4 b5 b6 F)) = b6)
Proof
  rpt Cases
  >> simp[source_Char_def, source_horner8_def,
          source_bool_num_def, stringTheory.ORD_CHR_RWT,
          bitTheory.BIT_def, bitTheory.BITS_THM]
QED

Theorem source_Char_ascii_eq_iff:
  !b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6.
    (source_Char b0 b1 b2 b3 b4 b5 b6 F =
     source_Char c0 c1 c2 c3 c4 c5 c6 F) <=>
    (b0 = c0) /\ (b1 = c1) /\ (b2 = c2) /\ (b3 = c3) /\
    (b4 = c4) /\ (b5 = c5) /\ (b6 = c6)
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qspecl_then
           [`b0`, `b1`, `b2`, `b3`, `b4`, `b5`, `b6`]
           strip_assume_tac source_Char_ascii_bits
      >> qspecl_then
           [`c0`, `c1`, `c2`, `c3`, `c4`, `c5`, `c6`]
           strip_assume_tac source_Char_ascii_bits
      >> fs[]
      >> metis_tac[])
  >> simp[]
QED

Theorem source_Literal_eq_iff:
  !b0 b1 b2 b3 b4 b5 b6 s c0 c1 c2 c3 c4 c5 c6 t.
    (source_Literal b0 b1 b2 b3 b4 b5 b6 s =
     source_Literal c0 c1 c2 c3 c4 c5 c6 t) <=>
    (b0 = c0) /\ (b1 = c1) /\ (b2 = c2) /\ (b3 = c3) /\
    (b4 = c4) /\ (b5 = c5) /\ (b6 = c6) /\ (s = t)
Proof
  simp[source_Literal_def, source_literal_abs_11,
       source_Literal_valid, source_Char_ascii_eq_iff,
       source_literal_explode_11, boolTheory.CONJ_ASSOC]
QED

Theorem source_literal_empty_neq_Literal:
  !b0 b1 b2 b3 b4 b5 b6 literal.
    source_literal_empty <>
    source_Literal b0 b1 b2 b3 b4 b5 b6 literal
Proof
  rpt gen_tac
  >> strip_tac
  >> first_x_assum (mp_tac o AP_TERM ``source_literal_explode``)
  >> simp[source_literal_empty_def, source_Literal_def,
          source_literal_explode_abs, source_Literal_valid,
          source_literal_valid_def]
QED

Theorem source_Literal_neq_empty:
  !b0 b1 b2 b3 b4 b5 b6 literal.
    source_Literal b0 b1 b2 b3 b4 b5 b6 literal <>
    source_literal_empty
Proof
  metis_tac[source_literal_empty_neq_Literal]
QED

Definition source_Literal_prime_def:
  source_Literal_prime = source_Literal
End

Theorem source_Literal_code_computation_unfold:
  source_Literal = source_Literal_prime
Proof
  simp[source_Literal_prime_def]
QED

Definition source_literal_append_def:
  source_literal_append left right =
    source_literal_abs
      (source_literal_explode left ++ source_literal_explode right)
End

Theorem source_literal_append_valid:
  !left right.
    source_literal_valid
      (source_literal_explode left ++ source_literal_explode right)
Proof
  rw[source_literal_valid_def]
  >> metis_tac[source_literal_explode_valid,
               source_literal_valid_def]
QED

Theorem source_literal_explode_append:
  !left right.
    source_literal_explode (source_literal_append left right) =
    source_literal_explode left ++ source_literal_explode right
Proof
  simp[source_literal_append_def, source_literal_explode_abs,
       source_literal_append_valid]
QED

(* The source code-generator integer is represented by HOL4's signed
   integers.  Euclidean division by two exposes one low bit at a time,
   including for negative inputs. *)
Definition source_bit_cut_integer_def:
  source_bit_cut_integer (number : int) =
    (number / 2, number % 2 = 1)
End

Definition source_char_of_integer_def:
  source_char_of_integer (number : int) =
    CHR (Num (number % 256))
End

Definition source_integer_of_char_def:
  source_integer_of_char character = &(ORD character)
End

Theorem source_integer_byte_bounds:
  !number : int.
    Num (number % 256) < 256
Proof
  gen_tac
  >> `0 <= number % 256 /\ number % 256 < (256 : int)`
       by (mp_tac (Q.SPECL [`number`, `256`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `Num (number % 256) < Num (&(256 : num))`
       by simp[integerTheory.NUM_LT]
  >> fs[integerTheory.NUM_OF_INT]
QED

Theorem source_integer_low_bit:
  !number : int.
    &source_bool_num (number % 2 = 1) = number % 2
Proof
  gen_tac
  >> `0 <= number % 2 /\ number % 2 < (2 : int)`
       by (mp_tac (Q.SPECL [`number`, `2`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `number % 2 = 0 \/ number % 2 = 1`
       by intLib.COOPER_TAC
  >> fs[source_bool_num_def]
QED

Theorem source_integer_division_two:
  !number : int.
    number = (number / 2) * 2 + number % 2 /\
    0 <= number % 2 /\ number % 2 < 2
Proof
  gen_tac
  >> mp_tac (Q.SPEC `2` integerTheory.INT_DIVISION)
  >> simp[]
QED

Theorem source_integer_remainder_two_bounds:
  !number : int. 0 <= number % 2 /\ number % 2 < 2
Proof
  simp[source_integer_division_two]
QED

Definition source_int_horner8_def:
  source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7 =
    r0 + 2 * (r1 + 2 * (r2 + 2 * (r3 + 2 *
      (r4 + 2 * (r5 + 2 * (r6 + 2 * r7))))))
End

Theorem source_horner8_int:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    &source_horner8 b0 b1 b2 b3 b4 b5 b6 b7 =
    source_int_horner8
      (&source_bool_num b0) (&source_bool_num b1)
      (&source_bool_num b2) (&source_bool_num b3)
      (&source_bool_num b4) (&source_bool_num b5)
      (&source_bool_num b6) (&source_bool_num b7)
Proof
  rpt Cases
  >> simp[source_horner8_def, source_int_horner8_def,
          source_bool_num_def]
QED

Theorem source_int_horner8_bounds:
  !r0 r1 r2 r3 r4 r5 r6 r7 : int.
    0 <= r0 /\ r0 < 2 ==>
    0 <= r1 /\ r1 < 2 ==>
    0 <= r2 /\ r2 < 2 ==>
    0 <= r3 /\ r3 < 2 ==>
    0 <= r4 /\ r4 < 2 ==>
    0 <= r5 /\ r5 < 2 ==>
    0 <= r6 /\ r6 < 2 ==>
    0 <= r7 /\ r7 < 2 ==>
    0 <= source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7 /\
    source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7 < 256
Proof
  rpt strip_tac
  >> simp[source_int_horner8_def]
  >> intLib.COOPER_TAC
QED

Theorem source_integer_eight_step:
  !number q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 : int.
    number = q1 * 2 + r0 ==>
    q1 = q2 * 2 + r1 ==>
    q2 = q3 * 2 + r2 ==>
    q3 = q4 * 2 + r3 ==>
    q4 = q5 * 2 + r4 ==>
    q5 = q6 * 2 + r5 ==>
    q6 = q7 * 2 + r6 ==>
    q7 = q8 * 2 + r7 ==>
    number = q8 * 256 +
      source_int_horner8 r0 r1 r2 r3 r4 r5 r6 r7
Proof
  rpt strip_tac
  >> fs[]
  >> simp[source_int_horner8_def]
  >> intLib.INT_RING_TAC
QED

Theorem source_integer_eight_bit_expansion:
  !number : int.
    number =
    (number / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2) * 256 +
    source_int_horner8
      (number % 2) ((number / 2) % 2)
      ((number / 2 / 2) % 2) ((number / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2)
Proof
  gen_tac
  >> irule
       (Q.SPECL
          [`number`,
           `number / 2`, `number / 2 / 2`,
           `number / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2 / 2 / 2`,
           `number / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2`,
           `number % 2`, `(number / 2) % 2`,
           `(number / 2 / 2) % 2`,
           `(number / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2 / 2 / 2) % 2`,
           `(number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2`]
          source_integer_eight_step)
  >> simp[source_integer_division_two]
QED

Theorem source_integer_mod_256_horner:
  !number : int.
    number % 256 =
    source_int_horner8
      (number % 2) ((number / 2) % 2)
      ((number / 2 / 2) % 2) ((number / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2) % 2)
      ((number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2)
Proof
  gen_tac
  >> irule integerTheory.INT_MOD_UNIQUE
  >> qexists_tac
       `number / 2 / 2 / 2 / 2 / 2 / 2 / 2 / 2`
  >> simp[]
  >> conj_tac
  >- simp[source_integer_eight_bit_expansion]
  >> irule source_int_horner8_bounds
  >> simp[source_integer_remainder_two_bounds]
QED

Theorem source_num_mod_256_horner:
  !number : int.
    Num (number % 256) =
    source_horner8
      (number % 2 = 1) ((number / 2) % 2 = 1)
      ((number / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2 / 2 / 2) % 2 = 1)
      ((number / 2 / 2 / 2 / 2 / 2 / 2 / 2) % 2 = 1)
Proof
  gen_tac
  >> SIMP_TAC bool_ss [GSYM integerTheory.INT_INJ]
  >> `0 <= number % 256`
       by (mp_tac (Q.SPECL [`number`, `256`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `&Num (number % 256) = number % 256`
       by metis_tac[integerTheory.INT_OF_NUM]
  >> pop_assum (fn theorem => ONCE_REWRITE_TAC [theorem])
  >> simp[source_horner8_int, source_integer_low_bit,
          source_integer_mod_256_horner]
QED

Theorem source_char_of_integer_eq_iff:
  !number b0 b1 b2 b3 b4 b5 b6 b7.
    source_char_of_integer number =
    source_Char b0 b1 b2 b3 b4 b5 b6 b7 <=>
    Num (number % 256) =
    source_horner8 b0 b1 b2 b3 b4 b5 b6 b7
Proof
  simp[source_char_of_integer_def, source_Char_def,
       GSYM stringTheory.ORD_11, stringTheory.ORD_CHR_RWT,
       source_integer_byte_bounds, source_horner8_bound]
QED

Theorem source_char_of_integer_code:
  !number : int.
    source_char_of_integer number =
    (let (q0, b0) = source_bit_cut_integer number in
     let (q1, b1) = source_bit_cut_integer q0 in
     let (q2, b2) = source_bit_cut_integer q1 in
     let (q3, b3) = source_bit_cut_integer q2 in
     let (q4, b4) = source_bit_cut_integer q3 in
     let (q5, b5) = source_bit_cut_integer q4 in
     let (q6, b6) = source_bit_cut_integer q5 in
     let (q7, b7) = source_bit_cut_integer q6 in
       source_Char b0 b1 b2 b3 b4 b5 b6 b7)
Proof
  gen_tac
  >> simp[source_char_of_integer_def, source_bit_cut_integer_def,
          source_Char_def, GSYM stringTheory.ORD_11,
          stringTheory.ORD_CHR_RWT, source_horner8_bound,
          source_integer_byte_bounds]
  >> SIMP_TAC bool_ss [GSYM integerTheory.INT_INJ]
  >> `0 <= number % 256`
       by (mp_tac (Q.SPECL [`number`, `256`]
             integerTheory.INT_MOD_BOUNDS)
           >> simp[])
  >> `&Num (number % 256) = number % 256`
       by metis_tac[integerTheory.INT_OF_NUM]
  >> pop_assum (fn theorem => ONCE_REWRITE_TAC [theorem])
  >> SIMP_TAC bool_ss
       [source_horner8_int, source_integer_low_bit]
  >> simp[source_integer_mod_256_horner]
QED

Theorem source_integer_of_char_code:
  !b0 b1 b2 b3 b4 b5 b6 b7.
    source_integer_of_char
      (source_Char b0 b1 b2 b3 b4 b5 b6 b7) =
    &source_horner8 b0 b1 b2 b3 b4 b5 b6 b7
Proof
  simp[source_integer_of_char_def, source_Char_def,
       source_horner8_bound, stringTheory.ORD_CHR_RWT]
QED

Theorem source_char_of_integer_of_char:
  !character.
    source_char_of_integer (&source_of_char character) = character
Proof
  simp[source_char_of_integer_def, source_of_char_def,
       integerTheory.INT_MOD, arithmeticTheory.LESS_MOD,
       stringTheory.ORD_BOUND, stringTheory.CHR_ORD]
QED

Definition source_literal_asciis_def:
  source_literal_asciis literal =
    MAP source_integer_of_char (source_literal_explode literal)
End

Definition source_literal_of_asciis_def:
  source_literal_of_asciis numbers =
    source_literal_abs
      (MAP (source_ascii_of o source_char_of_integer) numbers)
End

Theorem source_literal_of_asciis_valid:
  !numbers.
    source_literal_valid
      (MAP (source_ascii_of o source_char_of_integer) numbers)
Proof
  simp[source_literal_valid_def, listTheory.EVERY_MAP,
       source_ascii_of_bound]
QED

Theorem source_literal_explode_bound:
  !literal character.
    MEM character (source_literal_explode literal) ==>
    ORD character < 128
Proof
  rpt strip_tac
  >> mp_tac (SPEC ``literal : source_literal``
       source_literal_explode_valid)
  >> simp[source_literal_valid_def, listTheory.EVERY_MEM]
  >> metis_tac[]
QED

Theorem source_literal_character_code_roundtrip:
  !character.
    ORD character < 128 ==>
    source_ascii_of
      (source_char_of_integer (source_integer_of_char character)) =
    character
Proof
  simp[source_integer_of_char_def, GSYM source_of_char_def,
       source_char_of_integer_of_char, source_ascii_of_idem]
QED

Theorem source_literal_roundtrip_map_valid:
  !literal.
    source_literal_valid
      (MAP
        (source_ascii_of o source_char_of_integer o
         source_integer_of_char)
        (source_literal_explode literal))
Proof
  simp[source_literal_valid_def, listTheory.EVERY_MAP,
       source_ascii_of_bound]
QED

Theorem source_literal_roundtrip_map:
  !characters.
    source_literal_valid characters ==>
    MAP
      (source_ascii_of o source_char_of_integer o
       source_integer_of_char)
      characters = characters
Proof
  Induct
  >> simp[source_literal_valid_def,
          source_literal_character_code_roundtrip]
QED

Theorem source_literal_of_asciis_asciis:
  !literal.
    source_literal_of_asciis (source_literal_asciis literal) = literal
Proof
  gen_tac
  >> rw[GSYM source_literal_explode_11,
        source_literal_of_asciis_def, source_literal_asciis_def]
  >> rw[source_literal_explode_abs,
        source_literal_of_asciis_valid,
        source_literal_roundtrip_map_valid]
  >> simp[listTheory.MAP_MAP_o]
  >> irule source_literal_roundtrip_map
  >> simp[source_literal_explode_valid]
QED

(* Isabelle/HOL src/HOL/String.thy:914-921.  Code.abort has this
   ordinary logical meaning; the target-language exception hook is not
   part of the theorem statement. *)
Definition source_abort_def:
  source_abort (_ : source_literal) (function : unit -> 'a) = function ()
End

(* Isabelle/HOL src/HOL/List.thy:3345-3351.  The code-abort declaration
   affects extraction only; logically this is application to EMPTY. *)
Definition source_abort_empty_set_def:
  source_abort_empty_set (function : 'a set -> 'a) = function EMPTY
End

(* Isabelle/HOL src/HOL/List.thy:2088.  Isabelle's partial list selectors
   use the same polymorphic undefined value on the empty list, whereas
   HOL4's independently specified HD and LAST need not agree there. *)
Definition source_hd_def:
  source_hd ([] : 'a list) = ARB /\
  source_hd (head::tail) = head
End

Definition source_last_def:
  source_last ([] : 'a list) = ARB /\
  source_last (head::tail) =
    if tail = [] then head else source_last tail
End

Theorem source_hd_nonempty:
  !items : 'a list.
    items <> [] ==> source_hd items = HD items
Proof
  Cases >> simp[source_hd_def]
QED

Theorem source_last_nonempty:
  !items : 'a list.
    items <> [] ==> source_last items = LAST items
Proof
  Induct >> simp[source_last_def, listTheory.LAST_DEF]
QED

Theorem source_hd_nil_eq_last_nil:
  source_hd ([] : 'a list) = source_last []
Proof
  simp[source_hd_def, source_last_def]
QED

Theorem source_set_empty_abort:
  !function.
    function (LIST_TO_SET []) = source_abort_empty_set function
Proof
  simp[source_abort_empty_set_def]
QED

(* Isabelle/HOL src/HOL/List.thy:994-1011. *)
Theorem source_hd_append:
  !xs ys : 'a list.
    HD (xs ++ ys) = if xs = [] then HD ys else HD xs
Proof
  Cases
  >> simp[]
QED

Theorem source_last_append:
  !xs ys : 'a list.
    LAST (xs ++ ys) = if ys = [] then LAST xs else LAST ys
Proof
  Cases_on `ys`
  >> simp[listTheory.LAST_APPEND_CONS]
QED

Theorem source_front_append:
  !xs ys : 'a list.
    FRONT (xs ++ ys) = if ys = [] then FRONT xs else xs ++ FRONT ys
Proof
  Cases_on `ys` THENL
    [simp[],
     REWRITE_TAC [listTheory.NOT_CONS_NIL, boolTheory.COND_CLAUSES]
     >> MATCH_ACCEPT_TAC
          (Q.SPECL [`xs : 'a list`, `t : 'a list`, `h : 'a`]
             rich_listTheory.FRONT_APPEND)]
QED

Theorem source_mem_front:
  !value (items : 'a list).
    MEM value (FRONT items) ==> MEM value items
Proof
  Cases_on `items` THENL
    [simp[], metis_tac[rich_listTheory.MEM_FRONT]]
QED

Theorem source_front_by_take:
  !items : 'a list.
    FRONT items = TAKE (LENGTH items - 1) items
Proof
  Cases_on `items`
  >> simp[rich_listTheory.FRONT_BY_TAKE]
QED

Theorem source_lt_length_take:
  !index limit (items : 'a list).
    index < LENGTH (TAKE limit items) <=>
    index < limit /\ index < LENGTH items
Proof
  rpt gen_tac
  >> Cases_on `limit <= LENGTH items`
  >> fs[listTheory.LENGTH_TAKE_EQ]
  >> Omega.OMEGA_TAC
QED

Theorem source_lt_length_drop:
  !index limit (items : 'a list).
    index < LENGTH (DROP limit items) <=>
    index + limit < LENGTH items
Proof
  rw[listTheory.LENGTH_DROP]
  >> Omega.OMEGA_TAC
QED

Theorem source_less_not_ge:
  !left right : num.
    left < right ==> ~(right <= left)
Proof
  Omega.OMEGA_TAC
QED

Theorem source_not_add_less_left:
  !left right : num.
    ~(left + right < left)
Proof
  Omega.OMEGA_TAC
QED

Theorem source_dropWhile_nonempty:
  !predicate (items : 'a list).
    EXISTS ($~ o predicate) items ==>
    dropWhile predicate items <> []
Proof
  REWRITE_TAC
    [listTheory.dropWhile_eq_nil, listTheory.EVERY_NOT_EXISTS,
     combinTheory.o_DEF]
QED

Theorem source_last_suffix:
  !whole suffix : 'a list.
    IS_SUFFIX whole suffix ==>
    suffix <> [] ==>
    LAST suffix = LAST whole
Proof
  rw[rich_listTheory.IS_SUFFIX_APPEND]
  >> ONCE_REWRITE_TAC[boolTheory.EQ_SYM_EQ]
  >> irule rich_listTheory.LAST_APPEND_NOT_NIL
  >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem source_zip_map_fst_snd:
  !pairs : ('a # 'b) list.
    ZIP (MAP FST pairs, MAP SND pairs) = pairs
Proof
  REWRITE_TAC
    [GSYM listTheory.UNZIP_MAP, listTheory.ZIP_UNZIP]
QED

Theorem source_count_list_zero:
  !value (items : 'a list).
    LIST_ELEM_COUNT value items = 0 <=> ~MEM value items
Proof
  ONCE_REWRITE_TAC
    [GSYM arithmeticTheory.NOT_LT_ZERO_EQ_ZERO]
  >> REWRITE_TAC
       [REWRITE_RULE [arithmeticTheory.GREATER_DEF]
          rich_listTheory.LIST_ELEM_COUNT_MEM]
QED

Theorem source_length_nub_card:
  !items : 'a list.
    LENGTH (nub items) = CARD (LIST_TO_SET items)
Proof
  ONCE_REWRITE_TAC[boolTheory.EQ_SYM_EQ]
  >> MATCH_ACCEPT_TAC listTheory.CARD_LIST_TO_SET_EQN
QED

Definition source_takeWhile_def[simp]:
  (source_takeWhile predicate [] = []) /\
  (source_takeWhile predicate (head::tail) =
     if predicate head then
       head::source_takeWhile predicate tail
     else [])
End

Theorem source_takeWhile_all:
  !predicate (items : 'a list).
    EVERY predicate items ==>
    source_takeWhile predicate items = items
Proof
  gen_tac
  >> Induct
  >> simp[source_takeWhile_def]
QED

Theorem source_takeWhile_none:
  !predicate (items : 'a list).
    EVERY ($~ o predicate) items ==>
    source_takeWhile predicate items = []
Proof
  gen_tac
  >> Cases
  >> simp[source_takeWhile_def, combinTheory.o_DEF]
QED

Theorem source_dropWhile_eq_self_iff:
  !predicate (items : 'a list).
    dropWhile predicate items = items <=>
    items = [] \/ ~predicate (source_hd items)
Proof
  gen_tac
  >> Cases
  >> simp[source_hd_def, listTheory.dropWhile_id]
QED

Theorem source_hd_replicate:
  !count (item : 'a).
    source_hd (REPLICATE count item) =
    if count = 0 then ARB else item
Proof
  Cases
  >> simp[source_hd_def]
QED

Theorem source_replicate_hd_disjunction:
  !count (item : 'a) predicate.
    (count = 0 \/ predicate (HD (REPLICATE count item)) <=>
     count = 0 \/ predicate item)
Proof
  Cases
  >> simp[rich_listTheory.REPLICATE]
QED

Theorem source_replicate_hd_disjunction_neg:
  !count (item : 'a) predicate.
    ~predicate item ==>
    count = 0 \/ ~predicate (HD (REPLICATE count item))
Proof
  Cases
  >> simp[rich_listTheory.REPLICATE]
QED

(* Isabelle/HOL src/HOL/List.thy:2529-2553. *)
Theorem source_takeWhile_dropWhile_id:
  !predicate (items : 'a list).
    source_takeWhile predicate items ++ dropWhile predicate items = items
Proof
  gen_tac
  >> Induct
  >> simp[source_takeWhile_def]
  >> rw[]
QED

Theorem source_takeWhile_append1:
  !predicate (items : 'a list) suffix item.
    MEM item items ==>
    ~predicate item ==>
    source_takeWhile predicate (items ++ suffix) =
    source_takeWhile predicate items
Proof
  gen_tac
  >> Induct_on `items`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `predicate h`
  >> simp[source_takeWhile_def]
  >> metis_tac[]
QED

Theorem source_takeWhile_append2:
  !predicate (items : 'a list) suffix.
    EVERY predicate items ==>
    source_takeWhile predicate (items ++ suffix) =
    items ++ source_takeWhile predicate suffix
Proof
  gen_tac
  >> Induct_on `items`
  >> simp[source_takeWhile_def]
QED

Theorem source_takeWhile_eq_nil_iff:
  !predicate (items : 'a list).
    source_takeWhile predicate items = [] <=>
    items = [] \/ ~predicate (HD items)
Proof
  rpt gen_tac
  >> Cases_on `items`
  >> simp[source_takeWhile_def]
  >> Cases_on `predicate h`
  >> simp[]
QED

(* Isabelle/HOL src/HOL/List.thy:2566-2574. *)
Theorem source_dropWhile_append1:
  !predicate (items : 'a list) suffix item.
    MEM item items ==>
    ~predicate item ==>
    dropWhile predicate (items ++ suffix) =
    dropWhile predicate items ++ suffix
Proof
  rpt strip_tac
  >> irule listTheory.dropWhile_APPEND_EXISTS
  >> simp[listTheory.EXISTS_MEM, combinTheory.o_DEF]
  >> metis_tac[]
QED

Theorem source_dropWhile_append2:
  !predicate (items : 'a list) suffix.
    EVERY predicate items ==>
    dropWhile predicate (items ++ suffix) =
    dropWhile predicate suffix
Proof
  metis_tac[listTheory.dropWhile_APPEND_EVERY]
QED

Theorem source_list_rel_all_mem_aux:
  (!left right.
     relation left right ==>
     (left_predicate left <=> right_predicate right)) ==>
  !left_items right_items.
    LIST_REL relation left_items right_items ==>
    ((!item. MEM item left_items ==> left_predicate item) <=>
     !item. MEM item right_items ==> right_predicate item)
Proof
  strip_tac
  >> Induct_on `LIST_REL`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_list_rel_all_mem:
  !relation left_items right_items.
    LIST_REL relation left_items right_items ==>
    !left_predicate right_predicate.
    (!left right.
       relation left right ==>
       (left_predicate left <=> right_predicate right)) ==>
    ((!item. MEM item left_items ==> left_predicate item) <=>
     !item. MEM item right_items ==> right_predicate item)
Proof
  rpt gen_tac
  >> strip_tac
  >> rpt gen_tac
  >> strip_tac
  >> irule source_list_rel_all_mem_aux
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/Map.thy:193-845. *)
Definition source_alookup_def[simp]:
  (source_alookup ([] : ('a # 'b) list) key = NONE) /\
  (source_alookup ((stored_key,value)::rest) key =
     if key = stored_key then SOME value
     else source_alookup rest key)
End

Overload ALOOKUP = “source_alookup”

Theorem source_alookup_append:
  !left right key.
    source_alookup (left ++ right) key =
    option_CASE (source_alookup left key)
      (source_alookup right key) SOME
Proof
  Induct
  >- simp[source_alookup_def]
  >> Cases_on `h`
  >> rpt gen_tac
  >> simp[source_alookup_def]
  >> Cases_on `key = q`
  >> simp[]
QED

Theorem source_option_overlay_assoc:
  !first second third.
    option_CASE (option_CASE first second SOME) third SOME =
    option_CASE first (option_CASE second third SOME) SOME
Proof
  Cases
  >> simp[]
QED

Theorem source_option_overlay_not_none:
  !left right.
    (option_CASE right left SOME <> NONE <=>
     right <> NONE \/ left <> NONE)
Proof
  Cases_on `right`
  >> Cases_on `left`
  >> simp[]
QED

Theorem source_map_upds_cons_pointwise:
  !function head_key tail_keys head_value tail_values key.
    option_CASE
      (source_alookup
        (REVERSE
          (ZIP
            (head_key::tail_keys, head_value::tail_values))) key)
      (function key) SOME =
    option_CASE
      (source_alookup
        (REVERSE (ZIP (tail_keys, tail_values))) key)
      (if key = head_key then SOME head_value else function key) SOME
Proof
  rpt gen_tac
  >> simp[listTheory.ZIP_def, listTheory.REVERSE_DEF,
          source_alookup_append, source_alookup_def]
  >> Cases_on
       `source_alookup
          (REVERSE (ZIP (tail_keys, tail_values))) key`
  >> Cases_on `key = head_key`
  >> simp[]
QED

Theorem source_alookup_some_mem:
  !pairs key value.
    source_alookup pairs key = SOME value ==>
    MEM (key,value) pairs
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[source_alookup_def]
  >> Cases_on `h`
  >> Cases_on `key = q`
  >> fs[source_alookup_def]
QED

Theorem source_mem_alookup_some:
  !pairs key value.
    MEM (key,value) pairs ==>
    ?result. source_alookup pairs key = SOME result
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[source_alookup_def]
  >> Cases_on `h`
  >> Cases_on `key = q`
  >> fs[source_alookup_def]
  >> metis_tac[]
QED

Theorem source_mem_fst:
  !pairs key value.
    MEM (key,value) pairs ==>
    MEM key (MAP FST pairs)
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[]
  >> gen_tac
  >> Cases_on `h`
  >> simp[]
  >> metis_tac[]
QED

Theorem source_distinct_keys_unique:
  !pairs key left right.
    ALL_DISTINCT (MAP FST pairs) /\
    MEM (key,left) pairs /\ MEM (key,right) pairs ==>
    left = right
Proof
  rpt gen_tac
  >> Induct_on `pairs`
  >- simp[]
  >> Cases_on `h`
  >> rw[]
  >> imp_res_tac source_mem_fst
  >> fs[]
QED

Theorem source_mem_map_fst_zip:
  !key keys values.
    MEM key (MAP FST (ZIP (keys,values))) ==>
    MEM key keys
Proof
  gen_tac
  >> Induct_on `keys`
  >- simp[listTheory.ZIP_def]
  >> Cases_on `values`
  >- simp[listTheory.ZIP_def]
  >> simp[listTheory.ZIP_def]
  >> metis_tac[]
QED

Theorem source_mem_fst_zip:
  !pair keys values.
    MEM pair (ZIP (keys,values)) ==>
    MEM (FST pair) keys
Proof
  rpt strip_tac
  >> `MEM (FST pair) (MAP FST (ZIP (keys,values)))`
       by metis_tac[listTheory.MEM_MAP]
  >> metis_tac[source_mem_map_fst_zip]
QED

Theorem source_map_fst_zip_take:
  !keys values.
    MAP FST (ZIP (keys,values)) =
    TAKE (LENGTH values) keys
Proof
  Induct_on `keys`
  >> Cases_on `values`
  >> simp[listTheory.ZIP_def]
QED

Theorem source_mem_fst_zip_take:
  !pair keys values.
    MEM pair (ZIP (keys,values)) ==>
    MEM (FST pair) (TAKE (LENGTH values) keys)
Proof
  rpt strip_tac
  >> `MEM (FST pair) (MAP FST (ZIP (keys,values)))`
       by metis_tac[listTheory.MEM_MAP]
  >> fs[source_map_fst_zip_take]
QED

Theorem source_alookup_reverse_zip_none:
  !key keys values.
    ~MEM key (TAKE (LENGTH values) keys) ==>
    ALOOKUP (REVERSE (ZIP (keys,values))) key = NONE
Proof
  rpt gen_tac
  >> strip_tac
  >> Cases_on `ALOOKUP (REVERSE (ZIP (keys,values))) key`
  >- simp[]
  >> pop_assum
       (fn th => assume_tac
          (MATCH_MP
             (Q.SPECL
                [`REVERSE (ZIP (keys,values))`, `key`, `x`]
                source_alookup_some_mem)
             th))
  >> fs[listTheory.MEM_REVERSE]
  >> pop_assum
       (fn th => assume_tac
          (MATCH_MP
             (Q.SPECL
                [`(key,x)`, `keys`, `values`]
                source_mem_fst_zip_take)
             th))
  >> fs[]
QED

Theorem source_alookup_reverse_zip_some:
  !key keys values.
    MEM key (TAKE (LENGTH values) keys) ==>
    ?result.
      ALOOKUP (REVERSE (ZIP (keys,values))) key = SOME result
Proof
  rpt strip_tac
  >> `MEM key (MAP FST (ZIP (keys,values)))`
       by fs[source_map_fst_zip_take]
  >> `?pair.
        key = FST pair /\ MEM pair (ZIP (keys,values))`
       by metis_tac[listTheory.MEM_MAP]
  >> pop_assum strip_assume_tac
  >> Cases_on `pair`
  >> fs[]
  >> `MEM (key,r) (REVERSE (ZIP (keys,values)))`
       by fs[listTheory.MEM_REVERSE]
  >> metis_tac[source_mem_alookup_some]
QED

Theorem source_alookup_reverse_zip_is_some:
  !key keys values.
    (?result.
       ALOOKUP (REVERSE (ZIP (keys,values))) key = SOME result) <=>
    MEM key (TAKE (LENGTH values) keys)
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> pop_assum
           (fn th => assume_tac
              (MATCH_MP
                 (Q.SPECL
                    [`REVERSE (ZIP (keys,values))`, `key`, `result`]
                    source_alookup_some_mem)
                 th))
      >> fs[listTheory.MEM_REVERSE]
      >> pop_assum
           (fn th => assume_tac
              (MATCH_MP
                 (Q.SPECL
                    [`(key,result)`, `keys`, `values`]
                    source_mem_fst_zip_take)
                 th))
      >> fs[])
  >> strip_tac
  >> pop_assum
       (fn th => ACCEPT_TAC
          (MATCH_MP
             (Q.SPECL [`key`, `keys`, `values`]
                source_alookup_reverse_zip_some)
             th))
QED

(* src/HOL/Map.thy: map_upd_upds_conv_if. *)
Theorem source_map_upd_upds_conv_if:
  !function key value keys values.
    (\query.
       option_CASE
         (ALOOKUP (REVERSE (ZIP (keys,values))) query)
         (if query = key then SOME value else function query)
         SOME) =
    if MEM key (TAKE (LENGTH values) keys) then
      (\query.
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (function query)
           SOME)
    else
      (\query.
         if query = key then SOME value
         else
           option_CASE
             (ALOOKUP (REVERSE (ZIP (keys,values))) query)
             (function query)
             SOME)
Proof
  rpt gen_tac
  >> simp[boolTheory.FUN_EQ_THM]
  >> gen_tac
  >> Cases_on `query = key`
  >> fs[]
  >> Cases_on `ALOOKUP (REVERSE (ZIP (keys,values))) key`
  >> fs[GSYM source_alookup_reverse_zip_is_some]
QED

Theorem source_not_mem_take:
  !key keys count.
    ~MEM key keys ==>
    ~MEM key (TAKE count keys)
Proof
  metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem source_alookup_reverse_zip_none_full:
  !key keys values.
    ~MEM key keys ==>
    ALOOKUP (REVERSE (ZIP (keys,values))) key = NONE
Proof
  metis_tac[source_not_mem_take,
            source_alookup_reverse_zip_none]
QED

Theorem source_alookup_reverse_zip_some_mem:
  !key value keys values.
    ALOOKUP (REVERSE (ZIP (keys,values))) key = SOME value ==>
    MEM key keys
Proof
  rpt strip_tac
  >> CCONTR_TAC
  >> fs[source_alookup_reverse_zip_none_full]
QED

Theorem source_option_update_twist:
  !lookup function key value.
    lookup key = NONE ==>
    (\query.
       option_CASE (lookup query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else option_CASE (lookup query) (function query) SOME)
Proof
  rpt strip_tac
  >> simp[boolTheory.FUN_EQ_THM]
  >> gen_tac
  >> Cases_on `query = key`
  >> fs[]
QED

Theorem source_alookup_update_twist:
  !entries function key value.
    ALOOKUP entries key = NONE ==>
    (\query.
       option_CASE (ALOOKUP entries query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else option_CASE (ALOOKUP entries query) (function query) SOME)
Proof
  metis_tac[source_option_update_twist]
QED

Theorem source_map_upd_upds_conv_not_mem:
  !function key value keys values.
    ~MEM key (TAKE (LENGTH values) keys) ==>
    (\query.
       option_CASE
         (ALOOKUP (REVERSE (ZIP (keys,values))) query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (function query)
           SOME)
Proof
  rpt strip_tac
  >> rw[source_map_upd_upds_conv_if]
QED

Theorem source_map_upd_upds_twist_full:
  !function key value keys values.
    ~MEM key keys ==>
    (\query.
       option_CASE
         (ALOOKUP (REVERSE (ZIP (keys,values))) query)
         (if query = key then SOME value else function query)
         SOME) =
    (\query.
       if query = key then SOME value
       else
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (function query)
           SOME)
Proof
  metis_tac[source_not_mem_take, source_map_upd_upds_conv_not_mem]
QED

Theorem source_map_upd_upds_twist_full_iff:
  !function key value keys values.
    ((~MEM key keys ==>
      (\query.
         option_CASE
           (ALOOKUP (REVERSE (ZIP (keys,values))) query)
           (if query = key then SOME value else function query)
           SOME) =
      (\query.
         if query = key then SOME value
         else
           option_CASE
             (ALOOKUP (REVERSE (ZIP (keys,values))) query)
             (function query)
             SOME)) <=> T)
Proof
  simp[source_map_upd_upds_twist_full]
QED

Theorem source_finite_graph_alookup:
  !entries.
    FINITE
      (\pair.
         alist$ALOOKUP entries (FST pair) = SOME (SND pair))
Proof
  gen_tac
  >> irule pred_setTheory.SUBSET_FINITE
  >> qexists_tac `LIST_TO_SET entries`
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[alistTheory.ALOOKUP_MEM, pairTheory.PAIR]
QED

Theorem source_ran_update_old_witness:
  !function key old_value new_value value candidate.
    function key = SOME old_value ==>
    function candidate = SOME value ==>
    value <> old_value ==>
    ?witness.
      (witness = key ==> new_value = value) /\
      (witness <> key ==> function witness = SOME value)
Proof
  rpt strip_tac
  >> qexists_tac `candidate`
  >> Cases_on `candidate = key`
  >> fs[]
QED

Theorem source_ran_update_new_witness:
  !function key new_value value.
    value = new_value ==>
    ?witness.
      (witness = key ==> new_value = value) /\
      (witness <> key ==> function witness = SOME value)
Proof
  rpt strip_tac
  >> qexists_tac `key`
  >> simp[]
QED

Theorem source_ran_update_injective_pointwise:
  !function key old_value new_value.
    function key = SOME old_value ==>
    (!left right.
       (?value. function left = SOME value) /\
       (?value. function right = SOME value) ==>
       function left = function right ==>
       left = right) ==>
    (!candidate. function candidate <> SOME new_value) ==>
    !value.
      ((?candidate.
          (candidate = key ==> new_value = value) /\
          (candidate <> key ==> function candidate = SOME value)) <=>
       ((?candidate. function candidate = SOME value) /\
        value <> old_value) \/
       value = new_value)
Proof
  rpt gen_tac
  >> strip_tac
  >> strip_tac
  >> strip_tac
  >> gen_tac
  >> eq_tac
  >> metis_tac[source_ran_update_old_witness,
                source_ran_update_new_witness]
QED

Theorem source_ran_update_injective_pointwise_iff:
  !function key old_value new_value.
    ((function key = SOME old_value ==>
      (!left right.
         (?value. function left = SOME value) /\
         (?value. function right = SOME value) ==>
         function left = function right ==>
         left = right) ==>
      (!candidate. function candidate <> SOME new_value) ==>
      !value.
        ((?candidate.
            (candidate = key ==> new_value = value) /\
            (candidate <> key ==> function candidate = SOME value)) <=>
         ((?candidate. function candidate = SOME value) /\
          value <> old_value) \/
         value = new_value)) <=> T)
Proof
  rpt gen_tac
  >> rewrite_tac[boolTheory.EQ_CLAUSES]
  >> qspecl_then [`function`, `key`, `old_value`, `new_value`]
       MATCH_ACCEPT_TAC source_ran_update_injective_pointwise
QED

Theorem source_num_set_induction:
  !index predicate.
    ((!numbers.
        0 IN numbers /\
        (!number. number IN numbers ==> SUC number IN numbers) ==>
        index IN numbers) /\
     predicate 0 /\
     (!number. predicate number ==> predicate (SUC number))) ==>
    predicate index
Proof
  rpt strip_tac
  >> first_x_assum
       (qspec_then `\number. predicate number` mp_tac)
  >> simp[]
QED

Theorem source_num_set_induction_iff:
  !index predicate.
    (((!numbers.
         0 IN numbers /\
         (!number. number IN numbers ==> SUC number IN numbers) ==>
         index IN numbers) /\
      predicate 0 /\
      (!number. predicate number ==> predicate (SUC number))) ==>
     predicate index) <=>
    T
Proof
  simp[source_num_set_induction]
QED

(* src/HOL/Map.thy: map_le_antisym and map_add_le_mapI. *)
Theorem source_map_le_antisym:
  !left right.
    (!key value.
       left key = SOME value ==>
       right key = SOME value) ==>
    (!key value.
       right key = SOME value ==>
       left key = SOME value) ==>
    left = right
Proof
  rpt gen_tac
  >> strip_tac
  >> strip_tac
  >> simp[boolTheory.FUN_EQ_THM]
  >> gen_tac
  >> Cases_on `left x`
  >> Cases_on `right x`
  >> res_tac
  >> fs[]
QED

Theorem source_map_add_le_mapI:
  !left right upper.
    (!key value.
       left key = SOME value ==>
       upper key = SOME value) ==>
    (!key value.
       right key = SOME value ==>
       upper key = SOME value) ==>
    !key value.
      option_CASE (right key) (left key) SOME = SOME value ==>
      upper key = SOME value
Proof
  rpt gen_tac
  >> strip_tac
  >> strip_tac
  >> rpt gen_tac
  >> Cases_on `right key`
  >> fs[]
QED

Theorem source_map_add_subsumed_step:
  !left right.
    (!key value.
       left key = SOME value ==>
       right key = SOME value) ==>
    !key.
      (right key = NONE /\ left key = right key) \/
      (?value.
         right key = SOME value /\
         SOME value = right key)
Proof
  rpt gen_tac
  >> strip_tac
  >> gen_tac
  >> Cases_on `left key`
  >> Cases_on `right key`
  >> res_tac
  >> fs[]
QED

Theorem source_range_update_none:
  !mapping key value query.
    mapping key = NONE ==>
    ((?witness.
        (if witness = key then SOME value else mapping witness) =
        SOME query) <=>
     query = value \/
     ?witness. mapping witness = SOME query)
Proof
  rpt strip_tac >>
  eq_tac
  >- (strip_tac >>
      Cases_on `witness = key` >>
      fs[] >>
      metis_tac[]) >>
  strip_tac
  >- (qexists_tac `key` >> simp[]) >>
  qexists_tac `witness` >>
  Cases_on `witness = key` >>
  fs[]
QED

Theorem source_domI:
  !function key value.
    function key = SOME value ==>
    key IN (\candidate. function candidate <> NONE)
Proof
  simp[]
QED

(* Isabelle/HOL src/HOL/List.thy:8687. *)
Theorem source_mem_product:
  !pair (xs : 'a list) (ys : 'b list).
    MEM pair
      (FLAT (MAP (\x. MAP (\y. (x,y)) ys) xs)) <=>
    MEM (FST pair) xs /\ MEM (SND pair) ys
Proof
  rpt gen_tac
  >> Cases_on `pair`
  >> Induct_on `xs`
  >> simp[listTheory.MEM_MAP]
  >> metis_tac[]
QED

(* Isabelle/HOL src/HOL/List.thy:8705. *)
Theorem source_mem_relcomp_row:
  !pair (xy : 'a # 'c) (yzs : ('c # 'b) list).
    MEM pair
      (FLAT
         (MAP
            (\yz.
               if SND xy = FST yz then
                 [(FST xy,SND yz)]
               else [])
            yzs)) <=>
    FST pair = FST xy /\
    MEM (SND xy,SND pair) yzs
Proof
  rpt gen_tac
  >> Cases_on `pair`
  >> Cases_on `xy`
  >> Induct_on `yzs`
  >- simp[]
  >> Cases_on `h`
  >> Cases_on `r' = q''`
  >> fs[boolTheory.LEFT_AND_OVER_OR]
QED

(* Isabelle/HOL src/HOL/List.thy:8705. *)
Theorem source_mem_relcomp:
  !pair (xys : ('a # 'c) list) (yzs : ('c # 'b) list).
    MEM pair
      (FLAT
         (MAP
            (\xy.
               FLAT
                 (MAP
                    (\yz.
                       if SND xy = FST yz then
                         [(FST xy,SND yz)]
                       else [])
                    yzs))
            xys)) <=>
    ?middle.
      MEM (FST pair,middle) xys /\
      MEM (middle,SND pair) yzs
Proof
  rpt gen_tac
  >> Cases_on `pair`
  >> Induct_on `xys`
  >- simp[]
  >> simp[source_mem_relcomp_row]
  >> gen_tac
  >> Cases_on `h`
  >> simp[boolTheory.LEFT_AND_OVER_OR]
  >> metis_tac[]
QED

Theorem source_tl_append:
  !xs ys : 'a list.
    TL (xs ++ ys) =
    list_CASE xs (TL ys) (\value tail. tail ++ ys)
Proof
  Cases
  >> simp[]
QED

Theorem source_num_offset_interval:
  !lower upper value : num.
    lower <= value /\ value < upper <=>
    ?offset. value = lower + offset /\ offset < upper - lower
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qexists_tac `value - lower : num`
      >> (CONJ_TAC THENL
            [ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM]
             >> simp[arithmeticTheory.SUB_ADD],
             Omega.OMEGA_TAC]))
  >> strip_tac
  >> rw[]
  >> (CONJ_TAC THENL
        [MATCH_ACCEPT_TAC
           (Q.SPECL [`lower : num`, `offset : num`]
              arithmeticTheory.LESS_EQ_ADD),
         ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM]
         >> irule
              (iffLR
                (Q.SPECL
                   [`offset : num`, `upper : num`, `lower : num`]
                   arithmeticTheory.SUB_LEFT_LESS))
         >> FIRST_ASSUM ACCEPT_TAC])
QED

Theorem source_num_offset_open_interval:
  !lower upper value : num.
    lower < value /\ value < upper <=>
    ?offset. value = SUC lower + offset /\
             offset < upper - SUC lower
Proof
  metis_tac
    [source_num_offset_interval, arithmeticTheory.LESS_EQ]
QED

Theorem source_num_offset_open_closed:
  !lower upper value : num.
    lower < value /\ value <= upper <=>
    ?offset. value = SUC lower + offset /\
             offset < upper - lower
Proof
  metis_tac
    [source_num_offset_interval, arithmeticTheory.LESS_EQ,
     arithmeticTheory.LT_SUC_LE, arithmeticTheory.SUB_MONO_EQ]
QED

Theorem source_num_offset_closed:
  !lower upper value : num.
    lower <= value /\ value <= upper <=>
    ?offset. value = lower + offset /\
             offset < SUC upper - lower
Proof
  metis_tac
    [source_num_offset_interval, arithmeticTheory.LT_SUC_LE]
QED

(* Isabelle/HOL src/HOL/Transitive_Closure.thy:1452-1497 and
   src/HOL/List.thy:8701-8703.  A set of pairs is represented by its
   characteristic, curried relation.  This is the executable code
   equation for ntrancl: paths of between one and SUC bound steps. *)
Definition source_list_relation_def:
  source_list_relation pairs left right = MEM (left, right) pairs
End

Definition source_ntrancl_def:
  (source_ntrancl 0 relation left right = relation left right) /\
  (source_ntrancl (SUC bound) relation left right =
     (source_ntrancl bound relation left right \/
      ?middle.
        source_ntrancl bound relation left middle /\
        relation middle right))
End

Theorem source_ntrancl_nrc:
  !bound relation left right.
    source_ntrancl bound relation left right <=>
    ?extra. extra <= bound /\
            arithmetic$NRC relation (SUC extra) left right
Proof
  Induct
  >- simp[source_ntrancl_def, arithmeticTheory.NRC_1]
  >> rw[source_ntrancl_def]
  >> eq_tac
  >- (strip_tac
      >- (qexists_tac `extra`
          >> simp[])
      >> qexists_tac `SUC extra`
      >> conj_tac
      >- simp[]
      >> simp[Once arithmeticTheory.NRC_SUC_RECURSE_LEFT]
      >> qexists_tac `middle`
      >> simp[])
  >> strip_tac
  >> Cases_on `extra <= bound`
  >- (disj1_tac
          >> qexists_tac `extra`
      >> simp[])
  >> `extra = SUC bound` by Omega.OMEGA_TAC
  >> disj2_tac
  >> fs[]
  >> qpat_x_assum
       `arithmetic$NRC relation (SUC (SUC bound)) left right`
       mp_tac
  >> simp[Once arithmeticTheory.NRC_SUC_RECURSE_LEFT]
  >> strip_tac
  >> qexists_tac `z`
  >> conj_tac
  >- (qexists_tac `bound`
      >> simp[])
  >> metis_tac[]
QED

Theorem source_lrc_append:
  !relation prefix suffix left right.
    list$LRC relation (prefix ++ suffix) left right <=>
    ?middle.
      list$LRC relation prefix left middle /\
      list$LRC relation suffix middle right
Proof
  gen_tac
  >> Induct
  >- simp[listTheory.LRC_def]
  >> simp[listTheory.LRC_def]
  >> metis_tac[]
QED

Theorem source_lrc_simple:
  !relation path left right.
    list$LRC relation path left right ==>
    ?simple.
      list$LRC relation simple left right /\
      ALL_DISTINCT simple /\
      LIST_TO_SET simple SUBSET LIST_TO_SET path /\
      (path <> [] ==> simple <> [])
Proof
  gen_tac
  >> Induct
  >- (simp[listTheory.LRC_def]
      >> metis_tac[])
  >> rw[listTheory.LRC_def]
  >> first_x_assum drule
  >> strip_tac
  >> Cases_on `MEM h simple`
  >- (`?prefix suffix. simple = prefix ++ h::suffix`
        by metis_tac[listTheory.MEM_SPLIT]
      >> qexists_tac `h::suffix`
      >> fs[source_lrc_append, listTheory.LRC_def]
      >> conj_tac
      >- metis_tac[]
      >> conj_tac
      >- fs[listTheory.ALL_DISTINCT_APPEND]
      >> fs[pred_setTheory.SUBSET_DEF])
  >> qexists_tac `h::simple`
  >> simp[listTheory.LRC_def]
  >> metis_tac[]
QED

Theorem source_lrc_edges:
  !relation path left right.
    list$LRC relation path left right ==>
    ?edges.
      MAP FST edges = path /\
      EVERY (\edge. relation (FST edge) (SND edge)) edges
Proof
  gen_tac
  >> Induct
  >- (simp[listTheory.LRC_def]
      >> metis_tac[])
  >> rw[listTheory.LRC_def]
  >> first_x_assum drule
  >> strip_tac
  >> qexists_tac `(h,z)::edges`
  >> simp[]
QED

Theorem source_lrc_list_relation_bound:
  !pairs path left right.
    list$LRC (source_list_relation pairs) path left right /\
    ALL_DISTINCT path ==>
    LENGTH path <= CARD (LIST_TO_SET pairs)
Proof
  rpt gen_tac
  >> strip_tac
  >> drule source_lrc_edges
  >> strip_tac
  >> `ALL_DISTINCT edges`
       by metis_tac[listTheory.ALL_DISTINCT_MAP]
  >> `LIST_TO_SET edges SUBSET LIST_TO_SET pairs`
       by (fs[listTheory.EVERY_MEM, source_list_relation_def,
              pred_setTheory.SUBSET_DEF]
           >> metis_tac[])
  >> `CARD (LIST_TO_SET edges) <= CARD (LIST_TO_SET pairs)`
       by metis_tac[pred_setTheory.CARD_SUBSET,
                    listTheory.FINITE_LIST_TO_SET]
  >> `LENGTH edges = LENGTH path`
       by metis_tac[listTheory.LENGTH_MAP]
  >> `CARD (LIST_TO_SET edges) = LENGTH edges`
       by metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET]
  >> Omega.OMEGA_TAC
QED

Theorem source_trancl_set_ntrancl:
  !pairs.
    relation$TC (source_list_relation pairs) =
    source_ntrancl (CARD (LIST_TO_SET pairs) - 1)
      (source_list_relation pairs)
Proof
  gen_tac
  >> simp[FUN_EQ_THM, EQ_IMP_THM]
  >> rpt gen_tac
  >> conj_tac
  >- (rpt strip_tac
      >> fs[arithmeticTheory.TC_eq_NRC]
      >> drule (iffLR listTheory.NRC_LRC)
      >> strip_tac
      >> drule source_lrc_simple
      >> strip_tac
      >> `ls <> []` by (Cases_on `ls` >> fs[])
      >> `simple <> []` by metis_tac[]
      >> drule source_lrc_list_relation_bound
      >> impl_tac
      >- simp[]
      >> strip_tac
      >> Cases_on `simple`
      >- fs[]
      >> rw[source_ntrancl_nrc]
      >> qexists_tac `LENGTH t`
      >> conj_tac
      >- (fs[] >> Omega.OMEGA_TAC)
      >> simp[listTheory.NRC_LRC]
      >> qexists_tac `h::t`
      >> simp[])
  >> rpt strip_tac
  >> fs[source_ntrancl_nrc, arithmeticTheory.TC_eq_NRC]
  >> qexists_tac `extra`
  >> metis_tac[]
QED

Theorem source_abort_cong:
  !message message' function.
    message = message' ==>
    source_abort message function = source_abort message' function
Proof
  simp[source_abort_def]
QED

(* src/HOL/Option.thy uses option.split as a local simplifier split rule. *)
Theorem source_option_split:
  !predicate value none_case some_case.
    predicate (option_CASE value none_case some_case) <=>
    ((value = NONE ==> predicate none_case) /\
     !item. value = SOME item ==> predicate (some_case item))
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Option.thy: map_option_case. *)
Theorem source_map_option_case:
  !function value.
    OPTION_MAP function value =
    option_CASE value NONE (\item. SOME (function item))
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Option.thy: rel_option_iff. *)
Theorem source_rel_option_iff:
  !relation left right.
    OPTREL relation left right <=>
    UNCURRY
      (\left_option right_option.
         option_CASE left_option
           (option_CASE right_option T (\right_item. F))
           (\left_item.
              option_CASE right_option F
                (\right_item. relation left_item right_item)))
      (left,right)
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> simp[optionTheory.OPTREL_def]
QED

(* src/HOL/Option.thy: rel_option_unfold. *)
Theorem source_rel_option_unfold:
  !relation left right.
    OPTREL relation left right <=>
    ((IS_NONE left <=> IS_NONE right) /\
     (~IS_NONE left ==>
      ~IS_NONE right ==>
      relation (THE left) (THE right)))
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> simp[optionTheory.OPTREL_def]
QED

(* src/HOL/Option.thy: these_empty_eq. *)
Theorem source_these_empty_eq:
  !source : 'a option set.
    ((\item. SOME item IN source) = {}) <=>
    (source = {} \/ source = {NONE})
Proof
  gen_tac
  >> simp[pred_setTheory.EXTENSION, optionTheory.FORALL_OPTION]
  >> metis_tac[]
QED

Theorem source_no_some_member_none:
  !source value.
    value IN source ==>
    (!item. SOME item NOTIN source) ==>
    NONE IN source
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
  >> metis_tac[]
QED

(* src/HOL/String.thy: card_image on the character representation. *)
Theorem source_chr_inj_count:
  !limit left right.
    limit <= 256 ==>
    left IN count limit ==>
    right IN count limit ==>
    CHR left = CHR right ==>
    left = right
Proof
  rpt strip_tac
  >> fs[]
  >> `left < 256 /\ right < 256` by Omega.OMEGA_TAC
  >> metis_tac[stringTheory.CHR_11]
QED

Theorem source_card_image_chr_count:
  !limit.
    limit <= 256 ==>
    CARD (IMAGE CHR (count limit)) = limit
Proof
  rpt strip_tac
  >> `CARD (IMAGE CHR (count limit)) = CARD (count limit)` by
       (match_mp_tac pred_setTheory.CARD_IMAGE_INJ
        >> conj_tac
        >- metis_tac[source_chr_inj_count]
        >> simp[])
  >> simp[]
QED

(* src/HOL/List.thy uses list.split as a local simplifier split rule. *)
Theorem source_list_split:
  !predicate value nil_case cons_case.
    predicate (list_CASE value nil_case cons_case) <=>
    ((value = [] ==> predicate nil_case) /\
     !head tail. value = head::tail ==>
       predicate (cons_case head tail))
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/List.thy: neq_Nil_conv. *)
Theorem source_neq_nil_conv:
  !items : 'a list.
    items <> [] <=> ?head tail. items = head::tail
Proof
  Cases
  >> simp[]
QED

(* src/HOL/Set.thy uses bool_induct as an introduction rule. *)
Theorem source_bool_induct:
  !predicate value.
    predicate T ==>
    predicate F ==>
    predicate value
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Set.thy: bool_contrapos. *)
Theorem source_bool_contrapos:
  !predicate value.
    predicate value ==>
    ~predicate F ==>
    predicate T
Proof
  rpt gen_tac
  >> Cases_on `value`
  >> simp[]
QED

(* src/HOL/Option.thy: UNIV_option_conv. *)
Theorem source_UNIV_option_conv:
  (UNIV : 'a option set) =
  NONE INSERT IMAGE SOME (UNIV : 'a set)
Proof
  simp[pred_setTheory.EXTENSION, optionTheory.FORALL_OPTION]
QED

(* src/HOL/Set.thy uses conj_cong as a local simplifier congruence. *)
Theorem source_conj_cong:
  !left left' right right'.
    (left <=> left') ==>
    (left' ==> (right <=> right')) ==>
    (left /\ right <=> left' /\ right')
Proof
  metis_tac[]
QED

Theorem source_rev_conj_cong:
  !left left' right right'.
    (right <=> right') ==>
    (right' ==> (left <=> left')) ==>
    (left /\ right <=> left' /\ right')
Proof
  metis_tac[]
QED

(* src/HOL/Set.thy: Uniq_def. *)
Theorem source_unique_member_transfer:
  !family left right shared query.
    (!element first second.
       (family first /\ first element) /\
       family second /\ second element ==>
       !candidate. first candidate = second candidate) ==>
    family left ==>
    family right ==>
    left shared ==>
    right shared ==>
    left query ==>
    right query
Proof
  metis_tac[]
QED

Theorem source_set_zip:
  !xs ys.
    LIST_TO_SET (ZIP (xs, ys)) =
    (\pair.
       ?index.
         pair = (EL index xs, EL index ys) /\
         index < MIN (LENGTH xs) (LENGTH ys))
Proof
  simpLib.SIMP_TAC (clasimpLib.clasimp_ss ())
    [FUN_EQ_THM, pred_setTheory.SPECIFICATION,
     pairTheory.FORALL_PROD, source_set_conv_nth,
     listTheory.LENGTH_ZIP_MIN, source_el_zip_min,
     source_fst_el_zip_min, source_snd_el_zip_min,
     simpLib.Cong source_rev_conj_cong]
QED

(* src/HOL/Product_Type.thy: unique pair selection used by The_split_eq. *)
Theorem source_choice_unique_pair:
  !predicate first second.
    (!left right.
       predicate left right <=> first = left /\ second = right) ==>
    CHOICE (UNCURRY predicate) = (first, second)
Proof
  rpt strip_tac >>
  `UNCURRY predicate = {(first, second)}` by
    (simp[pred_setTheory.EXTENSION, pairTheory.FORALL_PROD,
          pairTheory.PAIR_EQ] >>
     metis_tac[]) >>
  simp[]
QED

(* src/HOL/Product_Type.thy: pair-predicate monotonicity. *)
Theorem source_uncurry_subset_mono:
  !pairs predicate consequence.
    (!left.
       left IN IMAGE FST pairs ==>
       !right.
         right IN IMAGE SND pairs ==>
         predicate left right ==>
         consequence left right) ==>
    pairs SUBSET UNCURRY predicate ==>
    pairs SUBSET UNCURRY consequence
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_IMAGE,
       pairTheory.FORALL_PROD] >>
  metis_tac[pairTheory.FST, pairTheory.SND]
QED

Theorem source_pair_map_inj:
  !left_map right_map left_domain right_domain left_range right_range.
    INJ left_map left_domain left_range ==>
    INJ right_map right_domain right_range ==>
    INJ
      (\pair. (left_map (FST pair), right_map (SND pair)))
      (\pair.
         FST pair IN left_domain /\ SND pair IN right_domain)
      (\pair.
         FST pair IN left_range /\ SND pair IN right_range)
Proof
  simp[pred_setTheory.INJ_DEF, pairTheory.FORALL_PROD,
       pairTheory.PAIR_EQ] >>
  metis_tac[]
QED

Theorem source_pair_map_surj:
  !left_map right_map left_domain right_domain left_range right_range.
    SURJ left_map left_domain left_range ==>
    SURJ right_map right_domain right_range ==>
    SURJ
      (\pair. (left_map (FST pair), right_map (SND pair)))
      (\pair.
         FST pair IN left_domain /\ SND pair IN right_domain)
      (\pair.
         FST pair IN left_range /\ SND pair IN right_range)
Proof
  simp[pred_setTheory.SURJ_DEF, pairTheory.FORALL_PROD,
       pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem source_bij_intro:
  !function domain range.
    INJ function domain range ==>
    SURJ function domain range ==>
    BIJ function domain range
Proof
  metis_tac[pred_setTheory.BIJ_DEF]
QED

Theorem source_bij_components:
  !function domain range.
    BIJ function domain range ==>
    INJ function domain range /\ SURJ function domain range
Proof
  metis_tac[pred_setTheory.BIJ_DEF]
QED

(* src/HOL/Set.thy: membership in a union of an indexed image. *)
Theorem source_mem_bigunion_image:
  !element family indices.
    (element IN BIGUNION (IMAGE family indices) <=>
     ?index. index IN indices /\ element IN family index)
Proof
  simp[pred_setTheory.IN_BIGUNION, pred_setTheory.IN_IMAGE] >>
  metis_tac[]
QED

Theorem source_exists_swapped_conj:
  !first second tail.
    ((?item. first item /\ second item) /\ tail <=>
     ?item. second item /\ first item /\ tail)
Proof
  metis_tac[]
QED

(* src/HOL/Set.thy: subset_imageE. *)
Theorem source_subset_imageE:
  !function source target conclusion.
    source SUBSET IMAGE function target ==>
    (!preimage.
       preimage SUBSET target ==>
       source = IMAGE function preimage ==>
       conclusion) ==>
    conclusion
Proof
  metis_tac[pred_setTheory.SUBSET_IMAGE]
QED

(* src/HOL/List.thy: rev_swap. *)
Theorem source_rev_swap:
  !xs ys.
    REVERSE xs = ys <=> xs = REVERSE ys
Proof
  metis_tac[listTheory.REVERSE_REVERSE]
QED

(* src/HOL/List.thy: split_list. *)
Theorem source_split_list:
  !item items.
    MEM item items ==>
    ?prefix suffix.
      items = prefix ++ item::suffix
Proof
  metis_tac[listTheory.MEM_SPLIT]
QED

(* src/HOL/List.thy: split_list_first and split_list_last. *)
Theorem source_split_list_first:
  !item items.
    MEM item items ==>
    ?prefix suffix.
      items = prefix ++ item::suffix /\
      ~MEM item prefix
Proof
  rpt gen_tac
  >> strip_tac
  >> drule_then strip_assume_tac
       (iffLR listTheory.MEM_SPLIT_APPEND_first)
  >> fs[]
  >> metis_tac[]
QED

Theorem source_split_list_last:
  !item items.
    MEM item items ==>
    ?prefix suffix.
      items = prefix ++ item::suffix /\
      ~MEM item suffix
Proof
  rpt gen_tac
  >> strip_tac
  >> drule_then strip_assume_tac
       (iffLR listTheory.MEM_SPLIT_APPEND_last)
  >> fs[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: split_list_prop. *)
Theorem source_split_list_prop:
  !items predicate.
    (?item. MEM item items /\ predicate item) ==>
    ?prefix item suffix.
      items = prefix ++ item::suffix /\ predicate item
Proof
  metis_tac[listTheory.MEM_SPLIT]
QED

(* src/HOL/List.thy: split_list_first_prop. *)
Theorem source_split_list_first_prop:
  !items predicate.
    (?item. MEM item items /\ predicate item) ==>
    ?prefix item suffix.
      items = prefix ++ item::suffix /\
      predicate item /\
      (!earlier. MEM earlier prefix ==> ~predicate earlier)
Proof
  gen_tac
  >> Induct_on `items`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `predicate h`
  >- (strip_tac
      >> map_every qexists_tac [`[]`, `h`, `items`]
      >> simp[])
  >> strip_tac
  >> qpat_x_assum `!predicate. _`
       (qspec_then `predicate` mp_tac)
  >> impl_tac
  >- (qexists_tac `item`
      >> conj_tac
      >- (Cases_on `item = h` >> fs[])
      >> fs[])
  >> strip_tac
  >> rename [`items = prefix ++ chosen::suffix`]
  >> map_every qexists_tac [`h::prefix`, `chosen`, `suffix`]
  >> simp[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: split_list_last_prop. *)
Theorem source_split_list_last_prop:
  !items predicate.
    (?item. MEM item items /\ predicate item) ==>
    ?prefix item suffix.
      items = prefix ++ item::suffix /\
      predicate item /\
      (!later. MEM later suffix ==> ~predicate later)
Proof
  gen_tac
  >> Induct_on `items`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `?item. MEM item items /\ predicate item`
  >- (strip_tac
      >> qpat_x_assum `!predicate. _`
           (qspec_then `predicate` mp_tac)
      >> impl_tac
      >- simp[]
      >> strip_tac
      >> rename [`items = prefix ++ chosen::suffix`]
      >> map_every qexists_tac [`h::prefix`, `chosen`, `suffix`]
      >> simp[])
  >> strip_tac
  >> map_every qexists_tac [`[]`, `h`, `items`]
  >> fs[]
  >> metis_tac[]
QED

(* src/HOL/List.thy: map_inj_on and map_injective. *)
Theorem source_map_inj_on:
  !function xs ys.
    MAP function xs = MAP function ys ==>
    INJ function (LIST_TO_SET xs UNION LIST_TO_SET ys) UNIV ==>
    xs = ys
Proof
  metis_tac[listTheory.INJ_MAP_EQ]
QED

Theorem source_map_injective:
  !function xs ys.
    MAP function xs = MAP function ys ==>
    INJ function UNIV UNIV ==>
    xs = ys
Proof
  metis_tac[listTheory.INJ_MAP_EQ,
            pred_setTheory.INJ_SUBSET_UNIV]
QED

(* src/HOL/List.thy: inj_mapI and inj_mapD. *)
Theorem source_inj_mapI:
  !function.
    INJ function UNIV UNIV ==>
    INJ (MAP function) UNIV UNIV
Proof
  rpt gen_tac
  >> strip_tac
  >> simp[pred_setTheory.INJ_DEF]
  >> rpt strip_tac
  >> match_mp_tac (Q.SPEC `function` listTheory.INJ_MAP_EQ)
  >> conj_tac
  >- (irule pred_setTheory.INJ_SUBSET_UNIV
      >> FIRST_ASSUM ACCEPT_TAC)
  >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem source_inj_mapD:
  !function.
    INJ (MAP function) UNIV UNIV ==>
    INJ function UNIV UNIV
Proof
  simp[pred_setTheory.INJ_DEF]
  >> rpt strip_tac
  >> rename [`function left = function right`]
  >> qpat_x_assum
       `!xs ys. MAP function xs = MAP function ys ==> xs = ys`
       (qspecl_then [`[left]`, `[right]`] mp_tac)
  >> simp[]
QED

(* src/HOL/Set.thy: inj_onI and inj_onD. *)
Theorem source_inj_onI:
  !function source.
    (!left right.
       left IN source ==>
       right IN source ==>
       function left = function right ==>
       left = right) ==>
    INJ function source UNIV
Proof
  simp[pred_setTheory.INJ_DEF]
QED

Theorem source_inj_onD:
  !function source left right.
    INJ function source UNIV ==>
    left IN source ==>
    right IN source ==>
    function left = function right ==>
    left = right
Proof
  metis_tac[pred_setTheory.INJ_DEF]
QED

(* src/HOL/List.thy: Cons_eq_append_conv. *)
Theorem source_Cons_eq_append_conv:
  !head tail left right.
    (head::tail = left ++ right <=>
     left = [] /\ head::tail = right \/
     ?left_tail.
       head::left_tail = left /\ tail = left_tail ++ right)
Proof
  Cases_on `left`
  >> simp[]
QED

(* src/HOL/List.thy: concat_eq_concat_iff. *)
Theorem source_concat_eq_concat_iff:
  !xs ys.
    (!pair.
       pair IN LIST_TO_SET (ZIP (xs, ys)) ==>
       UNCURRY (\left right. LENGTH left = LENGTH right) pair) ==>
    LENGTH xs = LENGTH ys ==>
    (FLAT xs = FLAT ys <=> xs = ys)
Proof
  Induct
  >> Cases_on `ys`
  >> simp[boolTheory.DISJ_IMP_THM,
          boolTheory.FORALL_AND_THM,
          listTheory.APPEND_11_LENGTH]
QED

Theorem source_concat_eq_concat_iff_curried:
  !xs ys.
    (!left right.
       (left, right) IN LIST_TO_SET (ZIP (xs, ys)) ==>
       LENGTH left = LENGTH right) ==>
    LENGTH xs = LENGTH ys ==>
    (FLAT xs = FLAT ys <=> xs = ys)
Proof
  Induct
  >> Cases_on `ys`
  >> simp[boolTheory.DISJ_IMP_THM,
          boolTheory.FORALL_AND_THM,
          listTheory.APPEND_11_LENGTH]
QED

(* src/HOL/List.thy: concat_eq_appendD. *)
Theorem source_concat_eq_appendD:
  !xss ys zs.
    FLAT xss = ys ++ zs ==>
    xss <> [] ==>
    ?xss1 xs xs' xss2.
      xss = xss1 ++ (xs ++ xs')::xss2 /\
      ys = FLAT xss1 ++ xs /\
      zs = xs' ++ FLAT xss2
Proof
  rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `FLAT xss = ys ++ zs` mp_tac
  >> simp[listTheory.FLAT_EQ_APPEND]
  >> strip_tac
  >> strip_tac
  >- (Cases_on `p` using listTheory.SNOC_CASES
      >- (fs[]
          >> Cases_on `s`
          >> fs[]
          >> map_every qexists_tac [`[]`, `h`, `t`]
          >> simp[])
      >> fs[listTheory.SNOC_APPEND]
      >> map_every qexists_tac [`l`, `x`, `[]`, `s`]
      >> simp[])
  >> map_every qexists_tac [`p`, `ip`, `is`, `s`]
  >> simp[]
QED

(* src/HOL/List.thy: filter_eq_ConsD. *)
Theorem source_filter_eq_ConsD:
  !predicate items head tail.
    FILTER predicate items = head::tail ==>
    ?prefix suffix.
      items = prefix ++ head::suffix /\
      (!item. MEM item prefix ==> ~predicate item) /\
      predicate head /\
      tail = FILTER predicate suffix
Proof
  rpt gen_tac
  >> strip_tac
  >> drule_then strip_assume_tac
       (iffLR listTheory.FILTER_EQ_CONS)
  >> rename [`items = prefix ++ [head] ++ suffix`]
  >> qexists_tac `prefix`
  >> qexists_tac `suffix`
  >> fs[listTheory.FILTER_EQ_NIL,
        listTheory.EVERY_MEM]
QED

Theorem source_filter_eq_ConsI:
  !predicate items head tail prefix suffix.
    items = prefix ++ head::suffix ==>
    (!item. MEM item prefix ==> ~predicate item) ==>
    predicate head ==>
    tail = FILTER predicate suffix ==>
    FILTER predicate items = head::tail
Proof
  rpt strip_tac >>
  fs[listTheory.FILTER_APPEND_DISTRIB, listTheory.FILTER_EQ_NIL,
     listTheory.EVERY_MEM]
QED

(* src/HOL/List.thy: Diff_eq [symmetric] and minus_set_fold. *)
Theorem source_Diff_eq_symmetric:
  !left right.
    left INTER COMPL right = left DIFF right
Proof
  simp[pred_setTheory.EXTENSION,
       pred_setTheory.DIFF_DEF]
QED

Theorem source_fold_delete_commute:
  !items source item.
    FOLDR (\removed result. result DELETE removed)
      (source DELETE item) items =
    FOLDR (\removed result. result DELETE removed)
      source items DELETE item
Proof
  Induct
  >> simp[pred_setTheory.DELETE_COMM]
QED

Theorem source_minus_set_fold:
  !items source.
    source DIFF LIST_TO_SET items =
    FOLDR (\item result. result DELETE item) source items
Proof
  Induct
  >> simp[pred_setTheory.DIFF_INSERT,
          source_fold_delete_commute]
QED

Theorem source_mem_fold_delete:
  !items source value.
    FOLDR (\item result. result DELETE item) source items value <=>
    value IN source /\ ~MEM value items
Proof
  Induct
  >> simp[pred_setTheory.SPECIFICATION,
          pred_setTheory.IN_DELETE]
  >> metis_tac[]
QED

(* src/HOL/List.thy: upt_rec and upt_conv_Cons.  Isabelle's half-open
   interval [start..<finish] is represented by the GENLIST expression
   below throughout the executable corpus. *)
Theorem source_upt_rec:
  !start finish.
    GENLIST (\offset. start + offset) (finish - start) =
    if start < finish then
      start ::
        GENLIST (\offset. SUC start + offset) (finish - SUC start)
    else []
Proof
  rpt gen_tac
  >> Cases_on `start < finish`
  >- (`finish - start = SUC (finish - SUC start)` by decide_tac
      >> SRW_TAC[ARITH_ss]
           [listTheory.GENLIST_CONS, listTheory.GENLIST_FUN_EQ])
  >> `finish - start = 0` by decide_tac
  >> simp[]
QED

Theorem source_tl_num_genlist:
  !start length.
    TL (GENLIST (\offset. start + offset) length) =
    GENLIST (\offset. SUC start + offset) (PRE length)
Proof
  rpt gen_tac
  >> Cases_on `length`
  >- simp[]
  >> simp[listTheory.TL_GENLIST, listTheory.GENLIST_FUN_EQ,
          combinTheory.o_DEF]
QED

(* src/HOL/List.thy: le_Suc_eq and length_Suc_conv at the one-element
   boundary. *)
Theorem source_length_le_one:
  !items : 'a list.
    LENGTH items <= 1 <=>
    items = [] \/ ?item. items = [item]
Proof
  Cases_on `items`
  >> simp[]
  >> Cases_on `t`
  >> simp[]
QED

(* src/HOL/ex/Set_Theory.thy: singleton witnesses used by force. *)
Theorem source_predicate_set_witness:
  !predicate witness.
    predicate witness ==>
    ?aset.
      (!item. item IN aset ==> predicate item) /\
      witness IN aset
Proof
  rpt strip_tac
  >> qexists_tac `{witness}`
  >> simp[]
QED

Theorem source_nonempty_predicate_set:
  !predicate.
    ((?aset.
        (!item. item IN aset ==> predicate item) /\
        ?witness. witness IN aset) <=>
     ?witness. predicate witness)
Proof
  gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac `{witness}`
  >> simp[]
QED

Theorem source_set_separates_image:
  !element forbidden.
    ((?aset.
        element IN aset /\
        !index. forbidden index NOTIN aset) <=>
     !index. element <> forbidden index)
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac `{element}`
  >> simp[]
QED

Theorem source_nonnegative_neq_negative:
  !nonnegative negative : int.
    0 <= nonnegative ==>
    negative < 0 ==>
    nonnegative <> negative
Proof
  intLib.ARITH_TAC
QED

Theorem source_set_separates_two:
  !left element right.
    ((?aset.
        left NOTIN aset /\
        element IN aset /\
        right NOTIN aset) <=>
     left <> element /\ right <> element)
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[]
  >> strip_tac
  >> qexists_tac `{element}`
  >> simp[]
QED

Theorem source_exists_not_member:
  !element. (?aset. element NOTIN aset) <=> T
Proof
  gen_tac
  >> eq_tac
  >- simp[]
  >> strip_tac
  >> qexists_tac `{}`
  >> simp[]
QED

Theorem source_exists_singleton_superset:
  !sets.
    ((?element. sets SUBSET {element}) <=>
     !left right.
       left IN sets /\ right IN sets ==>
       left = right)
Proof
  gen_tac
  >> eq_tac
  >- (simp[pred_setTheory.SUBSET_DEF] >> metis_tac[])
  >> strip_tac
  >> Cases_on `sets = {}`
  >- (qexists_tac `ARB` >> simp[])
  >> `?element. element IN sets` by
       metis_tac[pred_setTheory.MEMBER_NOT_EMPTY]
  >> qexists_tac `element`
  >> simp[pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_set_equality_elim:
  !left right.
    left = right ==>
    left SUBSET right /\ right SUBSET left
Proof
  simp[]
QED

Theorem source_forall_iffD1:
  !predicate other item.
    (!candidate. predicate candidate <=> other candidate) ==>
    predicate item ==>
    other item
Proof
  metis_tac[]
QED

Theorem source_forall_iffD2:
  !predicate other item.
    (!candidate. predicate candidate <=> other candidate) ==>
    other item ==>
    predicate item
Proof
  metis_tac[]
QED

Theorem source_complement_exI:
  !value predicate.
    predicate (COMPL value) ==>
    ?witness.
      value = COMPL witness /\ predicate witness
Proof
  rpt strip_tac
  >> qexists_tac `COMPL value`
  >> simp[]
QED

Theorem source_pow_insert_image_witness:
  !element set subset.
    subset IN POW (element INSERT set) ==>
    element IN subset ==>
    ?base.
      base IN POW set /\
      subset = element INSERT base
Proof
  rpt strip_tac
  >> qexists_tac `subset DELETE element`
  >> fs[pred_setTheory.IN_POW,
        pred_setTheory.SUBSET_DEF,
        pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_pow_insert_image_case:
  !element source subset.
    element IN subset ==>
    subset DELETE element IN POW source ==>
    ?base.
      base IN POW source /\
      subset = element INSERT base
Proof
  rpt strip_tac
  >> qexists_tac `subset DELETE element`
  >> simp[pred_setTheory.INSERT_DELETE]
QED

Theorem source_pow_insert_image_case_iff:
  !element source subset.
    (element IN subset /\
     subset DELETE element IN POW source) <=>
    ?base.
      base IN POW source /\
      subset = element INSERT base
Proof
  rpt gen_tac
  >> eq_tac
  >- metis_tac[source_pow_insert_image_case]
  >> strip_tac
  >> fs[pred_setTheory.IN_POW,
        pred_setTheory.SUBSET_DEF]
  >> rpt strip_tac
  >> fs[]
QED

Theorem source_in_pow_insert:
  !element set subset.
    subset IN POW (element INSERT set) <=>
    subset IN POW set \/
    (element IN subset /\
     subset DELETE element IN POW set)
Proof
  simp[pred_setTheory.IN_POW, pred_setTheory.SUBSET_DEF]
  >> metis_tac[]
QED

Theorem source_doubleton_eq_iff:
  !first second third fourth.
    (first INSERT (second INSERT {}) =
       third INSERT (fourth INSERT {})) <=>
    (first = third /\ second = fourth) \/
    (first = fourth /\ second = third)
Proof
  simp[pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem source_subset_image_iff:
  !target function source.
    target SUBSET IMAGE function source <=>
    ?preimage.
      preimage SUBSET source /\
      target = IMAGE function preimage
Proof
  simp[pred_setTheory.SUBSET_IMAGE]
QED

Theorem source_image_pow_surj:
  !function source target.
    IMAGE function source = target ==>
    IMAGE (IMAGE function) (POW source) = POW target
Proof
  rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `IMAGE function source = target`
       (fn theorem => assume_tac (GSYM theorem))
  >> pop_assum SUBST_ALL_TAC
  >> simp[pred_setTheory.EXTENSION,
          pred_setTheory.IN_POW,
          source_subset_image_iff,
          boolTheory.CONJ_COMM]
QED

Theorem source_image_pow_surj_iff:
  !function source target.
    ((IMAGE function source = target ==>
      IMAGE (IMAGE function) (POW source) = POW target) <=>
     T)
Proof
  simp[source_image_pow_surj]
QED

Theorem source_pow_singleton_iff:
  !source target.
    (POW source = target INSERT {}) <=>
    source = {} /\ target = {}
Proof
  rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> `{} IN POW source` by
           simp[pred_setTheory.IN_POW]
      >> `source IN POW source` by
           simp[pred_setTheory.IN_POW]
      >> qpat_x_assum `POW source = target INSERT {}`
           (fn equality =>
             qpat_x_assum `{} IN POW source`
               (fn empty_member =>
                 qpat_x_assum `source IN POW source`
                   (fn source_member =>
                     map_every assume_tac
                       [REWRITE_RULE [equality] empty_member,
                        REWRITE_RULE [equality] source_member])))
      >> fs[])
  >> strip_tac
  >> fs[pred_setTheory.EXTENSION,
        pred_setTheory.IN_POW,
        pred_setTheory.SUBSET_DEF]
QED

Theorem source_pow_compl:
  !source.
    POW (COMPL source) =
    \subset.
      ?superset.
        subset = COMPL superset /\
        source IN POW superset
Proof
  simp[pred_setTheory.EXTENSION,
       pred_setTheory.IN_POW,
       pred_setTheory.SUBSET_DEF]
  >> rpt gen_tac
  >> eq_tac
  >- (strip_tac
      >> qexists_tac `COMPL x`
      >> simp[]
      >> rpt strip_tac
      >> qpat_x_assum `!item. _`
           (qspec_then `x'` mp_tac)
      >> simp[])
  >> strip_tac
  >> fs[]
  >> rpt strip_tac
  >> qpat_x_assum `!item. item IN source ==> _`
       (qspec_then `x'` mp_tac)
  >> simp[]
QED

Theorem source_pow_compl_iff:
  !source.
    ((POW (COMPL source) =
      \subset.
        ?superset.
          subset = COMPL superset /\
          source IN POW superset) <=>
     T)
Proof
  simp[source_pow_compl]
QED

Theorem source_pairwise_image:
  !relation function source.
    ((!left.
        left IN IMAGE function source ==>
        !right.
          right IN IMAGE function source ==>
          left <> right ==>
          relation left right) <=>
     (!left.
        left IN source ==>
        !right.
          right IN source ==>
          left <> right ==>
          function left <> function right ==>
          relation (function left) (function right)))
Proof
  simp[]
  >> metis_tac[]
QED

Theorem source_is_singleton_bridge:
  !source.
    ((?element. source = {element}) <=>
     pred_set$SING source)
Proof
  simp[pred_setTheory.SING_DEF]
QED

Theorem source_is_singleton_unique:
  !source.
    pred_set$SING source <=>
    ?!element. element IN source
Proof
  simp[pred_setTheory.SING_DEF,
       boolTheory.EXISTS_UNIQUE_THM]
  >> metis_tac[pred_setTheory.UNIQUE_MEMBER_SING]
QED

Theorem source_is_singleton_choice:
  !source.
    pred_set$SING source <=>
    source = {CHOICE source}
Proof
  gen_tac
  >> eq_tac
  >- (strip_tac
      >> fs[pred_setTheory.SING_DEF])
  >> strip_tac
  >> simp[pred_setTheory.SING_DEF]
  >> qexists_tac `CHOICE source`
  >> simp[]
QED

Theorem source_subset_sandwich:
  !lower middle upper.
    lower SUBSET middle ==>
    middle SUBSET upper ==>
    lower = upper ==>
    lower = middle
Proof
  metis_tac[pred_setTheory.SUBSET_ANTISYM]
QED

val _ = export_theory ()
