Theory rich_listAutoSeed
Ancestors
  rich_list
Libs
  clasetLib clasimpLib

fun export_at attr (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = attr, args = [], thm = saved}
  end

fun export_iff entry = export_at "iff" entry

val sintro_spec =
  {kind = clasetRules.Intro, safe = true, prio = NONE}
val dest_spec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}
val forward_spec =
  {kind = clasetRules.Forward, safe = false, prio = SOME 10}

(* List.thy analogues and documented HOL4-local structural judgments. *)
val _ =
  List.app export_iff
    [("EVERY_REVERSE_AUTO", rich_listTheory.EVERY_REVERSE),
     ("MEM_REPLICATE_AUTO", rich_listTheory.MEM_REPLICATE),
     ("REPLICATE_NIL_AUTO", rich_listTheory.REPLICATE_NIL),
     ("LIST_REL_REVERSE_EQ_AUTO",
      rich_listTheory.LIST_REL_REVERSE_EQ),
     ("APPEND_EQ_APPEND_EQ_AUTO",
      rich_listTheory.APPEND_EQ_APPEND_EQ),
     ("LENGTH_FILTER_LEQ_AUTO", rich_listTheory.LENGTH_FILTER_LEQ),
     ("FILTER_ALL_DISTINCT_AUTO", listTheory.FILTER_ALL_DISTINCT)]

(* src/HOL/List.thy:3231 @ f7e02b7e.  [fold_append] is simp there and
   declared to no simpset here.  HOL4 reverses [rev (xs @ ys)]
   ambiently but leaves the fold over the result alone, so a goal that
   folds across an append stops one rewrite short. *)
val _ =
  export_at "simp" ("FOLDL_APPEND_AUTO", rich_listTheory.FOLDL_APPEND)

(* src/HOL/List.thy:1824 @ f7e02b7e.  [nth_append_length] is simp there:
   indexing an append at exactly the left length reaches the right
   list's head.  HOL4 states it on a non-empty right list and declares
   it nowhere.  Its [_plus] companion has no HOL4 counterpart, and the
   conditional halves [nth_append_left] and [_right] are simp in
   neither system; see the rest of the indexing family in
   listAutoSeed. *)
val _ =
  export_at "simp" ("EL_LENGTH_APPEND_AUTO", rich_listTheory.EL_LENGTH_APPEND)

(* src/HOL/List.thy @ f7e02b7e.  [take_append] is simp there and
   declared to no simpset here; its [drop_append] counterpart and the
   two length rules that finish the halves are seeded in
   listAutoSeed, which states them. *)
val _ =
  export_at "simp" ("TAKE_APPEND_AUTO", rich_listTheory.TAKE_APPEND)

val _ =
  List.app (clasetLib.export_rule sintro_spec)
    ["rich_list.IS_PREFIX_REFL", "rich_list.IS_SUFFIX_REFL"]

val _ =
  List.app (clasetLib.export_rule dest_spec)
    ["rich_list.EVERY_TAKE", "rich_list.EVERY_DROP",
     "rich_list.MEM_TAKE", "rich_list.MEM_DROP_IMP"]

val _ =
  List.app (clasetLib.export_rule forward_spec)
    ["rich_list.IS_PREFIX_ANTISYM", "rich_list.IS_PREFIX_TRANS",
     "rich_list.IS_SUFFIX_TRANS"]
