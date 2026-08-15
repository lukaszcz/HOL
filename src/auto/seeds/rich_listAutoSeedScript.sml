Theory rich_listAutoSeed
Ancestors
  rich_list
Libs
  clasetLib clasimpLib

fun export_iff (name, theorem) =
  let
    val saved = save_thm (name, theorem)
  in
    ThmAttribute.store_at_attribute
      {name = name, attrname = "iff", args = [], thm = saved}
  end

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
