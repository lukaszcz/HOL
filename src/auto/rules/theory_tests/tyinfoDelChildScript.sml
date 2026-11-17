Theory tyinfoDelChild
Ancestors
  tyinfoDelBase
Libs
  clasetLib

fun fail message = raise Fail ("claset TypeBase removal test: " ^ message)

val stem = "__claset_tyinfo_tyinfoDelBase_tyinfo_del_"

(* With no removal recorded, loading the parent cannot depend on whether
   the claset was forced first. *)
val _ =
  case Theory.LoadableThyData.segment_data_string
         {thy = "tyinfoDelBase", thydataty = "claset.deltas"} of
      NONE => ()
    | SOME data =>
        if String.isSubstring stem data then
          fail "a refused removal was recorded as a delta"
        else ()

val cs = the_claset ()

val _ =
  if not (List.exists (fn (_, (name, _)) => name = stem ^ "inject_0_intro")
            (rules_of cs))
  then fail "the injectivity rule is missing"
  else if not (List.exists (fn name => name = stem ^ "distinct")
                 (distinct_rule_names cs))
  then fail "the distinctness handle is missing"
  else ()
