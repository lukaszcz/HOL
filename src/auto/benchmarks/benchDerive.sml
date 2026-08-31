structure benchDerive :> benchDerive =
struct

val resolver =
  {theorems = benchNames.theorems, tactics = benchTactics.tactics,
   ambient = benchAmbient.arguments}

(* Everything the corpus took from Isabelle carries an Isabelle method
   to derive from.  The HOL4 regression goals the corpus adds alongside
   them do not, and are the only entries this rejects. *)
fun derivable (entry : benchLib.source_goal) =
  String.isPrefix "src/HOL/" (#file (#provenance entry))

(* Two distinct Isabelle facts can translate onto one HOL4 theorem --
   [list.pred_set] and [list_all_iff] are both [EVERY_MEM] -- and a
   proof citing one of them then reads as if it assumed what it proves.
   The citation is dropped rather than the goal: HOL4 is asked to close
   the goal without a fact Isabelle had, which can only under-credit
   HOL4, and [self_supplied] names where that happened so the report
   can say so rather than the measurement hiding it. *)
fun without_self goal recipe =
  let
    fun strip (benchLib.Invoke (tactic, arguments)) =
          benchLib.Invoke
            (tactic, List.filter (benchLib.permitted_for goal) arguments)
      | strip (benchLib.Then (left, right)) =
          benchLib.Then (strip left, strip right)
      | strip (benchLib.AllGoals (left, right)) =
          benchLib.AllGoals (strip left, strip right)
      | strip (benchLib.Otherwise (left, right)) =
          benchLib.Otherwise (strip left, strip right)
      | strip (benchLib.Repeat inner) = benchLib.Repeat (strip inner)
  in
    strip recipe
  end

fun recipe_of goal source_method =
  without_self goal
    (benchRecipe.to_recipe resolver goal (benchRecipe.parse source_method))

(* One recipe can carry a theorem twice -- an [unfolding] naming it and
   the ambient context repeating it under a qualified spelling -- and
   listing it twice would read as two facts withheld rather than one.
   The first spelling is the one kept. *)
fun distinct_arguments arguments =
  let
    fun same left right =
      case (benchLib.named_theorem left, benchLib.named_theorem right) of
          (SOME {theorem = one, ...}, SOME {theorem = other, ...}) =>
            Term.aconv (Thm.concl one) (Thm.concl other)
        | _ => benchLib.argument_name left = benchLib.argument_name right
    fun keep (argument, kept) =
      if List.exists (same argument) kept then kept else kept @ [argument]
  in
    List.foldl keep [] arguments
  end

fun self_supplied_of goal source_method =
  map benchLib.argument_name
    (distinct_arguments
      (List.filter (not o benchLib.permitted_for goal)
        (benchLib.recipe_arguments
          (benchRecipe.to_recipe resolver goal
            (benchRecipe.parse source_method)))))

fun self_supplied (entry : benchLib.source_goal) =
  self_supplied_of (#goal entry) (#source_method entry)

fun recipe (entry : benchLib.source_goal) =
  recipe_of (#goal entry) (#source_method entry)

fun restrict_ambient ambient goals =
  let
    val restricted =
      {theorems = benchNames.theorems, tactics = benchTactics.tactics,
       ambient = ambient}
    fun rederive (entry : benchLib.corpus_goal) =
      if not (String.isPrefix "src/HOL/" (#file (#provenance entry)))
      then entry
      else
        {id = #id entry, goal = #goal entry,
         source_method = #source_method entry,
         recipe =
           without_self (#goal entry)
             (benchRecipe.to_recipe restricted (#goal entry)
               (benchRecipe.parse (#source_method entry))),
         excl = #excl entry, provenance = #provenance entry,
         representative = #representative entry}
  in
    map rederive goals
  end

(* [family] names the corpus in the error a bad entry raises; the check
   itself is [benchLib.prepare_goal]'s, one goal at a time. *)
fun prepare family entries =
  let
    fun prepared entry =
      benchLib.prepare_goal (recipe entry) entry
      handle Portable.Interrupt => raise Portable.Interrupt
           | exn =>
               raise Feedback.mk_HOL_ERR "benchDerive" "prepare"
                 (family ^ ": " ^ #id entry ^ ": " ^
                  Feedback.exn_to_string exn)
  in
    map prepared entries
  end

fun native procedure entry =
  if derivable entry then
    raise Feedback.mk_HOL_ERR "benchDerive" "native"
      (#id entry ^ " comes from Isabelle; its tactic is derived, \
       \not named")
  else
    benchLib.prepare_goal (benchLib.Invoke (procedure, [])) entry

end
