structure benchAmbient :> benchAmbient =
struct

open HolKernel boolSyntax

(* True of a theorem that states equations, which is what a definition
   contributes to a simpset.  A translated type's [TY_DEF] predicate is
   not one; it would sit in every rewrite set matching nothing. *)
fun equational term =
  case strip_conj (snd (strip_forall term)) of
      [single] => is_eq single
    | conjuncts => List.all equational conjuncts

val definitions =
  let
    fun named (name, theorem) = {name = name, theorem = theorem}
    fun by_name ({name = left, ...} : benchLib.named_thm,
                 {name = right, ...} : benchLib.named_thm) =
      String.compare (left, right)
  in
    Listsort.sort by_name
      (map named
        (List.filter (equational o concl o #2)
          (DB.definitions "parityTranslation")))
  end

(* The one lemma in the ambient set.  Isabelle's [sorted] *is*
   [sorted_wrt (<=)], so every fact its simpset carries about a sorted
   list -- [sorted_upt] and the rest -- applies to the [sorted_wrt]
   reading without anyone naming it.  HOL4 states those facts about its
   own adjacent SORTED, and the translation's [source_sorted] unfolds
   to [source_sorted_wrt], whose definition is recursive and so is not
   a rewrite; without the correspondence the predicate is opaque and
   the ambient facts cannot reach it.  The bridge is conditional on
   transitivity, which is what the source linorder supplies, so it
   hands a goal nothing that Isabelle's [sorted] did not already have. *)
val sorted_wrt_correspondence =
  {name = "parityTranslation$source_sorted_wrt_bridge",
   theorem = DB.fetch "parityTranslation" "source_sorted_wrt_bridge"}

(* Results Isabelle declares simp about a constant the translation
   carries.  Its ambient context is its simpset and so has them; ours
   is the translation's definitions, so a method whose simp step leans
   on one reaches a residual that is the declared result itself, stated
   and out of reach.  Every entry cites the declaration it transplants
   and none is any corpus goal's statement, which the selftest checks:
   the list is the source's own ambient context and never a goal's
   answer.

   src/HOL/List.thy @ f7e02b7e declares [fold_append] simp, and
   List.thy:3424 [foldl_append] is reached through it.  The same file
   declares [takeWhile_append1] and [takeWhile_append2] simp, which is
   how a source proof that pushes a takeWhile across an append never
   names them: List.thy:2545 [takeWhile_append] states the two together
   and still cites them, and List.thy:4637 [extract_Some_iff] reaches
   one after unfolding [extract]. *)
val declared_results =
  let
    fun named name =
      {name = "parityTranslation$" ^ name,
       theorem = DB.fetch "parityTranslation" name}
  in
    map named
      ["source_fold_append",
       "source_takeWhile_append1",
       "source_takeWhile_append2"]
  end

val ambient_lemmas = sorted_wrt_correspondence :: declared_results

val arguments =
  map benchLib.RewriteAdd (definitions @ ambient_lemmas)

(* Self-reference in any clause, read off the constant the first clause
   defines.  A definition of several constants at once -- a [fun ... and
   ...] -- is judged by the first, which is how mutual recursion stays
   on the recursive side. *)
fun recursive term =
  let
    fun sides clause = Lib.total dest_eq (snd (strip_forall clause))
    val clauses = List.mapPartial sides (strip_conj (snd (strip_forall term)))
    fun defined (left, _) = fst (strip_comb left)
    fun mentions constant (_, right) = can (find_term (aconv constant)) right
  in
    case clauses of
        [] => false
      | first :: _ => List.exists (mentions (defined first)) clauses
  end

val recursive_definitions =
  List.filter (recursive o concl o #theorem) definitions

val recursive_arguments =
  map benchLib.RewriteAdd
    (recursive_definitions @ ambient_lemmas)

(* A definition unfolds one constant; a characterisation relates
   several.  [define_new_type_bijections] yields a single theorem whose
   clauses head on two different constants -- one of them stating
   [source_literal_valid r <=> source_literal_explode (source_literal_abs
   r) = r] -- and reading that as a definition would make every fact one
   ambient rewrite away from a goal count as stating it.  Clauses that
   all define the same head are what a wrapper and a [fun] definition
   look like, and the wrapper is what the comparison has to see
   through. *)
fun clausal term =
  let
    fun head clause =
      case Lib.total dest_eq (snd (strip_forall clause)) of
          NONE => NONE
        | SOME (left, _) =>
            Lib.total (#1 o dest_const) (fst (strip_comb left))
    val heads = map head (strip_conj (snd (strip_forall term)))
  in
    case heads of
        [] => false
      | first :: rest =>
          Option.isSome first andalso List.all (fn other => other = first) rest
  end

val wrapper_definitions =
  List.filter (clausal o concl o #theorem) definitions

(* The comparison that withholds a rule stating the goal reads these,
   and it lives in a module built below the translation theory.  The
   generous ambient set is the one filtered: a goal measured under the
   strict set is measured under fewer definitions, but the rule it must
   not be handed is the same rule either way. *)
val _ = benchLib.set_definitional_context (map #theorem wrapper_definitions)

(* The bridge is also the correspondence a recipe's own rules are
   offered across: it is what rewrites a goal out of [source_sorted_wrt]
   and into SORTED, so a cited rule stated on the translated predicate
   has to be available on the other side too. *)
val _ =
  benchLib.set_correspondences [#theorem sorted_wrt_correspondence]

end
