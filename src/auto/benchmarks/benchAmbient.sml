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

val arguments = map benchLib.RewriteAdd definitions

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

val recursive_arguments = map benchLib.RewriteAdd recursive_definitions

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

end
