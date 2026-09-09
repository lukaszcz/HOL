structure benchAmbient :> benchAmbient =
struct

open HolKernel boolSyntax

(* True of a theorem that states equations, which is what a definition
   contributes to a simpset.  A translated type's [TY_DEF] predicate is
   not one; it would sit in every rewrite set matching nothing.  The
   selftest reads the translation theory through this. *)
fun equational term =
  case strip_conj (snd (strip_forall term)) of
      [single] => is_eq single
    | conjuncts => List.all equational conjuncts

(* One theorem per mined constant.  Reading [DB.definitions] instead
   would miss four: HOL4 keeps the equations of a definition made by
   well-founded recursion in the theorem class, so [source_alookup],
   [source_lexordp], [source_lexordp_eq] and [source_upto] never appear
   there.  The theory read is the check rather than the construction --
   the selftest requires every definition it records to have a mined
   row -- and a row naming nothing raises here, at load. *)
val definitions =
  map
    (fn (name, _, _) =>
      {name = name, theorem = DB.fetch "parityTranslation" name})
    benchIsabelleAmbient.introductions

(* The one lemma in the ambient set.  Isabelle's [sorted] *is*
   [sorted_wrt (<=)], so every fact its simpset carries about a sorted
   list -- [sorted_upt] and the rest -- applies to the [sorted_wrt]
   reading without anyone naming it.  HOL4 states those facts about its
   own adjacent SORTED, and the translation's [source_sorted] unfolds
   to [source_sorted_wrt], whose definition takes a nil or a cons apart
   and says nothing about a list variable; without the correspondence
   the predicate is opaque and the ambient facts cannot reach it.  The
   bridge is conditional on transitivity, which is what the source
   linorder supplies, so it hands a goal nothing that Isabelle's
   [sorted] did not already have. *)
val sorted_wrt_correspondence =
  {name = "parityTranslation$source_sorted_wrt_bridge",
   theorem = DB.fetch "parityTranslation" "source_sorted_wrt_bridge"}

(* Results Isabelle declares simp about a constant the translation
   carries.  Its ambient context is its simpset and so has them; ours
   is the translation's definitions, so a method whose simp step leans
   on one reaches a residual that is the declared result itself, stated
   and out of reach.  Every entry cites the declaration it transplants.
   An entry may be a corpus goal's statement -- two Isabelle facts can
   translate onto one HOL4 theorem, and [map_add_find_right] is
   map_L887 once [map_le] is unfolded -- and the measurement then
   withholds it on that one goal, exactly as it withholds a citation
   that states its goal.  The list is the source's own ambient context
   and never a goal's answer.

   src/HOL/List.thy @ f7e02b7e declares [fold_append] simp, and
   List.thy:3424 [foldl_append] is reached through it.  The same file
   declares [takeWhile_append1] and [takeWhile_append2] simp, which is
   how a source proof that pushes a takeWhile across an append never
   names them: List.thy:2545 [takeWhile_append] states the two together
   and still cites them, and List.thy:4637 [extract_Some_iff] reaches
   one after unfolding [extract].

   Relation.thy:1572 declares [Image_singleton_iff] [iff]: the simpset
   takes a relational image of a singleton apart, though [Image] itself
   is a plain definition and stays folded.  String.thy:63 [char_of_char]
   and String.thy:89 [of_char_of] are the roundtrip pair Isabelle
   declares simp about [char_of], whose own definition it withholds;
   neither line was mined into the corpus, so transplanting them hands
   no goal its own statement.

   List.thy:2789 declares [nth_zip] simp, which is how a source proof
   that indexes into a zip never names it; HOL4's [EL_ZIP] asks for
   equal lengths instead of the two bounds the truncating ZIP needs,
   so the translation states Isabelle's form.

   Map.thy declares [map_add_find_right], [map_add_assoc],
   [map_le_refl] and [map_le_map_add] simp and [map_add_None] iff,
   about [map_add] and [map_le], whose definitions it withholds: a
   method that never names [map_add_def] still reads a value out of the
   right-hand map, reassociates two of them, and settles the order
   between a map and a sum it is part of. *)
val declared_results =
  let
    fun named name =
      {name = "parityTranslation$" ^ name,
       theorem = DB.fetch "parityTranslation" name}
  in
    map named
      ["source_fold_append",
       "source_takeWhile_append1",
       "source_takeWhile_append2",
       "source_nth_zip",
       "source_map_add_find_right",
       "source_map_add_assoc",
       "source_map_add_None",
       "source_map_le_refl",
       "source_map_le_map_add",
       "source_rel_image_singleton",
       "source_char_roundtrip",
       "source_code_roundtrip"]
  end

(* An alias definition is ambient, so by the time one of the lemmas
   above is tried the goal no longer spells the alias: [source_of_char]
   is gone and ORD stands where it was.  A lemma still stated on the
   alias then matches nothing -- [source_code_roundtrip] is the ambient
   reading of Isabelle's [of_char_of], and the residual it has to close
   spells the same term with ORD.  Reading the lemmas through the
   aliases states them in the vocabulary the ambient set leaves, and
   makes which of the two rules reaches a term first stop mattering.
   Only the aliases are unfolded: they rename a constant argument for
   argument, so the reading is the same statement. *)
val alias_definitions =
  List.filter
    (fn {name, ...} : benchLib.named_thm =>
      List.exists
        (fn (entry, introduction, _) =>
          entry = name andalso introduction = benchIsabelleAmbient.Alias)
        benchIsabelleAmbient.introductions)
    definitions

fun through_aliases ({name, theorem} : benchLib.named_thm) =
  {name = name,
   theorem =
     Rewrite.PURE_REWRITE_RULE (map #theorem alias_definitions) theorem}

val ambient_lemmas =
  map through_aliases (sorted_wrt_correspondence :: declared_results)

(* Isabelle's simpset carries a [fun]'s equations and not a plain
   [definition]'s, so the ambient set is the translation's definitions
   cut to that line.  [benchIsabelleAmbient] draws it one constant at a
   time against the Isabelle source, and raises on a definition it does
   not cover: a definition added to the translation is measured only
   once someone has read how Isabelle introduces it. *)
val ambient_definitions =
  List.filter
    (fn {name, ...} : benchLib.named_thm =>
      benchIsabelleAmbient.is_ambient name)
    definitions

(* The claset half.  Isabelle declares these about a constant whose
   definition it withholds, with a classical attribute rather than
   [simp], and its [blast], [safe], [clarify], [auto] and [force] read
   them without naming them.  A rewrite cannot stand in for one: the
   rules above match a map sum under [= NONE] or build one from a
   value, and none of them takes a sum apart under [= SOME x], which is
   the residual Isabelle's [dest!] rule closes.  As with the rewrites,
   a rule that states a corpus goal is withheld on that goal.

   Every entry is unsafe, whatever Isabelle's [!] says.  A safe
   elimination is applied at every tableau node and its major premise
   is entirely schematic, so it meets the undetermined literals a
   witness-guessing branch leaves behind: the seed clasets measured
   [set_L1610_Pow_Compl] at 88 tableau branches with such a rule
   unsafe and 3638 and past budget with the same rule [sdest].  That
   is the rule the seeds already follow, and it costs nothing here --
   [map_L611] closes in 0.107s safe and 0.100s unsafe. *)
val declared_rules =
  let
    fun named constructor name =
      constructor
        (benchLib.UnsafeRule,
         through_aliases
           {name = "parityTranslation$" ^ name,
            theorem = DB.fetch "parityTranslation" name})
  in
    (* src/HOL/Map.thy:359 [map_add_SomeD], declared [dest!]. *)
    [named benchLib.DestAdd "source_map_add_SomeD"]
  end

val arguments =
  map benchLib.RewriteAdd (ambient_definitions @ ambient_lemmas) @
  declared_rules

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
   and it lives in a module built below the translation theory.  Every
   definition is filtered, not just the ambient ones: a rule states a
   goal, or does not, whether or not the goal's context could have
   unfolded its way there. *)
val _ = benchLib.set_definitional_context (map #theorem wrapper_definitions)

(* The bridge is also the correspondence a recipe's own rules are
   offered across: it is what rewrites a goal out of [source_sorted_wrt]
   and into SORTED, so a cited rule stated on the translated predicate
   has to be available on the other side too. *)
val _ =
  benchLib.set_correspondences [#theorem sorted_wrt_correspondence]

end
