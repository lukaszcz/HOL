signature benchDerive =
sig
  (* The recipe an entry's Isabelle method calls for.

     The only inputs are the method string the source proof used and the
     goal's carrier type.  Nothing is read that an author could tune per
     goal: citations resolve through the global [benchNames] table and
     method heads through [benchTactics], both keyed by name alone, and
     the ambient context is one list shared by the whole corpus.  A goal
     therefore cannot be handed an argument its source proof never
     named. *)
  val recipe : benchLib.source_goal -> benchLib.method_recipe

  (* [recipe] on the two fields it actually reads, for a caller holding
     a goal that has already been prepared. *)
  val recipe_of : Term.term -> string -> benchLib.method_recipe

  (* The citations dropped from an entry's recipe because their HOL4
     theorem is the goal.  Empty for all but a handful of goals whose
     translation collapses two Isabelle facts onto one HOL4 theorem;
     those goals are still measured, but without a fact the Isabelle
     proof had.  A theorem the recipe carries twice is named once. *)
  val self_supplied : benchLib.source_goal -> string list

  (* [self_supplied] on the two fields it reads, for a goal that has
     already been prepared. *)
  val self_supplied_of : Term.term -> string -> string list

  (* True of the entries translated from Isabelle, which is where a
     method string exists to derive from.  False of the HOL4 regression
     goals the corpus adds alongside them. *)
  val derivable : benchLib.source_goal -> bool

  (* The same goals with their recipes re-derived under a different
     ambient context.  Nothing else changes: the exclusions belong to
     the goal and the provenance to the corpus file.  This is how the
     report measures the corpus a second time under the stricter
     ambient set without keeping a second corpus.  Goals that came from
     HOL4 rather than Isabelle have no method to re-derive from and are
     returned unchanged. *)
  val restrict_ambient :
    benchLib.method_arg list -> benchLib.corpus_goal list ->
    benchLib.corpus_goal list

  (* Every authored goal of one family, with its derived recipe and
     exclusions attached and checked.  This is the only route from what
     a corpus file writes to what the harness runs; [family] appears in
     the error a rejected entry raises. *)
  val prepare :
    string -> benchLib.source_goal list -> benchLib.corpus_goal list

  (* A goal that came from HOL4 rather than from Isabelle, run under a
     named procedure.  There is no Isabelle proof to compare against and
     so no parity claim to inflate; this is the one route by which a
     tactic is written down instead of derived, and it is confined to
     entries [derivable] rejects. *)
  val native :
    benchLib.tactic_id -> benchLib.source_goal -> benchLib.corpus_goal
end
