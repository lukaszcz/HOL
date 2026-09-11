signature benchDerive =
sig
  (* The recipe an entry's Isabelle method calls for.

     The only inputs are the method string the source proof used, the
     goal's carrier type, and the Isabelle line the proof sits on.
     Nothing is read that an author could tune per goal: citations
     resolve through the global [benchNames] table and method heads
     through [benchTactics], both keyed by name alone, and the ambient
     context is one set for the whole corpus cut by that mined line.  A
     goal therefore cannot be handed an argument its source proof never
     named, nor one that was not yet declared where it was proved. *)
  val recipe : benchLib.source_goal -> benchLib.method_recipe

  (* [recipe] on the three fields it actually reads, for a caller
     holding a goal that has already been prepared.  The first is the
     goal's Isabelle line, "src/HOL/<theory>.thy:<line>". *)
  val recipe_of : string -> Term.term -> string -> benchLib.method_recipe

  (* The citations dropped from an entry's recipe because their HOL4
     theorem is the goal.  Empty for all but a handful of goals whose
     translation collapses two Isabelle facts onto one HOL4 theorem;
     those goals are still measured, but without a fact the Isabelle
     proof had.  A theorem the recipe carries twice is named once. *)
  val self_supplied : benchLib.source_goal -> string list

  (* [self_supplied] on the three fields it reads, for a goal that has
     already been prepared. *)
  val self_supplied_of : string -> Term.term -> string -> string list

  (* True of the entries translated from Isabelle, which is where a
     method string exists to derive from.  False of the HOL4 regression
     goals the corpus adds alongside them. *)
  val derivable : benchLib.source_goal -> bool

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
