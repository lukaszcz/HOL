signature blastRule =
sig
  type hol_term = Term.term
  type thm = Thm.thm
  type goal = Abbrev.goal
  type pterm = blastTerm.term
  type var = blastTerm.var

  datatype origin =
      Stored of {is_elim : bool, theorem : thm}
    | ImpIntro
    | AllIntro

  type tableau_rule =
    {origin : origin,
     pattern : pterm,
     premises : pterm list list}

  (* A cache belongs to one tableau node.  Rule clauses contain mutable
     variables, so converted clauses must not be shared between nodes. *)
  type cache
  val newCache : unit -> cache
  val conversionCount : cache -> int

  (* HOL4 goals have no schematic term variables.  Thus the four TRANS
     failures in Isabelle's fromSubgoal are vacuous here: free term
     variables become nullary Skolems and free type variables stay rigid. *)
  val fromGoalTerm : hol_term -> pterm
  val initialBranch : goal -> (pterm * bool) list

  (* Conversion hooks are public for focused tests and diagnostics.  Normal
     clients acquire clauses through safeRules and unsafeRules. *)
  val convertIntro : cache -> var list -> thm -> tableau_rule
  val convertElim : cache -> var list -> thm -> tableau_rule option

  val safeRules :
    cache -> clasetLib.claset -> var list -> pterm -> tableau_rule list
  val unsafeRules :
    cache -> clasetLib.claset -> var list -> pterm -> tableau_rule list

  (* Introduction-rule duplication is deliberately absent: with delayed
     unsafe rules that arm is dead (Isabelle blast.ML:537-539). *)
  val replayTheorem : tableau_rule -> bool -> thm option
end
