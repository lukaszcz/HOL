signature benchRecipe =
sig
  (* The Isabelle method grammar the corpus actually uses, parsed.  The
     point of parsing is that the executed tactic becomes a function of
     what the source proof says, so no per-goal field is left for an
     agent to tune.

     Lemma names are kept exactly as the source writes them, attribute
     brackets included and internal whitespace collapsed, so the name
     table is keyed by the citation rather than by a chosen theorem. *)

  datatype modifier =
      SimpAdd of string list
    | SimpDelete of string list
    | Split of string list
    | Intro of benchLib.rule_strength * string list
    | Elim of benchLib.rule_strength * string list
    | Dest of benchLib.rule_strength * string list
    | Cong of string list
    (* [algebra add: ...]: facts for a method with no simpset. *)
    | FactsAdd of string list

  type method = {name : string, modifiers : modifier list}

  (* [facts] are the [using] premises, [unfolded] the [unfolding] names,
     and [methods] the one or two methods [by] applies. *)
  type parsed = {
    facts : string list,
    unfolded : string list,
    methods : method list
  }

  (* Raised with the offending string and the reason.  A method the
     parser does not cover is an error, never a silent fallback to a
     bare tactic. *)
  exception Unparseable of string * string

  val parse : string -> parsed
  (* Canonical rendering: [by (auto simp add: ...)] with one space per
     separator, whatever the source spacing was.  [parse o render] is the
     identity on parsed values. *)
  val render : parsed -> string

  (* Every lemma name the method cites, in citation order, deduplicated.
     This is the domain the name table has to cover. *)
  val cited_names : parsed -> string list
  (* The method names, e.g. ["auto"], for tactic selection. *)
  val method_heads : parsed -> string list

  (* [theorems] returns every HOL4 theorem a citation stands for.  The
     list is empty for a citation that contributes no argument -- an
     Isar context fact, whose content the translated goal already
     carries as a hypothesis -- and holds more than one theorem where
     the Isabelle name abbreviates a fact list, as [option.splits]
     does.  An unknown citation is the resolver's error to raise, not
     a silent empty list. *)
  type resolver = {
    theorems : string -> benchLib.named_thm list,
    tactic : string -> Term.term -> benchLib.tactic_id
  }

  (* The recipe the method denotes.  [resolver] supplies the HOL4 theorem
     for an Isabelle name and the HOL4 tactic for a method name at this
     goal; the goal is passed because Isabelle's [algebra] and [arith] are
     polymorphic where HOL4's counterparts are carrier-indexed. *)
  val to_recipe :
    resolver -> Term.term -> parsed -> benchLib.method_recipe
end
