signature aesopRule =
sig
  type term = Term.term
  type thm = Thm.thm

  datatype rphase =
      RNorm of int
    | RSafe
    | RUnsafe of int

  datatype rapply =
      EngineStep of clasetStep.step
    | RenderedTactic of NTactical.ntactic
    | MultiStep of clasetStep.step list

  type rule =
    {name : string, phase : rphase, apply : rapply, once : bool}

  type safe_scaffold =
    {closers : rule list,
     safe0_claset : rule list,
     safe_forward : rule list,
     safep_claset : rule list,
     conclusion_splits : rule list,
     assumption_splits : rule list}

  type ruleset =
    {norm : rule list, safe : safe_scaffold, unsafe : rule list}

  val default_percent : int
  val phase_of_spec : clasetRules.rulespec -> rphase

  val apply_rule :
    {name : string, phase : rphase, theorem : thm,
     mode : clasetUnify.mode} -> rule

  (* HOL goals are propositions, so this builder registers introduction
     rules for an inductive relation rather than datatype constructors in
     Lean's sense.  The ordinary form is unsafe by default. *)
  val constructors_rule :
    {name : string, theorems : thm list, percent : int option,
     mode : clasetUnify.mode} -> rule
  val safe_constructors_rule :
    {name : string, theorems : thm list,
     mode : clasetUnify.mode} -> rule

  val simp_rule_with :
    {name : string, simpset : simpLib.simpset,
     controls : thm list} -> rule
  val simp_rule : thm list -> rule

  val closers : unit -> rule list
  val safe_rules : safe_scaffold -> rule list

  (* Candidate retrieval is unification-based.  [qvars] identifies the
     engine metavariables which the invocation permits the index to match. *)
  val claset_rules :
    {claset : clasetLib.claset,
     mode : clasetUnify.mode,
     conclusion : term,
     assumptions : term list,
     qvars : term HOLset.set,
     simp_args : thm list} -> ruleset
end
