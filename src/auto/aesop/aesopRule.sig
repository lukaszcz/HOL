signature aesopRule =
sig
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

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

  (* [immediate] is a nonempty prefix of theorem premises.  Those premises
     are discharged from assumptions without consuming them; any remaining
     premise suffix stays as an implication in the added hypothesis. *)
  val forward_rule :
    {name : string, phase : rphase, theorem : thm, immediate : int,
     mode : clasetUnify.mode} -> rule
  val default_forward_rule :
    {name : string, phase : rphase, theorem : thm,
     mode : clasetUnify.mode} -> rule

  (* The search layer keeps the branch history.  This predicate performs
     its instantiate-then-alpha-equivalence duplicate check. *)
  val forward_duplicate :
    clasetMeta.store -> term list -> term -> bool

  val cases_rule :
    {name : string, phase : rphase, theorem : thm,
     patterns : term list, mode : clasetUnify.mode} -> rule
  val cases_rule_for : hol_type -> rule

  datatype tactic_index =
      TargetPattern of term
    | HypPattern of term

  (* Rendered tactic rules see engine metavariables as rigid marked frees.
     Consequently they can neither create nor assign engine metavariables. *)
  val tactic_rule :
    {name : string, phase : rphase, tactic : NTactical.ntactic,
     index : tactic_index option} -> rule
  val register_tactic_rule :
    {name : string, phase : rphase, tactic : NTactical.ntactic,
     index : tactic_index option} -> unit
  val registered_tactic_rules : unit -> rule list

  val split_rule_pair :
    {name : string, theorem : thm} ->
    {conclusion : rule, assumption : rule}
  val split_rules :
    unit -> {conclusion : rule list, assumption : rule list}

  val simp_rule_with :
    {name : string, simpset : simpLib.simpset,
     controls : thm list} -> rule
  val simp_rule : thm list -> rule

  (* The penalty-zero built-ins have this fixed order: implication
     introduction, universal introduction, hypothesis substitution, simp.
     Stable penalty ordering puts negative user rules before this chain and
     positive user rules after it. *)
  val norm_builtins : thm list -> rule list

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
