signature clasetReplay =
sig
  include Abbrev

  datatype rule_variant = Plain | Swapped | Duplicate | MakeElim

  datatype step_kind =
      Assumption of int
    | Contradiction of int * int
    | ModusPonens of {implication : int, antecedent : int}
    | RuleApplication of
        {original : thm, theorem : thm, variant : rule_variant,
         elim : bool}
    | Disch
    | Gen
    | HypSubst
    | CContr
    | SwappedBuiltin of int
    | MoveAssumptionToBack of int
    | Wrapper

  type created =
    {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}
  type replay_action = clasetMeta.store -> tactic
  type step_record
  type script
  type grounded_script

  datatype replay_failure =
    ReplayFailure of
      {goal : goal, step : step_kind option, message : string,
       script : string}
  datatype replay_outcome =
      Replayed of goal list * validation
    | ReplayFailed of replay_failure

  val make_record :
    {kind : step_kind, target : int, consumed : int option,
     created : created, eigenvariables : string list list,
     validation : validation, action : replay_action,
     children : step_record option list} -> step_record

  val kind_of : step_record -> step_kind
  val target_of : step_record -> int
  val consumed_of : step_record -> int option
  val created_of : step_record -> created
  val eigenvariables_of : step_record -> string list
  val validation_of : step_record -> validation
  val children_of : step_record -> step_record option list

  val empty : int -> script
  val append : script -> step_record -> script
  val length : script -> int
  val open_goals : script -> int
  val to_string : script -> string

  (* Grounding is deterministic: type metavariables become bool before
     remaining term metavariables become ARB at their grounded types. *)
  val ground : clasetMeta.store -> script -> grounded_script
  val grounded_store : grounded_script -> clasetMeta.store
  val grounded_to_string : grounded_script -> string

  (* [replay] reports malformed scripts as data.  [REPLAY_TAC] is the
     classical-driver policy: it raises a diagnostic HOL_ERR. *)
  val replay : grounded_script -> goal -> replay_outcome
  val REPLAY_TAC : grounded_script -> tactic

  (* Shared, position-directed replay vocabulary.  None of these tactics
     performs claset lookup or unification. *)
  val ASSUMPTION_TAC : clasetMeta.store -> int -> tactic
  val CONTRADICTION_TAC : clasetMeta.store -> int * int -> tactic
  val MP_TAC : clasetMeta.store ->
               {implication : int, antecedent : int} -> tactic
  val RULE_TAC :
    {theorem : thm, elim : bool, consumed : int option,
     parameters : string list, eigenvariables : string list list} -> tactic
  val HYP_SUBST_TAC : tactic
  val BLAST_HYP_SUBST_TAC : tactic
  val BLAST_HYP_SUBST_TAC_AT : int -> tactic
  val GEN_NAMED_TAC : string -> tactic
  val GOAL_NEGATION_TAC : tactic
  val SWAPPED_BUILTIN_TAC : clasetMeta.store -> int -> tactic
  val MOVE_ASSUMPTION_TO_BACK_TAC : int -> tactic

  val assumption_action : int -> replay_action
  (* Unlike [assumption_action], this exact-replay action never scans for a
     different closing assumption when the recorded occurrence has drifted. *)
  val strict_assumption_action : int -> replay_action
  val contradiction_action : int * int -> replay_action
  val mp_action : {implication : int, antecedent : int} -> replay_action
  val rule_action :
    (clasetMeta.store ->
      {theorem : thm, elim : bool, consumed : int option,
       parameters : string list,
       eigenvariables : string list list}) -> replay_action
  val hyp_subst_action : replay_action
  val blast_hyp_subst_action : replay_action
  val blast_hyp_subst_action_at : int -> replay_action
  val disch_action : replay_action
  val gen_action : string -> replay_action
  val goal_negation_action : replay_action
  val swapped_builtin_action : int -> replay_action
  val move_assumption_to_back_action : int -> replay_action
  val fixed_action : goal list * validation -> replay_action
end
