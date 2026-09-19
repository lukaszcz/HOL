signature clasimpLib =
sig
  include Abbrev

  (* The safe side-condition solver of the clasimp simpset.  It discharges
     only goals justified without witness instantiation or unsafe search,
     which is what makes it usable in a normalisation phase.  Exported so
     that simpsets derived elsewhere (aesop) share this one solver stack
     rather than restating it. *)
  val safe_solver : Traverse.ssolver

  (* The subgoaler of the clasimp simpset: the traversal's own recursion,
     then, on a side condition [QUANTIFY_CONDITIONS] left existentially
     closed, a match of the condition against the context assumptions
     that reads the witnesses off it.  Exported because a simpset rebuilt
     from [ssfrags_of] keeps only what the fragments carry, and the
     subgoaler is not one of those -- a caller that rebuilds this simpset
     restates it, as it already restates the solvers and the condition
     depth. *)
  val witness_subgoaler : Traverse.subgoaler

  (* Replaces the conditional congruence of a simpset by the weak form,
     which simplifies the condition and leaves the branches to whatever
     case split the caller arranges.  Exported so that the simpsets
     derived elsewhere in this layer (aesop) share the arrangement
     rather than restating it.  Reports a simpset with no conditional
     congruence to replace rather than returning it unchanged. *)
  val weaken_cond_congruence : simpLib.simpset -> simpLib.simpset

  val clasimp_ss : unit -> simpLib.simpset

  (* [with_extensionality simplify] runs [simplify] and, where it leaves
     a goal whose conclusion is an equation between functions, takes that
     equation pointwise and runs [simplify] again.  HOL4's library states
     applied what the source states at the function level, so a goal at
     the function level cannot meet the rule that settles it; this is the
     one step that brings the two together.  It wraps a method's
     simplification, not a step inside a search.  Exported so that a
     method built from HOL4's simplifier directly -- the parity corpus
     builds its simp method that way -- takes the step the layer's own
     methods take, rather than restating it. *)
  val with_extensionality : tactic -> tactic

  (* True of a rewrite that states how an equation between functions is
     to be read -- its own left-hand side is such an equation, which is
     what [fun_eq_iff] and a membership reading are and what no other
     rewrite is.  The extensional steps above impose a reading of their
     own, and they stand down where one of these takes the equation
     first.  Exported so that a method built from HOL4's simplifier
     directly -- the parity corpus builds its recipes that way -- can
     make the same decision about its own set-equality pass. *)
  val states_a_reading : thm -> bool

  val asm_full_simp : simpLib.simpset -> thm list -> tactic
  val safe_asm_full_simp : simpLib.simpset -> thm list -> tactic

  val add_simp_wrapper :
    simpLib.simpset -> thm list -> clasetLib.claset -> clasetLib.claset
  val add_safe_simp_wrapper :
    simpLib.simpset -> thm list -> clasetLib.claset -> clasetLib.claset

  (* Pure [iff] decision tree.  Callers choose where to install the
     derived claset rules and the normalized simpset rewrite. *)
  val iff_declaration :
    string -> thm ->
    {rules :
       (clasetRules.rulespec * (string * thm)) list,
     rewrite : thm}

  (* Installs the rules of an iff_declaration.  They are derived rather than
     named by the user, so a duplicate among them is dropped silently. *)
  val add_iff_rules :
    (clasetRules.rulespec * (string * thm)) list ->
    clasetLib.claset -> clasetLib.claset

  val remove_iff : string -> unit

  (* An [iff] whose simpset half is installed as a low-priority reducer,
     so that the traversal offers it a subject the rewrites and the
     descent have already left alone.  Isabelle's simplifier rewrites the
     innermost redex first and so never offers such a rule anything else;
     HOL4's rewrites the outermost first, where a rule about an arbitrary
     term of a type -- [x <> NONE] -- fires above every rule about that
     term's own head.  The claset halves are those of [iff]. *)
  val remove_iff_bottom_up : string -> unit

  (* The simpset half of that declaration, for a rewrite a caller
     installs for one invocation instead of declaring: a fragment whose
     rewrites the traversal reaches only once the rewrites and the
     descent have both left a node alone.  A rule whose left side reads
     an arbitrary term of its subject's type fires, in HOL4's order,
     above every rule about the subject's own head; in this fragment it
     is offered the subject the other rules have finished with, which is
     the only subject Isabelle's order ever offers it.  The rewrites are
     unconditional equations, as the declaration's are. *)
  val normalised_subject_fragment : thm list -> simpLib.ssfrag

  (* Whether the simplifier can make a rewrite of this argument that is
     able to fire.  A conditional rule whose conclusion is an equation
     between variables prepares to a rewrite matching every equation in
     the goal whose condition the match determines nothing of, which the
     simplifier then tries to discharge at each of them; an invocation
     declares such an argument to its claset instead of its simpset.  A
     caller that hands its arguments to a simpset directly asks here
     first. *)
  val simp_argument_can_fire : thm -> bool

  val extend_invocation :
    {iff_prefix : string, simp_rules : thm list, iff_rules : thm list,
     claset : clasetLib.claset, simpset : simpLib.simpset} ->
    clasetLib.claset * simpLib.simpset

  (* Shared packaging for theorem-list clasimp tactics.  The body receives
     the temporary claset, temporary simpset, and generic simp controls. *)
  val process_clasimp_args :
    (clasetLib.claset -> simpLib.simpset -> thm list -> tactic) ->
    clasetLib.claset -> simpLib.simpset -> thm list -> tactic

  val CS_AUTO_TAC :
    {blast : int, depth : int} ->
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_FORCE_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_FASTFORCE_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_SLOWSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_BESTSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic
  val CS_CLARSIMP_TAC :
    clasetLib.claset -> simpLib.simpset -> tactic

  val AUTO_DEPTH_TAC :
    {blast : int, depth : int} -> thm list -> tactic
  val AUTO_TAC : thm list -> tactic
  val FORCE_TAC : thm list -> tactic
  val FASTFORCE_TAC : thm list -> tactic
  val SLOWSIMP_TAC : thm list -> tactic
  val BESTSIMP_TAC : thm list -> tactic
  val CLARSIMP_TAC : thm list -> tactic

  (* METIS_TAC with each fact offered in the ambient normal form as well
     as its own.  A first-order step runs on a goal the simplification
     before it normalised, and a library lemma is not stated in that
     normal form; offering both spellings is what lets the fact meet the
     goal, and it can only add to what METIS_TAC would have found. *)
  val AMBIENT_METIS_TAC : thm list -> tactic

  (* Name each abstraction that stands in an argument position with a
     goal-level variable and carry its defining equation into the goal.
     A first-order search can then instantiate a function variable with
     the name, where instantiating it with the abstraction itself leaves
     a redex the search has no rule to reduce. *)
  val LAMBDA_LIFT_TAC : tactic
end
