signature benchAmbient =
sig
  (* The translation's definitional equations, ambient for every goal.

     A translated goal mentions constants that Isabelle introduced with
     [fun] or [definition]; the source proof never names their
     equations because an Isabelle method reads its simpset without
     naming it.  Supplying them here restores that much of the source
     context and no more.  It is generous in one direction: Isabelle
     puts a [fun] definition in the default simpset and a plain
     [definition] not, and this makes no such distinction.

     The set is read out of the translation theory rather than listed,
     so it grows only when a definition is added.  It is also the same
     set for every goal, so it cannot be tuned against one.

     [arguments] adds one lemma to it, and one only:
     [source_sorted_wrt_bridge].  Isabelle's [sorted] is
     [sorted_wrt (<=)], so its simpset's facts about sorted lists reach
     the [sorted_wrt] reading with nobody naming them; HOL4 states the
     same facts about its adjacent SORTED, and the correspondence
     between the two is what the translation has to supply for the
     ambient context to mean the same thing on both sides.  It is
     conditional on transitivity, and the bridge reads left to right,
     so it fires wherever that condition can be discharged: by the
     assigned method itself, or from the source linorder premise the
     goals carry, which the order-premise seeds put within reach of the
     simplifier's own condition solver.  That is sound, the two
     predicates agreeing under transitivity, and it costs a goal only
     where a cited rule is left on the far side; the crossing below is
     what keeps those rules usable. *)
  val definitions : benchLib.named_thm list

  (* [definitions] as recipe arguments, in the order a recipe takes. *)
  val arguments : benchLib.method_arg list

  (* The results Isabelle declares simp about a translated constant,
     which its simp step has and a context of definitions alone does
     not.  Each is part of [arguments]; none states a corpus goal. *)
  val declared_results : benchLib.named_thm list

  (* The subset Isabelle would have made ambient by itself.  The corpus
     does not record whether a constant arrived by [fun] or by
     [definition], so recursion stands in for the distinction: a
     definition whose right-hand side mentions the constant it defines
     is one no plain [definition] could have made.  The proxy errs
     towards the strict side -- a non-recursive [fun] is counted as a
     [definition] -- which is the direction that cannot flatter HOL4.

     The report measures the corpus under both sets and gives both
     counts, because choosing one would mean guessing which side of a
     distinction each constant fell on. *)
  val recursive_definitions : benchLib.named_thm list
  val recursive_arguments : benchLib.method_arg list

  (* The entries of [definitions] that define one constant: every
     clause heads on the same one.  A [define_new_type_bijections]
     theorem is not one of them -- its clauses relate two constants,
     and it is a characterisation rather than an unfolding. *)
  val wrapper_definitions : benchLib.named_thm list

  (* Loading this structure installs [wrapper_definitions] as benchLib's
     definitional context, so that a rule stating a goal under the
     translation's constants is recognised as stating it.  The
     characterisations stay out: being one ambient rewrite away from a
     goal is not stating it. *)

  (* Loading it also installs [source_sorted_wrt_bridge] as benchLib's
     ambient correspondence, so a recipe's own rules are offered on both
     sides of it.  The bridge rewrites goals left to right; without the
     crossing a rule cited in the translation's spelling stops meeting
     the goal as soon as the bridge's transitivity condition becomes
     dischargeable. *)
end
