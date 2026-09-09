signature benchAmbient =
sig
  (* The translation's definitional equations, ambient for every goal.

     A translated goal mentions constants that Isabelle introduced with
     [fun] or [definition]; the source proof never names their
     equations because an Isabelle method reads its simpset without
     naming it.  Supplying them here restores that much of the source
     context and no more.  Isabelle puts a [fun] definition in the
     default simpset and a plain [definition] not, and
     [ambient_definitions] is the subset that distinction leaves.

     The set is one theorem per mined constant, and the selftest holds
     it against what the translation theory records, so it grows only
     when a definition is added.  It is also the same set for every
     goal, so it cannot be tuned against one.

     [arguments] adds the lemmas below to it -- the declared results
     and one correspondence.  That correspondence is
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

  (* True of a theorem that states equations, which is what a definition
     contributes to a simpset.  A translated type's [TY_DEF] predicate
     is not one.  The selftest reads the translation theory through it
     to check nothing the theory defines is missing above. *)
  val equational : Term.term -> bool

  (* The subset of [definitions] whose equations Isabelle's own simpset
     carries.  [benchIsabelleAmbient] records how Isabelle introduces
     each translated constant, one constant at a time, with the source
     line that says so, and this is the set the corpus is measured
     under. *)
  val ambient_definitions : benchLib.named_thm list

  (* The ambient context as recipe arguments -- [ambient_definitions]
     and the lemmas below, then [declared_rules] -- in the order a
     recipe takes.  It has two halves, and each reaches only the
     methods that consult it: the rewrites go to the methods that read
     a simpset, the classical rules to those that read a claset. *)
  val arguments : benchLib.method_arg list

  (* The results Isabelle declares simp about a translated constant,
     which its simp step has and a context of definitions alone does
     not.  Each is part of [arguments].  One that states a corpus goal
     -- two Isabelle facts can translate onto one HOL4 theorem -- is
     withheld on that goal, as a citation stating its goal is.
     [arguments] carries them read through the ambient alias
     definitions, which have already rewritten the goal by the time one
     of them is tried. *)
  val declared_results : benchLib.named_thm list

  (* The results Isabelle declares [intro]/[elim]/[dest] about a
     translated constant whose definition it withholds.  Its claset has
     them and a context of rewrites does not, and no rewrite stands in
     for one: a classical rule takes a term apart in a direction the
     simplifier will not run.  Each cites the declaration it
     transplants and each is unsafe, whatever Isabelle's [!] says: a
     safe elimination is applied at every tableau node, which this
     layer's search cannot afford even for a rule that cannot match the
     goal. *)
  val declared_rules : benchLib.method_arg list

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
