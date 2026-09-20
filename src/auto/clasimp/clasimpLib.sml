structure clasimpLib :> clasimpLib =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "clasimpLib"

val clasimp_trace = ref 0
val _ = Feedback.register_trace ("clasimp", clasimp_trace, 3)

fun trace level message =
  if level <= Feedback.current_trace "clasimp" then
    Feedback.HOL_MESG ("Clasimp: " ^ message ())
  else ()

val safe_solver =
  simpLib.mk_tactic_solver
    ("clasimp safe",
     Tactical.FIRST
       [Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
        Tactic.REFL_TAC,
        Tactic.ACCEPT_TAC boolTheory.TRUTH,
        Tactical.FIRST_ASSUM Tactic.CONTR_TAC])

(* A rewrite whose condition carries a variable its left-hand side does
   not determine reaches the traversal with that variable existentially
   closed: [QUANTIFY_CONDITIONS] is what HOL4 has where Isabelle leaves
   a schematic in the condition.  [EVERY2_LENGTH] is the shape --
   [LIST_REL P l1 l2 ==> LENGTH l1 = LENGTH l2] prepares to
   [(?P. LIST_REL P l1 l2) ==> (LENGTH l1 = LENGTH l2 <=> T)] -- and
   Isabelle discharges the condition of its own [list_all2_lengthD] by
   assumption, the unifier reading the relation off the assumption the
   schematic meets.  The existential is what is left of that unification
   here, and nothing above answers it: the assumption is in the context,
   and the condition asks for the witness the assumption names.

   So this pass names it: the condition is matched against the context
   assumptions with the goal's own variables held fixed, and the
   witnesses the match reads off discharge the existential.  A rewrite
   with more than one premise arrives as one existential over their
   conjunction, so the conjuncts are matched in turn under what the
   earlier ones have named.  A match against an assumption already in
   the context is Isabelle's [assume_tac] step, not a search.

   It is the subgoaler, not a solver, because the subgoaler is the one
   slot only a side condition reaches: the traversal simplifies a
   condition through it and offers what survives to the solvers, while
   the solvers are also what a simplification tactic tries on the goal
   itself.  An existential goal is not a condition a rewrite left open,
   and simplification does not prove one in Isabelle either.  The
   subgoaler runs the traversal's own recursion first and looks only at
   what that leaves. *)
val witness_subgoaler : Traverse.subgoaler =
  let
    (* The conditions are matched one at a time against the context, each
       under what the earlier matches have already named: the rewrite's
       premises share the variables the traversal left open, which is how
       they determine one another in Isabelle's unifier too. *)
    fun witnesses assumptions fixed fixed_types conditions =
      let
        fun search [] instance = SOME instance
          | search (condition :: rest) instance =
              let
                val pattern = Term.subst instance condition
                fun attempt [] = NONE
                  | attempt (assumption :: others) =
                      case Lib.total
                             (Term.match_terml fixed_types fixed pattern)
                             assumption of
                          NONE => attempt others
                        | SOME (extra, _) =>
                            (case search rest (extra @ instance) of
                                 NONE => attempt others
                               | found => found)
              in
                attempt assumptions
              end
      in
        search conditions []
      end
    fun witness_tac (goal as (assumptions, w)) =
      let
        val (vars, body) = boolSyntax.strip_exists w
        val fixed =
          HOLset.difference
            (Term.FVL [w] Term.empty_tmset,
             HOLset.fromList Term.compare vars)
        val fixed_types = Term.type_vars_in_term w
        fun attempt conditions =
          witnesses assumptions fixed fixed_types conditions
        (* Whole first, so that a conjunction standing as one assumption
           is met by one match; the decomposed reading is for the
           premises the goal's own strip has taken apart. *)
        fun matched () =
          case attempt [body] of
              NONE => attempt (boolSyntax.strip_conj body)
            | found => found
      in
        if null vars then Tactical.NO_TAC goal
        else
          case matched () of
              NONE => Tactical.NO_TAC goal
            | SOME instance =>
                let
                  val accept = Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC
                in
                  Tactical.THEN
                    (Tactical.MAP_EVERY Tactic.EXISTS_TAC
                       (map (Term.subst instance) vars),
                     Tactical.ORELSE
                       (accept,
                        Tactical.THEN (Tactical.REPEAT Tactic.CONJ_TAC,
                                       accept)))
                    goal
                end
      end
    fun witness_proof context_thms term =
      Lib.total
        (fn goal =>
           Lib.itlist Drule.PROVE_HYP context_thms
             (Tactical.TAC_PROOF (goal, witness_tac)))
        (map Thm.concl context_thms, term)
  in
    fn ({recurse, context_thms, ...} : Traverse.simp_prover_ctxt) =>
      fn term =>
        let
          val reduction = recurse term
          val reduced = boolSyntax.rhs (Thm.concl reduction)
        in
          if Term.aconv reduced boolSyntax.T then reduction
          else
            case witness_proof context_thms reduced of
                NONE => reduction
              | SOME theorem =>
                  Thm.TRANS reduction (Drule.EQT_INTRO theorem)
        end
  end

(* HOL4's COND_CONG simplifies both branches of a conditional as well as
   its condition.  A recursive equation whose right-hand side is a
   conditional -- how an interval or an iteration is ordinarily stated --
   then rewrites its own unfolding without end: the branch holds an
   instance of the rule's own left-hand side, and rewriting it produces
   another.  Isabelle states such equations and rewrites with them, which
   its weak conditional congruence -- the condition simplified, the
   branches left alone -- is what allows.  Nothing short of that helps:
   the unfolding is licensed by the rule alone, so a congruence that
   descends into the branches at all diverges, whether or not it carries
   the condition down with it.  This layer follows Isabelle; the branch
   reasoning comes back from the case split, split_ss below.

   A congruence belongs to a fragment and a fragment is replaced whole,
   so the three other congruences of CONG_ss are restated here. *)
local
  infix THEN
  val op THEN = Tactical.THEN
in
val cond_weak_cong =
  Tactical.prove
    (``!condition simplified left right.
         (condition = simplified) ==>
         ((if condition then left else right) =
          (if simplified then left else right))``,
     Tactical.REPEAT Tactic.GEN_TAC THEN
     Tactic.DISCH_TAC THEN
     Rewrite.ASM_REWRITE_TAC [])
end

(* src/HOL/Set.thy:461,471 @ f7e02b7e.  [ball_cong_simp] and
   [bex_cong_simp] are default congruences there, so the body of a
   bounded quantifier is simplified with its bound in context.  HOL4
   spells a bounded quantifier unfolded -- [EXISTS_MEM] states
   [EXISTS P l] as [?e. MEM e l /\ P e], [IN_IMAGE] leaves the
   membership on the other side of the conjunction -- so the rule has to
   be stated of the conjunction the quantifier binds, once per
   membership and once per side.  Neither side subsumes the other: with
   the membership on the left the body is what its bound simplifies, and
   with the membership on the right the body is the context the
   membership simplifies in, which is where an assumption constraining
   the elements that answer an equation gets to fire.

   What it must not be stated of is every conjunction, which is
   Isabelle's [conj_cong]: Isabelle declines to make that a default
   congruence and a measurement agrees, the four-square identity of the
   algebra corpus going from 0.9s to 483s against a 30s budget as the
   conjunctive side conditions of the ring rewrites each acquire a
   context.  Keeping the bound rigid is not a weakening towards that
   measurement but the source's own shape: a bounded quantifier is what
   Isabelle carries a congruence for.  It also keeps the rule away from
   an existential a *rewrite* is conditional on -- [submonoid_element]
   in src/algebra states [x IN H] under [?h. h << g /\ ...], whose
   conjuncts are not a bound on the variable -- where opening the body
   re-enables the rewrite that raised the condition and the search
   recurses to the conditional depth.

   The last premise is what keeps the rule from taking the conjunction
   away from everything else.  A congruence decides the descent at the
   node it matches, so without it the conjunction under the quantifier
   would never again be a term the rewrites and the caller's own
   congruences see -- a [Cong] argument stated of a conjunction stops
   working under an existential, and the bound itself stops being
   rewritten.  Handing the rebuilt conjunction back to the traversal
   restores both, at one further pass over a body that is already in
   normal form.

   The bounded universal needs nothing: it unfolds to an implication,
   which [IMP_CONG] below already opens. *)
local
  infix THEN
  val op THEN = Tactical.THEN

  val element = Term.mk_var ("element", Type.alpha)
  val boolean = Type.alpha --> Type.bool

  fun membership_bounds element =
    [listSyntax.mk_mem
       (element, Term.mk_var ("elements", listSyntax.mk_list_type Type.alpha)),
     Term.mk_comb
       (boolSyntax.mk_icomb
          (Term.prim_mk_const {Thy = "bool", Name = "IN"}, element),
        Term.mk_var ("elements", boolean))]

  (* One schema, instantiated with the bound on either side of the
     conjunction: the left conjunct is simplified on its own, the right
     one with the simplified left in context, and the conjunction they
     rebuild is handed back to the traversal. *)
  fun bounded_cong bound bound_first =
    let
      val simplified_bound = Term.mk_var ("simplified_bound", boolean)
      val body = Term.mk_var ("body", boolean)
      val simplified_body = Term.mk_var ("simplified_body", boolean)
      val rebuilt = Term.mk_var ("rebuilt", boolean)
      fun apply f = Term.mk_comb (f, element)
      val (left, simplified_left, right, simplified_right) =
        if bound_first then
          (bound, apply simplified_bound, apply body, apply simplified_body)
        else
          (apply body, apply simplified_body, bound, apply simplified_bound)
      fun quantify statement = boolSyntax.mk_forall (element, statement)
      val left_alone = quantify (boolSyntax.mk_eq (left, simplified_left))
      val right_in_context =
        quantify
          (boolSyntax.mk_imp
             (simplified_left, boolSyntax.mk_eq (right, simplified_right)))
      val handed_back =
        quantify
          (boolSyntax.mk_eq
             (boolSyntax.mk_conj (simplified_left, simplified_right),
              apply rebuilt))
      val statement =
        boolSyntax.list_mk_imp
          ([left_alone, right_in_context, handed_back],
           boolSyntax.mk_eq
             (boolSyntax.mk_exists
                (element, boolSyntax.mk_conj (left, right)),
              boolSyntax.mk_exists (element, apply rebuilt)))
    in
      Tactical.prove
        (statement,
         Tactic.DISCH_TAC THEN
         Tactic.DISCH_TAC THEN
         Thm_cont.DISCH_THEN
           (fn equation => Rewrite.REWRITE_TAC [Conv.GSYM equation]) THEN
         Tactic.AP_TERM_TAC THEN
         Tactic.ABS_TAC THEN
         Rewrite.ASM_REWRITE_TAC [] THEN
         Tactic.ASM_CASES_TAC simplified_left THEN
         Tactic.RES_TAC THEN
         Rewrite.ASM_REWRITE_TAC [])
    end
in
val bounded_exists_congs =
  List.concat
    (map (fn bound => [bounded_cong bound true, bounded_cong bound false])
       (membership_bounds element))
end

val weak_cong_ss =
  simpLib.SSFRAG
    {name = SOME "CONGWEAK",
     congs =
       [Rewrite.REWRITE_RULE [Conv.GSYM boolTheory.AND_IMP_INTRO]
          boolTheory.IMP_CONG,
        cond_weak_cong,
        boolTheory.RES_FORALL_CONG,
        boolTheory.RES_EXISTS_CONG] @ bounded_exists_congs,
     convs = [], rewrs = [], filter = NONE, ac = [], dprocs = []}

(* HOL4's list-equation procedure is the analogue of the one src/HOL/
   List.thy installs over [append1_eq_conv], [append_same_eq] and
   [same_append_eq]: cancelling a common prefix or suffix of an
   equation is a step no rewrite set takes by itself, and both sides
   want it.  HOL4's reaches it through a normal form the layer does not
   share -- it left-nests an append and turns a trailing cons into a
   singleton append -- and it leaves the term renested even when
   nothing cancelled, which is how a goal arrives at a source rule in a
   spelling the rule cannot read.  Running it and then putting the
   result back into the source's spelling keeps the cancellation and
   drops the normal form; a run that only renested becomes no step at
   all, and the fragment says so rather than reporting progress it did
   not make. *)
val source_spelling_conv =
  Rewrite.PURE_REWRITE_CONV
    [Conv.GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]

fun list_equation_conv term =
  let
    val cancelled = listSimps.LIST_EQ_SIMP_CONV term
    val respelled =
      Thm.TRANS cancelled
        (source_spelling_conv (boolSyntax.rhs (Thm.concl cancelled)))
      handle Conv.UNCHANGED => cancelled
  in
    if aconv (boolSyntax.rhs (Thm.concl respelled)) term then
      raise Conv.UNCHANGED
    else respelled
  end

val list_equation_ss =
  simpLib.name_ss "AUTO list EQ"
    (simpLib.conv_ss
       {name = "SOURCE_LIST_EQ_CONV",
        trace = 2,
        key =
          SOME ([],
                let
                  val left =
                    mk_var ("l1", listSyntax.mk_list_type Type.alpha)
                in
                  boolSyntax.mk_eq (left, mk_var ("l2", type_of left))
                end),
        conv = K (K list_equation_conv)})

(* Two spellings of one statement reach a rewrite as two terms.
   Isabelle never meets the difference -- its rule and its goal are
   stated in the same theory and already agree on the order of a
   conjunction and the side an equation is written on, so its
   simplifier needs no ordering step and carries none: [conj_ac],
   [disj_ac] and [eq_ac] are all stated in HOL.thy and none of them is
   [simp] there.  A translated goal does meet it, because the HOL4
   result answering the source's states the same fact in its own order,
   and what is left is an equivalence between a term and a permutation
   of itself.

   Ordering the goal instead is not open to this layer.  A conjunction
   carries its left conjuncts into the right one's context -- that is
   what [rev_conj_cong] is, and the corpus names it -- so reordering a
   conjunction takes away the context a conditional rewrite is
   discharged in; measured, an ambient AC fragment costs the
   translation theory's own proof of [source_set_zip].  So the
   permutation is *decided* rather than imposed: the two sides are
   ordered privately, and if they agree the equivalence is closed.  The
   goal is either proved or untouched, and no term anywhere is
   reordered. *)
local
  val permutation_frag =
    simpLib.SSFRAG
      {name = SOME "AUTOPERMNF",
       convs = [], congs = [], filter = NONE, dprocs = [],
       ac = [(boolTheory.CONJ_ASSOC, boolTheory.CONJ_COMM),
             (boolTheory.DISJ_ASSOC, boolTheory.DISJ_COMM)],
       rewrs = [(NONE, boolTheory.EQ_SYM_EQ)]}
  val permutation_ss = simpLib.mk_simpset [permutation_frag]
in
  fun ordered term =
    simpLib.SIMP_CONV permutation_ss [] term
    handle Conv.UNCHANGED => Thm.REFL term
end

(* The two cheap conditions a permutation satisfies, tested before
   anything is ordered: the equation is an equivalence -- the net keys
   on [=], which is polymorphic, so most of what reaches here is an
   equation between terms of some other type -- and reordering and
   turning round both preserve the size of a term. *)
fun could_be_permuted (left, right) =
  Type.compare (type_of left, Type.bool) = EQUAL andalso
  Term.term_size left = Term.term_size right andalso
  not (aconv left right)

fun permuted_equivalence_conv term =
  let
    val (left, right) = boolSyntax.dest_eq term
    val _ =
      if could_be_permuted (left, right) then ()
      else raise ERR "permuted_equivalence_conv" "not a permutation"
    val ordered_left = ordered left
    val ordered_right = ordered right
  in
    if aconv (boolSyntax.rhs (Thm.concl ordered_left))
             (boolSyntax.rhs (Thm.concl ordered_right))
    then
      Drule.EQT_INTRO (Thm.TRANS ordered_left (Thm.SYM ordered_right))
    else raise ERR "permuted_equivalence_conv" "not one statement"
  end

val permuted_equivalence_ss =
  simpLib.name_ss "AUTO permuted equivalence"
    (simpLib.conv_ss
       {name = "PERMUTED_EQUIVALENCE_CONV",
        trace = 2,
        key =
          SOME ([],
                boolSyntax.mk_eq
                  (mk_var ("permuted_left", Type.bool),
                   mk_var ("permuted_right", Type.bool))),
        conv = K (K permuted_equivalence_conv)})

(* [remove_ssfrags] signals an absent fragment by raising UNCHANGED.
   Reporting that is what keeps the replacement honest: a caught
   exception here would leave the strong congruence in place under a
   name that says otherwise. *)
fun weaken_cond_congruence ss =
  simpLib.++
    (simpLib.remove_ssfrags ["CONG"] ss
       handle Conv.UNCHANGED =>
         raise ERR "weaken_cond_congruence"
           "the simpset carries no CONG fragment to replace",
     weak_cong_ss)

(* The unsafe side-condition solver added here reaches this simpset only:
   the simplifier offers unsafe solvers to every traversal regardless of
   the safe solvers, so a simpset with a normalisation phase to protect
   (aesop) names the decision procedures it wants rather than inheriting
   from here. *)
fun derive_clasimp_ss ss _ =
  ss
  |> weaken_cond_congruence
  |> simpLib.set_cond_depth 40
  |> (fn ss' => simpLib.++ (ss', simpLib.split_ss))
  (* ETA_ss is where Isabelle's matcher is and HOL4's is not.  Isabelle
     rewrites under higher-order patterns, which are matched modulo eta,
     so a rule about [$+ start] fires on a goal spelled
     [\offset. start + offset] as well.  HOL4's rewriter matches up to
     alpha and beta only, so without this the two silently fail to meet;
     a translated term arrives in both spellings, since the translation
     writes the abstraction and the simplifier contracts it only
     sometimes.  The classical search does close some such goals on its
     own -- it is the rewriting that stops at the mismatch. *)
  |> (fn ss' => simpLib.++ (ss', boolSimps.ETA_ss))
  (* The same mismatch one spelling further on.  Isabelle normalises the
     natural number 1 to [Suc 0] -- One_nat_def is a simp rule there --
     so a fact stated on SUC fires against a goal that bounds by a
     numeral.  HOL4 normalises the other way, numerals being the normal
     form, and a cited SUC rule then never meets the goal.  SUC_FILTER
     closes the gap from HOL4's side, deriving the numeral-matching
     variant of each SUC rule as it enters, which leaves HOL4's normal
     form alone. *)
  |> (fn ss' => simpLib.++ (ss', numSimps.SUC_FILTER_ss))
  (* The same mismatch again, and this one HOL4's normal form cannot be
     left alone through.  Isabelle's [append_assoc] is a simp rule that
     reads into the right-nested form and its [append_Cons] keeps a cons
     at the front, so every source result about a walk down [xs @ ys] is
     stated of a right-nested append.  HOL4 exports [APPEND_ASSOC] as a
     rewrite in the other direction and [listSimps]' equation
     normalisation turns a trailing cons into a singleton append, so the
     same term arrives as [(xs ++ [y]) ++ zs]; a rule about the prefix
     every element satisfies then has to read [xs ++ [y]] as that
     prefix, which is false of [y], and it never fires.  The two
     directions cannot both be ambient -- each is the other's reverse
     and the pair loops -- and the layer needs neither: dropping HOL4's
     leaves an append with the nesting it was written with, which for a
     translated goal is the source's.  The cons clause of APPEND is simp
     on both sides and keeps a leading cons at the front.  The equation
     procedure the exclusion drops comes back respelled: cancelling is
     wanted, its normal form is not. *)
  |> simpLib.remove_simps ["APPEND_ASSOC"]
  |> simpLib.exclude_ssfrags ["list EQ"]
  |> (fn ss' => simpLib.++ (ss', list_equation_ss))
  (* The same mismatch in the premises.  src/HOL/HOL.thy declares
     [disj_not1] -- [~P \/ Q <=> (P ==> Q)] -- simp, so a negated
     conjunction or existential reaches a source rule as an implication;
     HOL4 stops at the disjunction its own de Morgan rules leave.  The
     difference is not cosmetic: the simplifier's condition solver
     discharges a conditional rewrite's side condition from
     [!item. MEM item prefix ==> ~predicate item] and not from
     [!item. ~MEM item prefix \/ ~predicate item], so a rule whose
     condition constrains the elements of a list stops firing at exactly
     the goals that state the constraint negatively.  Isabelle declares
     this direction only -- [disj_not2] is left out there for changing
     the orientation -- and HOL4 carries no rewrite the other way, so
     the pair cannot loop. *)
  |> (fn ss' =>
        simpLib.++ (ss',
          simpLib.rewrites [Conv.GSYM boolTheory.IMP_DISJ_THM]))
  (* The permutation decision, for the reason given at
     [permuted_equivalence_conv]. *)
  |> (fn ss' => simpLib.++ (ss', permuted_equivalence_ss))
  (* HOL4 carries no order reasoning ambiently: a goal that supplies its
     own order -- as a [WeakLinearOrder] premise, say -- has the axioms
     and the steps in the assumptions and nothing chains them.  Isabelle
     reads such a chain off the linorder class without naming it
     (Provers/order_tac.ML, installed by Orderings.thy).  The decision
     procedure covers both places a chain is wanted, since it is asked
     about an atom wherever the traversal meets one: the atom the
     rewriting has left standing, and the side condition of a conditional
     rewrite, which is simplified with this same simpset. *)
  |> (fn ss' => simpLib.++ (ss', orderLib.ORDER_ss))
  (* Isabelle decides an arithmetic atom wherever the traversal meets
     one.  [Fields.thy]'s [fast_arith_nat] and [Int.thy]'s [fast_arith]
     are simprocs on [m < n], [m <= n] and [m = n], and the comment on
     the first says what the solver below is left with once they are
     there: the arithmetic solver "is really only useful to detect
     inconsistencies among the premises for subgoals which are not
     themselves (in)equalities, because the latter activate
     fast_nat_arith_simproc anyway".  The layer carried only that half,
     so an unfolded interval left a linear fact about num -- an atom in
     the goal rather than the condition of a rewrite -- standing. *)
  |> (fn ss' => simpLib.++ (ss', linarithLib.LINARITH_ss))
  (* The other half of that layer.  HOL4's own arithmetic simproc
     fragment normalises a linear term as well as deciding an atom --
     [std_ss ++ numSimps.ARITH_DP_ss] answers [LENGTH l - 1 - n] with
     [LENGTH l - (n + 1)] -- and the reducer above only decides.  So two
     spellings of one term never met here: this simpset folds the
     repeated subtraction to [LENGTH l - (1 + n)] and leaves it beside
     [LENGTH l - (n + 1)].  [ARITH_AC_ss] is that normalisation on its
     own, and it is num only; the int and real instances have no AC
     fragment to point at, which is a limit of this line and not of the
     argument for it. *)
  |> (fn ss' => simpLib.++ (ss', numSimps.ARITH_AC_ss))
  |> simpLib.set_safe_solvers [safe_solver]
  |> simpLib.add_unsafe_solver linarithLib.linarith_solver
  |> simpLib.set_subgoaler witness_subgoaler

(* This accessor is the only visible part of the private derived-value
   record.  BasicProvers marks the cache stale whenever srw_ss changes. *)
val {get = clasimp_ss, set = _} =
  BasicProvers.make_simpset_derived_value
    "clasimpLib.clasimp_ss" derive_clasimp_ss simpLib.empty_ss

(* Isabelle's asm_full_simp_tac simplifies premises mutually and turns the
   mksimps_pairs decomposition of premises into usable rewrites.

   strip=true       decomposes simplified conjunction, existential and
                    implication assumptions, covering that premise view;
   elimvars=false   avoids HOL4's stronger, Isabelle-incompatible
                    substitution and deletion of variable equations;
   droptrues=true   removes premises simplified to T, as implication
                    simplification does;
   oldestfirst=true visits assumptions in their original implication order.

   The extended flags supply mut_impc parity: the conclusion participates
   in the fixpoint and implication-shaped rewrites can rebuild the goal.
   The premises mut_impc is mutual over are the subgoal's, which a
   translated source result states as the antecedents of its conclusion,
   so imp_premises discharges those before the fixpoint; without it a
   goal stating its premises that way reaches the simplifier through the
   implication congruence alone, which offers a premise only the ones
   before it. *)
val asm_full_simp_base : simpLib.simptac_config =
  {strip = true, elimvars = false, droptrues = true, oldestfirst = true}

val asm_full_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = true,
   imp_premises = true}

fun ambient_simp safe ss =
  simpLib.GEN_GLOBAL_SIMP_TAC {safe = safe} asm_full_simp_config ss

(* The context-first pass below runs before the step that carries the
   invocation's rules, so it must leave the conclusion the shape those
   rules are stated on: discharging its antecedents takes an implication
   apart that a supplied rewrite may be stated on as a whole, and the
   step after would then find no redex.  The premises are read through
   the implication congruence in this pass and discharged by the step
   after, which is where they are wanted. *)
val context_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = true,
   imp_premises = false}

fun context_simp ss =
  simpLib.GEN_GLOBAL_SIMP_TAC {safe = false} context_simp_config ss

(* HOL4's simplifier rewrites outermost-first: at each node it tries the
   whole term before its subterms and re-descends into what it produced.
   Isabelle's works the other way round, and the difference shows
   wherever an ambient rule matches a term whose subterm the context has
   already settled: [takeWhile P xs ++ dropWhile P xs = xs] standing
   beside [takeWhile P xs = []] collapses to T here, the ambient
   decomposition matching the whole left-hand side, where the source
   simplifier rewrites the subterm first and is left with
   [dropWhile P xs = xs].  What is lost is a premise, and with it the
   goal it would have closed.

   Running the same step against the goal's own equations first --
   its assumptions, where a supplied fact stands, and none of the
   invocation's rules -- gives the subterm its chance.  The pass
   adds no rule to the goal: every rewrite it can make is one the step
   after it would have made too, in the other order.  It is not a
   bottom-up traversal -- an ambient rule can still consume a redex
   another ambient rule would have refined -- but the assumptions are
   where the two simplifiers disagree about what a goal still says.

   The supplied rewrites are left to the step after: a method's
   translation payload unfolds definitions the ambient simpset is
   needed to reduce again, and unfolding them with no simpset to hand
   builds terms the pass cannot put back together.

   What the pass keeps of the invocation's simpset is how it reads an
   assumption as a rewrite: [clear_rules] drops the rules, the decision
   procedures and the loopers and retains the canonicalisation, which
   is where a rewrite that would loop is recognised and stood down.  A
   case analysis on a walk leaves [xs = takeWhile ($~ o P) xs ++ x::r]
   among the assumptions -- an equation that reproduces its own
   left-hand side -- and read raw, as an empty simpset reads it, that
   rewrites forever. *)
fun context_first ss =
  Tactical.TRY (context_simp (simpLib.clear_rules ss) [])

(* Where the two sides are sets -- functions into bool -- the pointwise
   reading is membership and not application.  Every set and list fact
   HOL4 states is headed by [IN]: [MEM x l] is [x IN set l] itself, and
   [x IN s] is an application of [IN] rather than the application [s x]
   that FUN_EQ_THM produces.  Left applied, a set equation meets only
   what unfolds on its own -- an intersection is a comprehension
   underneath and reaches the membership reading anyway, while [set l]
   is opaque and stays as it is.  Isabelle needs no such step: its
   [set_eq_iff] is the membership reading outright. *)
val membership_extensionality =
  Tactical.prove
    (``!(left : 'a -> bool) right.
         (left = right) <=>
         !element. element IN left <=> element IN right``,
     Tactical.EVERY
       [Rewrite.REWRITE_TAC [boolTheory.IN_DEF, boolTheory.FUN_EQ_THM],
        Tactic.BETA_TAC,
        Rewrite.REWRITE_TAC []])

(* A rewrite states a fact about a head on the membership when its own
   left-hand side is a membership at that head: [MEM x l] is
   [x IN set l], [IN_IMAGE] and [IN_INTER] are the same shape, and
   [NOT_IN_EMPTY] is that shape negated.  The heads so collected are what
   the invocation states on the membership and nothing else is; the scan
   runs once where the tactic is built rather than once per equation the
   traversal reaches. *)
fun membership_heads ss =
  let
    fun subject theorem =
      let
        val (_, statement) =
          boolSyntax.strip_imp_only (Thm.concl (Drule.SPEC_ALL theorem))
      in
        case Lib.total boolSyntax.dest_neg statement of
            SOME negated => negated
          | NONE =>
              (case Lib.total boolSyntax.dest_eq statement of
                   SOME (left, _) => left
                 | NONE => statement)
      end
    fun head_of theorem =
      let
        val (_, set) = pred_setSyntax.dest_in (subject theorem)
        val (head, _) = boolSyntax.strip_comb set
      in
        if Term.is_const head then SOME (Term.dest_thy_const head) else NONE
      end
      handle HOL_ERR _ => NONE
    fun readings theorem =
      Drule.CONJUNCTS (Drule.SPEC_ALL theorem) handle HOL_ERR _ => [theorem]
    fun record (theorem, heads) =
      case head_of theorem of
          SOME {Thy, Name, ...} => Binaryset.add (heads, (Thy, Name))
        | NONE => heads
  in
    List.foldl record (Binaryset.empty (Lib.pair_compare (String.compare,
                                                          String.compare)))
      (List.concat
        (map readings
          (List.concat
            (map simpLib.frag_rewrites (simpLib.ssfrags_of ss)))))
  end

(* Which of the two readings an equation is given is decided by its
   sides.  A side headed by a constant HOL4 states facts about on the
   membership -- [set l], an image, an intersection -- is read there;
   where neither side is, there is no such fact to meet, and the applied
   reading is the one the goal's own context is in.  The source's
   [Collect_cong] is that case: it arrives with an applied premise about
   a predicate variable, and reading its conclusion as a membership puts
   the two out of each other's reach.  So is a constant-headed side that
   is a predicate short of an argument and no set -- [IS_NONE], a
   translated [source_superset] -- whose every fact is stated applied:
   read as a membership it meets none of them, and no rewrite brings the
   two readings back together. *)
fun membership_reading heads term =
  let
    fun head_constant side =
      Lib.total (Term.dest_thy_const o fst o boolSyntax.strip_comb) side
    fun stated_on_membership side =
      case head_constant side of
          SOME {Thy, Name, ...} => Binaryset.member (heads, (Thy, Name))
        | NONE => false
    fun both_sides (left, right) =
      snd (Type.dom_rng (Term.type_of left)) = Type.bool andalso
      (stated_on_membership left orelse stated_on_membership right)
  in
    Lib.can (Lib.assert both_sides o boolSyntax.dest_eq) term
  end

fun extensional_rule heads term =
  if membership_reading heads term then membership_extensionality
  else boolTheory.FUN_EQ_THM

(* Whether the engine's default takes an equation as a membership, for a
   method built from HOL4's simplifier directly -- the parity corpus
   builds its recipes that way -- to make the same decision about its own
   set-equality pass.  Applied to the simpset alone it collects the heads
   once, so a caller asking it of each equation its own pass reaches pays
   the scan once rather than once per equation. *)
fun reads_as_membership ss = membership_reading (membership_heads ss)

(* An equation between two functions is decided pointwise.  The source
   states its laws at the function level -- [f ^^ 0 = id],
   [set (filter P xs) = {x : set xs. P x}] -- where HOL4 states the same
   facts applied to an argument, so a goal that has reached the function
   level cannot meet the rule that settles it: the rewrite and the goal
   are the same fact at different arities.  Isabelle needs no step for
   this, its statements being already where its goals are; where a goal
   does reach it, [ext] is an introduction rule there.

   The equation is looked for under the goal's leading quantifiers and
   implications, which is where simplification leaves it, and taking it
   pointwise strips one arrow, so the step applies finitely often. *)
fun pointwise_conv heads term =
  if boolSyntax.is_forall term then
    Conv.QUANT_CONV (pointwise_conv heads) term
  else if boolSyntax.is_imp_only term then
    Conv.RAND_CONV (pointwise_conv heads) term
  else Conv.REWR_CONV (extensional_rule heads term) term

fun pointwise heads = Tactic.CONV_TAC (pointwise_conv heads)

(* The step is terminal: it runs on what simplification could not close,
   so no goal that already closes takes a different route.  Where
   simplification reports nothing to do the step still applies if the
   conclusion is a function equation -- that is the case it exists for
   -- and where neither applies the composite fails as it did.

   It belongs to a method, not to a step of one.  [extensional_normalize]
   below already puts a goal that arrives as a function equation into
   pointwise form before the search tactics start; what is left to this
   one is the equation that only appears once simplification has run,
   and asking for it again at every node of the classical cascade would
   pay for a whole simplification at each.  The safe cascade does not
   take it at all: Isabelle's [ext] is an introduction rule and not a
   safe one, and a safe step that rewrote every function equation would
   change what SAFE_TAC leaves. *)
fun with_extensionality ss simplify =
  let
    val pointwise_then =
      Tactical.THEN (pointwise (membership_heads ss), Tactical.TRY simplify)
  in
    Tactical.THEN
      (Tactical.ORELSE (simplify, pointwise_then),
       Tactical.REPEAT pointwise_then)
  end

(* Isabelle reads an ordered rewrite by its schematic variables.  Stated
   with them a rule is permutative, and the simplifier applies it only in
   the direction its term order takes downwards; the same rule
   instantiated at the goal's own fixed terms has no schematic variable
   left, is not permutative, and rewrites left to right.  That is how
   [force] closes a goal whose supplied fact commutes an operation: its
   search instantiates the fact at the goal's terms, and the simplifier
   it runs before each unsafe step reads the instance as an ordinary
   rewrite.

   HOL4 has no Free/Var distinction in a term, but it has one in a
   theorem: a variable free in a theorem's hypotheses is a local constant
   to matching, which is what [HO_PART_MATCH] computes its [lconsts]
   from.  So an instance is made rigid the way Isabelle's search makes
   one: the rule's conditions are discharged from the goal's own
   assumptions, and the terms those assumptions speak of can no longer be
   matched away.  A rule with nothing to discharge yields nothing here,
   which is right -- Isabelle refuses an uninstantiated permutative rule
   just as HOL4 does, and the parity gap is only about the instance a
   condition pins down.

   What the ordering guard sees is still a permutation, so the instance
   goes in *bounded*, which is that guard's own escape: bounded once per
   occurrence of the redex, since the rewrite removes the left-hand side
   it fires on and nothing else can reach it.  Every hypothesis of an
   instance is one of the goal's assumptions, so a proof that uses it
   still answers the goal it was read from. *)
local
  fun permutative_equation theorem =
    let
      val specialised = Drule.SPEC_ALL theorem
      val (_, equation) = boolSyntax.strip_imp (Thm.concl specialised)
      val (left, right) = boolSyntax.dest_eq equation
      val (head, _) = boolSyntax.strip_comb left
    in
      if Cond_rewr.is_var_perm (left, right) then SOME (specialised, head)
      else NONE
    end
    handle HOL_ERR _ => NONE

  (* The head of an operation the goal fixes is as often one of its own
     variables as it is a constant. *)
  fun headed_by head term =
    is_comb term andalso
    (let val (candidate, _) = boolSyntax.strip_comb term
     in
       if is_const head then is_const candidate andalso
                             same_const head candidate
       else aconv head candidate
     end)

  fun redexes head terms =
    let
      val found =
        List.concat (map (find_terms (headed_by head)) terms)
      fun occurrences term = length (List.filter (aconv term) found)
    in
      map (fn term => (term, occurrences term)) (Lib.op_mk_set aconv found)
    end

  fun discharge theorems matched =
    let
      val (conditions, _) = boolSyntax.strip_imp (Thm.concl matched)
      fun step (condition, theorem) =
        case List.find (fn fact => aconv (Thm.concl fact) condition)
               theorems of
            SOME fact => Thm.MP theorem fact
          | NONE => raise ERR "permutation_instances" "condition not assumed"
    in
      List.foldl step matched conditions
    end

  fun instance theorems specialised (redex, occurrences) =
    let
      val matched =
        Drule.PART_MATCH (boolSyntax.lhs o snd o boolSyntax.strip_imp)
          specialised redex
      val rewrite = discharge theorems matched
      val (left, right) = boolSyntax.dest_eq (Thm.concl rewrite)
    in
      if HOLset.equal (Thm.hypset matched, Thm.hypset specialised) andalso
         not (aconv left right) andalso
         Cond_rewr.ac_term_ord (left, right) <> GREATER andalso
         HOLset.isSubset (FVL [left] empty_tmset, Thm.hyp_frees rewrite)
      then SOME (BoundedRewrites.Ntimes rewrite occurrences)
      else NONE
    end
    handle HOL_ERR _ => NONE
in
  fun permutation_instances theorems (assumptions, conclusion) =
    let
      fun instances theorem =
        case permutative_equation theorem of
            NONE => []
          | SOME (specialised, head) =>
              List.mapPartial (instance theorems specialised)
                (redexes head (conclusion :: assumptions))
    in
      List.concat (map instances theorems)
    end
end

(* The instances are read off the goal the step is handed, before
   [context_first] has simplified it: an assumption that states a
   permutation is its own decreasing rewrite, so the pass that reads the
   goal's own equations turns it into T and drops it. *)
fun with_permutation_instances step simp_args =
  Tactical.ASSUM_LIST
    (fn theorems =>
       fn goal =>
         let
           val instances = permutation_instances theorems goal
           val _ =
             if null instances then ()
             else
               trace 2
                 (fn () =>
                    "permutation instances: " ^
                    String.concatWith ", "
                      (map (Parse.term_to_string o Thm.concl) instances))
         in
           step (simp_args @ instances) goal
         end)

fun asm_full_simp ss simp_args =
  with_permutation_instances
    (fn args => Tactical.THEN (context_first ss, ambient_simp false ss args))
    simp_args

fun safe_asm_full_simp ss simp_args =
  Tactical.THEN (context_first ss, ambient_simp true ss simp_args)

(* Inside the classical cascade the split between assumptions and
   conclusion is the cascade's own: its negation introduction strips a
   goal [~p] to [p |- F], and an implication rebuild re-forms [p ==> F]
   as [~p].  Safe saturation repeats while any step applies, so a
   wrapper that inverts one of its steps gives the two a cycle it never
   leaves; simplification participating in the cascade therefore
   normalises in place.  Discharging the conclusion's antecedents is
   left out for the same reason and costs nothing: the cascade's own
   implication introduction moves them into the assumptions, where the
   fixpoint reads them. *)
val cascade_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = false,
   imp_premises = false}

fun cascade_safe_simp ss =
  simpLib.GEN_GLOBAL_SIMP_TAC {safe = true} cascade_simp_config ss

fun add_simp_wrapper ss simp_args =
  let
    fun wrapper step =
      NTactical.NAPPEND
        (NTactical.NCHANGED
           (NTactical.LIFT (asm_full_simp ss simp_args)),
         step)
  in
    clasetLib.add_unsafe_wrapper ("asm_full_simp_tac", wrapper)
  end

fun add_safe_simp_wrapper ss simp_args =
  let
    fun wrapper step =
      NTactical.NORELSE
        (step,
         NTactical.NCHANGED
           (NTactical.LIFT (cascade_safe_simp ss simp_args)))
  in
    clasetLib.add_safe_wrapper
      ("safe_asm_full_simp_tac", wrapper)
  end

fun iff_declaration name theorem =
  let
    val th = Drule.SPEC_ALL theorem
  in
    {rules = clasetLib.iff_rules name theorem, rewrite = th}
  end

(* The derived rules are internal to the [iff] declaration, so a clash among
   them is not a declaration the user can correct.  add_derived_rule keeps
   the diagnostics quiet, and gives each declaration its own copy of a rule
   two declarations happen to derive alike, so retracting one declaration
   cannot silently disarm another. *)
fun add_iff_rules rules cs =
  List.foldl
    (fn ((rule_spec, named_rule), current) =>
      clasetLib.add_derived_rule rule_spec named_rule current)
    cs rules

fun persistent_iff_name name = KernelSig.name_toString name

val normalise_iff_name = clasetLib.normalise_rule_name

(* Persistent iff views live below the source theorem's public name.  Simp's
   prefix deletion means that Excl/delsimps on [Thy.Name] still affect the iff
   rewrite, while the dotted private key lets remove_iff retract only its own
   contribution.  The private claset stem likewise cannot collide with the
   ordinary rule generated by a theorem called [Name_intro]. *)
fun iff_view_name name = name ^ ".__clasimp_iff"

fun iff_rule_name kname =
  iff_view_name (persistent_iff_name kname)

fun iff_simp_kname ({Thy, Name} : KernelSig.kernelname) =
  {Thy = Thy, Name = iff_view_name Name}

(* Simp deletion keys use the public "Thy.Name" spelling.  Claset and iff-db
   keys deliberately retain the kernel's "Thy$Name" spelling. *)
fun simp_delete_key ({Thy, Name} : KernelSig.kernelname) =
  Thy ^ "." ^ Name

(* The private name contains a dot, so this is a three-field simp key.  Such
   keys retain their explicit theory qualifier even for the current scratch
   theory, which is intentionally absent from [ancestry "-"]. *)
fun iff_simp_delete_key kname =
  simp_delete_key (iff_simp_kname kname)

(* The one spelling of an iff rule name, shared by the declaration path and
   by the theory finaliser: the kernel "Thy$Name" form, the public "Thy.Name"
   form, or a bare name resolved against [default_thy].  remove_iff records
   only the kernel form, so the [default_thy] fallback serves the finaliser's
   reading of a name it did not itself record. *)
fun iff_kname {default_thy} name =
  case String.fields (equal #"$") name of
      [thy, theorem] => {Thy = thy, Name = theorem}
    | _ =>
        (case String.fields (equal #".") name of
             [thy, theorem] => {Thy = thy, Name = theorem}
           | [theorem] => {Thy = default_thy, Name = theorem}
           | _ =>
               raise ERR "iff_kname" ("malformed iff name: " ^ name))

fun persistent_iff_kname name =
  iff_kname {default_thy = current_theory ()} name

fun remove_iff_rules name =
  clasetLib.remove_rule (name ^ "_intro") o
  clasetLib.remove_rule (name ^ "_dest") o
  clasetLib.remove_rule (name ^ "_elim")

(* The simp stream is loaded before this later-registered iff stream, so a
   delsimps in the declaring theory would otherwise find the iff view
   resurrecting the named rewrite behind it.  The predicate makes such a
   removal persist, and both the declaration path and the finaliser apply
   it, so what a session ends with is what a descendant theory reloads.

   Only a theory-qualified removal counts.  A bare name is theory-agnostic
   in simp and matches by prefix, so honouring one here would let a
   delsimps aimed at an ancestor's rewrite silently suppress an unrelated
   local [iff] declaration that happens to share the theorem's name -- and
   the two delta streams carry no common ordering with which to tell the
   two apart.  remove_iff is the supported way to drop one's own
   declaration; a bare delsimps of it reaches the current session only. *)
fun theory_delsimped thyname =
  let
    val names =
      List.foldl
        (fn (ThmSetData.REMOVE name, names) => Symtab.update (name, ()) names
          | (_, names) => names)
        Symtab.empty
        (ThmSetData.theory_data {settype = "simp", thy = thyname})
  in
    fn (kname : KernelSig.kernelname) =>
      Symtab.defined names (simp_delete_key kname) orelse
      Symtab.defined names (iff_simp_delete_key kname)
  end

(* Installing and retracting a single declaration and installing a theory's
   whole batch are the same operation; the batched form is the only
   implementation.  [declarations] is in claset declaration order. *)
fun retract_persistent_iffs [] = ()
  | retract_persistent_iffs knames =
      let
        fun remove_rules cs =
          List.foldl
            (fn (kname, current) =>
              remove_iff_rules (iff_rule_name kname) current)
            cs knames
      in
        BasicProvers.temp_delsimps (map iff_simp_delete_key knames);
        clasetLib.augment_claset remove_rules
      end

(* The iff batch is a fragment of its own rather than one more contribution
   to the fragment BasicProvers names after the theory.  Sharing that name
   would leave Excl/ExclSF, diminish_srw_ss and exclude_ssfrags unable to
   address the [simp] and [iff] streams separately, and would let an
   exclusion already in force drop the whole batch unannounced. *)
fun iff_fragment_name thyname = thyname ^ "-iff"

fun install_persistent_iffs thyname declarations =
  let
    val delsimped = theory_delsimped thyname
    (* Reversed so that the most recent declaration takes precedence in the
       fragment, as successive single-declaration fragments do. *)
    val rewrites =
      List.rev
        (List.filter (fn (kname, _) => not (delsimped kname)) declarations)
    fun add_rules ((kname, theorem), cs) =
      add_iff_rules
        (#rules (iff_declaration (iff_rule_name kname) theorem)) cs
    val _ =
      if null rewrites then ()
      else
        BasicProvers.augment_srw_ss
          [simpLib.named_rewrites_with_names (iff_fragment_name thyname)
             (map
                (fn (kname, theorem) =>
                  (iff_simp_kname kname, Drule.SPEC_ALL theorem))
                rewrites)]
  in
    if null declarations then ()
    else
      clasetLib.augment_claset
        (fn cs => List.foldl add_rules cs declarations)
  end

fun retract_iff_declaration kname = retract_persistent_iffs [kname]

fun install_persistent_iff kname theorem =
  install_persistent_iffs (#Thy kname) [(kname, theorem)]

(* Only the source theorem is persistent; the db is the set of names whose
   claset and simpset views are currently installed. *)
fun apply_iff_delta delta db =
  case delta of
      ThmSetData.ADD (name, _) =>
        Symtab.update (persistent_iff_name name, ()) db
    | ThmSetData.REMOVE name =>
        Symtab.delete_safe (normalise_iff_name name) db

(* Retraction only ever applies to a name the db records as installed.
   Skipping it otherwise avoids a whole-history rebuild of the global
   simpset for every declaration replayed at theory load. *)
fun apply_iff_to_global delta db =
  let
    fun retract_if_present kname =
      if Symtab.defined db (persistent_iff_name kname)
      then retract_iff_declaration kname
      else ()
    val _ =
      case delta of
          ThmSetData.ADD (name, theorem) =>
            (retract_if_present name;
             install_persistent_iff name theorem)
        | ThmSetData.REMOVE name =>
            retract_if_present
              (persistent_iff_kname (normalise_iff_name name))
  in
    apply_iff_delta delta db
  end

(* Loading a theory resolves repeated declarations by their final event.
   Final-touch order preserves the recency tie-break of sequential replay. *)
fun iff_finaliser {thyname} deltas db =
  let
    fun delta_info (ThmSetData.ADD (kname, theorem)) =
          (kname, SOME (kname, theorem))
      | delta_info (ThmSetData.REMOVE name) =
          (iff_kname {default_thy = thyname} name, NONE)

    (* Scanning from the right keeps each name's final event, in the order
       those final events occur.  That is the recency order sequential
       replay would leave behind, at one pass over the deltas. *)
    fun remember (delta, (seen, touched)) =
      let
        val (kname, state) = delta_info delta
        val key = persistent_iff_name kname
      in
        if Symtab.defined seen key then (seen, touched)
        else (Symtab.update (key, ()) seen, (kname, state) :: touched)
      end

    val (_, touched) = List.foldr remember (Symtab.empty, []) deltas
    val stale =
      List.mapPartial
        (fn (kname, _) =>
          if Symtab.defined db (persistent_iff_name kname) then SOME kname
          else NONE)
        touched
    val live = List.mapPartial #2 touched
  in
    retract_persistent_iffs stale;
    install_persistent_iffs thyname live;
    List.foldl
      (fn (delta, current) => apply_iff_delta delta current)
      db deltas
  end

(* ------------------------------------------------------------------
   An [iff] whose rewrite may only run once its subject is normalized
   ------------------------------------------------------------------ *)

(* [not_None_eq] reads an arbitrary option through a constructor: the
   subject of its left side [x <> NONE] is a pattern variable, so the rule
   is about every term of the type.  Isabelle declares it [iff] and its
   simplifier rewrites the innermost redex first, so the rule is only ever
   offered a subject already in normal form.  HOL4's rewrites the outermost
   redex first, so a rule of that shape fires above every rule about the
   subject's own head, and its right side re-embeds the subject where none
   of them match: [(m ++ n) x <> NONE] becomes the stuck
   [?y. (m ++ n) x = SOME y], where Isabelle rewrites the inner [= NONE] by
   [map_add_None] and reaches the disjunction that discharges it.

   A low-priority reducer is what the traversal reaches only once the
   rewrites and the descent have both left a node alone, which is the order
   Isabelle applies such a rule in: on the term above it now yields
   [n x = NONE ==> ?y. m x = SOME y], and on a subject that is a variable
   it yields what the rewrite did.  So the declaration differs from [iff]
   in where its simpset half goes and nowhere else -- the claset halves are
   the same derived rules, under the same names.

   The rewrite is not a named simpset entry, so [delsimps] does not address
   it; [remove_iff_bottom_up] retracts a declaration, as [remove_iff] does
   for [iff]. *)

exception bottom_up_context

val bottom_up_fragment_name = "clasimp-bottom-up"

(* The declarations the reducer applies.  It reads them when it runs, so a
   declaration or a retraction changes what the fragment does without the
   fragment being replaced: a reducer is a closure rather than a named
   rewrite, so a simpset cannot address one of several, and rebuilding the
   fragment would mean removing it -- which forces the srw_ss state, and the
   replay of an ancestor's deltas at load time has no theory to force it
   in. *)
val bottom_up_rewrites = ref ([] : thm list)

val bottom_up_installed = ref false

val bottom_up_reducer =
  Traverse.REDUCER
    {name = SOME bottom_up_fragment_name,
     initial = bottom_up_context,
     addcontext = fn (context, _) => context,
     apply =
       fn _ => fn term =>
         Conv.FIRST_CONV
           (map (Conv.REWR_CONV o Drule.SPEC_ALL) (!bottom_up_rewrites))
           term}

val bottom_up_fragment =
  simpLib.SSFRAG
    {name = SOME bottom_up_fragment_name, convs = [], rewrs = [], ac = [],
     filter = NONE, dprocs = [bottom_up_reducer], congs = []}

(* The same mechanism for a rule installed for one invocation rather than
   declared: the rewrites are fixed when the fragment is built, where the
   declaration's reducer reads a table that a later declaration changes. *)
val normalised_subject_fragment_name = "clasimp-normalised-subject"

fun normalised_subject_fragment rewrites =
  simpLib.SSFRAG
    {name = SOME normalised_subject_fragment_name, convs = [], rewrs = [],
     ac = [], filter = NONE, congs = [],
     dprocs =
       [Traverse.REDUCER
          {name = SOME normalised_subject_fragment_name,
           initial = bottom_up_context,
           addcontext = fn (context, _) => context,
           apply =
             fn _ => fn term =>
               Conv.FIRST_CONV
                 (map (Conv.REWR_CONV o Drule.SPEC_ALL) rewrites) term}]}

(* The fragment is installed by the first declaration and then stays, inert
   while nothing is declared. *)
fun install_bottom_up_fragment table =
  let
    val _ = bottom_up_rewrites := map #2 (Symtab.dest table)
  in
    if !bottom_up_installed then ()
    else
      (bottom_up_installed := true;
       BasicProvers.augment_srw_ss [bottom_up_fragment])
  end

fun bottom_up_rules kname theorem =
  #rules (iff_declaration (iff_rule_name kname) theorem)

fun apply_bottom_up_delta delta table =
  case delta of
      ThmSetData.ADD (kname, theorem) =>
        Symtab.update (persistent_iff_name kname, theorem) table
    | ThmSetData.REMOVE name =>
        Symtab.delete_safe (normalise_iff_name name) table

(* Retraction is addressed to what the table records as installed, and by
   the key it is recorded under: naming a declaration takes a theory to
   resolve a bare name against, and the replay of an ancestor's deltas at
   load time has no current theory.  Retracting before a repeated
   declaration keeps one name to one copy of the derived rules. *)
fun apply_bottom_up_to_global delta table =
  let
    fun retract_if_present key =
      if Symtab.defined table key
      then clasetLib.augment_claset (remove_iff_rules (iff_view_name key))
      else ()
    val _ =
      case delta of
          ThmSetData.ADD (kname, theorem) =>
            (retract_if_present (persistent_iff_name kname);
             clasetLib.augment_claset
               (add_iff_rules (bottom_up_rules kname theorem)))
        | ThmSetData.REMOVE name =>
            retract_if_present (normalise_iff_name name)
    val table = apply_bottom_up_delta delta table
    val _ = install_bottom_up_fragment table
  in
    table
  end

val _ =
  if List.exists (equal "iff_bottom_up") (ThmSetData.all_set_types ())
     orelse ThmAttribute.is_attribute "iff_bottom_up"
  then
    raise ERR "registration"
      "settype or attribute iff_bottom_up already exists"
  else ()

val bottom_up_data =
  ThmSetData.export_with_ancestry
    {settype = "iff_bottom_up",
     delta_ops =
       {apply_to_global = apply_bottom_up_to_global,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_bottom_up_delta}}

(* As for [iff]: resolve against what is installed, so that a bare name
   reaches an ancestor's declaration and an unknown one is refused here
   rather than replayed as a no-op by every descendant. *)
fun resolve_bottom_up_name name =
  let
    val installed = Symtab.keys (#get_global_value bottom_up_data ())
    fun denotes candidate =
      candidate = name orelse
      (case String.fields (equal #"$") candidate of
           [thy, theorem] => theorem = name orelse thy ^ "." ^ theorem = name
         | _ => false)
  in
    case List.filter denotes installed of
        [resolved] => resolved
      | [] =>
          raise ERR "remove_iff_bottom_up"
            ("no [iff_bottom_up] declaration named " ^ name ^
             " is installed")
      | _ =>
          raise ERR "remove_iff_bottom_up"
            ("ambiguous [iff_bottom_up] name " ^ name)
  end

fun remove_iff_bottom_up name =
  let
    val delta = ThmSetData.REMOVE (resolve_bottom_up_name name)
  in
    #record_delta bottom_up_data delta;
    #update_global_value bottom_up_data (apply_bottom_up_to_global delta)
  end

val _ =
  if List.exists (equal "iff") (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute "iff"
  then raise ERR "registration" "settype or attribute iff already exists"
  else ()

(* The source theorem is the only persistent declaration.  Its claset and
   simpset views are recomputed by this hook whenever the iff stream is
   replayed.  The views deliberately use the public augmentation APIs, so
   neither the claset cdelta schema nor the simp declaration stream changes.

   Claset candidate order uses declaration recency as a tie-break.  Since
   [intro] and [iff] inhabit different delta streams, their relative recency
   in one theory may be permuted on reload.  This affects ties only; a shared
   declaration counter can be introduced if later benchmarks need one. *)
val iff_data =
  ThmSetData.export_with_ancestry
    {settype = "iff",
     delta_ops =
       {apply_to_global = apply_iff_to_global,
        thy_finaliser = SOME iff_finaliser,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_iff_delta}}

(* Resolve against the declarations currently installed rather than against
   the current theory.  Removing an ancestor's declaration by its plain name
   is the ordinary case, and defaulting the theory part to the current
   theory would name nothing and retract nothing, silently.  Resolving here
   also settles the name before it reaches the delta stream: a descendant
   theory replays the recorded name, so an unknown or ambiguous one would
   otherwise be replayed as a no-op by every descendant in turn. *)
fun resolve_iff_name name =
  let
    val installed = Symtab.keys (#get_global_value iff_data ())
    fun denotes candidate =
      candidate = name orelse
      (case String.fields (equal #"$") candidate of
           [thy, theorem] => theorem = name orelse thy ^ "." ^ theorem = name
         | _ => false)
  in
    case List.filter denotes installed of
        [resolved] => resolved
      | [] =>
          raise ERR "remove_iff"
            ("no [iff] declaration named " ^ name ^ " is installed")
      | candidates =>
          raise ERR "remove_iff"
            ("ambiguous [iff] name " ^ name ^ ": " ^
             String.concatWith ", " candidates)
  end

fun remove_iff name =
  let
    val delta = ThmSetData.REMOVE (resolve_iff_name name)
  in
    #record_delta iff_data delta;
    #update_global_value iff_data (apply_iff_to_global delta)
  end

(* A conditional rule whose conclusion is an equation between variables --
   [inj_onD] is the standard one -- is a rewrite in Isabelle:
   [Simplifier.mksimps] keeps the schematic left-hand side, and the
   subgoaler instantiates the schematics its conditions carry by unifying
   them against the assumptions.  HOL4 matches the left-hand side first and
   only then proves the conditions, so a left-hand side that is a bare
   variable is refused and the rule is turned into an [<=> T] rewrite of
   its own conclusion, with the condition variables the conclusion does not
   carry existentially closed
   (IMP_EQ_CANON and QUANTIFY_CONDITIONS, src/simp/src/Cond_rewr.sml).
   [inj_onD] prepares to
   [(?f s t. INJ f s t /\ x IN s /\ y IN s /\ f x = f y) ==> (x = y <=> T)]:
   a rewrite whose pattern is an equation between two variables, so it
   matches every equation in the goal, and whose condition the match
   determines nothing of.  It cannot fire, and it is not merely inert: the
   simplifier reaches it at every equation and calls its solver on the
   existential, so a four-assumption goal does not come back in a minute
   where the same call without the argument returns at once.

   The rule reaches those goals as an unsafe destruction rule instead: its
   premises say where the condition variables come from, so the reasoner
   fires it on an assumption matching the first and resolves the rest --
   what Isabelle's subgoaler does when it instantiates the schematics a
   condition carries, and the declaration Isabelle's own libraries give
   this rule family ([dest: inj_onD]).  Conclusion-directed instead, as an
   introduction rule, it is offered on every equality goal with the
   witnesses its premises name left to the search to guess: measured on the
   corpus goal that names [inj_onD], the destruction rule closes it and the
   introduction rule does not close it in twelve times the time.

   The test is on that exact shape, and reads the argument's form rather
   than its name.  A conditional equation between variables whose conditions
   the two sides do determine -- [LIST_EQ] is one -- carries no existential
   and keeps its rewrite, and so does an argument that prepares to several
   rewrites of which any is usable. *)
val undetermined_dest_spec : clasetLib.rulespec =
  {kind = clasetRules.Dest, safe = false, prio = NONE}

fun rewrites_every_equation rule =
  let
    val conclusion = concl rule
  in
    boolSyntax.is_imp_only conclusion andalso
    boolSyntax.is_exists (fst (boolSyntax.dest_imp conclusion)) andalso
    (case Lib.total boolSyntax.dest_eq
            (snd (boolSyntax.dest_imp conclusion)) of
         SOME (pattern, value) =>
           aconv value boolSyntax.T andalso
           (case Lib.total boolSyntax.dest_eq pattern of
                SOME (left, right) => is_var left andalso is_var right
              | NONE => false)
       | NONE => false)
  end

fun simp_argument_can_fire theorem =
  case Lib.total Cond_rewr.mk_cond_rewrs
         (BoundedRewrites.dest_tagged_rewrite theorem) of
      NONE => true
    | SOME prepared =>
        List.exists (not o rewrites_every_equation o #1) prepared

(* The declaration takes the rule the bound was attached to: a bound counts
   rewrite applications, and there are none to count here. *)
fun declare_undetermined theorem cs =
  let
    val rule = #1 (BoundedRewrites.dest_tagged_rewrite theorem)
    val name =
      clasetLib.fresh_rule_name
        {prefix = "__clasimp_undetermined_arg_", from = 0} cs
  in
    clasetLib.add_derived_rule undetermined_dest_spec (name, rule) cs
  end

(* A fact the classical reasoner declines too stays a rewrite: it is then
   no worse off than it was, and the argument is not silently dropped. *)
fun route_simp_argument (theorem, (cs, rewrites)) =
  if simp_argument_can_fire theorem then (cs, theorem :: rewrites)
  else
    case Lib.total (declare_undetermined theorem) cs of
        SOME extended =>
          (trace 1
             (fn () =>
               "no rewrite of " ^ Parse.thm_to_string theorem ^
               " can fire; declaring it as an unsafe destruction rule");
           (extended, rewrites))
      | NONE => (cs, theorem :: rewrites)

fun extend_invocation
      {iff_prefix,simp_rules,iff_rules,claset,simpset} =
  let
    val (routed_claset, rewritable) =
      List.foldr route_simp_argument (claset, []) simp_rules
    val simp_ss = simpLib.++ (simpset, simpLib.rewrites rewritable)
    val declarations =
      map
        (fn (index, rule) =>
          iff_declaration (iff_prefix ^ Int.toString index) rule)
        (Lib.enumerate 0 iff_rules)
    val invocation_cs =
      List.foldl
        (fn ({rules,...}, cs) => add_iff_rules rules cs)
        routed_claset declarations
    (* A single fragment rebuilds the rewrite net once.  Its head has the
       highest precedence, so reverse the declarations to match successive
       fragment insertion. *)
    val invocation_ss =
      if null declarations then simp_ss
      else
        simpLib.++
          (simp_ss,
           simpLib.rewrites (List.rev (map #rewrite declarations)))
  in
    (invocation_cs, invocation_ss)
  end

fun no_extra_markers theorems cs = (cs, theorems)

fun process_clasimp_args body base_cs base_ss =
  clasetLib.with_invocation_args
    {iff_prefix="__clasimp_iff_arg_", extra_markers=no_extra_markers}
    (fn cs => fn SOME ss => body cs ss
      | _ => raise ERR "process_clasimp_args" "simpset was not installed")
    base_cs (SOME {base=base_ss, extend=extend_invocation})

fun must_close name =
  Tactical.check_delta
    (ERR name "tactic did not close the goal")
    (fn (_, goals) => null goals)

(* Search tactics benefit from putting extensional equalities into their
   pointwise form before simplification and rule search, in the same two
   readings the terminal step takes.  The conversion is deliberately
   root-only: expanding a nested test such as [f = EMPTY] would lose a
   useful case split, and a pointwise goal must not be extensionalized
   again.

   Which of the two readings an equation is given is this layer's
   default and not the invocation's, and the invocation has the better
   claim where one of its own rewrites states a reading: Isabelle's
   [fun_eq_iff] names the applied one outright.  Only a rewrite of
   equations between functions states one -- [states_a_reading] is
   that test, and it is what keeps every other rewrite that happens to
   match the goal's statement out of the decision -- and the step
   stands down for one that takes this equation where it stands.
   Taken first, the default puts the equation out of that rewrite's
   reach for good -- a membership at a constant-headed side that is a
   predicate short of an argument, and no set, meets none of the facts
   the predicate's own are stated on, and no rewrite brings the two
   readings back together. *)
fun states_a_reading theorem =
  let
    val (premises, equivalence) =
      boolSyntax.strip_imp_only (Thm.concl (Drule.SPEC_ALL theorem))
    val (equation, _) = boolSyntax.dest_eq equivalence
    val (equated, _) = boolSyntax.dest_eq equation
  in
    null premises andalso Lib.can Type.dom_rng (Term.type_of equated)
  end
  handle HOL_ERR _ => false

(* [Conv.REWR_CONV] rejects a theorem it cannot read as a rewrite when
   it is given the theorem, not when the conversion is run, so the
   rejection escapes a [can] that is handed the conversion already
   built.  Applying it inside the [can] is what keeps one unusable
   rewrite in the simpset from raising out of the test and standing
   the step down everywhere. *)
fun read_by_a_rewrite ss term =
  let
    fun readings theorem =
      Drule.CONJUNCTS (Drule.SPEC_ALL theorem) handle HOL_ERR _ => [theorem]
    fun applies theorem =
      states_a_reading theorem andalso
      Lib.can (fn subject => Conv.REWR_CONV theorem subject) term
  in
    List.exists (List.exists applies o readings)
      (List.concat (map simpLib.frag_rewrites (simpLib.ssfrags_of ss)))
  end

fun extensional_normalize ss =
  let
    val heads = membership_heads ss
  in
    Tactical.CONV_TAC
      (Conv.CHANGED_CONV
         (fn term =>
            if read_by_a_rewrite ss term then
              raise ERR "extensional_normalize"
                "a rewrite of the invocation's takes the equation"
            else
              Conv.REWR_CONV (extensional_rule heads term) term))
  end

fun search_stages limit =
  let
    fun loop bound stages =
      if bound >= limit then List.rev (limit :: stages)
      else loop (bound * 2) (bound :: stages)
  in
    if limit <= 0 then [] else loop 1 []
  end

(* Try the witness-producing tableau at its invocation bound, then deepen
   the classical engine geometrically.  Re-running tableau from depth one
   repeats its whole frontier and caused previously cheap depth-four goals
   to spend their budget before reaching that bound.  Both legs remain
   bounded, and tableau witnesses are not hidden behind a complete
   classical traversal. *)
fun staged_auto_search {blast, depth} tableau_cs classical_cs =
  let
    fun report engine bound tactic goal =
      let
        val result = tactic goal
        val suffix =
          if engine = "classical" then
            ", expansions=" ^ Int.toString (clasetSearch.node_count ())
          else
            ", enable 'blast' trace level 2 for expansion statistics"
        val _ =
          trace 1
            (fn () =>
              engine ^ " search solved at stage " ^ Int.toString bound ^
              suffix)
      in
        result
      end
    val tableau =
      if blast <= 0 then []
      else
        [report "tableau" blast
           (tableauLib.CS_BLAST_DEPTH_TAC tableau_cs blast)]
    val classical =
      map
        (fn bound =>
          report "classical" bound
            (NTactical.DETERM
               (classicalLib.CS_DEPTH_SOLVE_TAC
                  {dup = false} bound classical_cs)))
        (search_stages depth)
  in
    Tactical.FIRST (tableau @ classical)
  end

fun auto_with {blast, depth} cs ss simp_args =
  let
    val search_cs = add_simp_wrapper ss simp_args cs
    val final_cs = add_safe_simp_wrapper ss simp_args cs
    val initial_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)
    val search =
      staged_auto_search {blast = blast, depth = depth} cs search_cs
    val final_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC final_cs)

    (* Isabelle repeatedly selects the first goal on which search succeeds.
       Both search legs solve their selected goal, and the repetition only
       revisits a residue when solving another goal instantiates shared
       schematic variables.  HOL4 kernel subgoals cannot share
       metavariables, so one TRY per subgoal (from THEN) is equivalent. *)
    val script =
      Tactical.EVERY
        [Tactical.TRY (extensional_normalize ss),
         with_extensionality ss (asm_full_simp ss simp_args),
         Tactical.TRY initial_safe,
         Tactical.TRY search,
         Tactical.TRY final_safe]
  in
    Tactical.CHANGED_TAC script
  end

fun CS_of body cs ss = body cs ss []

fun CS_AUTO_TAC bounds = CS_of (auto_with bounds)

(* The best-first leg's turn, in admitted expansions.  Every list/map
   corpus goal that leg closes under force closes far inside it: the
   longest of those solves, [ran_map_upd_Some], takes 0.6s.  A turn on a
   goal the leg cannot close is the cost the goals that need the other
   engine pay, and 500 expansions of one costs 11s, so a materially wider
   turn would spend a whole per-goal budget before the engine that closes
   the goal was reached. *)
val first_best_turn = 500

fun force_with name cs ss simp_args =
  let
    val search_cs = add_simp_wrapper ss simp_args cs
    val clarify =
      NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)

    (* Simplify before safe saturation.  In particular, this preserves an
       extensional IMAGE obligation until membership rewrites expose the
       constructor constraints from which tableau search builds a witness. *)
    val safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC search_cs)
    (* Isabelle's force_tac (src/Provers/clasimp.ML:167 @ Isabelle2025-2)
       ends in first_best_tac alone: the method carries no tableau leg.
       Ours keeps one, and neither leg may run to exhaustion in front of
       the other, because neither bound is a bound on work: best-first does
       not return on [snd_image_Sigma], which the tableau closes in 0.02s,
       and the tableau does not return on [ran_map_upd], which best-first
       closes in 0.1s.  Whichever goes first therefore loses the goals only
       the other closes.

       So each engine takes a bounded turn before either is let loose: a
       best-first turn, then the staged tableau and depth search at their
       invocation bounds, then the unbounded best-first the method is.
       Nothing force closes today is given up -- that last turn is what it
       runs now -- and a goal the first turn cannot close reaches the other
       engine with the budget it needs.  The last turn repeats the first
       one's expansions, which only a goal already spending seconds in
       best-first ever reaches. *)
    val search =
      Tactical.FIRST
        [classicalLib.CS_BOUNDED_FIRST_BEST_TAC search_cs first_best_turn,
         staged_auto_search {blast = 8, depth = 4} cs search_cs,
         NTactical.DETERM (classicalLib.CS_FIRST_BEST_TAC search_cs)]
    val script =
      Tactical.EVERY
        [Tactical.TRY clarify,
         Tactical.TRY (extensional_normalize ss),
         simpLib.FULL_SIMP_TAC ss simp_args,
         with_extensionality ss (asm_full_simp ss simp_args),
         Tactical.TRY safe,
         search]
  in
    must_close name script
  end

val CS_FORCE_TAC = CS_of (force_with "CS_FORCE_TAC")

(* The classical search drivers already succeed only with a closed engine
   state.  must_close is the public contract guard in case that invariant
   changes; it does not add another search step. *)
fun search_with_simp name engine cs ss simp_args =
  let
    val clarify =
      NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)
  in
    must_close name
      (Tactical.EVERY
         [Tactical.TRY clarify,
          Tactical.TRY (extensional_normalize ss),
          NTactical.DETERM
            (engine (add_simp_wrapper ss simp_args cs))])
  end

val simp_search =
  (classicalLib.CS_FAST_TAC, classicalLib.CS_SLOW_TAC,
   classicalLib.CS_BEST_TAC)
val (fast_search, slow_search, best_search) = simp_search

val CS_FASTFORCE_TAC =
  CS_of (search_with_simp "CS_FASTFORCE_TAC" fast_search)
val CS_SLOWSIMP_TAC =
  CS_of (search_with_simp "CS_SLOWSIMP_TAC" slow_search)
val CS_BESTSIMP_TAC =
  CS_of (search_with_simp "CS_BESTSIMP_TAC" best_search)

fun clarsimp_with cs ss simp_args =
  let
    val clarify =
      NTactical.DETERM
        (classicalLib.CS_CLARIFY_TAC
           (add_safe_simp_wrapper ss simp_args cs))
    val script =
      Tactical.THEN
        (safe_asm_full_simp ss simp_args,
         (* Isabelle's clarify tactic succeeds unchanged.  The HOL4
            CS_CLARIFY_TAC deliberately fails on a no-op, so TRY restores
            the sequencing behavior; CHANGED_TAC below guards the complete
            script. *)
         Tactical.TRY clarify)
  in
    Tactical.CHANGED_TAC script
  end

val CS_CLARSIMP_TAC = CS_of clarsimp_with

fun restore_normalized_target target validation theorems =
  let
    val theorem = validation theorems
    val normalization =
      Conv.QCONV
        (Conv.REDEPTH_CONV
           (Conv.ORELSEC (Thm.BETA_CONV, Drule.ETA_CONV))) target
    val normalized = boolSyntax.rhs (concl normalization)
  in
    if aconv (concl theorem) target then theorem
    else if aconv (concl theorem) normalized then
      EQ_MP (SYM normalization) theorem
    else theorem
  end

fun public body theorems (goal as (_, target)) =
  let
    val (goals, validation) =
      process_clasimp_args body
        (clasetLib.the_claset ()) (clasimp_ss ()) theorems goal
  in
    (goals, restore_normalized_target target validation)
  end

fun AUTO_DEPTH_TAC bounds theorems =
  public (auto_with bounds) theorems

fun AUTO_TAC theorems =
  AUTO_DEPTH_TAC {blast = 4, depth = 2} theorems

fun FORCE_TAC theorems =
  public (force_with "FORCE_TAC") theorems

fun FASTFORCE_TAC theorems =
  public (search_with_simp "FASTFORCE_TAC" fast_search) theorems

fun SLOWSIMP_TAC theorems =
  public (search_with_simp "SLOWSIMP_TAC" slow_search) theorems

fun BESTSIMP_TAC theorems =
  public (search_with_simp "BESTSIMP_TAC" best_search) theorems

fun CLARSIMP_TAC theorems =
  public clarsimp_with theorems

(* A first-order step meets a goal the simplification before it left in
   the ambient normal form, and HOL4's normal forms are not the ones its
   library states lemmas in: a list equation normalises [x::l] to
   [[x] ++ l], and the ambient EVERY_MEM iff reads EVERY as membership.
   A fact stated the library's way then never meets such a goal, where
   Isabelle's metis reads its facts in the one normal form its simp
   leaves goals in.  Each fact enters in every spelling -- the same
   closing of a normal-form gap from HOL4's side that SUC_FILTER
   performs for the simpset -- so nothing METIS_TAC would have found is
   lost. *)
local
  (* A rule the ambient set already carries normalizes to nothing when
     the whole of it is rewritten -- it rewrites itself away -- so the
     consequent is normalized on its own as well: an equivalence keeps
     the left-hand side it is triggered by and gains the right-hand
     side in the form the goal is in. *)
  fun consequent_conv conv term =
    if boolSyntax.is_forall term then
      Conv.QUANT_CONV (consequent_conv conv) term
    else if boolSyntax.is_imp_only term then
      Conv.RAND_CONV (consequent_conv conv) term
    else if boolSyntax.is_eq term then Conv.RAND_CONV conv term
    else conv term

  fun attempt rule theorem =
    SOME (rule theorem)
    handle Portable.Interrupt => raise Portable.Interrupt
         | HOL_ERR _ => NONE
         | Conv.UNCHANGED => NONE
in
  fun ambient_forms theorem =
    let
      val ss = clasimp_ss ()
      val forms =
        [attempt (simpLib.SIMP_RULE ss []) theorem,
         attempt (Conv.CONV_RULE (consequent_conv (simpLib.SIMP_CONV ss [])))
           theorem]
      fun add (NONE, kept) = kept
        | add (SOME form, kept) =
            if aconv (concl form) boolSyntax.T orelse
               List.exists (fn k => aconv (concl k) (concl form)) kept
            then kept
            else kept @ [form]
    in
      List.foldl add [theorem] forms
    end
end

(* Isabelle's first-order step lambda-lifts before it searches: an
   abstraction standing in an argument position becomes a constant with
   a defining equation, so a fact whose function variable has to take
   that abstraction as its value is instantiated first-order and the
   result is used without a beta step.  HOL4's clausifier carries the
   same transformation (normalForms.extract_lambdas) but does not run
   it, so the instantiation leaves a redex the search cannot reduce and
   the step is not taken.

   An abstraction argument of a constant of theory bool or min is the
   body of a binder rather than data, and is descended into instead;
   an eta-contractible one already names a function; and one mentioning
   a variable an enclosing binder binds cannot be named by a goal-level
   variable.  Naming happens whenever there is anything to name, as it
   does in Isabelle: the defining equation goes into the goal with the
   name, so the search is given back everything the abstraction said. *)
local
  fun binder_head term =
    let
      val head = fst (strip_comb term)
    in
      is_const head andalso
      let val {Thy, ...} = dest_thy_const head
      in Thy = "bool" orelse Thy = "min" end
    end

  fun scan bound term found =
    if is_abs term then
      let val (variable, body) = dest_abs term
      in scan (variable :: bound) body found end
    else if is_comb term then
      let
        val opaque = binder_head term
        val (head, arguments) = strip_comb term
        fun argument (argument_term, found) =
          let val found = scan bound argument_term found
          in
            if is_abs argument_term andalso not opaque andalso
               not (Lib.can Drule.ETA_CONV argument_term) andalso
               not (List.exists (fn v => op_mem aconv v bound)
                      (free_vars argument_term))
            then argument_term :: found
            else found
          end
      in
        List.foldl argument (scan bound head found) arguments
      end
    else found

  fun abstractions terms =
    op_mk_set aconv (List.foldl (fn (t, a) => scan [] t a) [] terms)

  fun definition (name, abstraction) =
    let
      val (variables, body) = strip_abs abstraction
    in
      boolSyntax.list_mk_forall
        (variables,
         boolSyntax.mk_eq (list_mk_comb (name, variables), body))
    end

  fun beta_theorem (name, abstraction) =
    let
      val (variables, _) = strip_abs abstraction
    in
      Thm.GENL variables
        (Drule.LIST_BETA_CONV (list_mk_comb (abstraction, variables)))
    end
in
  fun LAMBDA_LIFT_TAC (assumptions, conclusion) =
    let
      val lifted = abstractions (conclusion :: assumptions)
      val _ =
        if null lifted then
          raise ERR "LAMBDA_LIFT_TAC" "no abstraction stands in an argument"
        else ()
      val avoid = free_varsl (conclusion :: assumptions)
      val names =
        snd (List.foldl
               (fn (abstraction, (avoid, names)) =>
                  let
                    val name =
                      variant avoid
                        (mk_var ("lifted", type_of abstraction))
                  in (name :: avoid, (name, abstraction) :: names) end)
               (avoid, []) lifted)
      val forwards = map (fn (name, a) => a |-> name) names
      val backwards = map (fn (name, a) => name |-> a) names
      val goal =
        (map (subst forwards) assumptions,
         boolSyntax.list_mk_imp
           (map definition names, subst forwards conclusion))
    in
      ([goal],
       fn theorems =>
         List.foldl
           (fn (entry, theorem) => Thm.MP theorem (beta_theorem entry))
           (Thm.INST backwards (hd theorems)) names)
    end
end

fun AMBIENT_METIS_TAC theorems =
  Tactical.THEN
    (Tactical.TRY LAMBDA_LIFT_TAC,
     metisLib.METIS_TAC (List.concat (map ambient_forms theorems)))

end
