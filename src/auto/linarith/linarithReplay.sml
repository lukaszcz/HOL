structure linarithReplay :> linarithReplay =
struct

open Abbrev HolKernel Conv Drule
open linarithSolve

val ERR = mk_HOL_ERR "linarithReplay"

val same_type = linarithData.same_type

type config = linarithData.linarith_config

fun is_literal tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => false
    | SOME instance =>
        Option.isSome (Lib.total (#dest_lit (#dest instance)) tm)

fun generalize terms =
  let
    val atoms =
      atoms_of_decomps (List.mapPartial linarithDecomp.decomp terms)
    val abstracted =
      List.filter (fn tm => not (Term.is_var tm) andalso
                            not (is_literal tm)) atoms
    val variables = List.map (genvar o Term.type_of) abstracted
    val generalizing = ListPair.map (fn (tm, var) => tm |-> var)
      (abstracted, variables)
    val restoring = ListPair.map (fn (var, tm) => var |-> tm)
      (variables, abstracted)
    val generalized = List.map (Term.subst generalizing) terms
  in
    (generalized, Thm.INST restoring)
  end

val dest_binary = linarithDecomp.binary_parts

fun relation_body tm =
  case Lib.total boolSyntax.dest_neg tm of
      SOME body => body
    | NONE => tm

fun relation_carrier tm =
  let
    val (_, left, _) = dest_binary (relation_body tm)
  in
    Term.type_of left
  end

fun instance_of_term tm =
  let val carrier = relation_carrier tm in
    case linarithData.instance_for carrier of
        SOME instance => instance
      | NONE =>
          raise ERR "mkthm"
            ("no linarith instance for " ^
             Parse.type_to_string carrier)
  end

fun instance_of_thm theorem = instance_of_term (Thm.concl theorem)

(* The first application of f that does not raise. *)
fun first_result f items = Lib.total (Lib.tryfind f) items

(* The first of a rule set's implications that matches.  Every set
   replay uses arrives derived from the registry, in the order the
   rules were given, so taking the first match over the flattened set
   is taking the first rule that matches. *)
fun match_implications implications theorem =
  first_result (fn implication => MATCH_MP implication theorem)
    implications

fun required_match operation implications theorem =
  case match_implications implications theorem of
      SOME result => result
    | NONE =>
        raise ERR "mkthm"
          ("Linear arithmetic: failed to " ^ operation ^ " theorem\n" ^
           Parse.thm_to_string theorem)

(* The conversions come from the registry already built; an injection
   with no usable homomorphism reports that by raising UNCHANGED, which
   is the same answer as a term the rewrites do not touch. *)
fun rewrite_injections conversion theorem =
  CONV_RULE conversion theorem handle UNCHANGED => theorem

(* Decomposition strips an injection from an argument built out of the
   operators it distributes over, counting the source carrier's
   successor as the sum that carrier's own normalizer turns it into.
   Normalizing an injected argument with its carrier's norm_conv is what
   puts replay in step with that: it is the step that makes &(SUC n) the
   &(n + 1) the add homomorphism can then split.  It fails, rather than
   raising UNCHANGED, on a term that is not an injection, because
   ONCE_DEPTH_CONV descends past a failure and not past UNCHANGED. *)
fun injected_argument_conv tm =
  let
    val (operator, _) = Term.dest_comb tm
    val injection =
      case linarithData.injection_by_const operator of
          SOME injection => injection
        | NONE => raise ERR "injected_argument_conv" "not an injection"
  in
    case linarithData.instance_for (#from_ty injection) of
        SOME source => RAND_CONV (#norm_conv source) tm
      | NONE => raise ERR "injected_argument_conv" "no source instance"
  end

fun with_injected_arguments conversion =
  ONCE_DEPTH_CONV injected_argument_conv THENC conversion

fun normalize_lift conversion theorem =
  rewrite_injections (with_injected_arguments conversion) theorem

fun normalize_injections theorem =
  rewrite_injections
    (with_injected_arguments
       (linarithData.all_injection_rewrite_conv ()))
    theorem

(* Where an instance's norm_conv meets a conclusion: at the two sides of
   its relation, or at the conclusion entire -- which is how norm_conv
   gets to report that the relation reduces to T or F. *)
datatype depth = Sides | Whole

fun depth_conv depth instance =
  case depth of
      Sides => BINOP_CONV (#norm_conv instance)
    | Whole => #norm_conv instance

(* Apply an instance's norm_conv at the depth the conclusion needs.  A
   negated conclusion carries its relation one level deeper, so a caller
   that is handed one reaches it through normalize_under_negation; the
   callers that only ever see a plain relation stay with normalize_at,
   which leaves a negation alone rather than descending into it. *)
fun normalize_at depth instance theorem =
  CONV_RULE (depth_conv depth instance) theorem

fun normalize_under_negation depth instance theorem =
  CONV_RULE (RAND_CONV (depth_conv depth instance)) theorem

(* Normalizing is opportunistic at some call sites: a conclusion whose
   carrier has no instance, or one norm_conv declines, is answered with
   the theorem we already had.  CONV_RULE absorbs UNCHANGED itself, so
   the second handler is for a conv that raises it before CONV_RULE is
   reached. *)
fun absorb normalize theorem =
  normalize theorem
  handle HOL_ERR _ => theorem
       | UNCHANGED => theorem

fun normalize_relation_sides theorem =
  absorb (fn thm => normalize_at Sides (instance_of_thm thm) thm) theorem

(* One lift per registered injection whose order homomorphisms the
   relation matches, pushed inwards again by the rewrite conversion the
   registry built for that injection. *)
fun lift_by (entry : linarithData.derived_injection) theorem =
  Option.map (normalize_lift (#rewrite_conv entry))
    (match_implications (#relation_imps entry) theorem)

fun lifts visited theorem =
  let
    val normalized = normalize_relation_sides theorem
    fun unseen_lift entry =
      case lift_by entry normalized of
          NONE => NONE
        | SOME lifted =>
            let val carrier = relation_carrier (Thm.concl lifted) in
              if List.exists (same_type carrier) visited then NONE
              else SOME (lifted, carrier :: visited)
            end
  in
    List.mapPartial unseen_lift
      (linarithData.derived_injections ())
  end

fun same_conclusion theorem1 theorem2 =
  Term.aconv (Thm.concl theorem1) (Thm.concl theorem2)

(* Breadth-first, because try_add_pairs takes the first pair that adds
   and so depends on this order: the theorem itself, then its lifts,
   then theirs.  Each queued theorem also carries the carriers already
   visited on its path.  An injection cycle may return to an earlier
   carrier with a newly nested conclusion, so conclusion equality alone
   cannot close it.  The carrier-simple paths retain conversions between
   sibling carriers through their common source and are bounded by the
   finite registry.

   The queue is kept as a front list and a reversed back list, and the
   result is accumulated reversed, so neither the enqueueing nor the
   appending walks what it has already built. *)
fun conversion_closure theorem =
  let
    fun explore ([], []) found = List.rev found
      | explore ([], back) found = explore (List.rev back, []) found
      | explore ((current, visited) :: front, back) found =
          if List.exists (same_conclusion current) found then
            explore (front, back) found
          else
            explore (front, List.revAppend (lifts visited current, back))
              (current :: found)
  in
    explore ([(theorem, [relation_carrier (Thm.concl theorem)])], []) []
  end

(* The relation's operator constant, read off the first subterm of the
   rule that the instance's destructor accepts. *)
fun relation_operator destructor theorem =
  Option.map (#1 o dest_binary)
    (Lib.total (find_term (Lib.can destructor)) (Thm.concl theorem))

fun operator_in_rules destructor rules =
  Lib.get_first (relation_operator destructor) rules

fun required_operator function what destructor rules =
  case operator_in_rules destructor rules of
      SOME operator => operator
    | NONE =>
        raise ERR function
          ("no " ^ what ^ " operator occurs in the instance kit")

fun equality_as_le instance theorem =
  if not (boolSyntax.is_eq (relation_body (Thm.concl theorem))) then
    theorem
  else
    let
      val dest = #dest instance
      val operator =
        required_operator "equality_as_le" "leq" (#dest_leq dest)
          (#add_mono (#kit instance))
      val (left, _) = boolSyntax.dest_eq (Thm.concl theorem)
      val variable = genvar (#ty instance)
      fun leq l r = Term.list_mk_comb (operator, [l, r])
      val relation = leq left left
      val reflexive = EQT_ELIM (#norm_conv instance relation)
      val function = Term.mk_abs (variable, leq left variable)
      val congruence =
        CONV_RULE (BINOP_CONV BETA_CONV) (AP_TERM function theorem)
    in
      EQ_MP congruence reflexive
    end

fun add_equalities instance theorem1 theorem2 =
  let
    val operator =
      required_operator "add_equalities" "plus"
        (#dest_plus (#dest instance)) (#add_mono (#kit instance))
  in
    MK_COMB (MK_COMB (REFL operator, theorem1), theorem2)
  end

fun add_direct_raw instance theorem1 theorem2 =
  match_implications
    (#add_mono (linarithData.instance_implications instance))
    (CONJ theorem1 theorem2)

fun add_direct theorem1 theorem2 =
  let
    val instance = instance_of_thm theorem1
    val equality1 =
      boolSyntax.is_eq (relation_body (Thm.concl theorem1))
    val equality2 =
      boolSyntax.is_eq (relation_body (Thm.concl theorem2))
  in
    case add_direct_raw instance theorem1 theorem2 of
        SOME theorem => SOME theorem
      | NONE =>
          if equality1 andalso equality2 then
            SOME (add_equalities instance theorem1 theorem2)
          else
            add_direct_raw instance
              (equality_as_le instance theorem1)
              (equality_as_le instance theorem2)
  end
  handle HOL_ERR _ => NONE

fun try_add theorem others = Lib.get_first (add_direct theorem) others

fun try_add_pairs theorems others =
  Lib.get_first (fn theorem => try_add theorem others) theorems

fun add_failure theorem1 theorem2 =
  let
    val _ = linarithData.trace_thm 1 "failed add, left:" theorem1
    val _ = linarithData.trace_thm 1 "failed add, right:" theorem2
  in
    raise ERR "mkthm" "Linear arithmetic: failed to add thms"
  end

fun add_thms theorem1 theorem2 =
  case add_direct theorem1 theorem2 of
      SOME theorem => theorem
    | NONE =>
        (case try_add_pairs
                (conversion_closure theorem1)
                (conversion_closure theorem2) of
             SOME theorem => theorem
           | NONE => add_failure theorem1 theorem2)

(* The multiplier is a Fourier--Motzkin coefficient -- a product of lcms
   -- so it is unbounded, and n - 1 additions is too many.  Double
   instead, adding one copy back on a set bit: O(log n) additions.  The
   intermediate sums come out balanced rather than right-nested, but
   normalize_sides is what the caller reads, and that is unchanged. *)
fun mult_by_add n theorem =
  if Arbint.< (n, Arbint.one) then
    raise ERR "mult_by_add" "non-positive inequality multiplier"
  else
    let
      (* i copies of theorem summed, for i >= 1. *)
      fun multiple i =
        if i = Arbint.one then theorem
        else
          let
            val (half, bit) = Arbint.divmod (i, Arbint.two)
            val halved = multiple half
            val doubled = add_thms halved halved
          in
            if bit = Arbint.zero then doubled
            else add_thms theorem doubled
          end
    in
      multiple n
    end

(* Linear, and deliberately not doubled the way the multiplication above
   it is.  What is built here is a term, not a chain of inferences, and
   apply_to_product abstracts the variable out of it and beta-reduces on
   the spot.  The variable occurs at every node a doubled construction
   would share, so substitution copies each shared path back out: the
   term that reaches cancellation has n summands and n nodes whichever
   shape it was assembled in, and the instance's norm_conv walks it in
   O(n) either way.  Doubling would bound the recursion depth here and
   buy nothing else.

   This is the path an instance takes whose mult_mono mentions no
   multiplication, which is a registration the layer supports rather
   than a malformed one. *)
fun additive_scale instance n variable =
  let
    val dest = #dest instance
    val zero = #mk_lit dest Arbrat.zero
    val operator =
      required_operator "additive_scale" "addition" (#dest_plus dest)
        (#add_mono (#kit instance))
    fun add left right =
      Term.list_mk_comb (operator, [left, right])
    fun sum i =
      if i = Arbint.zero then zero
      else if i = Arbint.one then variable
      else add variable (sum (Arbint.- (i, Arbint.one)))
  in
    sum n
  end

(* Beta-reduced before it leaves, as the congruence equality_as_le
   builds is: an instance's expression conversion normalizes
   polynomials, not redexes, so a scaled side left as (\v. v * 3) x
   reaches cancellation as an atom distinct from the 3 * x it has to
   meet, and the certificate replays to a true relation instead of to
   falsity. *)
fun apply_to_product instance n literal theorem =
  let
    val dest = #dest instance
    val variable = genvar (#ty instance)
    val body =
      case operator_in_rules (#dest_mult dest)
             (#mult_mono (#kit instance)) of
          SOME operator =>
            Term.list_mk_comb (operator, [variable, literal])
        | NONE => additive_scale instance n variable
    val function = Term.mk_abs (variable, body)
  in
    CONV_RULE (BINOP_CONV BETA_CONV) (AP_TERM function theorem)
  end

fun specialize_literal literal theorem =
  let
    fun loop result =
      case Lib.total boolSyntax.dest_forall (Thm.concl result) of
          NONE => result
        | SOME _ => loop (SPEC literal result)
  in
    loop theorem
  end

fun prove_positive instance tm =
  EQT_ELIM (#norm_conv instance tm)

(* One rule's implications, both passes over them made before the next
   rule is tried: a rule that matches only with a positive premise
   still wins over a later rule that matches directly. *)
fun apply_mult_rule instance literal theorem implications =
  let
    fun direct implication =
      specialize_literal literal (MATCH_MP implication theorem)

    fun with_positive implication =
      let
        val opened = SPEC_ALL implication
        val variables =
          List.filter
            (fn variable =>
              same_type (Term.type_of variable) (#ty instance))
            (Term.free_vars (Thm.concl opened))
        fun try_variable variable =
          let
            val specialized = INST [variable |-> literal] opened
            val (antecedent, _) =
              boolSyntax.dest_imp (Thm.concl specialized)
            val (left, right) = boolSyntax.dest_conj antecedent
            fun positive_first () =
              MATCH_MP specialized
                (CONJ (prove_positive instance left) theorem)
            fun positive_second () =
              MATCH_MP specialized
                (CONJ theorem (prove_positive instance right))
          in
            case Lib.total positive_first () of
                SOME result => result
              | NONE => positive_second ()
          end
      in
        case first_result try_variable variables of
            SOME result => result
          | NONE => raise ERR "apply_mult_rule" "positive premise failed"
      end
  in
    case first_result direct implications of
        SOME result => result
      | NONE =>
          (case first_result with_positive implications of
               SOME result => result
             | NONE => raise ERR "apply_mult_rule" "rule does not match")
  end

fun mult_positive instance n theorem =
  let
    val literal = #mk_lit (#dest instance) (Arbrat.fromAInt n)
  in
    case first_result
           (apply_mult_rule instance literal theorem)
           (#mult_mono (linarithData.instance_implications instance)) of
        SOME result => result
      | NONE => mult_by_add n theorem
  end

(* Renormalize the two sides of a relation, which sit one level deeper
   when the conclusion is a negated one.  Scaling produces both kinds,
   so this is the one caller that descends. *)
fun normalize_sides instance theorem =
  (if boolSyntax.is_neg (Thm.concl theorem) then normalize_under_negation
   else normalize_at) Sides instance theorem

(* Scaling has to renormalize whatever it built, and for both kinds of
   relation.  Scaling an inequality did not, so a row scaled again on
   the way to a refutation kept the shape t * 2 * 3, which cancellation
   cannot match against the t * 6 on the other side, and replay ended at
   a true relation instead of at falsity. *)
fun mult_thm n theorem =
  let
    val instance = instance_of_thm theorem
    val equality = boolSyntax.is_eq (relation_body (Thm.concl theorem))
    val negative = Arbint.< (n, Arbint.zero)
    val magnitude = if negative then Arbint.~ n else n
    val scaled =
      if n = Arbint.~ Arbint.one then SYM theorem
      else if equality then
        let
          val literal =
            #mk_lit (#dest instance) (Arbrat.fromAInt magnitude)
          val product =
            apply_to_product instance magnitude literal theorem
        in
          if negative then SYM product else product
        end
      else if negative then
        raise ERR "mult_thm" "negative multiplier on an inequality"
      else mult_positive instance n theorem
  in
    normalize_sides instance scaled
  end

exception FalseReached of thm

(* Whole, not Sides: norm_conv normalizes both sides of a relation
   itself, so a BINOP_CONV pass before it would only run the carrier's
   polynomial conversion -- the most expensive step of the replay loop --
   a second time for no change. *)
fun normalize_added theorem =
  let
    val expanded = normalize_injections theorem
    val theorem' = normalize_at Whole (instance_of_thm expanded) expanded
  in
    if Term.aconv (Thm.concl theorem') boolSyntax.F then
      raise FalseReached theorem'
    else if Term.aconv (Thm.concl theorem') boolSyntax.T then expanded
    else theorem'
  end

fun normalize_final theorem =
  if Term.aconv (Thm.concl theorem) boolSyntax.F then theorem
  else
    let
      val expanded = normalize_injections theorem
    in
      normalize_at Whole (instance_of_thm expanded) expanded
    end

fun implications_of theorem =
  linarithData.instance_implications (instance_of_thm theorem)

fun mkthm assumptions justification =
  let
    (* A certificate names the same assumption at many of its leaves,
       so the list is indexed once here rather than walked per leaf. *)
    val indexed = Vector.fromList assumptions
    fun assumption index =
      Vector.sub (indexed, index)
      handle Subscript =>
        raise ERR "mkthm"
          ("assumption index " ^ Int.toString index ^
           " is out of range")
    fun one (Asm index) = assumption index
      | one (Nonneg atom) =
          (case linarithData.instance_for (Term.type_of atom) of
               NONE =>
                 raise ERR "mkthm"
                   ("no linarith instance for nonnegative atom " ^
                    Parse.term_to_string atom)
             | SOME instance =>
                 (case #nonneg (#kit instance) atom of
                      SOME theorem => theorem
                    | NONE =>
                        raise ERR "mkthm"
                          ("instance declined nonnegative atom " ^
                           Parse.term_to_string atom)))
      | one (LessD why) = from_instance "LessD" #lessD why
      | one (NotLessD why) = from_instance "NotLessD" #not_less why
      | one (NotLeD why) = from_instance "NotLeD" #not_le why
      | one (NotLeDD why) =
          let
            val theorem = one why
            val imps = implications_of theorem
            val less =
              required_match "apply NotLeDD to" (#not_le imps) theorem
          in
            required_match "finish NotLeDD on" (#lessD imps) less
          end
      | one (Multiplied (n, why)) = mult_thm n (one why)
      | one (Added (left, right)) =
          normalize_added (add_thms (one left) (one right))
    (* Apply the rules the justification's own carrier supplies.  Only
       a discrete carrier supplies the lessD LessD and NotLeDD ask for,
       and those justifications never arise for a dense one, whose
       lessD implications are empty. *)
    and from_instance name
          (select : linarithData.instance_implications -> thm list) why =
          let
            val theorem = one why
          in
            required_match ("apply " ^ name ^ " to")
              (select (implications_of theorem)) theorem
          end

    val theorem =
      (normalize_final (one justification)
       handle FalseReached theorem => theorem)
    val _ = linarithData.trace_thm 2 "replayed certificate:" theorem
  in
    if Term.aconv (Thm.concl theorem) boolSyntax.F then theorem
    else
      let
        val _ =
          linarithData.trace_items 1 "Assumptions:"
            Parse.thm_to_string assumptions
        val _ = linarithData.trace_thm 1 "Proved:" theorem
        val message =
          "Linear arithmetic should have refuted the assumptions but " ^
          "failed to."
        val _ = HOL_WARNING "linarithReplay" "mkthm" message
      in
        raise ERR "mkthm" message
      end
  end

(* Both replay paths use this operation to select neqE from the instance
   belonging to the disequality's carrier.  REL_NEQ is the only encoding
   to test for: decomp canonicalises a negated equality into it (see
   linarithSolve.sig). *)
fun is_disequality tm =
  case linarithDecomp.decomp tm of
      SOME (Decomp {rel = REL_NEQ, ...}) => true
    | _ => false

datatype split = Split of thm * term * term

fun extract_split theorem =
  let
    val (left_imp, rest) = boolSyntax.dest_imp (Thm.concl theorem)
    val (left, left_result) = boolSyntax.dest_imp left_imp
    val (right_imp, result) = boolSyntax.dest_imp rest
    val (right, right_result) = boolSyntax.dest_imp right_imp
  in
    if Term.aconv left_result boolSyntax.F andalso
       Term.aconv right_result boolSyntax.F andalso
       Term.aconv result boolSyntax.F
    then Split (theorem, left, right)
    else raise ERR "extract_split" "neqE has an unexpected conclusion"
  end

(* Which assumptions are splittable is decided by exactly the test the
   search used -- the disequality-elimination step inside linarithSolve
   asks whether a row is a disequality and whether it is discrete, which
   are is_disequality and the instance's discreteness here -- because
   the search emits one justification per case it generated and replay
   has to produce the matching goal for each.  Answering NONE for an
   assumption the search split leaves refute_tac's THENL with more
   tactics than goals, and the arity mismatch is what the user then
   sees.  So neqE not applying to an assumption that passed the test is
   an ill-formed instance, and is reported as one here. *)
fun split_assumption discrete_only theorem =
  (* An assumption whose carrier replay cannot even name is one decomp
     answers NONE for, so reading the instance first costs nothing and
     spares the traversal.  It is only a short circuit: everything the
     answer depends on is below. *)
  case Lib.total instance_of_thm theorem of
      NONE => NONE
    | SOME instance =>
        if not (is_disequality (Thm.concl theorem)) then NONE
        else if discrete_only andalso
                not (Option.isSome (#discrete instance))
        then NONE
        else
          (case
             match_implications
               (#neqE (linarithData.instance_implications instance))
               theorem
           of
               SOME implication => SOME (extract_split implication)
             | NONE =>
                 raise ERR "split_assumption"
                   ("the neqE of the linarith instance for " ^
                    Parse.type_to_string (#ty instance) ^
                    " does not apply to\n" ^
                    Parse.thm_to_string theorem))

fun finish_forward conclusion negated false_theorem =
  if boolSyntax.is_neg conclusion then
    Thm.NOT_INTRO (Thm.DISCH negated false_theorem)
  else Thm.CCONTR conclusion false_theorem

fun find_split discrete_only assumptions =
  let
    fun find _ [] = NONE
      | find prefix (theorem :: rest) =
          case split_assumption discrete_only theorem of
              SOME split => SOME (List.rev prefix, rest, split)
            | NONE => find (theorem :: prefix) rest
  in
    find [] (List.map Thm.ASSUME assumptions)
  end

fun neq_elim_step (prefix, suffix, Split (split, left, right)) =
  let
    val common = List.map Thm.concl (prefix @ suffix)
    val goals =
      [(common @ [left], boolSyntax.F),
       (common @ [right], boolSyntax.F)]
    fun justify [left_false, right_false] =
          Thm.MP
            (Thm.MP split (Thm.DISCH left left_false))
            (Thm.DISCH right right_false)
      | justify _ =
          raise ERR "neq_elim_tac" "invalid justification"
  in
    (goals, justify)
  end

(* Tactical.REPEAT ends its loop on any HOL_ERR, so it cannot tell the
   "nothing left to split" that legitimately ends this one from the
   diagnostic split_assumption raises where replay and search disagree,
   and would leave the user with the arity mismatch that diagnostic
   exists to replace.  Hence the loop written out: it ends exactly where
   find_split reports no splittable disequality. *)
fun neq_elim_tac discrete_only (goal as (assumptions, conclusion)) =
  if not (Term.aconv conclusion boolSyntax.F) then
    Tactical.ALL_TAC goal
  else
    case find_split discrete_only assumptions of
        NONE => Tactical.ALL_TAC goal
      | SOME found =>
          let
            fun step (_ : goal) = neq_elim_step found
          in
            Tactical.THEN (step, neq_elim_tac discrete_only) goal
          end

fun append_negated_tac (assumptions, conclusion) =
  let
    val negated = negate conclusion
    val goal = (assumptions @ [negated], boolSyntax.F)
    fun justify [false_theorem] =
          finish_forward conclusion negated false_theorem
      | justify _ =
          raise ERR "append_negated_tac" "invalid justification"
  in
    ([goal], justify)
  end

fun justification_tac justification (assumptions, goal) =
  if not (Term.aconv goal boolSyntax.F) then
    raise ERR "justification_tac" "goal is not false"
  else
    Tactic.ACCEPT_TAC
      (mkthm (List.map Thm.ASSUME assumptions) justification)
      (assumptions, goal)

fun refute_tac split_neq justifications =
  let
    val split_tac =
      if split_neq then
        Tactical.THEN (neq_elim_tac true, neq_elim_tac false)
      else Tactical.ALL_TAC
    val leaves = List.map justification_tac justifications
  in
    Tactical.THEN
      (append_negated_tac, Tactical.THENL (split_tac, leaves))
  end

fun refute config assumptions conclusion =
  let
    val (split_neq, result) =
      linarithSolve.prove config linarithDecomp.decomp
        linarithDecomp.is_nonnegative assumptions conclusion
  in
    Option.map (refute_tac split_neq) result
  end

(* The forward proof is the tactic replay run on a goal made of the
   premises' own conclusions.  Reproducing the disequality case split a
   second time as a tree of theorems would have to stay case-for-case in
   step with refute_tac, since both consume the one justification list
   in the order the search's disequality elimination generated it. *)
fun fwd_prove config theorems conclusion =
  let
    val hypotheses = List.map Thm.concl theorems
    val tactic =
      case refute config hypotheses conclusion of
          SOME tactic => tactic
        | NONE =>
            raise ERR "fwd_prove" "linear arithmetic found no proof"
    val (goals, validation) = tactic (hypotheses, conclusion)
    val _ =
      if null goals then ()
      else raise ERR "fwd_prove" "replay left a subgoal open"
    val theorem = Lib.rev_itlist PROVE_HYP theorems (validation [])
    val _ = linarithData.trace_thm 2 "forward proof:" theorem
  in
    theorem
  end

end
