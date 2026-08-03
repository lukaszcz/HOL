structure linarithReplay :> linarithReplay =
struct

open Abbrev HolKernel Conv Drule
open linarithSolve

val ERR = mk_HOL_ERR "linarithReplay"

type config = linarithData.linarith_config

fun nth what items index =
  List.nth (items, index)
  handle Subscript =>
    raise ERR "mkthm" (what ^ " index " ^ Int.toString index ^
      " is out of range")

fun is_literal tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => false
    | SOME instance =>
        Option.isSome (Lib.total (#dest_lit (#dest instance)) tm)

fun generalize terms prove =
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
    Thm.INST restoring (prove generalized)
  end

val dest_binary = linarithDecomp.binary_parts

fun relation_body tm =
  case Lib.total boolSyntax.dest_neg tm of
      SOME body => body
    | NONE => tm

fun instance_of_term tm =
  let
    val (_, left, _) = dest_binary (relation_body tm)
  in
    case linarithData.instance_for (Term.type_of left) of
        SOME instance => instance
      | NONE =>
          raise ERR "mkthm"
            ("no linarith instance for " ^
             Parse.type_to_string (Term.type_of left))
  end

fun instance_of_thm theorem = instance_of_term (Thm.concl theorem)

fun implications theorem =
  if boolSyntax.is_imp
       (snd (boolSyntax.strip_forall (Thm.concl theorem)))
  then [theorem]
  else
    let
      val (forward, backward) = EQ_IMP_RULE (SPEC_ALL theorem)
    in
      [GEN_ALL forward, GEN_ALL backward]
    end
    handle HOL_ERR _ => [theorem]

(* The first application of f that does not raise. *)
fun first_result f items = Lib.total (Lib.tryfind f) items

fun first_match rules theorem =
  Lib.get_first
    (fn rule =>
      first_result (fn implication => MATCH_MP implication theorem)
        (implications rule))
    rules

fun required_match operation rules theorem =
  case first_match rules theorem of
      SOME result => result
    | NONE =>
        raise ERR "mkthm"
          ("Linear arithmetic: failed to " ^ operation ^ " theorem\n" ^
           Parse.thm_to_string theorem)

fun relation_homs injection =
  let
    val hom = #hom injection
  in
    [#le hom, #lt hom, #eq hom]
  end

fun injection_at_top injection tm =
  case Lib.total Term.dest_comb tm of
      SOME (operator, _) => Term.aconv operator (#inj injection)
    | NONE => false

fun orient_injection_hom injection theorem =
  let
    val opened = SPEC_ALL theorem
    val (left, right) = boolSyntax.dest_eq (Thm.concl opened)
  in
    if injection_at_top injection left then opened
    else if injection_at_top injection right then Thm.SYM opened
    else opened
  end

fun injection_rewrites injection =
  let
    val hom = #hom injection
  in
    List.mapPartial
      (Lib.total (orient_injection_hom injection))
      [#add hom, #mul hom]
  end

fun rewrite_injections rewrites theorem =
  if null rewrites then theorem
  else
    CONV_RULE
      (TOP_DEPTH_CONV (FIRST_CONV (map REWR_CONV rewrites))) theorem
    handle UNCHANGED => theorem

fun normalize_lift injection theorem =
  rewrite_injections (injection_rewrites injection) theorem

fun normalize_injections theorem =
  rewrite_injections
    (List.concat
      (map injection_rewrites (linarithData.injections ()))) theorem

fun normalize_relation_sides theorem =
  let
    val instance = instance_of_thm theorem
  in
    CONV_RULE (BINOP_CONV (#norm_conv instance)) theorem
  end
  handle HOL_ERR _ => theorem
       | UNCHANGED => theorem

fun lifts theorem =
  let
    val normalized = normalize_relation_sides theorem
  in
    List.mapPartial
      (fn injection =>
        Option.map (normalize_lift injection)
          (first_match (relation_homs injection) normalized))
      (linarithData.injections ())
  end

fun same_conclusion theorem1 theorem2 =
  Term.aconv (Thm.concl theorem1) (Thm.concl theorem2)

fun conversion_closure theorem =
  let
    fun explore [] found = found
      | explore (current :: pending) found =
          if List.exists (same_conclusion current) found then
            explore pending found
          else
            explore (pending @ lifts current) (found @ [current])
  in
    explore [theorem] []
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
  first_match (#add_mono (#kit instance)) (CONJ theorem1 theorem2)

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

fun add_thms theorem1 theorem2 =
  case add_direct theorem1 theorem2 of
      SOME theorem => theorem
    | NONE =>
        (case try_add_pairs
                (conversion_closure theorem1)
                (conversion_closure theorem2) of
             SOME theorem => theorem
           | NONE => add_failure theorem1 theorem2)
and add_failure theorem1 theorem2 =
  let
    val _ = linarithData.trace_thm 1 "failed add, left:" theorem1
    val _ = linarithData.trace_thm 1 "failed add, right:" theorem2
  in
    raise ERR "mkthm" "Linear arithmetic: failed to add thms"
  end

fun mult_by_add n theorem =
  if Arbint.< (n, Arbint.one) then
    raise ERR "mult_by_add" "non-positive inequality multiplier"
  else
    let
      fun loop i result =
        if i = Arbint.one then result
        else loop (Arbint.- (i, Arbint.one))
               (add_thms theorem result)
    in
      loop n theorem
    end

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
    AP_TERM function theorem
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

fun apply_mult_rule instance literal theorem rule =
  let
    fun direct implication =
      specialize_literal literal (MATCH_MP implication theorem)

    fun with_positive implication =
      let
        val opened = SPEC_ALL implication
        val variables =
          List.filter
            (fn variable =>
              Type.compare (Term.type_of variable, #ty instance) = EQUAL)
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
    case first_result direct (implications rule) of
        SOME result => result
      | NONE =>
          (case first_result with_positive (implications rule) of
               SOME result => result
             | NONE => raise ERR "apply_mult_rule" "rule does not match")
  end

fun mult_positive instance n theorem =
  let
    val literal = #mk_lit (#dest instance) (Arbrat.fromAInt n)
  in
    case first_result
           (apply_mult_rule instance literal theorem)
           (#mult_mono (#kit instance)) of
        SOME result => result
      | NONE => mult_by_add n theorem
  end

(* Renormalize the two sides of a relation, which sit one level deeper
   when the conclusion is a negated one. *)
fun normalize_sides instance theorem =
  let
    val sides = BINOP_CONV (#norm_conv instance)
  in
    CONV_RULE
      (if boolSyntax.is_neg (Thm.concl theorem) then RAND_CONV sides
       else sides)
      theorem
  end

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

fun normalize_added theorem =
  let
    val expanded = normalize_injections theorem
    val instance = instance_of_thm expanded
    (* norm_conv normalizes both sides of a relation itself, so a
       BINOP_CONV pass before it would only run the carrier's polynomial
       conversion -- the most expensive step of the replay loop -- a
       second time for no change. *)
    val theorem' = CONV_RULE (#norm_conv instance) expanded
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
      val instance = instance_of_thm expanded
    in
      CONV_RULE (#norm_conv instance) expanded
    end

(* Only a discrete carrier can strengthen a strict inequality to the
   non-strict one about its successor; a dense carrier supplies no such
   rule, and the LessD/NotLeDD justifications never arise for it. *)
fun lessD_rules (instance : linarithData.linarith_instance) =
  case #discrete instance of
      SOME {lessD} => lessD
    | NONE => []

fun mkthm assumptions justification =
  let
    fun one (Asm index) = nth "assumption" assumptions index
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
      | one (LessD why) = from_instance "LessD" lessD_rules why
      | one (NotLessD why) =
          from_instance "NotLessD"
            (fn instance => [#not_less (#kit instance)]) why
      | one (NotLeD why) =
          from_instance "NotLeD"
            (fn instance => [#not_le (#kit instance)]) why
      | one (NotLeDD why) =
          let
            val theorem = one why
            val instance = instance_of_thm theorem
            val less =
              required_match "apply NotLeDD to"
                [#not_le (#kit instance)] theorem
          in
            required_match "finish NotLeDD on" (lessD_rules instance) less
          end
      | one (Multiplied (n, why)) = mult_thm n (one why)
      | one (Added (left, right)) =
          normalize_added (add_thms (one left) (one right))
    (* Apply the rules the justification's own carrier supplies. *)
    and from_instance name select why =
          let
            val theorem = one why
            val instance = instance_of_thm theorem
          in
            required_match ("apply " ^ name ^ " to")
              (select instance) theorem
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
   belonging to the disequality's carrier. *)
fun is_disequality tm =
  case linarithDecomp.decomp tm of
      SOME (Decomp {rel = REL_NEQ, negated = false, ...}) => true
    | SOME (Decomp {rel = REL_EQ, negated = true, ...}) => true
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

fun split_assumption discrete_only theorem =
  let
    val tm = Thm.concl theorem
    val instance = instance_of_thm theorem
  in
    if is_disequality tm andalso
       (not discrete_only orelse Option.isSome (#discrete instance))
    then
      Option.map extract_split
        (first_match [#neqE (#kit instance)] theorem)
    else NONE
  end
  handle HOL_ERR _ => NONE

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

fun neq_elim_tac discrete_only (assumptions, goal) =
  if not (Term.aconv goal boolSyntax.F) then
    raise ERR "neq_elim_tac" "goal is not false"
  else
    case find_split discrete_only assumptions of
        NONE => raise ERR "neq_elim_tac" "no matching disequality"
      | SOME (prefix, suffix, Split (split, left, right)) =>
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
        Tactical.THEN
          (Tactical.REPEAT (neq_elim_tac true),
           Tactical.REPEAT (neq_elim_tac false))
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
   in the order elim_neq generated it. *)
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
