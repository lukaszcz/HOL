structure linarithReplay :> linarithReplay =
struct

open Abbrev HolKernel Conv Drule
open linarithSolve

val ERR = mk_HOL_ERR "linarithReplay"

fun nth what items index =
  List.nth (items, index)
  handle Subscript =>
    raise ERR "mkthm" (what ^ " index " ^ Int.toString index ^
      " is out of range")

fun add_aconv tm terms =
  if List.exists (Term.aconv tm) terms then terms else terms @ [tm]

fun add_decomp_atoms
      (Decomp {lhs, rhs, ...}, atoms) =
  List.foldl (fn ((tm, _), acc) => add_aconv tm acc)
    (List.foldl (fn ((tm, _), acc) => add_aconv tm acc) atoms lhs) rhs

fun atoms_of terms =
  List.foldl
    (fn (tm, atoms) =>
      case linarithDecomp.decomp tm of
          NONE => atoms
        | SOME decomp => add_decomp_atoms (decomp, atoms))
    [] terms

datatype instance_env = Env of term list

fun mk_instance_env terms = Env (atoms_of terms)

fun is_literal tm =
  case linarithData.instance_for (Term.type_of tm) of
      NONE => false
    | SOME instance =>
        Option.isSome (Lib.total (#dest_lit (#dest instance)) tm)

fun generalize terms prove =
  let
    val atoms = atoms_of terms
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

fun dest_binary tm =
  let
    val (rator, right) = Term.dest_comb tm
    val (operator, left) = Term.dest_comb rator
  in
    (operator, left, right)
  end

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

fun first_result _ [] = NONE
  | first_result f (item :: rest) =
      case Lib.total f item of
          SOME result => SOME result
        | NONE => first_result f rest

fun first_match rules theorem =
  first_result
    (fn rule =>
      case first_result (fn implication => MATCH_MP implication theorem)
             (implications rule) of
          SOME result => result
        | NONE => raise ERR "first_match" "rule does not match")
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

fun lifts theorem =
  List.mapPartial
    (fn injection => first_match (relation_homs injection) theorem)
    (linarithData.injections ())

fun add_direct theorem1 theorem2 =
  let
    val instance = instance_of_thm theorem1
  in
    first_match (#add_mono (#kit instance)) (CONJ theorem1 theorem2)
  end
  handle HOL_ERR _ => NONE

fun try_add lifted other =
  first_result
    (fn theorem =>
      case add_direct theorem other of
          SOME result => result
        | NONE => raise ERR "try_add" "addition does not match")
    lifted

fun add_thms theorem1 theorem2 =
  case add_direct theorem1 theorem2 of
      SOME theorem => theorem
    | NONE =>
        (case try_add (lifts theorem1) theorem2 of
             SOME theorem => theorem
           | NONE =>
               (case try_add (lifts theorem2) theorem1 of
                    SOME theorem => theorem
                  | NONE => add_failure theorem1 theorem2))
and add_failure theorem1 theorem2 =
  let
    val _ = linarithData.trace_thm 1 "failed add, left:" theorem1
    val _ = linarithData.trace_thm 1 "failed add, right:" theorem2
  in
    raise ERR "mkthm" "Linear arithmetic: failed to add thms"
  end

fun mult_by_add n theorem =
  if Arbint.< (n, Arbint.one) then
    raise ERR "mkthm" "non-positive inequality multiplier"
  else
    let
      fun loop i result =
        if i = Arbint.one then result
        else loop (Arbint.- (i, Arbint.one))
               (add_thms theorem result)
    in
      loop n theorem
    end

fun operator_in_rules destructor rules =
  let
    fun search tm =
      case Lib.total destructor tm of
          SOME _ => SOME (#1 (dest_binary tm))
        | NONE =>
            if Term.is_abs tm then search (#2 (Term.dest_abs tm))
            else
              (case Lib.total Term.dest_comb tm of
                   NONE => NONE
                 | SOME (rator, rand) =>
                     (case search rator of
                          SOME operator => SOME operator
                        | NONE => search rand))
    fun find [] = NONE
      | find (theorem :: rest) =
          (case search (Thm.concl theorem) of
               SOME operator => SOME operator
             | NONE => find rest)
  in
    find rules
  end

fun additive_scale instance n variable =
  let
    val kit = #kit instance
    val dest = #dest instance
    val zero = #mk_lit dest Arbrat.zero
    val operator =
      case operator_in_rules (#dest_plus dest) (#add_mono kit) of
          SOME operator => operator
        | NONE =>
            raise ERR "mkthm"
              "no addition operator occurs in the instance kit"
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

fun mult_thm n theorem =
  let
    val instance = instance_of_thm theorem
    val equality = boolSyntax.is_eq (relation_body (Thm.concl theorem))
    val negative = Arbint.< (n, Arbint.zero)
    val magnitude = if negative then Arbint.~ n else n
    val result =
      if n = Arbint.~ Arbint.one then SYM theorem
      else if equality then
        let
          val literal =
            #mk_lit (#dest instance) (Arbrat.fromAInt magnitude)
          val scaled =
            apply_to_product instance magnitude literal theorem
          val normalized =
            CONV_RULE (BINOP_CONV (#norm_conv instance)) scaled
        in
          if negative then SYM normalized else normalized
        end
      else if negative then
        raise ERR "mkthm" "negative multiplier on an inequality"
      else mult_positive instance n theorem
  in
    result
  end

exception FalseReached of thm

fun normalize_added theorem =
  let
    val instance = instance_of_thm theorem
    val norm = #norm_conv instance
    val theorem' = CONV_RULE (BINOP_CONV norm THENC norm) theorem
  in
    if Term.aconv (Thm.concl theorem') boolSyntax.F then
      raise FalseReached theorem'
    else theorem'
  end

fun normalize_final theorem =
  if Term.aconv (Thm.concl theorem) boolSyntax.F then theorem
  else
    let
      val instance = instance_of_thm theorem
    in
      CONV_RULE (#norm_conv instance) theorem
    end

fun mkthm (Env atoms) assumptions justification =
  let
    fun one (Asm index) = nth "assumption" assumptions index
      | one (Nonneg index) =
          let
            val atom = nth "atom" atoms index
          in
            case linarithData.instance_for (Term.type_of atom) of
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
                            Parse.term_to_string atom))
          end
      | one (LessD why) =
          let
            val theorem = one why
            val kit = #kit (instance_of_thm theorem)
          in
            required_match "apply LessD to" (#lessD kit) theorem
          end
      | one (NotLessD why) =
          let
            val theorem = one why
            val kit = #kit (instance_of_thm theorem)
          in
            required_match "apply NotLessD to" [#not_less kit] theorem
          end
      | one (NotLeD why) =
          let
            val theorem = one why
            val kit = #kit (instance_of_thm theorem)
          in
            required_match "apply NotLeD to" [#not_le kit] theorem
          end
      | one (NotLeDD why) =
          let
            val theorem = one why
            val kit = #kit (instance_of_thm theorem)
            val less =
              required_match "apply NotLeDD to" [#not_le kit] theorem
          in
            required_match "finish NotLeDD on" (#lessD kit) less
          end
      | one (Multiplied (n, why)) = mult_thm n (one why)
      | one (Added (left, right)) =
          normalize_added (add_thms (one left) (one right))

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

end
