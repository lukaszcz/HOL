structure linarithLib :> linarithLib =
struct

open Abbrev HolKernel Drule

val ERR = mk_HOL_ERR "linarithLib"

val load_hint =
  " (load intLinarith / realLinarith / ratLinarith?)"

fun same_type left right = Type.compare (left, right) = EQUAL

fun relation_carrier tm =
  let
    val (_, body0) = boolSyntax.strip_forall tm
    val (_, body1) = boolSyntax.strip_imp_only body0
    val body =
      case Lib.total boolSyntax.dest_neg body1 of
          SOME inner => inner
        | NONE => body1
  in
    case Lib.total boolSyntax.dest_eq body of
        SOME (left, right) =>
          if same_type (Term.type_of left) (Term.type_of right)
          then SOME (Term.type_of left)
          else NONE
      | NONE =>
          (case Lib.total strip_comb body of
               SOME (_, [left, right]) =>
                 if same_type (Term.type_of left) (Term.type_of right) andalso
                    same_type (Term.type_of body) Type.bool
                 then SOME (Term.type_of left)
                 else NONE
             | _ => NONE)
  end

fun check_registered function tm =
  case relation_carrier tm of
      NONE => ()
    | SOME ty =>
        (case linarithData.instance_for ty of
             SOME _ => ()
           | NONE =>
               raise ERR function
                 ("no linarith instance for " ^
                  Parse.type_to_string ty ^ load_hint))

val classical_markers =
  [(clasetLib.destSIntro, "SIntro"),
   (clasetLib.destIntro, "Intro"),
   (clasetLib.destSElim, "SElim"),
   (clasetLib.destElim, "Elim"),
   (clasetLib.destSDest, "SDest"),
   (clasetLib.destDest, "Dest"),
   (clasetLib.destNorm, "Norm"),
   (clasetLib.destForward, "Forward"),
   (clasetLib.destSForward, "SForward")]

fun first_marker _ [] = NONE
  | first_marker theorem ((dest, name) :: rest) =
      case dest theorem of
          SOME _ => SOME name
        | NONE => first_marker theorem rest

fun reject function name =
  raise ERR function (name ^ " marker is not accepted by " ^ function)

fun validate_split function theorem =
  (ignore (splitLib.is_asm_split theorem)
   handle HOL_ERR _ =>
     raise ERR function "Malformed Split theorem (expected P-form)")

fun process_argument function theorem =
  if markerLib.is_Split theorem then
    let
      val split = markerLib.destSplit theorem
      val _ = validate_split function split
    in
      reject function "Split"
    end
  else
    let
      val {simp_rules, iff_rules, simp_controls, rest} =
        clasetLib.classify_simp_args [theorem]
    in
      if not (null simp_rules) then reject function "Simp"
      else if not (null iff_rules) then reject function "Iff"
      else if not (null simp_controls) then
        reject function "simplifier-control"
      else
        case rest of
            [plain] =>
              (case first_marker plain classical_markers of
                   SOME name => reject function name
                 | NONE =>
                     (case clasetLib.destDel plain of
                          SOME _ => reject function "Del"
                        | NONE => plain))
          | _ =>
              raise ERR function "internal argument-classification error"
    end

fun process_arguments function = map (process_argument function)

fun simple_core (assumptions, conclusion) =
  let
    val _ = check_registered "SIMPLE_LINARITH_TAC" conclusion
    val (split_neq, result) =
      linarithSolve.prove linarithData.default_config
        linarithDecomp.decomp assumptions conclusion
  in
    case result of
        SOME justifications =>
          linarithReplay.refute_tac split_neq justifications
            (assumptions, conclusion)
      | NONE =>
          raise ERR "SIMPLE_LINARITH_TAC"
            "linear arithmetic found no proof"
  end

fun SIMPLE_LINARITH_TAC arguments =
  let
    val facts =
      linarithData.arith_facts () @
      process_arguments "SIMPLE_LINARITH_TAC" arguments
  in
    Tactical.THEN (clasetLib.INSERT_FACTS_TAC facts, simple_core)
  end

fun atomized_assumptions premises =
  List.concat (map (CONJUNCTS o Thm.ASSUME) premises)

fun forward_prove premises conclusion =
  let
    val premise_theorems = atomized_assumptions premises
    val premise_terms = map Thm.concl premise_theorems
    val terms = premise_terms @ [conclusion]
    fun prove generalized =
      let
        val generalized_premises =
          List.take (generalized, List.length premise_terms)
        val generalized_conclusion = List.last generalized
      in
        linarithReplay.fwd_prove linarithData.default_config
          (map Thm.ASSUME generalized_premises)
          generalized_conclusion
      end
    val theorem = linarithReplay.generalize terms prove
  in
    List.foldl
      (fn (premise, result) => PROVE_HYP premise result)
      theorem premise_theorems
  end

fun LINARITH_PROVE tm =
  let
    val (variables, body) = boolSyntax.strip_forall tm
    val (premises, conclusion) = boolSyntax.strip_imp_only body
    val _ = check_registered "LINARITH_PROVE" conclusion
    val theorem = forward_prove premises conclusion
    val implication =
      List.foldr (fn (premise, result) => Thm.DISCH premise result)
        theorem premises
    val result = GENL variables implication
  in
    if Term.aconv (Thm.concl result) tm then result
    else
      raise ERR "LINARITH_PROVE"
        "internal error: reconstructed theorem has the wrong conclusion"
  end

fun attempt prove tm = SOME (prove tm) handle HOL_ERR _ => NONE

fun LINARITH_CONV tm =
  let
    val _ = check_registered "LINARITH_CONV" tm
  in
    case attempt LINARITH_PROVE tm of
        SOME theorem => EQT_INTRO theorem
      | NONE =>
          let
            val negated = boolSyntax.mk_neg tm
          in
            case attempt LINARITH_PROVE negated of
                SOME theorem => EQF_INTRO theorem
              | NONE =>
                  raise ERR "LINARITH_CONV"
                    "linear arithmetic could neither prove nor disprove term"
          end
  end

val _ = linarithData.register_instance linarithNum.instance

end
