structure clasetReplay :> clasetReplay =
struct

open Abbrev HolKernel boolSyntax

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
  | MoveAssumptionToBack of int
  | Wrapper

type created =
  {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}
type replay_action = clasetMeta.store -> tactic

datatype step_record =
  StepRecord of
    {kind : step_kind,
     target : int,
     consumed : int option,
     created : created,
     eigenvariables : string list list,
     validation : validation,
     action : replay_action,
     children : step_record option list}

datatype script = Script of step_record option list
datatype grounded_script =
  Grounded of {store : clasetMeta.store, script : script}

datatype replay_failure =
  ReplayFailure of
    {goal : goal, step : step_kind option, message : string,
     script : string}
datatype replay_outcome =
    Replayed of goal list * validation
  | ReplayFailed of replay_failure

val classical_trace = ref 0
val _ = Feedback.register_trace ("classical", classical_trace, 7)

fun make_record fields = StepRecord fields
fun kind_of (StepRecord {kind, ...}) = kind
fun target_of (StepRecord {target, ...}) = target
fun consumed_of (StepRecord {consumed, ...}) = consumed
fun created_of (StepRecord {created, ...}) = created
fun validation_of (StepRecord {validation, ...}) = validation
fun children_of (StepRecord {children, ...}) = children
fun action_of (StepRecord {action, ...}) = action

fun eigenvariables_of (StepRecord {eigenvariables, ...}) =
  List.concat eigenvariables

fun nth1 function_name values pos =
  if pos < 1 then
    raise mk_HOL_ERR "clasetReplay" function_name
      "positions are one-based"
  else
    List.nth (values, pos - 1)
    handle Subscript =>
      raise mk_HOL_ERR "clasetReplay" function_name
        "position out of range"

fun delete_nth function_name values pos =
  let
    val _ = nth1 function_name values pos
  in
    List.take (values, pos - 1) @ List.drop (values, pos)
  end

val normalize_conv =
  Conv.QCONV
    (Conv.REDEPTH_CONV
      (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV)))

fun normalize_thm th = Conv.CONV_RULE normalize_conv th

fun normalize_rule_thm th =
  let
    fun normalize_hypothesis (hypothesis, current) =
      let
        val equality = normalize_conv hypothesis
        val normalized = rhs (concl equality)
        val original = EQ_MP (SYM equality) (ASSUME normalized)
      in
        Drule.PROVE_HYP original current
      end
  in
    normalize_thm (List.foldl normalize_hypothesis th (hyp th))
  end

fun assumption_thm store asm target =
  let
    val asm' = clasetMeta.norm store asm
    val target' = clasetMeta.norm store target
    val normalized = normalize_thm (ASSUME asm')
  in
    if aconv (concl normalized) target' then
      EQ_MP (ALPHA (concl normalized) target') normalized
    else
      raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
        "the selected assumption does not close the goal"
  end

fun ASSUMPTION_TAC store pos (asl, w) =
  let
    val asm = nth1 "ASSUMPTION_TAC" asl pos
    fun validation [] = assumption_thm store asm w
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
            "validation received child theorems"
  in
    ([], validation)
  end

fun CONTRADICTION_TAC store (negative_pos, positive_pos) (asl, w) =
  let
    val negative = nth1 "CONTRADICTION_TAC" asl negative_pos
    val positive = nth1 "CONTRADICTION_TAC" asl positive_pos
    val negative' = clasetMeta.norm store negative
    val proposition = dest_neg negative'
    fun validation [] =
          let
            val nthm = assumption_thm store negative negative'
            val pthm = assumption_thm store positive proposition
          in
            Drule.CONTR (clasetMeta.norm store w)
              (MP (NOT_ELIM nthm) pthm)
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "CONTRADICTION_TAC"
            "validation received child theorems"
  in
    ([], validation)
  end

fun MP_TAC store {implication, antecedent} (asl, w) =
  let
    val implication_tm = nth1 "MP_TAC" asl implication
    val antecedent_tm = nth1 "MP_TAC" asl antecedent
    val implication' = clasetMeta.norm store implication_tm
    val (premise, consequence) = dest_imp_only implication'
    val child = (consequence :: delete_nth "MP_TAC" asl implication, w)

    fun validation [child_thm] =
          let
            val ithm = assumption_thm store implication_tm implication'
            val athm = assumption_thm store antecedent_tm premise
            val consequence_thm = MP ithm athm
          in
            Drule.PROVE_HYP consequence_thm child_thm
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "MP_TAC"
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun cons_assumptions assumptions asl =
  List.foldl (fn (asm, current) => asm :: current) asl assumptions

fun rule_child parent_asl premise names =
  let
    val (bounds, body) = strip_forall premise
    val _ =
      if length bounds = length names then ()
      else
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          "recorded eigenvariable arity is corrupt"
    val fresh =
      ListPair.map
        (fn (bound, name) => mk_var (name, type_of bound))
        (bounds, names)
    val substitution =
      ListPair.map
        (fn (bound, variable) => {redex = bound, residue = variable})
        (bounds, fresh)
    val body' = Term.subst substitution body
    val (antecedents, conclusion) = strip_imp_only body'
  in
    ((cons_assumptions antecedents parent_asl, conclusion),
     (fresh, antecedents, premise))
  end

fun normalize_assumption asm =
  let val equality = normalize_conv asm
  in (rhs (concl equality), EQ_MP equality (ASSUME asm)) end

fun theorem_hypothesis asl hypothesis =
  case List.find (fn (normalized, _) => aconv normalized hypothesis)
    (map normalize_assumption asl)
  of
      SOME (_, theorem) => theorem
    | NONE =>
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          "a theorem hypothesis is absent from the goal"

fun RULE_TAC {theorem, elim, consumed, eigenvariables} (asl, w) =
  let
    val rule0 = normalize_rule_thm theorem
    val target_equality = normalize_conv w
    val normalized_target = rhs (concl target_equality)
    val rule =
      List.foldl
        (fn (hypothesis, current) =>
          Drule.PROVE_HYP (theorem_hypothesis asl hypothesis) current)
        rule0 (hyp rule0)
    val (premises0, conclusion) = strip_imp_only (concl rule)
    val _ =
      if aconv conclusion normalized_target then ()
      else
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          ("the instantiated rule conclusion misses the goal: " ^
           Parse.term_to_string conclusion ^ " versus " ^
           Parse.term_to_string normalized_target)
    val (supplied, premises, parent_asl) =
      if elim then
        let
          val major_pos =
            case consumed of
                SOME pos => pos
              | NONE =>
                  raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
                    "an elimination record has no consumed assumption"
          val major = nth1 "RULE_TAC" asl major_pos
          val rule_major = hd premises0
          val (normalized_major, major_thm) =
            normalize_assumption major
          val major_thm =
            if aconv normalized_major rule_major then major_thm
            else
              raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
                "the selected assumption misses the major premise"
        in
          ([major_thm], tl premises0,
           delete_nth "RULE_TAC" asl major_pos)
        end
      else ([], premises0, asl)
    val _ =
      if length premises = length eigenvariables then ()
      else
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          "recorded child arity is corrupt"
    val child_data =
      ListPair.map
        (fn (premise, names) =>
          rule_child parent_asl premise names)
        (premises, eigenvariables)
    val child_goals = map #1 child_data
    val rebuild_data = map #2 child_data

    fun rebuild ((fresh, antecedents, premise), child_thm) =
      let
        val discharged =
          List.foldr (fn (antecedent, th) => DISCH antecedent th)
            child_thm antecedents
        val generalized = GENL fresh discharged
      in
        EQ_MP (ALPHA (concl generalized) premise) generalized
      end

    fun validation child_thms =
      if length child_thms <> length premises then
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          "validation received the wrong number of theorems"
      else
        let
          val premise_thms =
            ListPair.map rebuild (rebuild_data, child_thms)
          val result0 = Drule.LIST_MP (supplied @ premise_thms) rule
          val result =
            EQ_MP (ALPHA (concl result0) normalized_target) result0
        in
          EQ_MP (SYM target_equality) result
        end
  in
    (child_goals, validation)
  end
  handle Empty =>
    raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
      "an elimination rule has no major premise"

val HYP_SUBST_TAC =
  let
    val {hyp_subst_tac, ...} = clasetLib.claset_config
  in
    Tactical.THEN (hyp_subst_tac, Tactical.REPEAT hyp_subst_tac)
  end

fun GEN_NAMED_TAC name (asl, w) =
  let
    val (bound, _) = dest_forall w
    val variable = mk_var (name, type_of bound)
  in
    Tactic.X_GEN_TAC variable (asl, w)
  end

val GOAL_NEGATION_TAC = Tactic.CCONTR_TAC

fun MOVE_ASSUMPTION_TO_BACK_TAC pos (asl, w) =
  let
    val selected = nth1 "MOVE_ASSUMPTION_TO_BACK_TAC" asl pos
    val rest = delete_nth "MOVE_ASSUMPTION_TO_BACK_TAC" asl pos
    fun validation [theorem] = theorem
      | validation _ =
          raise mk_HOL_ERR "clasetReplay"
            "MOVE_ASSUMPTION_TO_BACK_TAC"
            "validation received the wrong number of theorems"
  in
    ([(rest @ [selected], w)], validation)
  end

fun assumption_action pos store = ASSUMPTION_TAC store pos
fun contradiction_action positions store =
  CONTRADICTION_TAC store positions
fun mp_action positions store = MP_TAC store positions
fun rule_action make store = RULE_TAC (make store)
val hyp_subst_action = fn _ => HYP_SUBST_TAC
val disch_action = fn _ => Tactic.DISCH_TAC
fun gen_action name _ = GEN_NAMED_TAC name
val goal_negation_action = fn _ => GOAL_NEGATION_TAC
fun move_assumption_to_back_action pos _ =
  MOVE_ASSUMPTION_TO_BACK_TAC pos
fun fixed_action result _ _ = result

fun open_record (StepRecord {children, ...}) =
  List.foldl
    (fn (NONE, total) => total + 1
      | (SOME child, total) => open_record child + total)
    0 children

fun open_option NONE = 1
  | open_option (SOME record) = open_record record

fun empty count =
  if count < 0 then
    raise mk_HOL_ERR "clasetReplay" "empty" "negative root count"
  else Script (List.tabulate (count, fn _ => NONE))

fun open_goals (Script roots) =
  List.foldl (fn (root, total) => open_option root + total) 0 roots

fun fill_option target record NONE =
      if target = 1 then (SOME record, true, 0)
      else (NONE, false, target - 1)
  | fill_option target record (SOME old) =
      let
        val StepRecord
          {kind, target = old_target, consumed, created,
           eigenvariables, validation, action, children} = old

        fun fill_children remaining [] = ([], false, remaining)
          | fill_children remaining (child :: rest) =
              let
                val (child', found, remaining') =
                  fill_option remaining record child
              in
                if found then (child' :: rest, true, remaining')
                else
                  let
                    val (rest', found', final_remaining) =
                      fill_children remaining' rest
                  in
                    (child' :: rest', found', final_remaining)
                  end
              end
        val (children', found, remaining) =
          fill_children target children
      in
        (SOME
          (StepRecord
            {kind = kind, target = old_target, consumed = consumed,
             created = created, eigenvariables = eigenvariables,
             validation = validation, action = action,
             children = children'}), found, remaining)
      end

fun append (Script roots) record =
  let
    val target = target_of record

    fun fill_roots remaining [] = ([], false, remaining)
      | fill_roots remaining (root :: rest) =
          let
            val (root', found, remaining') =
              fill_option remaining record root
          in
            if found then (root' :: rest, true, remaining')
            else
              let
                val (rest', found', final_remaining) =
                  fill_roots remaining' rest
              in
                (root' :: rest', found', final_remaining)
              end
          end
    val (roots', found, _) = fill_roots target roots
  in
    if found then Script roots'
    else
      raise mk_HOL_ERR "clasetReplay" "append"
        "the target does not identify an open goal"
  end

fun record_count (StepRecord {children, ...}) =
  1 + List.foldl
    (fn (NONE, total) => total
      | (SOME child, total) => record_count child + total)
    0 children

fun script_length (Script roots) =
  List.foldl
    (fn (NONE, total) => total
      | (SOME record, total) => record_count record + total)
    0 roots

fun variant_name Plain = "plain"
  | variant_name Swapped = "swapped"
  | variant_name Duplicate = "duplicate"
  | variant_name MakeElim = "make-elim"

fun kind_name (Assumption pos) = "assumption " ^ Int.toString pos
  | kind_name (Contradiction (left, right)) =
      "contradiction " ^ Int.toString left ^ "," ^ Int.toString right
  | kind_name (ModusPonens _) = "mp"
  | kind_name (RuleApplication {variant, elim, ...}) =
      "rule(" ^ variant_name variant ^
      (if elim then ",elim)" else ",intro)")
  | kind_name Disch = "DISCH"
  | kind_name Gen = "GEN"
  | kind_name HypSubst = "hyp-subst"
  | kind_name CContr = "CCONTR"
  | kind_name (MoveAssumptionToBack pos) =
      "move-back " ^ Int.toString pos
  | kind_name Wrapper = "wrapper"

fun lines_of_record indent (StepRecord {kind, target, children, ...}) =
  let
    val line = indent ^ Int.toString target ^ ": " ^ kind_name kind
    val child_lines =
      List.concat
        (map
          (fn NONE => [indent ^ "  open"]
            | SOME child => lines_of_record (indent ^ "  ") child)
          children)
  in
    line :: child_lines
  end

fun to_string (Script roots) =
  String.concatWith "\n"
    (List.concat
      (map
        (fn NONE => ["open"]
          | SOME record => lines_of_record "" record)
        roots))

fun ground store script =
  Grounded {store = clasetMeta.ground store, script = script}

fun grounded_store (Grounded {store, ...}) = store
fun grounded_to_string (Grounded {script, ...}) = to_string script

exception ReplayError of step_record * goal * string

fun split_lengths [] theorems =
      if List.null theorems then []
      else raise Fail "extra replay theorems"
  | split_lengths (count :: counts) theorems =
      let
        val prefix = List.take (theorems, count)
        val suffix = List.drop (theorems, count)
      in
        prefix :: split_lengths counts suffix
      end

fun replay_option _ NONE goal = ([goal], fn [th] => th | _ =>
      raise mk_HOL_ERR "clasetReplay" "replay"
        "open-goal validation arity")
  | replay_option store (SOME record) goal =
      let
        val (children, parent_validation) =
          Tactical.VALID (action_of record store) goal
          handle error =>
            raise ReplayError (record, goal, Feedback.exn_to_string error)
        val subtrees = children_of record
        val _ =
          if length children = length subtrees then ()
          else
            raise ReplayError
              (record, goal, "recorded and emitted child arities differ")
        val replayed =
          ListPair.map
            (fn (subtree, child) =>
              replay_option store subtree child)
            (subtrees, children)
        val residuals = List.concat (map #1 replayed)
        val counts = map (length o #1) replayed
        val validations = map #2 replayed

        fun validation theorems =
          let
            val groups = split_lengths counts theorems
            val child_theorems =
              ListPair.map (fn (validate, group) => validate group)
                (validations, groups)
          in
            parent_validation child_theorems
          end
      in
        (residuals, validation)
      end

fun replay_roots _ [] [] = ([], fn [] => [] | _ =>
      raise mk_HOL_ERR "clasetReplay" "replay_roots"
        "root validation arity")
  | replay_roots store (root :: roots) (goal :: goals) =
      let
        val (first_goals, first_validation) =
          replay_option store root goal
        val (rest_goals, rest_validation) =
          replay_roots store roots goals
        val first_count = length first_goals
        fun validation theorems =
          let
            val first = List.take (theorems, first_count)
            val rest = List.drop (theorems, first_count)
          in
            first_validation first :: rest_validation rest
          end
      in
        (first_goals @ rest_goals, validation)
      end
  | replay_roots _ _ _ =
      raise mk_HOL_ERR "clasetReplay" "replay_roots"
        "script root count does not match the input"

fun replay (Grounded {store, script = Script roots}) goal =
  let
    val (goals, validate_roots) = replay_roots store roots [goal]
    fun validation theorems =
      case validate_roots theorems of
          [theorem] => theorem
        | _ =>
            raise mk_HOL_ERR "clasetReplay" "replay"
              "single-goal replay produced several root theorems"
  in
    Replayed (goals, validation)
  end
  handle ReplayError (record, bad_goal, message) =>
    ReplayFailed
      (ReplayFailure
        {goal = bad_goal, step = SOME (kind_of record),
         message = message, script = to_string (Script roots)})
       | error =>
    ReplayFailed
      (ReplayFailure
        {goal = goal, step = NONE,
         message = Feedback.exn_to_string error,
         script = to_string (Script roots)})

fun goal_string (asl, w) =
  let
    val assumptions =
      String.concatWith ", " (map Parse.term_to_string asl)
  in
    "[" ^ assumptions ^ "] ?- " ^ Parse.term_to_string w
  end

fun REPLAY_TAC grounded goal =
  case replay grounded goal of
      Replayed result => result
    | ReplayFailed
        (ReplayFailure {goal = bad_goal, step, message, script}) =>
        let
          val step_text =
            case step of NONE => "<script>" | SOME kind => kind_name kind
          val diagnostic =
            "Replay failed at " ^ step_text ^ " on " ^
            goal_string bad_goal ^ ": " ^ message
          val _ =
            if Feedback.current_trace "classical" >= 1 then
              Feedback.HOL_MESG
                (diagnostic ^ "\nReplay script:\n" ^ script)
            else ()
        in
          raise mk_HOL_ERR "clasetReplay" "REPLAY_TAC" diagnostic
        end

val length = script_length

end
