structure clasetStep :> clasetStep =
struct

open Abbrev HolKernel boolSyntax

type node = clasetGoal.node
type goalpos = int

datatype step_kind =
    Assumption of int
  | Contradiction of int * int
  | ModusPonens of {implication : int, antecedent : int}
  | RuleApplication of {elim : bool, theorem : thm}
  | Disch
  | Gen
  | HypSubst
  | Wrapper

datatype step_record =
  StepRecord of
    {kind : step_kind,
     target : goalpos,
     consumed : int option,
     eigenvariables : string list,
     validation : validation}

type step = node * goalpos -> (step_record * node) seq.seq

fun kind_of (StepRecord {kind, ...}) = kind
fun target_of (StepRecord {target, ...}) = target
fun consumed_of (StepRecord {consumed, ...}) = consumed
fun eigenvariables_of (StepRecord {eigenvariables, ...}) = eigenvariables
fun validation_of (StepRecord {validation, ...}) = validation

val classical_trace = ref 0
val _ = Feedback.register_trace ("classical", classical_trace, 7)

fun trace level message =
  if level <= !classical_trace then
    Feedback.HOL_MESG ("Classical reasoner: " ^ message)
  else ()

val normalize_conv =
  Conv.QCONV
    (Conv.REDEPTH_CONV
      (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV)))

fun normalize_term store tm = clasetMeta.norm store tm

fun closing_equal store left right =
  aconv (normalize_term store left) (normalize_term store right)

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

fun assumption_thm asm target =
  let
    val normalized = normalize_thm (ASSUME asm)
  in
    if aconv (concl normalized) target then
      EQ_MP (ALPHA (concl normalized) target) normalized
    else
      raise mk_HOL_ERR "clasetStep" "assumption_thm"
        "the assumption does not close the target"
  end

fun nth1 values pos = List.nth (values, pos - 1)

fun delete_nth values pos =
  List.take (values, pos - 1) @ List.drop (values, pos)

fun position_map f values =
  let
    fun recurse _ [] = []
      | recurse pos (value :: rest) =
          (pos, f value) :: recurse (pos + 1) rest
  in
    recurse 1 values
  end

fun goal_equal ((asl1, w1), (asl2, w2)) =
  boolSyntax.goal_eq (asl1, w1) (asl2, w2)

fun goals_equal (left, right) =
  ListPair.allEq goal_equal (left, right)

fun member_aconv tm = List.exists (fn old => aconv tm old)

fun new_free_names (asl, w) goals =
  let
    val old_frees = free_varsl (w :: asl)
    val new_frees =
      free_varsl
        (List.concat
          (map (fn (child_asl, child_w) => child_w :: child_asl) goals))
    val introduced =
      List.filter (fn variable => not (member_aconv variable old_frees))
        new_frees
  in
    map (fst o dest_var) introduced
  end

fun distinct_strings values =
  let
    fun recurse _ [] = []
      | recurse seen (value :: rest) =
          if List.exists (fn old => old = value) seen then
            recurse seen rest
          else value :: recurse (value :: seen) rest
  in
    recurse [] values
  end

datatype direct =
  Direct of
    {kind : step_kind,
     consumed : int option,
     eigenvariables : string list,
     result : goal list * validation,
     store : clasetMeta.store}

fun direct_result (Direct {result, ...}) = result
fun direct_store (Direct {store, ...}) = store
fun direct_kind (Direct {kind, ...}) = kind
fun direct_consumed (Direct {consumed, ...}) = consumed
fun direct_eigens (Direct {eigenvariables, ...}) = eigenvariables

fun tactic_direct kind consumed node pos tactic =
  let
    val rendered = clasetGoal.render node pos
    val result as (goals, _) = tactic rendered
    val eigens = new_free_names rendered goals
  in
    SOME
      (Direct
        {kind = kind, consumed = consumed,
         eigenvariables = eigens, result = result,
         store = clasetGoal.store node})
  end
  handle HOL_ERR _ => NONE

fun first_nonempty [] _ = seq.empty
  | first_nonempty (step :: rest) input =
      seq.delay
        (fn () =>
          case seq.cases (step input) of
              NONE => first_nonempty rest input
            | SOME (value, tail) => seq.cons value tail)

fun list_seq thunk = seq.delay (fn () => seq.fromList (thunk ()))

fun assumption_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos
        val store = clasetGoal.store node
        fun closes (asm_pos, asm) = closing_equal store asm w
        fun result (asm_pos, asm) =
          let
            fun validation [] =
                  assumption_thm asm (normalize_term store w)
              | validation _ =
                  raise mk_HOL_ERR "clasetStep" "assumption_results"
                    "assumption validation received child theorems"
          in
            Direct
              {kind = Assumption asm_pos,
               consumed = SOME asm_pos,
               eigenvariables = [], result = ([], validation),
               store = store}
          end
      in
        map result (List.filter closes (position_map (fn x => x) asl))
      end)

fun contradiction_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos
        val store = clasetGoal.store node
        val positioned = position_map (fn x => x) asl

        fun negatives [] = []
          | negatives ((neg_pos, neg_tm) :: rest) =
              if is_neg (normalize_term store neg_tm) then
                let
                  val normalized_neg = normalize_term store neg_tm
                  val positive = dest_neg normalized_neg
                  fun matches (_, tm) = closing_equal store tm positive
                  fun make (pos_pos, pos_tm) =
                    let
                      fun validation [] =
                            let
                              val nthm = assumption_thm neg_tm normalized_neg
                              val pthm = assumption_thm pos_tm positive
                              val false_thm = MP (NOT_ELIM nthm) pthm
                            in
                              Drule.CONTR
                                (normalize_term store w) false_thm
                            end
                        | validation _ =
                            raise mk_HOL_ERR "clasetStep"
                              "contradiction_results"
                              "contradiction validation has children"
                    in
                      Direct
                        {kind = Contradiction (neg_pos, pos_pos),
                         consumed = SOME neg_pos, eigenvariables = [],
                         result = ([], validation), store = store}
                    end
                in
                  map make (List.filter matches positioned) @ negatives rest
                end
              else negatives rest
      in
        negatives positioned
      end)

fun assume_or_contradiction input =
  first_nonempty [assumption_results, contradiction_results] input

fun mp_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos
        val store = clasetGoal.store node
        val positioned = position_map (fn x => x) asl

        fun implications [] = []
          | implications ((imp_pos, imp_tm) :: rest) =
              let
                val normalized_imp = normalize_term store imp_tm
              in
                case total dest_imp_only normalized_imp of
                    NONE => implications rest
                  | SOME (antecedent, consequent) =>
                      let
                        fun matches (_, tm) =
                          closing_equal store tm antecedent
                        fun make (ante_pos, ante_tm) =
                          let
                            val child_asl =
                              consequent :: delete_nth asl imp_pos
                            val child = (child_asl, normalize_term store w)
                            fun validation [child_thm] =
                                  let
                                    val ithm =
                                      assumption_thm imp_tm normalized_imp
                                    val athm =
                                      assumption_thm ante_tm antecedent
                                    val consequent_thm = MP ithm athm
                                    val result =
                                      Drule.PROVE_HYP
                                        consequent_thm child_thm
                                  in
                                    EQ_MP
                                      (ALPHA (concl result)
                                        (normalize_term store w))
                                      result
                                  end
                              | validation _ =
                                  raise mk_HOL_ERR "clasetStep" "mp_results"
                                    "modus ponens validation arity"
                          in
                            Direct
                              {kind =
                                 ModusPonens
                                   {implication = imp_pos,
                                    antecedent = ante_pos},
                               consumed = SOME imp_pos,
                               eigenvariables = [],
                               result = ([child], validation),
                               store = store}
                          end
                      in
                        map make (List.filter matches positioned) @
                        implications rest
                      end
              end
      in
        implications positioned
      end)

fun eq_mp_results input =
  first_nonempty [contradiction_results, mp_results] input

fun tag_equal
  ({weight = weight1, index = index1} : clasetLib.tag,
   {weight = weight2, index = index2} : clasetLib.tag) =
  weight1 = weight2 andalso index1 = index2

fun dedup_tagged [] = []
  | dedup_tagged (entry :: rest) =
      let
        fun drop_same [] = []
          | drop_same (next :: tail) =
              if tag_equal (#1 entry, #1 next) then drop_same tail
              else next :: tail
      in
        entry :: dedup_tagged (drop_same rest)
      end

fun candidates part (asl, w) =
  let
    val intros = clasetLib.match_intro_candidates part w
    val elims =
      List.concat (map (clasetLib.match_elim_candidates part) asl)
  in
    dedup_tagged (clasetRules.candidate_order (intros @ elims))
  end

fun type_variables th =
  HOLset.listItems
    (HOLset.fromList Type.compare
      (List.concat (map type_vars_in_term (concl th :: hyp th))))

fun freshen_rule node pos is_elim theorem =
  let
    val store0 = clasetGoal.store node
    val params = #params (clasetGoal.goal_at node pos)
    val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
    val form = clasetRules.canonical_form_of kind theorem
    val canonical = #thm form

    fun add_type (ty, (substitution, metas, store)) =
      let val (meta, store') = clasetMeta.new_tymeta store
      in
        ({redex = ty, residue = meta} :: substitution,
         meta :: metas, store')
      end

    val (type_substitution, rev_types, store1) =
      List.foldl add_type ([], [], store0) (type_variables canonical)
    val typed = INST_TYPE type_substitution canonical
    val (variables, _) = strip_forall (concl typed)

    fun add_term (variable, (metas, store)) =
      let
        val (meta, store') =
          clasetMeta.new_meta
            {allow = params, ty = type_of variable} store
      in
        (meta :: metas, store')
      end

    val (rev_terms, store2) =
      List.foldl add_term ([], store1) variables
    val terms = List.rev rev_terms
    val core = Drule.SPECL terms typed
    val (premises, conclusion) = strip_imp_only (concl core)
  in
    {core = core, premises = premises, conclusion = conclusion,
     metas = {terms = terms, types = List.rev rev_types},
     store = store2}
  end

fun same_term_meta left right =
  is_var left andalso is_var right andalso
  fst (dest_var left) = fst (dest_var right)

fun same_type_meta left right =
  clasetMeta.is_tymeta left andalso clasetMeta.is_tymeta right andalso
  dest_vartype left = dest_vartype right

fun unresolved_in_premises store
  ({terms, types} : clasetUnify.rule_metas) premises =
  let
    val premise_metas =
      List.concat (map (clasetMeta.metas_of store) premises)
    val premise_types =
      List.concat
        (map (type_vars_in_term o normalize_term store) premises)
    fun created_term meta =
      List.exists (fn created => same_term_meta created meta) terms
    fun created_type ty =
      List.exists (fn created => same_type_meta created ty) types
  in
    List.exists created_term premise_metas orelse
    List.exists created_type premise_types
  end

fun ground_created store
  ({terms, types} : clasetUnify.rule_metas) =
  let
    fun ground_type (meta, current) =
      let val normalized = clasetMeta.norm_type current meta
      in
        if clasetMeta.is_tymeta normalized then
          (case clasetMeta.bind_ty (normalized, Type.bool) current of
               SOME next => next
             | NONE => current)
        else current
      end
    val typed_store = List.foldl ground_type store types

    fun ground_term (meta, current) =
      let val normalized = clasetMeta.walk current meta
      in
        if clasetMeta.is_meta normalized then
          let
            val arbitrary =
              mk_arb (clasetMeta.norm_type current (type_of normalized))
          in
            case clasetMeta.bind (normalized, arbitrary) current of
                SOME next => next
              | NONE => current
          end
        else current
      end
  in
    List.foldl ground_term typed_store terms
  end

fun cgoal_render store ({asl, w, ...} : clasetGoal.cgoal) =
  (map (normalize_term store) asl, normalize_term store w)

fun rule_validation normalized_rule supplied children premises target =
  let
    fun rebuild ((child, premise), child_thm) =
      let
        val {params, ...} : clasetGoal.cgoal = child
        val (bounds, body) = strip_forall premise
        val fresh = List.drop (params, length params - length bounds)
        val substitution =
          ListPair.map (fn (bound, variable) =>
            {redex = bound, residue = variable}) (bounds, fresh)
        val body' = Term.subst substitution body
        val (antecedents, _) = strip_imp_only body'
        val discharged =
          List.foldr (fn (antecedent, th) => DISCH antecedent th)
            child_thm antecedents
        val generalized = GENL fresh discharged
      in
        EQ_MP (ALPHA (concl generalized) premise) generalized
      end

    fun validate child_thms =
      if length child_thms <> length children then
        raise mk_HOL_ERR "clasetStep" "rule_validation"
          "rule validation arity"
      else
        let
          val premise_thms =
            ListPair.map rebuild
              (ListPair.zip (children, premises), child_thms)
          val result =
            Drule.LIST_MP (supplied @ premise_thms) normalized_rule
        in
          EQ_MP (ALPHA (concl result) target) result
        end
  in
    validate
  end

fun try_rule node pos (tag, (is_elim, theorem)) assumption =
  let
    val (asl, w) = clasetGoal.render node pos
    val fresh = freshen_rule node pos is_elim theorem
    val config =
      {mode = clasetUnify.Match, rule_metas = #metas fresh}
    val store1 =
      case clasetUnify.unify (#store fresh) config
        (#conclusion fresh, w)
      of
          NONE => raise Match
        | SOME store => store
    val (consumed, supplied, remaining, store2) =
      if is_elim then
        let
          val (assumption_pos, major) = valOf assumption
          val rule_major = hd (#premises fresh)
          val store =
            case clasetUnify.unify store1 config (rule_major, major) of
                NONE => raise Match
              | SOME result => result
        in
          (SOME assumption_pos, [major], tl (#premises fresh), store)
        end
      else (NONE, [], #premises fresh, store1)
    val residual_terms = remaining @ hyp (#core fresh)
    val _ =
      if unresolved_in_premises store2 (#metas fresh) residual_terms then
        (trace 1 "skipping safe rule with unfixed premise variables";
         raise Match)
      else ()
    val final_store = ground_created store2 (#metas fresh)
    val (type_substitution, term_substitution) =
      clasetMeta.collapse final_store
    val instantiated =
      Drule.INST_TY_TERM
        (term_substitution, type_substitution) (#core fresh)
    val normalized_rule0 = normalize_rule_thm instantiated
    val normalized_premises =
      map (normalize_term final_store) remaining

    fun align_hypothesis (hypothesis, current) =
      case List.find
        (fn assumption =>
          closing_equal final_store hypothesis assumption) asl
      of
          NONE => raise Match
        | SOME assumption =>
            Drule.PROVE_HYP
              (assumption_thm assumption hypothesis) current

    val normalized_rule =
      List.foldl align_hypothesis normalized_rule0
        (hyp normalized_rule0)
    val working = clasetGoal.set_store final_store node
    val (children, child_store) =
      clasetGoal.children working
        {pos = pos, premises = normalized_premises,
         consumed = consumed}
    val child_goals = map (cgoal_render child_store) children
    val supplied_thms =
      case (is_elim, assumption) of
          (true, SOME (_, major)) =>
            [assumption_thm major
              (hd
                (clasetRules.rule_premises_of clasetRules.Elim
                  normalized_rule))]
        | _ => []
    val target = normalize_term child_store w
    val validation =
      rule_validation normalized_rule supplied_thms children
        normalized_premises target
    val eigenvariables =
      distinct_strings
        (List.concat
          (map (fn ({params, ...} : clasetGoal.cgoal) =>
             map (fst o dest_var) params) children))
    val old_params =
      map (fst o dest_var) (#params (clasetGoal.goal_at node pos))
    val new_eigens =
      List.filter
        (fn name => not (List.exists (fn old => old = name) old_params))
        eigenvariables
  in
    Direct
      {kind = RuleApplication {elim = is_elim, theorem = theorem},
       consumed = consumed, eigenvariables = new_eigens,
       result = (child_goals, validation), store = child_store}
  end
  handle Match => raise Match
       | HOL_ERR _ => raise Match
       | Empty => raise Match

fun rule_results part weight_filter (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered as (asl, _) = clasetGoal.render node pos
        val tagged = List.filter (weight_filter o #1)
          (candidates part rendered)

        fun intro_application entry =
          seq.delay
            (fn () =>
              case total (fn () => try_rule node pos entry NONE) () of
                  SOME result => seq.result result
                | NONE => seq.empty)

        fun elim_applications _ [] = seq.empty
          | elim_applications entry ((assumption_pos, major) :: rest) =
              seq.delay
                (fn () =>
                  case total
                    (fn () =>
                      try_rule node pos entry
                        (SOME (assumption_pos, major))) ()
                  of
                      SOME result =>
                        seq.cons result (elim_applications entry rest)
                    | NONE => elim_applications entry rest)

        fun applications (entry as (_, (false, _))) =
              intro_application entry
          | applications (entry as (_, (true, _))) =
              elim_applications entry (position_map (fn x => x) asl)

        fun entries [] = seq.empty
          | entries (entry :: rest) =
              seq.delay
                (fn () =>
                  case seq.cases (applications entry) of
                      NONE => entries rest
                    | SOME (result, tail) =>
                        seq.cons result (seq.append tail (entries rest)))
      in
        entries tagged
      end)

fun all_weights _ = true
fun weight_is expected ({weight, ...} : clasetLib.tag) = weight = expected

fun builtin_results (node, pos) =
  let
    val (_, w) = clasetGoal.render node pos
  in
    if is_imp_only w then
      (case tactic_direct Disch NONE node pos Tactic.DISCH_TAC of
           SOME result => seq.result result
         | NONE => seq.empty)
    else if is_forall w then
      (case tactic_direct Gen NONE node pos Tactic.GEN_TAC of
           SOME result => seq.result result
         | NONE => seq.empty)
    else seq.empty
  end

fun has_metavariables node pos =
  let
    val (asl, w) = clasetGoal.render node pos
  in
    List.exists clasetMeta.is_meta (free_varsl (w :: asl)) orelse
    List.exists clasetMeta.is_tymeta
      (List.concat (map type_vars_in_term (w :: asl)))
  end

(* TASK_10 replaces this empty engine-internal branch. *)
fun internal_hyp_subst_results _ = seq.empty

fun materialized_hyp_subst_results (node, pos) =
  let
    val {hyp_subst_tac, ...} = clasetLib.claset_config
    val repeated =
      Tactical.THEN
        (hyp_subst_tac, Tactical.REPEAT hyp_subst_tac)
  in
    case tactic_direct HypSubst NONE node pos repeated of
        SOME result => seq.result result
      | NONE => seq.empty
  end

fun hyp_subst_results (input as (node, pos)) =
  if has_metavariables node pos then internal_hyp_subst_results input
  else materialized_hyp_subst_results input

fun safe_cascade cs input =
  first_nonempty
    [assumption_results,
     eq_mp_results,
     rule_results (clasetLib.safe0_part cs) all_weights,
     builtin_results,
     hyp_subst_results,
     rule_results (clasetLib.safep_part cs) all_weights]
    input

fun close_plain goal =
  let
    val node = clasetGoal.from_goal goal
  in
    case seq.cases (assume_or_contradiction (node, 1)) of
        NONE => NONE
      | SOME (result, _) => SOME result
  end

fun close_one_child direct =
  let
    val Direct
      {kind, consumed, eigenvariables, result = (goals, validation),
       store} = direct
  in
    case goals of
        [left, right] =>
          (case close_plain left of
               SOME (Direct {result = ([], close_validation), ...}) =>
                 let
                   fun combined [right_thm] =
                         validation [close_validation [], right_thm]
                     | combined _ =
                         raise mk_HOL_ERR "clasetStep" "close_one_child"
                           "left-close validation arity"
                 in
                   SOME
                     (Direct
                       {kind = kind, consumed = consumed,
                        eigenvariables = eigenvariables,
                        result = ([right], combined), store = store})
                 end
             | _ =>
                 (case close_plain right of
                      SOME
                        (Direct
                          {result = ([], close_validation), ...}) =>
                        let
                          fun combined [left_thm] =
                                validation [left_thm, close_validation []]
                            | combined _ =
                                raise mk_HOL_ERR "clasetStep"
                                  "close_one_child"
                                  "right-close validation arity"
                        in
                          SOME
                            (Direct
                              {kind = kind, consumed = consumed,
                               eigenvariables = eigenvariables,
                               result = ([left], combined), store = store})
                        end
                    | _ => NONE))
      | _ => NONE
  end

fun bimatch2_results part input =
  seq.mapPartial close_one_child
    (rule_results part (weight_is 2) input)

fun clarify_cascade cs input =
  first_nonempty
    [assume_or_contradiction,
     rule_results (clasetLib.safe0_part cs) all_weights,
     builtin_results,
     hyp_subst_results,
     rule_results (clasetLib.safep_part cs) (weight_is 1),
     bimatch2_results (clasetLib.safep_part cs)]
    input

fun take_direct goals directs =
  let
    fun recurse _ [] = NONE
      | recurse previous (direct :: rest) =
          if goals_equal (#1 (direct_result direct), goals) then
            SOME (direct, List.rev previous @ rest)
          else recurse (direct :: previous) rest
  in
    recurse [] directs
  end

fun make_record target validation direct =
  StepRecord
    {kind = direct_kind direct,
     target = target,
     consumed = direct_consumed direct,
     eigenvariables = direct_eigens direct,
     validation = validation}

fun wrapper_direct rendered goals validation store =
  Direct
    {kind = Wrapper, consumed = NONE,
     eigenvariables = new_free_names rendered goals,
     result = (goals, validation), store = store}

fun wrapped_step cascade cs (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered = clasetGoal.render node pos
        val available = ref ([] : direct list)

        fun remember direct =
          (available := !available @ [direct]; direct_result direct)

        fun base goal =
          if goal_equal (goal, rendered) then
            seq.map remember (cascade cs (node, pos))
          else
            let
              val temporary = clasetGoal.from_goal goal
            in
              seq.map direct_result (cascade cs (temporary, 1))
            end

        val wrapped = clasetLib.app_safe_wrappers cs base rendered

        fun lift sequence =
          seq.delay
            (fn () =>
              case seq.cases sequence of
                  NONE => seq.empty
                | SOME (result as (goals, validation), rest) =>
                    let
                      val direct =
                        case take_direct goals (!available) of
                            SOME (found, remaining) =>
                              (available := remaining; found)
                          | NONE =>
                              wrapper_direct rendered goals validation
                                (clasetGoal.store node)
                      val stored =
                        clasetGoal.set_store (direct_store direct) node
                    in
                      case clasetGoal.unrender stored pos result of
                          NONE => lift rest
                        | SOME next =>
                            seq.cons
                              (make_record pos validation direct, next)
                              (lift rest)
                    end)
      in
        lift wrapped
      end)

fun safe_step cs = wrapped_step safe_cascade cs
fun clarify_step cs = wrapped_step clarify_cascade cs

end
