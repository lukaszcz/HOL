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

type created =
  {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}

val no_created : created = {terms = [], types = []}

datatype step_record =
  StepRecord of
    {kind : step_kind,
     target : goalpos,
     consumed : int option,
     created : created,
     eigenvariables : string list,
     validation : validation}

type step = node * goalpos -> (step_record * node) seq.seq

fun kind_of (StepRecord {kind, ...}) = kind
fun target_of (StepRecord {target, ...}) = target
fun consumed_of (StepRecord {consumed, ...}) = consumed
fun created_of (StepRecord {created, ...}) = created
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
     created : created,
     eigenvariables : string list,
     result : goal list * validation,
     children : clasetGoal.cgoal list option,
     store : clasetMeta.store}

fun direct_result (Direct {result, ...}) = result
fun direct_store (Direct {store, ...}) = store
fun direct_kind (Direct {kind, ...}) = kind
fun direct_consumed (Direct {consumed, ...}) = consumed
fun direct_created (Direct {created, ...}) = created
fun direct_eigens (Direct {eigenvariables, ...}) = eigenvariables
fun direct_children (Direct {children, ...}) = children

fun tactic_direct kind consumed node pos tactic =
  let
    val rendered = clasetGoal.render node pos
    val result as (goals, _) = tactic rendered
    val eigens = new_free_names rendered goals
  in
    SOME
      (Direct
        {kind = kind, consumed = consumed, created = no_created,
         eigenvariables = eigens, result = result, children = NONE,
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
               consumed = SOME asm_pos, created = no_created,
               eigenvariables = [], result = ([], validation),
               children = SOME [], store = store}
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
                         consumed = SOME neg_pos, created = no_created,
                         eigenvariables = [], result = ([], validation),
                         children = SOME [], store = store}
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
        val {params, ...} = clasetGoal.goal_at node pos

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
                            val child_w = normalize_term store w
                            val child = (child_asl, child_w)
                            val child_cgoal =
                              {params = params, asl = child_asl, w = child_w}
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
                               created = no_created, eigenvariables = [],
                               result = ([child], validation),
                               children = SOME [child_cgoal], store = store}
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

fun candidates mode part (asl, w) =
  let
    val (intro_lookup, elim_lookup) =
      case mode of
          clasetUnify.Match =>
            (clasetLib.match_intro_candidates,
             clasetLib.match_elim_candidates)
        | clasetUnify.Unify =>
            (clasetLib.unify_intro_candidates,
             clasetLib.unify_elim_candidates)
    val intros = intro_lookup part w
    val elims = List.concat (map (elim_lookup part) asl)
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
        if same_type_meta meta normalized then
          (case clasetMeta.bind_ty (meta, Type.bool) current of
               SOME next => next
             | NONE => current)
        else current
      end
    val typed_store = List.foldl ground_type store types

    fun ground_term (meta, current) =
      let val normalized = clasetMeta.walk current meta
      in
        if same_term_meta meta normalized then
          let
            val arbitrary =
              mk_arb (clasetMeta.norm_type current (type_of meta))
          in
            case clasetMeta.bind (meta, arbitrary) current of
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

fun try_rule mode node pos (tag, (is_elim, theorem)) assumption =
  let
    val (asl, w) = clasetGoal.render node pos
    val fresh = freshen_rule node pos is_elim theorem
    val config = {mode = mode, rule_metas = #metas fresh}
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
      case mode of
          clasetUnify.Match =>
            if unresolved_in_premises store2 (#metas fresh) residual_terms
            then
              (trace 1 "skipping safe rule with unfixed premise variables";
               raise Match)
            else ()
        | clasetUnify.Unify => ()
    val final_store =
      case mode of
          clasetUnify.Match => ground_created store2 (#metas fresh)
        | clasetUnify.Unify => store2
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
    val created = #metas fresh
  in
    Direct
      {kind = RuleApplication {elim = is_elim, theorem = theorem},
       consumed = consumed, created = created,
       eigenvariables = new_eigens,
       result = (child_goals, validation), children = SOME children,
       store = child_store}
  end
  handle Match => raise Match
       | HOL_ERR _ => raise Match
       | Empty => raise Match

fun rule_results mode part weight_filter (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered as (asl, _) = clasetGoal.render node pos
        val tagged = List.filter (weight_filter o #1)
          (candidates mode part rendered)

        fun intro_application entry =
          seq.delay
            (fn () =>
              case total (fn () => try_rule mode node pos entry NONE) () of
                  SOME result => seq.result result
                | NONE => seq.empty)

        fun elim_applications _ [] = seq.empty
          | elim_applications entry ((assumption_pos, major) :: rest) =
              seq.delay
                (fn () =>
                  case total
                    (fn () =>
                      try_rule mode node pos entry
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
    val rendered as (_, w) = clasetGoal.render node pos

    fun make kind tactic =
      case total tactic rendered of
          NONE => seq.empty
        | SOME (result as (goals, _)) =>
            let
              val {params, ...} = clasetGoal.goal_at node pos
              val input_frees =
                free_varsl (params @ (#2 rendered :: #1 rendered))

              fun is_new variable =
                not (List.exists (fn old => aconv old variable)
                  input_frees)
              fun lift_child (child_asl, child_w) =
                let
                  val fresh =
                    List.filter is_new
                      (free_varsl (child_w :: child_asl))
                in
                  ({params = params @ fresh,
                    asl = child_asl, w = child_w}, fresh)
                end

              val lifted = map lift_child goals
              val children = map #1 lifted
              val new_params = List.concat (map #2 lifted)
              fun register (param, store) =
                case clasetMeta.register_eigen param store of
                    SOME next => next
                  | NONE => store
              val store =
                List.foldl register (clasetGoal.store node) new_params
            in
              seq.result
                (Direct
                  {kind = kind, consumed = NONE, created = no_created,
                   eigenvariables = map (fst o dest_var) new_params,
                   result = result, children = SOME children,
                   store = store})
            end
  in
    if is_imp_only w then make Disch Tactic.DISCH_TAC
    else if is_forall w then make Gen Tactic.GEN_TAC
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

fun reflexive_equality tm =
  case total dest_eq tm of
      SOME (left, right) => if aconv left right then SOME left else NONE
    | NONE => NONE

fun subst_orientation equality =
  case total dest_eq equality of
      NONE => NONE
    | SOME (left, right) =>
        if is_var left andalso not (clasetMeta.is_meta left) andalso
           not (free_in left right)
        then SOME (left, right, ASSUME equality)
        else if is_var right andalso not (clasetMeta.is_meta right) andalso
                not (free_in right left)
        then SOME (right, left, SYM (ASSUME equality))
        else NONE

fun internal_hyp_subst_results (node, pos) =
  let
    val rendered = clasetGoal.render node pos
    val initial_params = #params (clasetGoal.goal_at node pos)
    fun find_candidate _ [] = NONE
      | find_candidate asm_pos (equality :: rest) =
          (case reflexive_equality equality of
               SOME _ => SOME (asm_pos, equality, NONE)
             | NONE =>
                 (case subst_orientation equality of
                      SOME orientation =>
                        SOME (asm_pos, equality, SOME orientation)
                    | NONE => find_candidate (asm_pos + 1) rest))

    fun once (goal as (asl, w)) =
      case find_candidate 1 asl of
          NONE => raise mk_HOL_ERR "clasetStep" "internal_hyp_subst"
                    "no substitutable equality"
        | SOME (asm_pos, equality, NONE) =>
            let
              val reflexive = valOf (reflexive_equality equality)
              val child = (delete_nth asl asm_pos, w)
              fun validation [child_thm] =
                    Drule.PROVE_HYP (REFL reflexive) child_thm
                | validation _ =
                    raise mk_HOL_ERR "clasetStep" "internal_hyp_subst"
                      "reflexive deletion validation arity"
            in
              ([child], validation)
            end
        | SOME (asm_pos, _, SOME (_, _, equality_thm)) =>
            Tactic.SUBST_ALL_TAC equality_thm
              (delete_nth asl asm_pos, w)

    val repeated = Tactical.THEN (once, Tactical.REPEAT once)
  in
    case total repeated rendered of
        NONE => seq.empty
      | SOME (result as ([(child_asl, child_w)], _)) =>
          let
            val child =
              {params = initial_params, asl = child_asl, w = child_w}
          in
            seq.result
              (Direct
                {kind = HypSubst, consumed = NONE,
                 created = no_created, eigenvariables = [],
                 result = result, children = SOME [child],
                 store = clasetGoal.store node})
          end
      | SOME _ => seq.empty
  end

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
     rule_results clasetUnify.Match
       (clasetLib.safe0_part cs) all_weights,
     builtin_results,
     hyp_subst_results,
     rule_results clasetUnify.Match
       (clasetLib.safep_part cs) all_weights]
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
      {kind, consumed, created, eigenvariables,
       result = (goals, validation), children, store} = direct
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
                       {kind = kind, consumed = consumed, created = created,
                        eigenvariables = eigenvariables,
                        result = ([right], combined),
                        children = Option.map tl children, store = store})
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
                               created = created,
                               eigenvariables = eigenvariables,
                               result = ([left], combined),
                               children =
                                 Option.map (fn values => [hd values])
                                   children,
                               store = store})
                        end
                    | _ => NONE))
      | _ => NONE
  end

fun bimatch2_results part input =
  seq.mapPartial close_one_child
    (rule_results clasetUnify.Match part (weight_is 2) input)

fun clarify_cascade cs input =
  first_nonempty
    [assume_or_contradiction,
     rule_results clasetUnify.Match
       (clasetLib.safe0_part cs) all_weights,
     builtin_results,
     hyp_subst_results,
     rule_results clasetUnify.Match
       (clasetLib.safep_part cs) (weight_is 1),
     bimatch2_results (clasetLib.safep_part cs)]
    input

fun append_results left right input =
  seq.append (left input) (seq.delay (fn () => right input))

fun append_many [] _ = seq.empty
  | append_many [operation] input = operation input
  | append_many (operation :: rest) input =
      seq.append (operation input)
        (seq.delay (fn () => append_many rest input))

val empty_rule_metas : clasetUnify.rule_metas = {terms = [], types = []}
val unify_config =
  {mode = clasetUnify.Unify, rule_metas = empty_rule_metas}

fun unifying_assumption_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos

        fun attempt (asm_pos, asm) =
          case clasetUnify.unify (clasetGoal.store node) unify_config
            (w, asm)
          of
              NONE => NONE
            | SOME store =>
                let
                  fun validation [] =
                        assumption_thm (normalize_term store asm)
                          (normalize_term store w)
                    | validation _ =
                        raise mk_HOL_ERR "clasetStep"
                          "unifying_assumption_results"
                          "assumption validation has children"
                in
                  SOME
                    (Direct
                      {kind = Assumption asm_pos,
                       consumed = SOME asm_pos, created = no_created,
                       eigenvariables = [], result = ([], validation),
                       children = SOME [], store = store})
                end
      in
        List.mapPartial attempt (position_map (fn value => value) asl)
      end)

fun unifying_contradiction_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos
        val params = #params (clasetGoal.goal_at node pos)
        val positioned = position_map (fn value => value) asl

        fun major_alternatives (major_pos, major) =
          let
            val (positive, store1) =
              clasetMeta.new_meta {allow = params, ty = Type.bool}
                (clasetGoal.store node)
            val (result, fresh_store) =
              clasetMeta.new_meta {allow = params, ty = Type.bool} store1
            val created = {terms = [positive, result], types = []}
            val config =
              {mode = clasetUnify.Unify, rule_metas = created}
          in
            case clasetUnify.unify fresh_store config (result, w) of
                NONE => []
              | SOME result_store =>
                  case clasetUnify.unify result_store config
                    (mk_neg positive, major)
                  of
                      NONE => []
                    | SOME major_store =>
                  let
                    val remaining =
                      List.filter (fn (other_pos, _) =>
                        other_pos <> major_pos) positioned
                    val exact =
                      List.find (fn (_, candidate) =>
                        closing_equal major_store positive candidate)
                        remaining
                    val stores =
                      case exact of
                          SOME (positive_pos, candidate) =>
                            [(positive_pos, candidate, major_store)]
                        | NONE =>
                            List.mapPartial
                              (fn (positive_pos, candidate) =>
                                Option.map
                                  (fn store =>
                                    (positive_pos, candidate, store))
                                  (clasetUnify.unify major_store
                                    unify_config (positive, candidate)))
                              remaining

                    fun make (positive_pos, candidate, store) =
                      let
                        fun validation [] =
                              let
                                val normalized_major =
                                  normalize_term store major
                                val normalized_positive =
                                  normalize_term store positive
                                val negative_thm =
                                  assumption_thm major normalized_major
                                val positive_thm =
                                  assumption_thm candidate
                                    normalized_positive
                                val false_thm =
                                  MP (NOT_ELIM negative_thm) positive_thm
                              in
                                Drule.CONTR (normalize_term store w)
                                  false_thm
                              end
                          | validation _ =
                              raise mk_HOL_ERR "clasetStep"
                                "unifying_contradiction_results"
                                "contradiction validation has children"
                      in
                        Direct
                          {kind =
                             Contradiction (major_pos, positive_pos),
                           consumed = SOME major_pos, created = created,
                           eigenvariables = [],
                           result = ([], validation),
                           children = SOME [], store = store}
                      end
                  in
                    map make stores
                  end
          end
      in
        List.concat (map major_alternatives positioned)
      end)

fun inst0_cascade cs input =
  append_many
    [unifying_assumption_results,
     unifying_contradiction_results,
     rule_results clasetUnify.Unify
       (clasetLib.safe0_part cs) all_weights]
    input

fun instp_cascade cs =
  rule_results clasetUnify.Unify (clasetLib.safep_part cs) all_weights

fun inst_cascade cs input =
  append_results (inst0_cascade cs) (instp_cascade cs) input

fun unsafe_cascade cs =
  rule_results clasetUnify.Unify (clasetLib.unsafe_part cs) all_weights

fun dup_cascade cs =
  rule_results clasetUnify.Unify (clasetLib.dup_part cs) all_weights

fun depth_cascade part cs input =
  append_results (instp_cascade cs)
    (rule_results clasetUnify.Unify part all_weights) input

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
     created = direct_created direct,
     eigenvariables = direct_eigens direct,
     validation = validation}

fun wrapper_direct rendered goals validation store =
  Direct
    {kind = Wrapper, consumed = NONE, created = no_created,
     eigenvariables = new_free_names rendered goals,
     result = (goals, validation), children = NONE, store = store}

fun wrapped_step apply_wrappers cascade cs (node, pos) =
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

        val wrapped = apply_wrappers cs base rendered

        fun lift sequence =
          seq.delay
            (fn () =>
              case seq.cases sequence of
                  NONE => seq.empty
                | SOME (result as (goals, validation), rest) =>
                    let
                      val (direct, exact) =
                        case take_direct goals (!available) of
                            SOME (found, remaining) =>
                              (available := remaining; (found, true))
                          | NONE =>
                              (wrapper_direct rendered goals validation
                                 (clasetGoal.store node), false)
                      val stored =
                        clasetGoal.set_store (direct_store direct) node
                      val lifted =
                        if exact then
                          case clasetGoal.unrender stored pos result of
                              SOME next => SOME next
                            | NONE =>
                                Option.map
                                  (fn children =>
                                    clasetGoal.replace_goal stored
                                      {pos = pos, children = children,
                                       store = direct_store direct})
                                  (direct_children direct)
                        else clasetGoal.unrender stored pos result
                    in
                      case lifted of
                          NONE => lift rest
                        | SOME next =>
                            seq.cons
                              (make_record pos validation direct, next)
                              (lift rest)
                    end)
      in
        lift wrapped
      end)

fun safe_step cs =
  wrapped_step clasetLib.app_safe_wrappers safe_cascade cs

fun clarify_step cs =
  wrapped_step clasetLib.app_safe_wrappers clarify_cascade cs

fun inst0_step cs =
  wrapped_step (fn _ => fn tactic => tactic) inst0_cascade cs

fun instp_step cs =
  wrapped_step (fn _ => fn tactic => tactic) instp_cascade cs

fun inst_step cs =
  wrapped_step (fn _ => fn tactic => tactic) inst_cascade cs

fun unsafe_step cs =
  wrapped_step (fn _ => fn tactic => tactic) unsafe_cascade cs

fun dup_step cs =
  wrapped_step (fn _ => fn tactic => tactic) dup_cascade cs

fun first_result sequence =
  case seq.cases sequence of
      NONE => NONE
    | SOME (result, _) => SOME result

fun safe_steps_at cs node pos =
  let
    val initial_count = length (clasetGoal.goals node)

    fun repeat last current =
      if length (clasetGoal.goals current) < initial_count then
        (last, current)
      else
        case first_result (safe_step cs (current, pos)) of
            NONE => (last, current)
          | SOME (record, next) => repeat record next
  in
    case first_result (safe_step cs (node, pos)) of
        NONE => NONE
      | SOME (record, next) => SOME (repeat record next)
  end

fun safe_saturate_all cs node =
  let
    fun first_goal pos current =
      if pos > length (clasetGoal.goals current) then NONE
      else
        case safe_steps_at cs current pos of
            NONE => first_goal (pos + 1) current
          | result => result

    fun saturate last current =
      case first_goal 1 current of
          NONE => Option.map (fn record => (record, current)) last
        | SOME (record, next) => saturate (SOME record) next
  in
    saturate NONE node
  end

fun unsafe_rung fast cs input =
  if fast then first_nonempty [inst_cascade cs, unsafe_cascade cs] input
  else append_results (inst_cascade cs) (unsafe_cascade cs) input

fun general_step fast cs (input as (node, _)) =
  case safe_saturate_all cs node of
      SOME result => seq.result result
    | NONE =>
        wrapped_step clasetLib.app_unsafe_wrappers
          (unsafe_rung fast) cs input

fun step cs = general_step true cs
fun slow_step cs = general_step false cs

fun depth_step cs part bound (node, pos) =
  let
    fun child_count old_node new_node =
      length (clasetGoal.goals new_node) -
      length (clasetGoal.goals old_node) + 1

    fun solve_many _ 0 result = seq.result result
      | solve_many m count (record, current) =
          seq.bind (solve_one m (current, pos))
            (solve_many m (count - 1))

    and solve_one m (current, target) =
      case safe_steps_at cs current target of
          SOME (result as (_, safe_node)) =>
            solve_many m (child_count current safe_node) result
        | NONE =>
            let
              val closers = inst0_step cs (current, target)
              val branching =
                if m <= 0 then seq.empty
                else
                  seq.bind
                    (wrapped_step clasetLib.app_unsafe_wrappers
                      (depth_cascade part) cs (current, target))
                    (fn result as (_, next) =>
                      solve_many (m - 1)
                        (child_count current next) result)
            in
              seq.append closers branching
            end
  in
    if bound < 0 then seq.empty else solve_one bound (node, pos)
  end

end
