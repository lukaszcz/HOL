structure clasetStep :> clasetStep =
struct

open Abbrev HolKernel boolSyntax

type node = clasetGoal.node
type goalpos = int

datatype rule_variant = datatype clasetReplay.rule_variant
datatype step_kind = datatype clasetReplay.step_kind

type created = clasetReplay.created
val no_created : created = {terms = [], types = []}

type step_record = clasetReplay.step_record
type step = node * goalpos -> (step_record * node) seq.seq

val kind_of = clasetReplay.kind_of
val target_of = clasetReplay.target_of
val consumed_of = clasetReplay.consumed_of
val created_of = clasetReplay.created_of
val eigenvariables_of = clasetReplay.eigenvariables_of
val validation_of = clasetReplay.validation_of

fun trace level message =
  if level <= Feedback.current_trace "classical" then
    Feedback.HOL_MESG ("Classical reasoner: " ^ message)
  else ()

val normalize_conv = clasetNorm.normalize_conv

fun normalize_term store tm = clasetMeta.norm store tm

fun closing_equal store left right =
  aconv (normalize_term store left) (normalize_term store right)

val normalize_thm = clasetNorm.normalize_thm
val normalize_rule_thm = clasetNorm.normalize_rule_thm

fun split_imp_prefix function_name arity tm =
  clasetNorm.split_imp_prefix ("clasetStep", function_name) arity tm

val normalize_assumption_thm = clasetNorm.normalize_assumption_thm
val normalize_assumption = clasetNorm.normalize_assumption

fun assumption_thm asm target =
  let
    val (normalized, theorem) = normalize_assumption asm
  in
    if aconv normalized target then
      EQ_MP (ALPHA normalized target) theorem
    else
      raise mk_HOL_ERR "clasetStep" "assumption_thm"
        "the assumption does not close the target"
  end

fun supplied_major_thm store major target =
  let
    val (type_substitution, term_substitution) =
      clasetMeta.collapse store
    val instantiated =
      Drule.INST_TY_TERM
        (term_substitution, type_substitution) (ASSUME major)
    val (normalized, theorem) =
      normalize_assumption_thm instantiated
  in
    if aconv normalized target then
      EQ_MP (ALPHA normalized target) theorem
    else
      let
        val major' = normalize_term store major
        val (normalized', theorem') = normalize_assumption major'
      in
        if aconv normalized' target then
          EQ_MP (ALPHA normalized' target) theorem'
        else
          raise mk_HOL_ERR "clasetStep" "supplied_major_thm"
            "the selected assumption misses the instantiated major premise"
      end
  end

val nth1 = clasetNorm.nth1 ("clasetStep", "nth1")
val delete_nth = clasetNorm.delete_nth ("clasetStep", "delete_nth")

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

fun new_free_names_by_goal (asl, w) goals =
  let
    val old_frees = free_varsl (w :: asl)
    fun names (child_asl, child_w) =
      map (fst o dest_var)
        (List.filter
          (fn variable => not (tmem variable old_frees))
          (free_varsl (child_w :: child_asl)))
  in
    map names goals
  end

datatype direct =
  Direct of
    {kind : step_kind,
     consumed : int option,
     created : created,
     eigenvariables : string list list,
     result : goal list * validation,
     children : clasetGoal.cgoal list option,
     action : clasetReplay.replay_action,
     closed : direct option list,
     store : clasetMeta.store}

fun direct_result (Direct {result, ...}) = result
fun direct_store (Direct {store, ...}) = store
fun direct_kind (Direct {kind, ...}) = kind
fun direct_consumed (Direct {consumed, ...}) = consumed
fun direct_created (Direct {created, ...}) = created
fun direct_eigens (Direct {eigenvariables, ...}) = eigenvariables
fun direct_children (Direct {children, ...}) = children
fun direct_action (Direct {action, ...}) = action
fun direct_closed (Direct {closed, ...}) = closed

fun tactic_direct kind consumed node pos tactic =
  let
    val rendered = clasetGoal.render node pos
    val result as (goals, _) = tactic rendered
    val eigens = new_free_names_by_goal rendered goals
  in
    SOME
      (Direct
        {kind = kind, consumed = consumed, created = no_created,
         eigenvariables = eigens, result = result, children = NONE,
         action = clasetReplay.fixed_action result,
         closed = map (fn _ => NONE) goals,
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

(* [seq.take] materializes a list; a bound on a search alternative must
   itself stay lazy, so that truncating costs nothing until pulled. *)
fun take_seq count sequence =
  if count <= 0 then seq.empty
  else
    seq.delay
      (fn () =>
        case seq.cases sequence of
            NONE => seq.empty
          | SOME (value, rest) =>
              seq.cons value (take_seq (count - 1) rest))

fun assumption_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, w) = clasetGoal.render node pos
        val store = clasetGoal.store node
        val normalized_w = normalize_term store w
        fun closes (asm_pos, asm) =
          aconv (normalize_term store asm) normalized_w
        fun result (asm_pos, asm) =
          let
            fun validation [] =
                  assumption_thm asm normalized_w
              | validation _ =
                  raise mk_HOL_ERR "clasetStep" "assumption_results"
                    "assumption validation received child theorems"
          in
            Direct
              {kind = Assumption asm_pos,
               consumed = SOME asm_pos, created = no_created,
               eigenvariables = [], result = ([], validation),
               children = SOME [],
               action = clasetReplay.assumption_action asm_pos,
               closed = [], store = store}
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
        val normalized_w = normalize_term store w
        val positioned = position_map (fn x => x) asl

        fun negatives [] = []
          | negatives ((neg_pos, neg_tm) :: rest) =
            let
              val normalized_neg = normalize_term store neg_tm
            in
              if is_neg normalized_neg then
                let
                  val positive = dest_neg normalized_neg
                  val normalized_positive = normalize_term store positive
                  fun matches (_, tm) =
                    aconv (normalize_term store tm) normalized_positive
                  fun make (pos_pos, pos_tm) =
                    let
                      fun validation [] =
                            let
                              val nthm = assumption_thm neg_tm normalized_neg
                              val pthm = assumption_thm pos_tm positive
                              val false_thm = MP (NOT_ELIM nthm) pthm
                            in
                              Drule.CONTR normalized_w false_thm
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
                         children = SOME [],
                         action =
                           clasetReplay.contradiction_action
                             (neg_pos, pos_pos),
                         closed = [], store = store}
                    end
                in
                  map make (List.filter matches positioned) @ negatives rest
                end
              else negatives rest
            end
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
        val normalized_w = normalize_term store w
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
                        val normalized_antecedent =
                          normalize_term store antecedent
                        fun matches (_, tm) =
                          aconv (normalize_term store tm)
                            normalized_antecedent
                        fun make (ante_pos, ante_tm) =
                          let
                            val child_asl =
                              consequent :: delete_nth asl imp_pos
                            val child_w = normalized_w
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
                                      (ALPHA (concl result) normalized_w)
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
                               created = no_created,
                               eigenvariables = [[]],
                               result = ([child], validation),
                               children = SOME [child_cgoal],
                               action =
                                 clasetReplay.mp_action
                                   {implication = imp_pos,
                                    antecedent = ante_pos},
                               closed = [NONE], store = store}
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

(* Freshening starts from the canonical form.  Callers that apply one rule
   many times canonicalize once and reuse the result here. *)
fun freshen_canonical node pos (form : clasetRules.canonical) =
  let
    val store0 = clasetGoal.store node
    val params = #params (clasetGoal.goal_at node pos)
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

fun freshen_rule node pos kind theorem =
  freshen_canonical node pos (clasetRules.canonical_form_of kind theorem)

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

fun exact_rule_validation normalized_rule supplied rebuilds target =
  let
    fun validate child_thms =
      if length child_thms <> length rebuilds then
        raise mk_HOL_ERR "clasetStep" "exact_rule_validation"
          "rule validation arity"
      else
        let
          val premise_thms =
            ListPair.map
              (fn (data, theorem) =>
                clasetReplay.rebuild_exact_prefix data theorem)
              (rebuilds, child_thms)
          val result =
            Drule.LIST_MP (supplied @ premise_thms) normalized_rule
        in
          EQ_MP (ALPHA (concl result) target) result
        end
  in
    validate
  end

fun theorem_equal left right =
  aconv (concl left) (concl right) andalso
  ListPair.allEq (fn (left_tm, right_tm) => aconv left_tm right_tm)
    (hyp left, hyp right)

(* The claset stores each declaration's derived forms, so this identifies
   the declaration behind an applied theorem by reading them rather than by
   deriving them again -- with real kernel inferences -- for every
   declaration it scans.  The scan also stops at the first match: replay
   runs this once per successful rule application. *)
fun rule_origin cs duplicated theorem =
  let
    fun inspect ({spec, thm = original, info, ...} : clasetLib.aesop_rule) =
      let
        val {rl = (plain, swapped), dup_rl = (duplicate, dup_swapped)} = info
        val made =
          case #kind spec of clasetRules.Dest => MakeElim | _ => Plain
      in
        if theorem_equal theorem plain andalso not duplicated then
          SOME (original, made)
        else if Option.getOpt
                  (Option.map (theorem_equal theorem) swapped, false)
                andalso not duplicated
        then SOME (original, Swapped)
        else if theorem_equal theorem duplicate then
          SOME (original, Duplicate)
        else if Option.getOpt
                  (Option.map (theorem_equal theorem) dup_swapped, false)
        then SOME (original, Duplicate)
        else if theorem_equal theorem plain then SOME (original, made)
        else NONE
      end
    fun search [] = (theorem, if duplicated then Duplicate else Plain)
      | search (rule :: rest) =
          (case inspect rule of
               SOME result => result
             | NONE => search rest)
  in
    search (clasetLib.all_rules cs)
  end

datatype prefix_policy = LegacyPrefixes | ExactBlastPrefixes

fun minor_prefixes policy is_elim premises =
  case policy of
      LegacyPrefixes => NONE
    | ExactBlastPrefixes =>
        let val minors = if is_elim then tl premises else premises
        in SOME (map clasetReplay.exact_prefix_descriptor minors) end

fun try_rule policy mode cs duplicated node pos
    (tag, (is_elim, theorem)) assumption =
  let
    val (asl, w) = clasetGoal.render node pos
    val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
    val fresh = freshen_rule node pos kind theorem
    val prefixes = minor_prefixes policy is_elim (#premises fresh)
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
    val (all_premises, _) =
      split_imp_prefix "try_rule" (length (#premises fresh))
        (concl normalized_rule)
    val normalized_premises =
      if is_elim then
        (case all_premises of
             _ :: premises => premises
           | [] =>
               raise mk_HOL_ERR "clasetStep" "try_rule"
                 "an elimination rule has no major premise")
      else all_premises
    val working = clasetGoal.set_store final_store node
    val (children, child_store, rebuilds) =
      case prefixes of
          NONE =>
            let
              val (children, child_store) =
                clasetGoal.children working
                  {pos = pos, premises = normalized_premises,
                   consumed = consumed}
            in
              (children, child_store, NONE)
            end
        | SOME descriptors =>
            let
              val (children, child_store, data) =
                clasetGoal.exact_blast_children working
                  {pos = pos, premises = normalized_premises,
                   prefixes = descriptors, consumed = consumed}
            in
              (children, child_store, SOME data)
            end
    val child_goals = map (cgoal_render child_store) children
    val supplied_thms =
      case (is_elim, assumption) of
          (true, SOME (_, major)) =>
            [supplied_major_thm final_store major (hd all_premises)]
        | _ => []
    val target = normalize_term child_store w
    val validation =
      case rebuilds of
          NONE =>
            rule_validation normalized_rule supplied_thms children
              normalized_premises target
        | SOME data =>
            exact_rule_validation normalized_rule supplied_thms data target
    val old_params =
      map (fst o dest_var) (#params (clasetGoal.goal_at node pos))
    fun child_eigens ({params, ...} : clasetGoal.cgoal) =
      List.filter
        (fn name => not (List.exists (fn old => old = name) old_params))
        (map (fst o dest_var) params)
    val new_eigens = map child_eigens children
    val created = #metas fresh
    val (original, variant) = rule_origin cs duplicated theorem

    fun replay_theorem store =
      let
        val (type_substitution, term_substitution) =
          clasetMeta.collapse store
      in
        Drule.INST_TY_TERM
          (term_substitution, type_substitution) normalized_rule
      end
    fun replay_instance store =
      {theorem = replay_theorem store, elim = is_elim,
       consumed = consumed, parameters = old_params,
       eigenvariables = new_eigens}
    fun blast_replay_instance descriptors store =
      {theorem = replay_theorem store, elim = is_elim,
       consumed = consumed, parameters = old_params,
       eigenvariables = new_eigens, prefixes = descriptors}
    val action =
      case prefixes of
          NONE => clasetReplay.rule_action replay_instance
        | SOME descriptors =>
            clasetReplay.blast_rule_action
              (blast_replay_instance descriptors)
  in
    Direct
      {kind =
         RuleApplication
           {original = original, theorem = theorem,
            variant = variant, elim = is_elim},
       consumed = consumed, created = created,
       eigenvariables = new_eigens,
       result = (child_goals, validation), children = SOME children,
       action = action,
       closed = map (fn _ => NONE) children, store = child_store}
  end
  handle Match => raise Match
       | HOL_ERR _ => raise Match
       | Empty => raise Match

(* Resolving every immediate premise against every assumption is a
   cartesian product, so one declaration can offer far more applications
   than a search can install.  The engine budgets whole searches by their
   rule-application count; bound the candidates one forward rule builds at
   one goal by the same measure, so that a single expansion cannot
   outproduce the search it feeds. *)
val forward_alternative_limit = 200

(* The major premise is the last immediate one and comes fixed from the
   caller; the earlier premises are resolved against the assumptions here.
   Committing to their first unifier would hide every conclusion but one of
   a rule with several premises, so each earlier premise contributes all of
   its choices and the combinations are enumerated lazily: a caller that
   inspects only the leading alternatives pays for those alone.  Each
   result carries the assumption it adds, for the duplicate filter in
   [forward_rule_results]. *)
fun try_forward mode {source, form} immediate node pos
    (major_pos, major) =
  let
    val (asl, w) = clasetGoal.render node pos
    val fresh = freshen_canonical node pos form
    val all_premises = #premises fresh
    val _ =
      if immediate > 0 andalso immediate <= length all_premises then ()
      else raise Match
    val immediate_premises = List.take (all_premises, immediate)
    val major_premise = List.last immediate_premises
    val config = {mode = mode, rule_metas = #metas fresh}
    val major_store =
      case clasetUnify.unify (#store fresh) config
        (major_premise, major)
      of
          NONE => raise Match
        | SOME store => store
    val positioned = position_map (fn value => value) asl

    (* An assumption already equal to the premise discharges it without
       binding anything, so those choices come first and keep their
       store. *)
    fun choices premise store =
      let
        val (equal, remaining) =
          List.partition
            (fn (_, assumption) =>
              closing_equal store premise assumption) positioned
      in
        map (fn (position, _) => (position, store)) equal @
        List.mapPartial
          (fn (position, assumption) =>
            Option.map
              (fn next => (position, next))
              (clasetUnify.unify store config (premise, assumption)))
          remaining
      end

    fun assignments [] rev_positions store =
          seq.result (List.rev rev_positions @ [major_pos], store)
      | assignments (premise :: rest) rev_positions store =
          seq.flatten
            (seq.map
              (fn (position, next) =>
                assignments rest (position :: rev_positions) next)
              (seq.fromList (choices premise store)))

    val earlier = List.take (immediate_premises, immediate - 1)
    val residual_terms =
      List.drop (all_premises, immediate) @
      [#conclusion fresh] @ hyp (#core fresh)

    fun build (positions, matched_store) =
      let
        val _ =
          case mode of
              clasetUnify.Match =>
                if unresolved_in_premises matched_store (#metas fresh)
                     residual_terms
                then raise Match
                else ()
            | clasetUnify.Unify => ()
        val final_store =
          case mode of
              clasetUnify.Match =>
                ground_created matched_store (#metas fresh)
            | clasetUnify.Unify => matched_store
        val (type_substitution, term_substitution) =
          clasetMeta.collapse final_store
        val instantiated =
          Drule.INST_TY_TERM
            (term_substitution, type_substitution) (#core fresh)
        val normalized_rule0 = normalize_rule_thm instantiated

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
        val (normalized_premises, _) =
          strip_imp_only (concl normalized_rule)
        val supplied =
          ListPair.map
            (fn (premise, position) =>
              supplied_major_thm final_store
                (nth1 asl position) premise)
            (List.take (normalized_premises, immediate), positions)
        val forward = Drule.LIST_MP supplied normalized_rule
        val added = concl forward
        val parent = clasetGoal.goal_at node pos
        val child = clasetGoal.cons_assumption added parent
        val child_goal = cgoal_render final_store child
        val target = normalize_term final_store w

        fun validation [child_thm] =
              let val result = Drule.PROVE_HYP forward child_thm
              in EQ_MP (ALPHA (concl result) target) result end
          | validation _ =
              raise mk_HOL_ERR "clasetStep" "try_forward"
                "forward validation arity"

        fun replay_theorem store =
          let
            val (type_substitution, term_substitution) =
              clasetMeta.collapse store
          in
            Drule.INST_TY_TERM
              (term_substitution, type_substitution) normalized_rule
          end

        fun replay_instance store =
          {theorem = replay_theorem store, immediate = immediate,
           assumptions = positions}
      in
        (added,
         Direct
           {kind =
              RuleApplication
                {original = source, theorem = source,
                 variant = MakeElim, elim = true},
            consumed = NONE, created = #metas fresh,
            eigenvariables = [[]],
            result = ([child_goal], validation),
            children = SOME [child],
            action = clasetReplay.forward_rule_action replay_instance,
            closed = [NONE], store = final_store})
      end
  in
    seq.mapPartial (total build) (assignments earlier [] major_store)
  end
  handle Match => raise Match
       | HOL_ERR _ => raise Match
       | Empty => raise Match

fun forward_rule_results mode rule immediate (node, pos) =
  seq.delay
    (fn () =>
      let
        val assumptions = #asl (clasetGoal.goal_at node pos)
        val store = clasetGoal.store node

        fun attempts _ [] = seq.empty
          | attempts position (major :: rest) =
              seq.delay
                (fn () =>
                  seq.append
                    (case total
                       (fn () =>
                         try_forward mode rule immediate node pos
                           (position, major)) ()
                     of
                         SOME candidates => candidates
                       | NONE => seq.empty)
                    (attempts (position + 1) rest))

        (* Forward chaining reruns at every expansion, so an alternative
           whose conclusion an assumption already states, or that an
           earlier alternative already added, is only work.  Filtering
           across the whole sequence rather than per major premise also
           removes the repetitions different major premises share.  The
           conclusions are compared in the store the goal arrived with:
           an alternative must not be discarded because a sibling, which
           the search may never take, assigns a metavariable. *)
        fun distinct seen candidates =
          seq.delay
            (fn () =>
              case seq.cases candidates of
                  NONE => seq.empty
                | SOME ((added, direct), rest) =>
                    if List.exists (closing_equal store added) seen then
                      distinct seen rest
                    else
                      seq.cons direct (distinct (added :: seen) rest))
      in
        distinct assumptions
          (take_seq forward_alternative_limit (attempts 1 assumptions))
      end)

fun rule_results mode cs duplicated part weight_filter (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered as (asl, _) = clasetGoal.render node pos
        val tagged = List.filter (weight_filter o #1)
          (candidates mode part rendered)

        fun intro_application entry =
          seq.delay
            (fn () =>
              case total
                (fn () =>
                  try_rule LegacyPrefixes mode cs duplicated node pos
                    entry NONE) ()
              of
                  SOME result => seq.result result
                | NONE => seq.empty)

        fun elim_applications _ [] = seq.empty
          | elim_applications entry ((assumption_pos, major) :: rest) =
              seq.delay
                (fn () =>
                  case total
                    (fn () =>
                      try_rule LegacyPrefixes mode cs duplicated node pos
                        entry
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

datatype exact_major_selector = AllMajors | ExactMajor of int option

(* Keep the legacy exact-rule path just as lazy as it was before selectors:
   introductions do not inspect the goal until their delayed attempt is
   pulled, and eliminations walk the original assumption list incrementally.
   Only the additive exact selector indexes an assumption eagerly. *)
fun exact_rule_attempts attempt selector elim node pos =
  case (selector, elim) of
      (AllMajors, false) => attempt NONE
    | (AllMajors, true) =>
        let
          fun eliminations _ [] = seq.empty
            | eliminations assumption_pos (major :: rest) =
                seq.append
                  (attempt (SOME (assumption_pos, major)))
                  (seq.delay
                    (fn () =>
                      eliminations (assumption_pos + 1) rest))
        in
          eliminations 1 (#asl (clasetGoal.goal_at node pos))
        end
    | (ExactMajor NONE, false) => attempt NONE
    | (ExactMajor (SOME major), true) =>
        let val assumptions = #asl (clasetGoal.goal_at node pos)
        in
          if major > 0 andalso major <= length assumptions then
            attempt (SOME (major, nth1 assumptions major))
          else seq.empty
        end
    | _ => seq.empty

fun supplied_rule_results_with selector policy mode cs
    {theorem, elim} (node, pos) =
  let
    val tag : clasetLib.tag = {weight = 0, index = 0}
    val entry = (tag, (elim, theorem))

    fun attempt assumption =
      seq.delay
        (fn () =>
          case total
            (fn () =>
              try_rule policy mode cs false node pos entry assumption) ()
          of
              SOME direct => seq.result direct
            | NONE => seq.empty)

  in
    exact_rule_attempts attempt selector elim node pos
  end

fun exact_rule_results_with selector cs specification =
  supplied_rule_results_with selector ExactBlastPrefixes
    clasetUnify.Unify cs specification

fun exact_rule_results cs specification =
  exact_rule_results_with AllMajors cs specification

fun all_weights _ = true
fun weight_is expected ({weight, ...} : clasetLib.tag) = weight = expected

fun builtin_results (node, pos) =
  let
    val rendered as (_, w) = clasetGoal.render node pos

    fun make initial_store kind action tactic =
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
              val child_params = map #2 lifted
              val new_params = List.concat child_params
              fun register (param, store) =
                if clasetMeta.is_eigen store param then store
                else
                  case clasetMeta.register_eigen param store of
                      SOME next => next
                    | NONE =>
                        raise mk_HOL_ERR "clasetStep" "builtin_results"
                          "a generated parameter is not fresh"
              val store = List.foldl register initial_store new_params
            in
              seq.result
                (Direct
                  {kind = kind, consumed = NONE, created = no_created,
                   eigenvariables =
                     map (map (fst o dest_var)) child_params,
                   result = result, children = SOME children,
                   action = action,
                   closed = map (fn _ => NONE) children,
                   store = store})
            end
  in
    if is_imp_only w then
      make (clasetGoal.store node) Disch clasetReplay.disch_action
        Tactic.DISCH_TAC
    else if is_forall w then
      let
        val (bound, _) = dest_forall w
        val (fresh, store) = clasetGoal.fresh_eigen node bound
        val name = fst (dest_var fresh)
      in
        make store Gen (clasetReplay.gen_action name)
          (clasetReplay.GEN_NAMED_TAC name)
      end
    else seq.empty
  end

fun swapped_builtin_results (node, pos) =
  list_seq
    (fn () =>
      let
        val (asl, _) = clasetGoal.render node pos
        val store = clasetGoal.store node

        fun attempt (asm_pos, assumption) =
          let
            val positive = total dest_neg assumption
            val supported =
              case positive of
                  SOME tm =>
                    can dest_imp_only tm orelse can dest_forall tm
                | NONE => false
          in
            if supported then
              case tactic_direct (SwappedBuiltin asm_pos)
                (SOME asm_pos) node pos
                (clasetReplay.SWAPPED_BUILTIN_TAC store asm_pos)
              of
                  NONE => NONE
                | SOME
                    (Direct
                      {kind, consumed, created, eigenvariables, result,
                       children, closed, store, ...}) =>
                    SOME
                      (Direct
                        {kind = kind, consumed = consumed,
                         created = created,
                         eigenvariables = eigenvariables,
                         result = result, children = children,
                         action =
                           clasetReplay.swapped_builtin_action asm_pos,
                         closed = closed, store = store})
            else NONE
          end
      in
        List.mapPartial attempt (position_map (fn value => value) asl)
      end)

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
                 created = no_created, eigenvariables = [[]],
                 result = result, children = SOME [child],
                 action = clasetReplay.hyp_subst_action,
                 closed = [NONE], store = clasetGoal.store node})
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

fun plain_tactic_results kind action tactic (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered = clasetGoal.render node pos
        val {params, ...} = clasetGoal.goal_at node pos
      in
        case total tactic rendered of
            NONE => seq.empty
          | SOME (result as (goals, _)) =>
              let
                fun child (asl, w) =
                  {params = params, asl = asl, w = w}
              in
                seq.result
                  (Direct
                    {kind = kind, consumed = NONE,
                     created = no_created,
                     eigenvariables = map (fn _ => []) goals,
                     result = result, children = SOME (map child goals),
                     action = action,
                     closed = map (fn _ => NONE) goals,
                     store = clasetGoal.store node})
              end
      end)

(* T1 affectedness is computed on the branch syntax, before beta/eta
   normalization.  Instantiate engine bindings structurally, but preserve
   those redexes so this transition agrees with blastSearch.equalSubst. *)
fun instantiate_without_reduction store tm =
  clasetMeta.instantiate store tm

type blast_hyp_subst_context =
  {store : clasetMeta.store,
   params : term list,
   assumption_count : int,
   goal : term list * term}

fun prepare_blast_hyp_subst node pos : blast_hyp_subst_context =
  let
    val store = clasetGoal.store node
    val {params, asl, w} = clasetGoal.goal_at node pos
    val instantiate = instantiate_without_reduction store
    val goal = (map instantiate asl, instantiate w)
  in
    {store = store, params = params, assumption_count = length asl,
     goal = goal}
  end

fun blast_hyp_subst_in
      ({store, params, assumption_count, goal} :
        blast_hyp_subst_context) {position, changed} =
  if position <= 0 orelse position > assumption_count then NONE
  else
    case total
      (fn () =>
        case changed of
            NONE =>
              clasetReplay.COMPUTE_BLAST_HYP_SUBST_TAC_AT position goal
          | SOME mask =>
              (mask,
               clasetReplay.BLAST_HYP_SUBST_TAC_AT
                 {position = position, changed = mask} goal)) () of
        NONE => NONE
      | SOME (changed, result as (goals, _)) =>
          let
            fun child (child_asl, child_w) =
              {params = params, asl = child_asl, w = child_w}
          in
            SOME
              (Direct
                {kind = HypSubst, consumed = NONE,
                 created = no_created,
                 eigenvariables = map (fn _ => []) goals,
                 result = result, children = SOME (map child goals),
                 action =
                   clasetReplay.blast_hyp_subst_action_at
                     {position = position, changed = changed},
                 closed = map (fn _ => NONE) goals, store = store})
          end

fun blast_hyp_subst_results (node, pos) =
  list_seq
    (fn () =>
      let
        val prepared = prepare_blast_hyp_subst node pos
        val positions =
          List.tabulate
            (#assumption_count prepared, fn index => index + 1)
      in
        List.mapPartial
          (fn position =>
            blast_hyp_subst_in prepared
              {position = position, changed = NONE}) positions
      end)

fun blast_hyp_subst_results_at {equality, changed} (node, pos) =
  list_seq
    (fn () =>
      case blast_hyp_subst_in (prepare_blast_hyp_subst node pos)
        {position = equality, changed = SOME changed} of
          NONE => []
        | SOME direct => [direct])

val ccontr_results =
  plain_tactic_results CContr
    clasetReplay.goal_negation_action
    clasetReplay.GOAL_NEGATION_TAC

fun move_back_results position =
  plain_tactic_results (MoveAssumptionToBack position)
    (clasetReplay.move_assumption_to_back_action position)
    (clasetReplay.MOVE_ASSUMPTION_TO_BACK_TAC position)

fun rendered_conclusion node pos = #2 (clasetGoal.render node pos)

fun eta_forall_bound tm =
  case strip_comb tm of
      (head, [predicate]) =>
        (case total Type.dom_rng (type_of predicate) of
             SOME (domain, range) =>
               let
                 val bound = genvar domain
                 val forall_head = #1 (strip_comb (mk_forall (bound, T)))
               in
                 if range = bool andalso same_const head forall_head then
                   SOME bound
                 else NONE
               end
           | NONE => NONE)
    | _ => NONE

fun forall_bound tm =
  case total dest_forall tm of
      SOME (bound, _) => SOME bound
    | NONE => eta_forall_bound tm

fun disch_results (input as (node, pos)) =
  if is_imp_only (rendered_conclusion node pos) then
    builtin_results input
  else seq.empty

fun gen_results (input as (node, pos)) =
  case forall_bound (rendered_conclusion node pos) of
      SOME bound =>
        let
          val (fresh, store) = clasetGoal.fresh_eigen node bound
          val name = fst (dest_var fresh)
          val rendered = clasetGoal.render node pos
        in
          case total (clasetReplay.GEN_NAMED_TAC name) rendered of
              NONE => seq.empty
            | SOME (result as (goals, validation)) =>
                let
                  val {params, ...} = clasetGoal.goal_at node pos
                  fun child (asl, w) =
                    {params = params @ [fresh], asl = asl, w = w}
                  val children = map child goals
                  val action = clasetReplay.gen_action name
                in
                  seq.result
                    (Direct
                      {kind = Gen, consumed = NONE, created = no_created,
                       eigenvariables = map (fn _ => [name]) goals,
                       result = result, children = SOME children,
                       action = action,
                       closed = map (fn _ => NONE) children,
                       store = store})
                end
        end
    | NONE => seq.empty

fun safe_cascade cs input =
  first_nonempty
    [assumption_results,
     eq_mp_results,
     rule_results clasetUnify.Match cs false
       (clasetLib.safe0_part cs) all_weights,
     builtin_results,
     swapped_builtin_results,
     hyp_subst_results,
     rule_results clasetUnify.Match cs false
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
       result = (goals, validation), children, action, closed, store} = direct
  in
    case goals of
        [left, right] =>
          (case close_plain left of
               SOME
                 (close_direct as
                   Direct {result = ([], close_validation), ...}) =>
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
                        children = Option.map tl children,
                        action = action,
                        closed = [SOME close_direct, List.nth (closed, 1)],
                        store = store})
                 end
             | _ =>
                 (case close_plain right of
                      SOME
                        (close_direct as
                          Direct {result = ([], close_validation), ...}) =>
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
                               action = action,
                               closed = [hd closed, SOME close_direct],
                               store = store})
                        end
                    | _ => NONE))
      | _ => NONE
  end

fun bimatch2_results cs part input =
  seq.mapPartial close_one_child
    (rule_results clasetUnify.Match cs false part (weight_is 2) input)

fun clarify_cascade cs input =
  first_nonempty
    [assume_or_contradiction,
     rule_results clasetUnify.Match cs false
       (clasetLib.safe0_part cs) all_weights,
     builtin_results,
     swapped_builtin_results,
     hyp_subst_results,
     rule_results clasetUnify.Match cs false
       (clasetLib.safep_part cs) (weight_is 1),
     bimatch2_results cs (clasetLib.safep_part cs)]
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

type unifying_assumption_context =
  {asl : term list, w : term, store : clasetMeta.store}

fun prepare_unifying_assumption node pos : unifying_assumption_context =
  let
    val (asl, w) = clasetGoal.render node pos
  in
    {asl = asl, w = w, store = clasetGoal.store node}
  end

fun unifying_assumption_candidate_with action_of
      ({w, store = initial_store, ...} : unifying_assumption_context)
      (asm_pos, asm) =
  case clasetUnify.unify initial_store unify_config (w, asm) of
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
                   children = SOME [],
                   action = action_of asm_pos,
                   closed = [], store = store})
            end

fun unifying_assumption_candidate prepared positioned =
  unifying_assumption_candidate_with clasetReplay.assumption_action
    prepared positioned

fun unifying_assumption_in
      action_of (prepared as {asl, ...} : unifying_assumption_context)
      asm_pos =
  if asm_pos <= 0 orelse asm_pos > length asl then NONE
  else
    unifying_assumption_candidate_with action_of prepared
      (asm_pos, nth1 asl asm_pos)

fun unifying_assumption_results (node, pos) =
  list_seq
    (fn () =>
      let
        val prepared = prepare_unifying_assumption node pos
      in
        List.mapPartial (unifying_assumption_candidate prepared)
          (position_map (fn value => value) (#asl prepared))
      end)

fun unifying_assumption_results_at asm_pos (node, pos) =
  list_seq
    (fn () =>
      case unifying_assumption_in
        clasetReplay.strict_assumption_action
        (prepare_unifying_assumption node pos) asm_pos of
          NONE => []
        | SOME direct => [direct])

type unifying_contradiction_context =
  {asl : term list,
   w : term,
   params : term list,
   store : clasetMeta.store}

fun prepare_unifying_contradiction node pos :
      unifying_contradiction_context =
  let
    val (asl, w) = clasetGoal.render node pos
    val params = #params (clasetGoal.goal_at node pos)
  in
    {asl = asl, w = w, params = params, store = clasetGoal.store node}
  end

fun unifying_contradiction_in
      ({asl, w, params, store = initial_store} :
        unifying_contradiction_context)
      {negative = negative_pos, positive = positive_pos} =
  if negative_pos <= 0 orelse positive_pos <= 0 orelse
     negative_pos > length asl orelse positive_pos > length asl orelse
     negative_pos = positive_pos
  then NONE
  else
    let
        val major = nth1 asl negative_pos
        val candidate = nth1 asl positive_pos
        val (positive, store1) =
          clasetMeta.new_meta {allow = params, ty = Type.bool}
            initial_store
        val (result, fresh_store) =
          clasetMeta.new_meta {allow = params, ty = Type.bool} store1
        val created = {terms = [positive, result], types = []}
        val config =
          {mode = clasetUnify.Unify, rule_metas = created}
      in
        case clasetUnify.unify fresh_store config (result, w) of
            NONE => NONE
          | SOME result_store =>
              (case clasetUnify.unify result_store config
                 (mk_neg positive, major)
               of
                   NONE => NONE
                 | SOME major_store =>
                     let
                       val selected_store =
                         if closing_equal major_store positive candidate then
                           SOME major_store
                         else
                           clasetUnify.unify major_store unify_config
                             (positive, candidate)
                     in
                       Option.map
                         (fn store =>
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
                                       MP (NOT_ELIM negative_thm)
                                         positive_thm
                                   in
                                     Drule.CONTR (normalize_term store w)
                                       false_thm
                                   end
                               | validation _ =
                                   raise mk_HOL_ERR "clasetStep"
                                     "unifying_contradiction_at"
                                     "contradiction validation has children"
                           in
                             Direct
                               {kind =
                                  Contradiction
                                    (negative_pos, positive_pos),
                                consumed = SOME negative_pos,
                                created = created, eigenvariables = [],
                                result = ([], validation),
                                children = SOME [],
                                action =
                                  clasetReplay.contradiction_action
                                    (negative_pos, positive_pos),
                                closed = [], store = store}
                           end)
                         selected_store
                     end)
    end

fun unifying_contradiction_results_at positions (node, pos) =
  list_seq
    (fn () =>
      case unifying_contradiction_in
        (prepare_unifying_contradiction node pos) positions of
          NONE => []
        | SOME direct => [direct])

fun unifying_contradiction_results (node, pos) =
  list_seq
    (fn () =>
      let
        val prepared = prepare_unifying_contradiction node pos
        val {asl, w, params, store = initial_store} = prepared
        val positioned = position_map (fn value => value) asl

        fun major_alternatives (major_pos, major) =
          let
            val (positive, store1) =
              clasetMeta.new_meta {allow = params, ty = Type.bool}
                initial_store
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
                           children = SOME [],
                           action =
                             clasetReplay.contradiction_action
                               (major_pos, positive_pos),
                           closed = [], store = store}
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
     rule_results clasetUnify.Unify cs false
       (clasetLib.safe0_part cs) all_weights]
    input

fun instp_cascade cs =
  rule_results clasetUnify.Unify cs false
    (clasetLib.safep_part cs) all_weights

fun inst_cascade cs input =
  append_results (inst0_cascade cs) (instp_cascade cs) input

fun unsafe_cascade cs =
  rule_results clasetUnify.Unify cs false
    (clasetLib.unsafe_part cs) all_weights

fun dup_cascade cs =
  rule_results clasetUnify.Unify cs true
    (clasetLib.dup_part cs) all_weights

fun depth_cascade part cs input =
  append_results (instp_cascade cs)
    (rule_results clasetUnify.Unify cs false part all_weights) input

fun selected_direct goals validation available =
  case List.find
    (fn (identity, _) => Portable.pointer_eq (identity, validation))
    available
  of
      NONE => NONE
    | SOME (_, direct) =>
        if goals_equal (#1 (direct_result direct), goals) then SOME direct
        else NONE

fun make_record target validation direct =
  let
    fun nested _ [] = []
      | nested index (child :: rest) =
          Option.map
            (fn selected =>
              make_record (target + index - 1)
                (#2 (direct_result selected)) selected)
            child :: nested (index + 1) rest
  in
    clasetReplay.make_record
      {kind = direct_kind direct,
       target = target,
       consumed = direct_consumed direct,
       created = direct_created direct,
       eigenvariables = direct_eigens direct,
       validation = validation,
       action = direct_action direct,
       children = nested 1 (direct_closed direct)}
  end

fun direct_step results (node, pos) =
  seq.map
    (fn direct =>
      let
        val (_, validation) = direct_result direct
        val stored = clasetGoal.set_store (direct_store direct) node
        val children =
          case direct_children direct of
              SOME values => values
            | NONE =>
                raise mk_HOL_ERR "clasetStep" "direct_step"
                  "an exact engine transition has no internal children"
        val next =
          clasetGoal.replace_goal stored
            {pos = pos, children = children,
             store = direct_store direct}
        val record = make_record pos validation direct
      in
        (record, clasetGoal.record_step record next)
      end)
    (results (node, pos))

val blast_assumption_step = direct_step unifying_assumption_results
val blast_contradiction_step =
  direct_step unifying_contradiction_results
fun rule_step {theorem, elim, mode} =
  direct_step
    (supplied_rule_results_with AllMajors LegacyPrefixes mode
      clasetLib.empty_cs {theorem = theorem, elim = elim})
fun forward_rule_step {theorem, immediate, mode} =
  let
    (* Canonicalizing here serves both the range check and every later
       application, so the rule is put in canonical form exactly once. *)
    val form = clasetRules.canonical_form_of clasetRules.Forward theorem
    val premise_count = length (#prems form)
    val count = Option.getOpt (immediate, premise_count)
    val _ =
      if count > 0 andalso count <= premise_count then ()
      else
        raise mk_HOL_ERR "clasetStep" "forward_rule_step"
          "the immediate-premise count is out of range"
  in
    direct_step
      (forward_rule_results mode {source = theorem, form = form} count)
  end
fun blast_assumption_step_at position =
  direct_step (unifying_assumption_results_at position)
fun blast_contradiction_step_at positions =
  direct_step (unifying_contradiction_results_at positions)
fun blast_rule_step cs specification =
  direct_step (exact_rule_results cs specification)
fun blast_rule_step_at cs {theorem, elim, major} =
  direct_step
    (exact_rule_results_with (ExactMajor major) cs
      {theorem = theorem, elim = elim})

val blast_disch_step = direct_step disch_results
val blast_gen_step = direct_step gen_results
val blast_ccontr_step = direct_step ccontr_results
val blast_hyp_subst_step = direct_step blast_hyp_subst_results
fun blast_hyp_subst_step_at fields =
  direct_step (blast_hyp_subst_results_at fields)
fun blast_move_back_step position =
  direct_step (move_back_results position)

fun wrapper_direct rendered goals validation store =
  let val result = (goals, validation)
  in
    Direct
      {kind = Wrapper, consumed = NONE, created = no_created,
       eigenvariables = new_free_names_by_goal rendered goals,
       result = result, children = NONE,
       action = clasetReplay.fixed_action result,
       closed = map (fn _ => NONE) goals, store = store}
  end

fun wrapped_step apply_wrappers cascade cs (node, pos) =
  seq.delay
    (fn () =>
      let
        val rendered = clasetGoal.render node pos
        val available = ref ([] : (validation * direct) list)

        (* A wrapper may reorder equal rendered results.  Give each direct
           result an opaque closure identity so its engine store and replay
           action follow the result selected by the wrapper. *)
        fun remember direct =
          let
            val (goals, validation) = direct_result direct
            fun identity theorems = validation theorems
          in
            available := (identity, direct) :: !available;
            (goals, identity)
          end

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
                        case selected_direct goals validation (!available) of
                            SOME found => (found, true)
                          | NONE =>
                              (wrapper_direct rendered goals validation
                                 (clasetGoal.store node), false)
                      val stored =
                        clasetGoal.set_store (direct_store direct) node
                      val lifted =
                        if exact then
                          case direct_children direct of
                              SOME children =>
                                SOME
                                  (clasetGoal.replace_goal stored
                                    {pos = pos, children = children,
                                     store = direct_store direct})
                            | NONE =>
                                clasetGoal.unrender stored pos result
                        else clasetGoal.unrender stored pos result
                    in
                      case lifted of
                          NONE => lift rest
                        | SOME next =>
                            let
                              val record =
                                make_record pos validation direct
                              val recorded =
                                if clasetGoal.replay_length next >
                                   clasetGoal.replay_length stored
                                then next
                                else clasetGoal.record_step record next
                            in
                              seq.cons (record, recorded) (lift rest)
                            end
                    end)
      in
        lift wrapped
      end)

fun safe_step cs =
  wrapped_step clasetLib.app_safe_wrappers safe_cascade cs

fun clarify_step cs =
  wrapped_step clasetLib.app_safe_wrappers clarify_cascade cs

(* Unsafe steps carry no wrappers: the claset's safe wrappers apply only
   to safe and clarify cascades. *)
fun no_wrappers _ tactic = tactic

fun inst0_step cs = wrapped_step no_wrappers inst0_cascade cs

fun instp_step cs = wrapped_step no_wrappers instp_cascade cs

fun inst_step cs = wrapped_step no_wrappers inst_cascade cs

fun unsafe_step cs = wrapped_step no_wrappers unsafe_cascade cs

fun dup_step cs = wrapped_step no_wrappers dup_cascade cs

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
