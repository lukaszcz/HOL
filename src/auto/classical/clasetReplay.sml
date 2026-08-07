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
  | SwappedBuiltin of int
  | MoveAssumptionToBack of int
  | Wrapper

type created =
  {terms : clasetMeta.meta list, types : clasetMeta.tymeta list}
type exact_prefix_descriptor = {foralls : int, implications : int}
type exact_prefix_rebuild =
  {fresh : term list, assumptions : term list, premise : term}
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

datatype script =
  Script of
    {roots : step_record option list,
     length : int,
     open_paths : int list list}
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

fun nth1 function_name =
  clasetNorm.nth1 ("clasetReplay", function_name)

fun delete_nth function_name =
  clasetNorm.delete_nth ("clasetReplay", function_name)

val normalize_conv = clasetNorm.normalize_conv
val normalize_thm = clasetNorm.normalize_thm

fun restore_target function_name target normalized_target theorem =
  let
    val conclusion = concl theorem
    val aligned =
      if aconv conclusion normalized_target then
        EQ_MP (ALPHA conclusion normalized_target) theorem
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "the produced theorem misses the normalized target"
    val target_equality = normalize_conv target
    val normalized_input_target = rhs (concl target_equality)
  in
    if aconv normalized_target target then
      EQ_MP (ALPHA normalized_target target) aligned
    else if aconv normalized_target normalized_input_target then
      EQ_MP (SYM target_equality)
        (EQ_MP
          (ALPHA normalized_target normalized_input_target) aligned)
    else
      raise mk_HOL_ERR "clasetReplay" function_name
        "the normalized target cannot be restored exactly"
  end

val normalize_rule_thm = clasetNorm.normalize_rule_thm

fun split_imp_prefix function_name arity tm =
  clasetNorm.split_imp_prefix ("clasetReplay", function_name) arity tm

fun assumption_thm store asm target =
  let
    val asm' = clasetMeta.norm store asm
    val target' = clasetMeta.norm store target
    val asm_equality = normalize_conv asm
    val normalized_input_asm = rhs (concl asm_equality)
    val assumption =
      if aconv asm' asm then ASSUME asm
      else if aconv asm' normalized_input_asm then
        EQ_MP asm_equality (ASSUME asm)
      else
        raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
          "the normalized assumption cannot be restored exactly"
    val normalized = normalize_thm assumption
  in
    if aconv (concl normalized) target' then
      restore_target "ASSUMPTION_TAC" target target' normalized
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
    val normalized_target = clasetMeta.norm store w
    fun validation [] =
          let
            val nthm = assumption_thm store negative negative'
            val pthm = assumption_thm store positive proposition
            val contradiction =
              Drule.CONTR normalized_target
                (MP (NOT_ELIM nthm) pthm)
          in
            restore_target "CONTRADICTION_TAC" w normalized_target
              contradiction
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

fun exact_prefix_descriptor premise =
  let
    val (bounds, body) = strip_forall premise
    val (assumptions, _) = strip_imp_only body
  in
    {foralls = length bounds, implications = length assumptions}
  end

fun split_foralls function_name count premise =
  let
    fun split 0 rev_bounds body = (List.rev rev_bounds, body)
      | split remaining rev_bounds body =
          (case total dest_forall body of
               SOME (bound, rest) =>
                 split (remaining - 1) (bound :: rev_bounds) rest
             | NONE =>
                 raise mk_HOL_ERR "clasetReplay" function_name
                   "the instantiated premise has too few foralls")
  in
    if count < 0 then
      raise mk_HOL_ERR "clasetReplay" function_name
        "negative forall-prefix arity"
    else split count [] premise
  end

fun exact_prefix_bounds
      ({foralls, implications} : exact_prefix_descriptor) premise =
  let
    val _ =
      if implications < 0 then
        raise mk_HOL_ERR "clasetReplay" "exact_prefix_bounds"
          "negative implication-prefix arity"
      else ()
    val (bounds, _) =
      split_foralls "exact_prefix_bounds" foralls premise
  in
    bounds
  end

fun split_exact_prefix
      {descriptor = {foralls, implications}, premise, fresh} =
  let
    val (bounds, body) =
      split_foralls "split_exact_prefix" foralls premise
    val _ =
      if implications < 0 then
        raise mk_HOL_ERR "clasetReplay" "split_exact_prefix"
          "negative implication-prefix arity"
      else if length bounds <> length fresh then
        raise mk_HOL_ERR "clasetReplay" "split_exact_prefix"
          "fresh-parameter arity differs from the descriptor"
      else if
        ListPair.allEq
          (fn (bound, variable) =>
            is_var variable andalso type_of bound = type_of variable)
          (bounds, fresh)
      then ()
      else
        raise mk_HOL_ERR "clasetReplay" "split_exact_prefix"
          "a fresh parameter has the wrong type"
    val substitution =
      ListPair.map
        (fn (bound, variable) => {redex = bound, residue = variable})
        (bounds, fresh)
    val body' = Term.subst substitution body
    val (assumptions, residual) =
      split_imp_prefix "split_exact_prefix" implications body'
    val rebuild =
      {fresh = fresh, assumptions = assumptions, premise = premise}
  in
    {assumptions = assumptions, residual = residual, rebuild = rebuild}
  end

fun rebuild_exact_prefix
      ({fresh, assumptions, premise} : exact_prefix_rebuild) child_thm =
  let
    val discharged =
      List.foldr (fn (assumption, th) => DISCH assumption th)
        child_thm assumptions
    val generalized = GENL fresh discharged
  in
    EQ_MP (ALPHA (concl generalized) premise) generalized
  end

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
     {fresh = fresh, assumptions = antecedents, premise = premise})
  end

fun blast_rule_child parent_asl premise names descriptor =
  let
    val bounds = exact_prefix_bounds descriptor premise
    val _ =
      if length bounds = length names then ()
      else
        raise mk_HOL_ERR "clasetReplay" "BLAST_RULE_TAC"
          "recorded eigenvariable arity is corrupt"
    val fresh =
      ListPair.map
        (fn (bound, name) => mk_var (name, type_of bound))
        (bounds, names)
    val {assumptions, residual, rebuild} =
      split_exact_prefix
        {descriptor = descriptor, premise = premise, fresh = fresh}
  in
    ((cons_assumptions assumptions parent_asl, residual), rebuild)
  end

val normalize_assumption = clasetNorm.normalize_assumption

fun theorem_hypothesis normalized_asl hypothesis =
  case List.find (fn (normalized, _) => aconv normalized hypothesis)
    normalized_asl
  of
      SOME (_, theorem) => theorem
    | NONE =>
        raise mk_HOL_ERR "clasetReplay" "RULE_TAC"
          "a theorem hypothesis is absent from the goal"

fun rule_tac_with function_name make_children
    {theorem, elim, consumed, parameters, eigenvariables} (asl, w) =
  let
    val rule0 = normalize_rule_thm theorem
    val target_equality = normalize_conv w
    val normalized_target = rhs (concl target_equality)
    val recorded_arity =
      length eigenvariables + (if elim then 1 else 0)
    val (_, initial_conclusion) =
      split_imp_prefix function_name recorded_arity (concl rule0)
    val (term_substitution, type_substitution) =
      Term.match_term initial_conclusion normalized_target
    fun allowed_parameter {redex, residue} =
      is_var redex andalso is_var residue andalso
      List.exists (fn name => name = fst (dest_var redex)) parameters
    val _ =
      if List.all allowed_parameter term_substitution then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "conclusion alignment would instantiate a rigid variable"
    val aligned_rule =
      Drule.INST_TY_TERM
        (term_substitution, type_substitution) rule0
    val normalized_asl = map normalize_assumption asl
    val rule =
      List.foldl
        (fn (hypothesis, current) =>
          Drule.PROVE_HYP
            (theorem_hypothesis normalized_asl hypothesis) current)
        aligned_rule (hyp aligned_rule)
    val (premises0, conclusion) =
      split_imp_prefix function_name recorded_arity (concl rule)
    val _ =
      if aconv conclusion normalized_target then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
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
                  raise mk_HOL_ERR "clasetReplay" function_name
                    "an elimination record has no consumed assumption"
          val major = nth1 function_name asl major_pos
          val rule_major = hd premises0
          val (normalized_major, major_thm) =
            normalize_assumption major
          val major_thm =
            if aconv normalized_major rule_major then major_thm
            else
              raise mk_HOL_ERR "clasetReplay" function_name
                "the selected assumption misses the major premise"
        in
          ([major_thm], tl premises0,
           delete_nth function_name asl major_pos)
        end
      else ([], premises0, asl)
    val _ =
      if length premises = length eigenvariables then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "recorded child arity is corrupt"
    val child_data = make_children parent_asl premises eigenvariables
    val child_goals = map #1 child_data
    val rebuild_data = map #2 child_data

    fun validation child_thms =
      if length child_thms <> length premises then
        raise mk_HOL_ERR "clasetReplay" function_name
          "validation received the wrong number of theorems"
      else
        let
          val premise_thms =
            ListPair.map
              (fn (data, theorem) =>
                rebuild_exact_prefix data theorem)
              (rebuild_data, child_thms)
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
    raise mk_HOL_ERR "clasetReplay" function_name
      "an elimination rule has no major premise"

fun ordinary_rule_children parent_asl premises eigenvariables =
  ListPair.map
    (fn (premise, names) =>
      rule_child parent_asl premise names)
    (premises, eigenvariables)

fun RULE_TAC fields =
  rule_tac_with "RULE_TAC" ordinary_rule_children fields

fun FORWARD_RULE_TAC {theorem, immediate, assumptions} (asl, w) =
  let
    val function_name = "FORWARD_RULE_TAC"
    val rule0 = normalize_rule_thm theorem
    val (premises, _) = strip_imp_only (concl rule0)
    val _ =
      if immediate > 0 andalso immediate <= length premises then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "the immediate-premise count is out of range"
    val _ =
      if length assumptions = immediate then ()
      else
        raise mk_HOL_ERR "clasetReplay" function_name
          "the recorded assumption arity is corrupt"
    val normalized_asl = map normalize_assumption asl
    val rule =
      List.foldl
        (fn (hypothesis, current) =>
          Drule.PROVE_HYP
            (theorem_hypothesis normalized_asl hypothesis) current)
        rule0 (hyp rule0)

    fun premise_thm (premise, position) =
      let
        val assumption = nth1 function_name asl position
        val (normalized, theorem) = normalize_assumption assumption
      in
        if aconv normalized premise then theorem
        else
          raise mk_HOL_ERR "clasetReplay" function_name
            "a selected assumption misses its immediate premise"
      end

    val supplied =
      ListPair.map premise_thm
        (List.take (premises, immediate), assumptions)
    val forward = Drule.LIST_MP supplied rule
    val added = concl forward
    val child = (added :: asl, w)

    fun validation [child_thm] = Drule.PROVE_HYP forward child_thm
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" function_name
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun BLAST_RULE_TAC
    {theorem, elim, consumed, parameters, eigenvariables, prefixes} =
  let
    fun make_children parent_asl premises names =
      if length premises = length prefixes then
        ListPair.map
          (fn ((premise, child_names), descriptor) =>
            blast_rule_child parent_asl premise child_names descriptor)
          (ListPair.zip (premises, names), prefixes)
      else
        raise mk_HOL_ERR "clasetReplay" "BLAST_RULE_TAC"
          "recorded prefix-descriptor arity is corrupt"
  in
    rule_tac_with "BLAST_RULE_TAC" make_children
      {theorem = theorem, elim = elim, consumed = consumed,
       parameters = parameters, eigenvariables = eigenvariables}
  end

val HYP_SUBST_TAC =
  let
    val {hyp_subst_tac, ...} = clasetLib.claset_config
  in
    Tactical.THEN (hyp_subst_tac, Tactical.REPEAT hyp_subst_tac)
  end

(* Blast records one equality substitution at a time.  Unlike the classical
   hyp-subst slot, affected assumptions are stably moved to the front. *)
fun eta_atom_conv tm =
  case total Drule.ETA_CONV tm of
      NONE => REFL tm
    | SOME theorem =>
        TRANS theorem (eta_atom_conv (rhs (concl theorem)))

fun blast_hyp_orientation equality =
  let
    val equality_conversion =
      Conv.THENC
        (Conv.LAND_CONV eta_atom_conv,
         Conv.RAND_CONV eta_atom_conv) equality
    val contracted = rhs (concl equality_conversion)
    val contracted_thm = EQ_MP equality_conversion (ASSUME equality)
  in
    case total dest_eq contracted of
        NONE => NONE
      | SOME (left, right) =>
          let
            fun suitable variable other =
              is_var variable andalso
              not (clasetMeta.is_meta variable) andalso
              not (free_in variable other)
          in
            if suitable left right then
              SOME (left, right, contracted_thm)
            else if suitable right left then
              SOME (right, left, SYM contracted_thm)
            else NONE
          end
  end

fun blast_hyp_subst_tac_at position recorded_changed (asl, w) =
  let
    val equality = nth1 "BLAST_HYP_SUBST_TAC_AT" asl position
    val (old, replacement, equality_thm) =
      case blast_hyp_orientation equality of
          SOME oriented => oriented
        | NONE =>
            raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
              "selected assumption is not a suitable equality"
    val remaining =
      delete_nth "BLAST_HYP_SUBST_TAC_AT" asl position
    val substitution = [{redex = old, residue = replacement}]
    fun substituted tm = Term.subst substitution tm
    fun affected tm = not (aconv (substituted tm) tm)
    val changed_mask =
      case recorded_changed of
          NONE => map affected remaining
        | SOME mask =>
            if length mask = length remaining then mask
            else
              raise mk_HOL_ERR "clasetReplay"
                "BLAST_HYP_SUBST_TAC_AT"
                "recorded changed mask has the wrong length"
    fun partition [] [] changed unchanged =
          (List.rev changed, List.rev unchanged)
      | partition (true :: flags) (tm :: terms) changed unchanged =
          partition flags terms (tm :: changed) unchanged
      | partition (false :: flags) (tm :: terms) changed unchanged =
          partition flags terms changed (tm :: unchanged)
      | partition _ _ _ _ =
          raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
            "recorded changed mask has the wrong length"
    val (changed, unchanged) =
      partition changed_mask remaining [] []
    val reordered = map substituted (changed @ unchanged)
    val target = substituted w
    val target_equality = normalize_conv w
    val normalized_target = rhs (concl target_equality)
    val (children, validation0) =
      Tactic.SUBST_ALL_TAC equality_thm (remaining, w)
    val _ =
      case children of
          [_] => ()
        | _ =>
            raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
              "substitution did not produce one child"

    fun validation [child_thm] =
          let
            val result0 = validation0 [child_thm]
            val result_equality = normalize_conv (concl result0)
            val normalized_result = rhs (concl result_equality)
            val result = EQ_MP result_equality result0
          in
            if aconv normalized_result normalized_target then
              restore_target "BLAST_HYP_SUBST_TAC_AT" w
                normalized_target result
            else
              raise mk_HOL_ERR "clasetReplay"
                "BLAST_HYP_SUBST_TAC_AT"
                "substitution validation misses the original target"
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC_AT"
            "validation received the wrong number of theorems"
  in
    (changed_mask, ([(reordered, target)], validation))
  end

fun BLAST_HYP_SUBST_TAC_AT {position, changed} goal =
  #2 (blast_hyp_subst_tac_at position (SOME changed) goal)

fun COMPUTE_BLAST_HYP_SUBST_TAC_AT position goal =
  blast_hyp_subst_tac_at position NONE goal

fun BLAST_HYP_SUBST_TAC (goal as (asl, _)) =
  let
    fun first _ [] =
          raise mk_HOL_ERR "clasetReplay" "BLAST_HYP_SUBST_TAC"
            "no suitable equality assumption"
      | first position (_ :: rest) =
          (#2 (COMPUTE_BLAST_HYP_SUBST_TAC_AT position goal)
           handle HOL_ERR _ => first (position + 1) rest)
  in
    first 1 asl
  end

fun eta_forall_predicate tm =
  case strip_comb tm of
      (head, [predicate]) =>
        (case total Type.dom_rng (type_of predicate) of
             SOME (domain, range) =>
               let
                 val bound = genvar domain
                 val forall_head = #1 (strip_comb (mk_forall (bound, T)))
               in
                 if range = bool andalso same_const head forall_head then
                   SOME (bound, predicate)
                 else NONE
               end
           | NONE => NONE)
    | _ => NONE

fun GEN_NAMED_TAC name (asl, w) =
  case total dest_forall w of
      SOME (bound, _) =>
        Tactic.X_GEN_TAC (mk_var (name, type_of bound)) (asl, w)
    | NONE =>
        (case eta_forall_predicate w of
             NONE =>
               raise mk_HOL_ERR "clasetReplay" "GEN_NAMED_TAC"
                 "goal is not universally quantified"
           | SOME (bound, predicate) =>
               let
                 val variable = mk_var (name, type_of bound)
                 val child = (asl, mk_comb (predicate, variable))

                 fun validation [child_thm] =
                       Conv.CONV_RULE
                         (Conv.RAND_CONV Drule.ETA_CONV)
                         (GEN variable child_thm)
                   | validation _ =
                       raise mk_HOL_ERR "clasetReplay" "GEN_NAMED_TAC"
                         "validation received the wrong number of theorems"
               in
                 ([child], validation)
               end)

val GOAL_NEGATION_TAC = Tactic.CCONTR_TAC

fun SWAPPED_BUILTIN_TAC _ pos (asl, w) =
  let
    val negative = nth1 "SWAPPED_BUILTIN_TAC" asl pos
    val positive = dest_neg negative
    val child_asl =
      mk_neg w :: delete_nth "SWAPPED_BUILTIN_TAC" asl pos
    val child = (child_asl, positive)

    fun validation [positive_thm] =
          let
            val negative_thm = ASSUME negative
            val false_thm = MP (NOT_ELIM negative_thm) positive_thm
          in
            CCONTR w false_thm
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "SWAPPED_BUILTIN_TAC"
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

fun NORMALIZED_SWAPPED_BUILTIN_TAC _ pos (asl, w) =
  let
    fun normalize tm = rhs (concl (normalize_conv tm))

    fun prove_normalized asm target =
      let
        val equality = normalize_conv asm
        val theorem = EQ_MP equality (ASSUME asm)
      in
        if aconv (concl theorem) target then
          EQ_MP (ALPHA (concl theorem) target) theorem
        else
          raise mk_HOL_ERR "clasetReplay"
            "NORMALIZED_SWAPPED_BUILTIN_TAC"
            "replay normalization differs from search normalization"
      end

    val negative0 = nth1 "SWAPPED_BUILTIN_TAC" asl pos
    val negative = normalize negative0
    val positive = dest_neg negative
    val target = normalize w
    val remaining0 = delete_nth "SWAPPED_BUILTIN_TAC" asl pos
    val remaining = map normalize remaining0
    val child = (mk_neg target :: remaining, positive)

    fun validation [positive_thm] =
          let
            val restored =
              ListPair.foldlEq
                (fn (original, normalized, theorem) =>
                  Drule.PROVE_HYP
                    (prove_normalized original normalized) theorem)
                positive_thm (remaining0, remaining)
            val negative_thm = prove_normalized negative0 negative
            val false_thm = MP (NOT_ELIM negative_thm) restored
            val result = CCONTR target false_thm
            val target_equality = normalize_conv w
          in
            EQ_MP (SYM target_equality) result
          end
      | validation _ =
          raise mk_HOL_ERR "clasetReplay" "SWAPPED_BUILTIN_TAC"
            "validation received the wrong number of theorems"
  in
    ([child], validation)
  end

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

(* Rule replay can introduce alpha-renamed eigenvariables in a different
   positional order from search.  Keep the recorded position when possible,
   but recover by the semantic closing condition if that position drifted. *)
fun assumption_action pos store (goal as (asl, w)) =
  let
    val selected = nth1 "ASSUMPTION_TAC" asl pos
    fun closes asm = can (fn () => assumption_thm store asm w) ()
    fun find _ [] =
          raise mk_HOL_ERR "clasetReplay" "ASSUMPTION_TAC"
            "no assumption closes the replay goal"
      | find current (asm :: rest) =
          if closes asm then current else find (current + 1) rest
    val actual = if closes selected then pos else find 1 asl
  in
    ASSUMPTION_TAC store actual goal
  end

(* Exact reconstruction must reject a stale occurrence selector. *)
fun strict_assumption_action pos store goal =
  ASSUMPTION_TAC store pos goal
fun contradiction_action positions store =
  CONTRADICTION_TAC store positions
fun mp_action positions store = MP_TAC store positions
fun rule_action make store = RULE_TAC (make store)
fun forward_rule_action make store =
  FORWARD_RULE_TAC (make store)
fun blast_rule_action make store = BLAST_RULE_TAC (make store)
val hyp_subst_action = fn _ => HYP_SUBST_TAC
val blast_hyp_subst_action = fn _ => BLAST_HYP_SUBST_TAC
fun blast_hyp_subst_action_at fields _ =
  BLAST_HYP_SUBST_TAC_AT fields
val disch_action = fn _ => Tactic.DISCH_TAC
fun gen_action name _ = GEN_NAMED_TAC name
val goal_negation_action = fn _ => GOAL_NEGATION_TAC
fun swapped_builtin_action pos store =
  NORMALIZED_SWAPPED_BUILTIN_TAC store pos
fun move_assumption_to_back_action pos _ =
  MOVE_ASSUMPTION_TO_BACK_TAC pos
fun same_goal ((left_asl, left_w), (right_asl, right_w)) =
  aconv left_w right_w andalso
  ListPair.allEq (fn (left, right) => aconv left right)
    (left_asl, right_asl)

(* Opaque wrapper results mention the marked frees visible when the wrapper
   ran.  Replay may have grounded only some of them, so apply every binding
   the covering store already has to both the children and a theorem schema
   for the validation.  The schema makes instantiation happen before the
   opaque closure consumes the replayed child theorems. *)
fun grounded_fixed_action (goals, validation) store _ =
  let
    fun ground_goal (child_asl, child_w) =
      (map (clasetMeta.norm store) child_asl,
       clasetMeta.norm store child_w)
    val (type_subst, term_subst) = clasetMeta.collapse store

    fun package_term (child_asl, child_w) =
      List.foldr boolSyntax.mk_imp child_w child_asl

    fun assume_package (child as (child_asl, _)) =
      let
        fun apply_assumptions [] theorem = theorem
          | apply_assumptions (asm :: rest) theorem =
              apply_assumptions rest (MP theorem (ASSUME asm))
      in
        apply_assumptions child_asl (ASSUME (package_term child))
      end

    val validation_schema = validation (map assume_package goals)
    val grounded_schema =
      Drule.INST_TY_TERM (term_subst, type_subst) validation_schema

    fun ground_validation theorems =
      let
        fun package_theorem ((child_asl, _), theorem) =
          List.foldr (fn (asm, result) => DISCH asm result)
            theorem child_asl
        val packaged =
          ListPair.map package_theorem
            (map ground_goal goals, theorems)
      in
        List.foldl
          (fn (theorem, result) => Drule.PROVE_HYP theorem result)
          grounded_schema packaged
      end
  in
    (map ground_goal goals, ground_validation)
  end

fun fixed_action_on recorded result store current =
  if same_goal (recorded, current) then result
  else grounded_fixed_action result store current

(* Compatibility for callers that did not record the wrapper's input.  A
   marked direct replay keeps the symbolic result, as it did historically;
   complete engine records use [fixed_action_on]. *)
fun fixed_action (result as (goals, validation)) store (goal as (asl, w)) =
  let
    val input_terms = w :: asl
    val marked_input =
      List.exists clasetMeta.is_meta (free_varsl input_terms) orelse
      List.exists clasetMeta.is_tymeta
        (List.concat (map type_vars_in_term input_terms))
  in
    if marked_input then result
    else grounded_fixed_action (goals, validation) store goal
  end

fun empty count =
  if count < 0 then
    raise mk_HOL_ERR "clasetReplay" "empty" "negative root count"
  else
    Script
      {roots = List.tabulate (count, fn _ => NONE), length = 0,
       open_paths = List.tabulate (count, fn index => [index])}

fun open_goals (Script {open_paths, ...}) = List.length open_paths

fun replace_nth values index replacement =
  List.take (values, index) @ replacement :: List.drop (values, index + 1)

fun install path record roots =
  let
    fun descend [] _ =
          raise mk_HOL_ERR "clasetReplay" "append"
            "the target does not identify an open goal"
      | descend [index] options =
          (case List.nth (options, index) of
               NONE => replace_nth options index (SOME record)
             | SOME _ =>
                 raise mk_HOL_ERR "clasetReplay" "append"
                   "the target does not identify an open goal")
      | descend (index :: rest) options =
          (case List.nth (options, index) of
               NONE =>
                 raise mk_HOL_ERR "clasetReplay" "append"
                   "the target does not identify an open goal"
             | SOME
                 (StepRecord
                   {kind, target, consumed, created, eigenvariables,
                    validation, action, children}) =>
                 replace_nth options index
                   (SOME
                     (StepRecord
                       {kind = kind, target = target, consumed = consumed,
                        created = created,
                        eigenvariables = eigenvariables,
                        validation = validation, action = action,
                        children = descend rest children})))
  in
    descend path roots
    handle Subscript =>
      raise mk_HOL_ERR "clasetReplay" "append"
        "the target does not identify an open goal"
  end

fun record_open_paths base (StepRecord {children, ...}) =
  let
    fun enumerate _ [] = []
      | enumerate index (NONE :: rest) =
          (base @ [index]) :: enumerate (index + 1) rest
      | enumerate index (SOME child :: rest) =
          record_open_paths (base @ [index]) child @
          enumerate (index + 1) rest
  in
    enumerate 0 children
  end

fun append
      (Script {roots, length, open_paths}) record =
  let
    val target = target_of record
    val index = target - 1
    val path =
      if index < 0 then
        raise mk_HOL_ERR "clasetReplay" "append"
          "the target does not identify an open goal"
      else
        List.nth (open_paths, index)
        handle Subscript =>
          raise mk_HOL_ERR "clasetReplay" "append"
            "the target does not identify an open goal"
    val roots' = install path record roots
    val open_paths' =
      List.take (open_paths, index) @ record_open_paths path record @
      List.drop (open_paths, index + 1)
  in
    Script
      {roots = roots', length = length + 1, open_paths = open_paths'}
  end

fun script_length (Script {length, ...}) = length

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
  | kind_name (SwappedBuiltin pos) =
      "swapped-builtin " ^ Int.toString pos
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

fun to_string (Script {roots, ...}) =
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

fun replay
      (Grounded
        {store, script = script as Script {roots, ...}}) goal =
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
         message = message, script = to_string script})
       | error =>
    ReplayFailed
      (ReplayFailure
        {goal = goal, step = NONE,
         message = Feedback.exn_to_string error,
         script = to_string script})

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
