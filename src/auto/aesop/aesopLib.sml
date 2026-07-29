structure aesopLib :> aesopLib =
struct

open Abbrev HolKernel

type aesop_config = aesopSearch.aesop_config
type rphase = aesopRule.rphase
type rule = aesopRule.rule

val default_config = aesopSearch.default_config
val ERR = mk_HOL_ERR "aesopLib"

fun check_config function_name
      ({max_rapps, max_depth} : aesop_config) =
  if max_rapps < 0 then
    raise ERR function_name "max_rapps must not be negative"
  else if max_depth < 0 then
    raise ERR function_name "max_depth must not be negative"
  else
    ()

fun qvars_of store ({asl, w, ...} : clasetGoal.cgoal) =
  HOLset.fromList Term.compare
    (List.concat
      (map (clasetMeta.metas_of store) (w :: asl)))

fun rule_source claset simpset simp_controls
      ({mode, cgoal = cgoal as {asl, w, ...}, store} :
       {mode : clasetUnify.mode, cgoal : clasetGoal.cgoal,
        store : clasetMeta.store}) =
  aesopRule.claset_rules_with
    {claset = claset, mode = mode, conclusion = w,
     assumptions = asl, qvars = qvars_of store cgoal,
     simpset = simpset, simp_controls = simp_controls}

fun initial_tree goal =
  aesopTree.create
    {node = clasetGoal.from_goal goal, unsafe_cursor = []}

fun close_raw function_name config claset simpset simp_controls goal =
  let
    val _ = check_config function_name config
    val source = rule_source claset simpset simp_controls
  in
    case aesopSearch.search config source (initial_tree goal) of
        aesopSearch.SearchProved tree =>
          aesopSearch.REPLAY_TAC tree goal
      | aesopSearch.SearchFailed _ => Tactical.NO_TAC goal
  end

fun singleton_replay store record =
  clasetReplay.REPLAY_TAC
    (clasetReplay.ground store
      (clasetReplay.append (clasetReplay.empty 1) record))

fun replay_records store records =
  Tactical.EVERY (map (singleton_replay store) records)

fun direct_children tree rid =
  List.filter
    (fn id =>
      not (Option.isSome (#copy_of (aesopTree.goal tree id))))
    (aesopTree.rapp_goals tree rid)

(* Safe search starts from a kernel goal without engine metavariables.
   Match-mode rules therefore produce a deterministic proof tree whose open
   leaves are genuine HOL goals.  Replay each local single-goal script and
   compose its child validations positionally. *)
fun safe_replay tree =
  let
    fun replay_goal id =
      let
        val goal = aesopTree.goal tree id
        val (norm_records, norm_store, norm_proved) =
          case #norm goal of
              aesopTree.Unnormalised =>
                ([], aesopTree.active_store goal, false)
            | aesopTree.Normalised {records, store, ...} =>
                (records, store, false)
            | aesopTree.NormProved {records, store} =>
                (records, store, true)
        val norm_tactic = replay_records norm_store norm_records
      in
        if norm_proved then
          norm_tactic
        else
          case aesopTree.child_rapps tree id of
              [] => norm_tactic
            | [rid] =>
                let
                  val rapp = aesopTree.rapp tree rid
                  val children = direct_children tree rid
                  val application =
                    replay_records (#store rapp) (#records rapp)
                  val descendants =
                    Tactical.THENL
                      (application, map replay_goal children)
                in
                  Tactical.THEN (norm_tactic, descendants)
                end
            | _ =>
                raise ERR "safe_replay"
                  "safe search committed more than one rule application"
      end
  in
    replay_goal (aesopTree.root tree)
  end

fun safe_raw function_name config claset simpset simp_controls goal =
  let
    val _ = check_config function_name config
    val source = rule_source claset simpset simp_controls
    val tree = initial_tree goal
  in
    case
      aesopSearch.safe_saturate
        {max_depth = #max_depth config, rules = source} tree
    of
        aesopSearch.SafeSaturated saturated =>
          safe_replay saturated goal
      | aesopSearch.SafeDepthLimit _ => Tactical.NO_TAC goal
      | aesopSearch.SafeNormalisationLimit _ => Tactical.NO_TAC goal
  end

fun changed tactic =
  NTactical.DETERM
    (NTactical.NCHANGED (NTactical.LIFT tactic))

fun declaration_name_member claset name =
  List.exists
    (fn (_, (candidate, _)) => candidate = name)
    (clasetLib.rules_of claset)

fun fresh_marker_name claset index =
  let
    fun find current =
      let
        val name = "__aesop_marker_" ^ Int.toString current
      in
        if declaration_name_member claset name then find (current + 1)
        else name
      end
  in
    find index
  end

fun aesop_marker theorem =
  case clasetLib.destNorm theorem of
      SOME rule =>
        SOME
          ({kind = clasetRules.Norm, safe = false, prio = NONE},
           rule)
    | NONE =>
        (case clasetLib.destForward theorem of
             SOME rule =>
               SOME
                 ({kind = clasetRules.Forward, safe = false,
                   prio = NONE}, rule)
           | NONE =>
               (case clasetLib.destSForward theorem of
                    SOME rule =>
                      SOME
                        ({kind = clasetRules.Forward, safe = true,
                          prio = NONE}, rule)
                  | NONE => NONE))

fun process_aesop_markers theorems claset =
  let
    fun process _ current rest [] = (current, List.rev rest)
      | process index current rest (theorem :: remaining) =
          case aesop_marker theorem of
              NONE =>
                process index current (theorem :: rest) remaining
            | SOME (spec, rule) =>
                let
                  val name = fresh_marker_name current index
                  val current' =
                    clasetLib.add_rule spec (name, rule) current
                in
                  process (index + 1) current' rest remaining
                end
  in
    process 0 claset [] theorems
  end

fun process_args body base_claset base_simpset =
  markerLib.ABBRS_THEN
    (fn theorems =>
      let
        val
          {simp_rules, iff_rules, simp_controls,
           rest = classical_arguments} =
          clasetLib.classify_simp_args theorems
        val simp_simpset =
          simpLib.++
            (base_simpset, simpLib.rewrites simp_rules)
        val iff_declarations =
          map
            (fn (index, theorem) =>
              clasimpLib.iff_declaration
                ("__aesop_iff_arg_" ^ Int.toString index)
                theorem)
            (Lib.enumerate 0 iff_rules)
        val iff_claset =
          List.foldl
            (fn ({rules, ...}, current) =>
              clasimpLib.add_iff_rules rules current)
            base_claset iff_declarations
        val invocation_simpset =
          if null iff_declarations then simp_simpset
          else
            simpLib.++
              (simp_simpset,
               simpLib.rewrites
                 (List.rev (map #rewrite iff_declarations)))
        val (classical_claset, aesop_arguments) =
          clasetLib.process_claset_tags
            classical_arguments iff_claset
        val (invocation_claset, facts) =
          process_aesop_markers aesop_arguments classical_claset
      in
        Tactical.THEN
          (clasetLib.INSERT_FACTS_TAC facts,
           body invocation_claset invocation_simpset simp_controls)
      end)

fun CS_AESOP_TAC config claset simpset =
  Tactical.VALID
    (close_raw "CS_AESOP_TAC" config claset simpset [])

fun CS_AESOP_SAFE_TAC config claset simpset =
  Tactical.VALID
    (changed
      (safe_raw "CS_AESOP_SAFE_TAC" config claset simpset []))

fun AESOP_TAC theorems =
  Tactical.VALID
    (process_args
      (close_raw "AESOP_TAC" default_config)
      (clasetLib.the_claset ()) (aesopData.aesop_ss ())
      theorems)

fun AESOP_SAFE_TAC theorems =
  Tactical.VALID
    (changed
      (process_args
        (safe_raw "AESOP_SAFE_TAC" default_config)
        (clasetLib.the_claset ()) (aesopData.aesop_ss ())
        theorems))

fun augment_aesop {name, phase, tactic} =
  aesopRule.register_tactic_rule
    {name = name, phase = phase, tactic = tactic, index = NONE}

val cases_rule_for = aesopRule.cases_rule_for

end
