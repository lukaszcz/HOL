structure aesopSearch :> aesopSearch =
struct

open Abbrev HolKernel

type cgoal = clasetGoal.cgoal
type store = clasetMeta.store
type tree = aesopTree.tree
type gid = aesopTree.gid

type aesop_config = {max_rapps : int, max_depth : int}
val default_config : aesop_config = {max_rapps = 200, max_depth = 30}

type rule_source =
  {mode : clasetUnify.mode, cgoal : cgoal, store : store} ->
  aesopRule.ruleset

datatype next_outcome =
    QueueEmpty of tree
  | ReadyForUnsafe of {goal : gid, tree : tree}
  | DepthLimit of {goal : gid, tree : tree}
  | NormalisationLimit of
      {goal : gid, tree : tree, iterations : int, rule : string}

datatype safe_outcome =
    SafeSaturated of tree
  | SafeDepthLimit of {goal : gid, tree : tree}
  | SafeNormalisationLimit of
      {goal : gid, tree : tree, iterations : int, rule : string}

datatype failure_reason =
    SearchExhausted
  | RappLimitReached
  | DepthLimitReached

datatype search_outcome =
    SearchProved of tree
  | SearchFailed of
      {tree : tree, safe_goals : (gid * cgoal) list,
       reason : failure_reason}

datatype application =
    Inapplicable
  | Applied of aesopTree.rapp_data

datatype safe_phase =
    Committed of tree
  | Deferred of aesopTree.rapp_data list

datatype unsafe_candidate =
    Stored of aesopTree.rapp_data
  | Rule of aesopRule.rule

val ERR = mk_HOL_ERR "aesopSearch"
val postponed_percent = 90

fun trace level message =
  if level <= Feedback.current_trace "aesop" then
    Feedback.HOL_MESG ("Aesop: " ^ message ())
  else ()

fun cgoal_string ({params, asl, w} : cgoal) =
  let
    val parameters =
      if null params then ""
      else
        "{" ^ String.concatWith ", " (map Parse.term_to_string params) ^
        "} "
    val assumptions =
      String.concatWith ", " (map Parse.term_to_string asl)
  in
    parameters ^ "[" ^ assumptions ^ "] ?- " ^ Parse.term_to_string w
  end

fun trace_goal label tree id =
  let val goal = aesopTree.goal tree id
  in
    trace 3
      (fn () =>
        label ^ " goal " ^ Int.toString id ^
        ", level=" ^ Int.toString (#level goal) ^
        ", priority=" ^ Real.toString (#prio goal) ^ ": " ^
        cgoal_string (aesopTree.active_cgoal goal))
  end

fun make_node (goal as {level, ...} : aesopTree.goal) =
  clasetGoal.create
    {goals = [aesopTree.active_cgoal goal],
     store = aesopTree.active_store goal, level = level + 1}

fun new_free_names (asl, w) goals =
  let
    val old_frees = free_varsl (w :: asl)
    fun is_new variable =
      not (List.exists (fn old => aconv variable old) old_frees)
    fun names (child_asl, child_w) =
      map (fst o dest_var)
        (List.filter is_new (free_varsl (child_w :: child_asl)))
  in
    map names goals
  end

fun rendered_result node (result as (goals, validation)) =
  case clasetGoal.unrender node 1 result of
      NONE => NONE
    | SOME next =>
        let
          val rendered = clasetGoal.render node 1
          val record =
            clasetReplay.make_record
              {kind = clasetReplay.Wrapper, target = 1,
               consumed = NONE,
               created = {terms = [], types = []},
               eigenvariables = new_free_names rendered goals,
               validation = validation,
               action = clasetReplay.fixed_action result,
               children = map (fn _ => NONE) goals}
        in
          SOME ([record], next)
        end

fun engine_results step node =
  seq.map
    (fn (record, next) => ([record], next))
    (step (node, 1))

fun rendered_results tactic node =
  seq.mapPartial (rendered_result node)
    (tactic (clasetGoal.render node 1))

fun append_sequences [] = seq.empty
  | append_sequences (first :: rest) =
      seq.append first
        (seq.delay (fn () => append_sequences rest))

fun application_results
      ({apply, ...} : aesopRule.rule) node =
  case apply of
      aesopRule.EngineStep step => engine_results step node
    | aesopRule.RenderedTactic tactic =>
        rendered_results tactic node
    | aesopRule.MultiStep steps =>
        append_sequences (map (fn step => engine_results step node) steps)

fun changed node next =
  null (clasetGoal.goals next) orelse
  not (clasetGoal.equal (node, next))

(* Safe applications are committed only when the rule has exactly one
   alternative.  Looking at two results is sufficient and does not force
   an otherwise lazy rule sequence. *)
fun deterministic_application rule node =
  (case seq.take 2 (application_results rule node) of
       [(records, next)] =>
         if changed node next then
           Applied
             {rule = #name rule, phase = #phase rule,
              records = records, node = next, forwarded = NONE}
         else Inapplicable
     | _ => Inapplicable)
  handle HOL_ERR _ => Inapplicable
       | Match => Inapplicable

fun forward_candidate parent node =
  case clasetGoal.goals node of
      [{asl = added :: rest, ...}] =>
        if length rest = length (#asl parent) then SOME added
        else NONE
    | _ => NONE

fun admissible_forward goal rule
      ({node, ...} : aesopTree.rapp_data) =
  if not (#once rule) then SOME NONE
  else
    case forward_candidate (aesopTree.active_cgoal goal) node of
        NONE => NONE
      | SOME added =>
          if
            aesopRule.forward_duplicate
              (clasetGoal.store node) (#forwarded goal) added
          then NONE
          else SOME (SOME added)

fun copies_in tree ids =
  length
    (List.filter
      (fn id => Option.isSome (#copy_of (aesopTree.goal tree id))) ids)

fun trace_install data result =
  let
    val count = copies_in (#tree result) (#goals result)
  in
    trace 2
      (fn () =>
        "installed " ^ #rule data ^ " below goal " ^
        Int.toString
        (#parent (aesopTree.rapp (#tree result) (#rapp result))) ^
        " with " ^ Int.toString (length (#goals result)) ^
        " child goal(s)");
    if count = 0 then ()
    else
      trace 2
        (fn () =>
          "copied " ^ Int.toString count ^
          " metavariable-coupled goal(s)")
  end

fun data_with_forwarded
      ({rule, phase, records, node, ...} : aesopTree.rapp_data)
      forwarded : aesopTree.rapp_data =
  {rule = rule, phase = phase, records = records, node = node,
   forwarded = forwarded}

fun data_with_phase
      ({rule, records, node, forwarded, ...} : aesopTree.rapp_data)
      phase : aesopTree.rapp_data =
  {rule = rule, phase = phase, records = records, node = node,
   forwarded = forwarded}

fun install_committed id data tree =
  let
    val installed = aesopTree.install_rapp id data tree
    val _ = trace_install data installed
  in
    #tree installed
    |> aesopTree.set_postponed id []
    |> aesopTree.set_unsafe_cursor id []
    |> aesopTree.set_safe_done id true
  end

fun application_assigned goal
      ({node, ...} : aesopTree.rapp_data) =
  not
    (aesopTree.dependencies_empty
      (aesopTree.assigned_between
        (aesopTree.active_store goal) (clasetGoal.store node)))

fun safe_phase id rules tree =
  let
    val goal = aesopTree.goal tree id
    val node = make_node goal
    val has_dependencies =
      not (aesopTree.dependencies_empty (#deps goal))

    fun scan postponed [] = Deferred (List.rev postponed)
      | scan postponed (rule :: rest) =
          if #phase rule <> aesopRule.RSafe then
            scan postponed rest
          else
            case deterministic_application rule node of
                Inapplicable => scan postponed rest
              | Applied data =>
                  (case admissible_forward goal rule data of
                       NONE => scan postponed rest
                     | SOME added =>
                        let val data' = data_with_forwarded data added
                        in
                         if
                           has_dependencies andalso
                           application_assigned goal data
                         then scan (data' :: postponed) rest
                         else
                           Committed
                             (install_committed id data' tree)
                        end)
  in
    scan [] rules
  end

fun rule_input mode goal =
  {mode = mode, cgoal = aesopTree.active_cgoal goal,
   store = aesopTree.active_store goal}

fun selected_mode goal =
  if aesopTree.dependencies_empty (#deps goal) then
    clasetUnify.Match
  else
    clasetUnify.Unify

fun prepare_unsafe id postponed source tree =
  let
    val current = aesopTree.goal tree id
    val unsafe = #unsafe (source (rule_input clasetUnify.Unify current))
  in
    tree
    |> aesopTree.set_postponed id postponed
    |> aesopTree.set_unsafe_cursor id unsafe
    |> aesopTree.set_safe_done id true
  end

fun next_safe_with include_irrelevant pop_goal
      (config as {max_depth, rules = source}) tree =
  case pop_goal tree of
      (NONE, remaining) => QueueEmpty remaining
    | (SOME id, remaining) =>
        let
          val initial_goal = aesopTree.goal remaining id
          val _ = trace 2
            (fn () => "expanding goal " ^ Int.toString id)
          val _ = trace_goal "candidate" remaining id
          val norm_rules =
            #norm (source (rule_input clasetUnify.Match initial_goal))
        in
          if #level initial_goal >= max_depth then
            DepthLimit {goal = id, tree = remaining}
          else case
            aesopNorm.normalise
              {max_depth = max_depth, rules = norm_rules}
              id remaining
          of
              aesopNorm.IterationLimit
                {tree = limited, iterations, rule} =>
                  NormalisationLimit
                    {goal = id, tree = limited,
                     iterations = iterations, rule = rule}
            | aesopNorm.Complete {tree = normalised, ...} =>
                let val goal = aesopTree.goal normalised id
                in
                  if
                    #state goal <> aesopTree.Unknown orelse
                    (not include_irrelevant andalso
                     aesopTree.goal_irrelevant normalised id)
                  then
                    next_safe_with include_irrelevant pop_goal
                      config normalised
                  else if #safe_done goal then
                    ReadyForUnsafe {goal = id, tree = normalised}
                  else
                    let
                      val safe =
                        aesopRule.safe_rules
                          (#safe
                            (source
                              (rule_input (selected_mode goal) goal)))
                    in
                      case safe_phase id safe normalised of
                          Committed installed =>
                            next_safe_with include_irrelevant pop_goal
                              config installed
                        | Deferred postponed =>
                            ReadyForUnsafe
                              {goal = id,
                               tree =
                                 prepare_unsafe id postponed source
                                   normalised}
                    end
                end
        end

fun next_safe config tree =
  next_safe_with false aesopTree.pop_goal config tree

fun next_safe_including_irrelevant config tree =
  next_safe_with true aesopTree.pop_goal_including_irrelevant config tree

fun safe_saturate config tree =
  let
    fun saturate current =
      case next_safe_including_irrelevant config current of
          QueueEmpty saturated => SafeSaturated saturated
        | ReadyForUnsafe {tree = remaining, ...} =>
            saturate remaining
        | DepthLimit result => SafeDepthLimit result
        | NormalisationLimit result =>
            SafeNormalisationLimit result
  in
    saturate tree
  end

fun proved_ancestor tree (goal : aesopTree.goal) =
  case #parent goal of
      NONE => false
    | SOME parent =>
        let
          val parent_goal =
            aesopTree.goal tree (#parent (aesopTree.rapp tree parent))
        in
          #state (aesopTree.cluster tree (#cluster goal)) =
            aesopTree.Proved orelse
          #state parent_goal = aesopTree.Proved orelse
          proved_ancestor tree parent_goal
        end

fun frontier_goal tree (goal : aesopTree.goal) =
  #safe_done goal andalso
  null (aesopTree.child_rapps tree (#id goal)) andalso
  not (proved_ancestor tree goal) andalso
  (case #norm goal of
       aesopTree.NormProved _ => false
     | _ => true)

fun cgoal_under store ({params, asl, w} : cgoal) : cgoal =
  {params = map (clasetMeta.norm store) params,
   asl = map (clasetMeta.norm store) asl,
   w = clasetMeta.norm store w}

fun safe_frontier tree =
  map
    (fn goal =>
      (#id goal,
       cgoal_under (aesopTree.active_store goal)
         (aesopTree.active_cgoal goal)))
    (List.filter (frontier_goal tree) (aesopTree.goals tree))

fun unsafe_percent ({phase = aesopRule.RUnsafe percent, ...} :
                    aesopRule.rule) =
      percent
  | unsafe_percent _ =
      raise ERR "unsafe_percent" "a non-unsafe rule reached the unsafe phase"

fun choose_unsafe (goal : aesopTree.goal) =
  case (#unsafe_cursor goal, #postponed goal) of
      ([], []) => NONE
    | ([], stored :: postponed) =>
        SOME
          (Stored stored, [], postponed)
    | (rule :: unsafe, []) =>
        SOME
          (Rule rule, unsafe, [])
    | (rule :: unsafe, stored :: postponed) =>
        if unsafe_percent rule >= postponed_percent then
          SOME
            (Rule rule, unsafe, stored :: postponed)
        else
          SOME
            (Stored stored, rule :: unsafe, postponed)

fun drain sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: drain rest

fun unsafe_applications goal rule =
  let
    val node = make_node goal

    fun prepare (records, next) =
      if not (changed node next) then NONE
      else
        let
          val data : aesopTree.rapp_data =
            {rule = #name rule, phase = #phase rule,
             records = records, node = next, forwarded = NONE}
        in
          Option.map
            (fn added => data_with_forwarded data added)
            (admissible_forward goal rule data)
        end
  in
    List.mapPartial prepare
      (drain (application_results rule node))
  end
  handle HOL_ERR _ => []
       | Match => []

fun stored_application data =
  [data_with_phase data (aesopRule.RUnsafe postponed_percent)]

fun install_alternatives id data tree =
  let
    fun install (application, current) =
      let
        val result = aesopTree.install_rapp id application current
        val _ = trace_install application result
      in
        #tree result
      end
  in
    List.foldl install tree data
  end

fun candidates_remain tree id =
  let val goal = aesopTree.goal tree id
  in
    not (null (#unsafe_cursor goal)) orelse
    not (null (#postponed goal))
  end

datatype unsafe_outcome =
    UnsafeContinue of tree
  | UnsafeRappLimit of tree

fun unsafe_phase {max_rapps, ...} id tree =
  let val goal = aesopTree.goal tree id
  in
    case choose_unsafe goal of
        NONE =>
          UnsafeContinue (aesopTree.exhaust_goal id tree)
      | SOME (candidate, unsafe, postponed) =>
          let
            val (name, applications) =
              case candidate of
                  Stored data =>
                    (#rule data ^ " (postponed)",
                     stored_application data)
                | Rule rule =>
                    (#name rule, unsafe_applications goal rule)
            val count = length (aesopTree.rapps tree)
            val needed = length applications
            val _ =
              trace 2
                (fn () =>
                  "unsafe rule " ^ name ^ " produced " ^
                  Int.toString needed ^ " rapp(s)")
          in
            if needed > 0 andalso count + needed > max_rapps then
              UnsafeRappLimit tree
            else
              let
                val installed =
                  install_alternatives id applications tree
                  |> aesopTree.set_unsafe_cursor id unsafe
                  |> aesopTree.set_postponed id postponed
                val current = aesopTree.goal installed id
                val queued =
                  if #state current = aesopTree.Unknown andalso
                     candidates_remain installed id
                  then aesopTree.enqueue_goal id installed
                  else installed
              in
                UnsafeContinue queued
              end
          end
  end

fun safe_completion {max_depth, rules} tree =
  let
    fun complete current =
      case
        next_safe_including_irrelevant
          {max_depth = max_depth, rules = rules} current
      of
          QueueEmpty saturated => saturated
        | ReadyForUnsafe {tree = remaining, ...} =>
            complete remaining
        | DepthLimit {goal, tree = limited} =>
            complete (aesopTree.exhaust_goal goal limited)
        | NormalisationLimit {goal, tree = limited, ...} =>
            complete (aesopTree.exhaust_goal goal limited)
  in
    complete tree
  end

fun reason_string SearchExhausted = "search exhausted"
  | reason_string RappLimitReached = "rapp limit reached"
  | reason_string DepthLimitReached = "depth limit reached"

fun report_failure reason safe_goals =
  (trace 1
     (fn () =>
       reason_string reason ^ "; " ^
       Int.toString (length safe_goals) ^ " safe goal(s)");
   List.app
     (fn (id, cgoal) =>
       trace 1
         (fn () =>
           "safe goal " ^ Int.toString id ^ ": " ^
           cgoal_string cgoal))
     safe_goals)

fun search
      (config as {max_rapps, max_depth} : aesop_config)
      rules initial =
  if max_rapps < 0 then
    raise ERR "search" "max_rapps must not be negative"
  else if max_depth < 0 then
    raise ERR "search" "max_depth must not be negative"
  else
    let
      fun failed reason tree =
        let
          val safe_tree =
            safe_completion {max_depth = max_depth, rules = rules}
              initial
          val safe_goals = safe_frontier safe_tree
          val _ = report_failure reason safe_goals
        in
          SearchFailed
            {tree = tree, safe_goals = safe_goals, reason = reason}
        end

      fun loop depth_limited tree =
        if
          #state (aesopTree.goal tree (aesopTree.root tree)) =
          aesopTree.Proved
        then
          (trace 1
             (fn () =>
               "search proved the root with " ^
               Int.toString (length (aesopTree.rapps tree)) ^
               " rapp(s)");
           SearchProved tree)
        else
          case
            next_safe {max_depth = max_depth, rules = rules} tree
          of
              QueueEmpty exhausted =>
                if
                  #state
                    (aesopTree.goal exhausted
                      (aesopTree.root exhausted)) =
                  aesopTree.Proved
                then loop depth_limited exhausted
                else
                  failed
                    (if depth_limited then DepthLimitReached
                     else SearchExhausted)
                    exhausted
            | DepthLimit {goal, tree = limited} =>
                (trace 2
                   (fn () =>
                     "depth limit stopped goal " ^
                     Int.toString goal);
                 loop true (aesopTree.exhaust_goal goal limited))
            | NormalisationLimit
                {goal, tree = limited, iterations, rule} =>
                (trace 2
                   (fn () =>
                     "normalisation limit stopped goal " ^
                     Int.toString goal ^ " after " ^
                     Int.toString iterations ^
                     " iteration(s), next rule " ^ rule);
                 loop true (aesopTree.exhaust_goal goal limited))
            | ReadyForUnsafe {goal, tree = ready} =>
                (case unsafe_phase config goal ready of
                     UnsafeContinue next => loop depth_limited next
                   | UnsafeRappLimit limited =>
                       failed RappLimitReached limited)
    in
      loop false initial
    end

fun proved_rapp tree id =
  case
    List.find
      (fn rid => #state (aesopTree.rapp tree rid) = aesopTree.Proved)
      (aesopTree.child_rapps tree id)
  of
      SOME rid => rid
    | NONE =>
        raise ERR "extract"
          ("proved goal " ^ Int.toString id ^
           " has no proved rule application")

fun proved_cluster_goal tree id =
  let val current = aesopTree.cluster tree id
  in
    case
      List.find
        (fn gid => #state (aesopTree.goal tree gid) = aesopTree.Proved)
        (#goals current)
    of
        SOME gid => gid
      | NONE =>
          raise ERR "extract"
            ("proved cluster " ^ Int.toString id ^
             " has no proved goal")
  end

fun direct_children tree rid =
  List.filter
    (fn id =>
      not (Option.isSome (#copy_of (aesopTree.goal tree id))))
    (aesopTree.rapp_goals tree rid)

(* A copied goal discharges the corresponding original sibling, but it is
   not a child emitted by the rule action that caused the copy.  First
   select the complete winning forest and record this redirection.  The
   later linearisation can then replay only real action children, in their
   original positional order. *)
fun winning_forest tree =
  let
    type selection = (gid, gid) Redblackmap.dict
    val empty_selection : selection = Redblackmap.mkDict Int.compare

    fun select actual (selection, stores) =
      let
        val current = aesopTree.goal tree actual
        val original =
          case #copy_of current of
              NONE => actual
            | SOME id => id
        val selection' =
          case Redblackmap.peek (selection, original) of
              NONE =>
                Redblackmap.insert (selection, original, actual)
            | SOME previous =>
                if previous = actual then selection
                else
                  raise ERR "extract"
                    ("winning forest selects goal " ^
                     Int.toString original ^ " twice")
      in
        case #norm current of
            aesopTree.NormProved {store, ...} =>
              (selection', store :: stores)
          | _ =>
              let
                val rid = proved_rapp tree actual
                val application = aesopTree.rapp tree rid
                fun select_cluster
                      (cid, accumulated) =
                  let
                    val cluster = aesopTree.cluster tree cid
                    val _ =
                      if #state cluster = aesopTree.Proved then ()
                      else
                        raise ERR "extract"
                          ("winning rule application contains unproved " ^
                           "cluster " ^ Int.toString cid)
                  in
                    select (proved_cluster_goal tree cid) accumulated
                  end
              in
                if null (#clusters application) then
                  (selection', #store application :: stores)
                else
                  List.foldl select_cluster
                    (selection', stores) (#clusters application)
              end
      end

    val root = aesopTree.root tree
    val root_goal = aesopTree.goal tree root
    val _ =
      if #state root_goal = aesopTree.Proved then ()
      else raise ERR "extract" "the root goal is not proved"
  in
    select root (empty_selection, [])
  end

fun selected_goal selection original =
  case Redblackmap.peek (selection, original) of
      SOME actual => actual
    | NONE =>
        raise ERR "extract"
          ("winning forest has no proof of goal " ^
           Int.toString original)

fun append_records records script =
  List.foldl
    (fn (record, current) =>
      if clasetReplay.target_of record = 1 then
        clasetReplay.append current record
      else
        raise ERR "extract"
          "a recorded single-goal action does not target position 1")
    script records

fun extract tree =
  let
    val (selection, final_stores) = winning_forest tree
    val root = aesopTree.root tree
    val root_store = #store (aesopTree.goal tree root)
    val covering_store =
      clasetMeta.absorb
        {base = root_store, extensions = final_stores}

    fun linearise original ancestors script =
      let
        val actual = selected_goal selection original
        val _ =
          if List.exists (fn id => id = actual) ancestors then
            raise ERR "extract" "cycle in the winning forest"
          else ()
        val current = aesopTree.goal tree actual
        val with_norm =
          case #norm current of
              aesopTree.Unnormalised => script
            | aesopTree.Normalised {records, ...} =>
                append_records records script
            | aesopTree.NormProved {records, ...} =>
                append_records records script
      in
        case #norm current of
            aesopTree.NormProved _ => with_norm
          | _ =>
              let
                val rid = proved_rapp tree actual
                val application = aesopTree.rapp tree rid
                val with_application =
                  append_records (#records application) with_norm
              in
                List.foldl
                  (fn (child, accumulated) =>
                    linearise child (actual :: ancestors) accumulated)
                  with_application (direct_children tree rid)
              end
      end

    val script =
      linearise root [] (clasetReplay.empty 1)
  in
    clasetReplay.ground covering_store script
  end

fun REPLAY_TAC tree goal =
  let
    val grounded = extract tree
    val result as (goals, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
    val _ =
      if null goals then ()
      else
        raise ERR "REPLAY_TAC"
          "kernel replay of a proved search tree left open goals"
  in
    result
  end
  handle error =>
    raise ERR "REPLAY_TAC"
      ("kernel replay of a proved search tree failed; this is an " ^
       "aesop engine bug: " ^ Feedback.exn_to_string error)

end
