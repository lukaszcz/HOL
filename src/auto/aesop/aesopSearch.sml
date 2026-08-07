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
      {tree : tree, safe_goals : unit -> (gid * cgoal) list,
       reason : failure_reason}

datatype safe_phase =
    Committed of tree
  | Deferred of aesopTree.rapp_data list
  | CommitLimit of tree

exception SafeRappLimitReached of tree

datatype unsafe_candidate =
    Stored of aesopTree.rapp_data
  | Rule of aesopRule.rule

val ERR = mk_HOL_ERR "aesopSearch"
val postponed_percent = 90

fun traced level = level <= Feedback.current_trace "aesop"

fun trace level message =
  if traced level then Feedback.HOL_MESG ("Aesop: " ^ message ())
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

fun application_data ({name, phase, ...} : aesopRule.rule)
      (records, next) : aesopTree.rapp_data =
  {rule = name, phase = phase, records = records, node = next,
   forwarded = NONE}

(* The safe phase walks a rule's alternatives one at a time, so a rule that
   raises where the engine expects a sequence has to be read there as
   offering no further alternative.  Only the two exceptions the rule
   vocabulary uses to say "inapplicable" are read that way. *)
fun next_application alternatives =
  seq.cases alternatives
  handle HOL_ERR _ => NONE
       | Match => NONE

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
  (trace 2
     (fn () =>
       "installed " ^ #rule data ^ " below goal " ^
       Int.toString
       (#parent (aesopTree.rapp (#tree result) (#rapp result))) ^
       " with " ^ Int.toString (length (#goals result)) ^
       " child goal(s)");
   if not (traced 2) then ()
   else
     case copies_in (#tree result) (#goals result) of
         0 => ()
       | count =>
           trace 2
             (fn () =>
               "copied " ^ Int.toString count ^
               " metavariable-coupled goal(s)"))

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
    aesopTree.set_search_state id
      {safe_done = true, unsafe_cursor = [], postponed = []}
      (#tree installed)
  end

fun application_assigned goal
      ({node, ...} : aesopTree.rapp_data) =
  not
    (aesopTree.dependencies_empty
      (aesopTree.assigned_between
        (aesopTree.active_store goal) (clasetGoal.store node)))

(* A forward rule neither consumes nor rewrites what it matched, and its
   alternatives are confluent: taking one leaves all the others available
   at the child goal, where the [once] duplicate filter offers exactly the
   conclusions not yet added.  Committing to the first admissible
   alternative therefore installs every alternative, one per safe step,
   along the single committed branch that the safe phase and its replay
   require -- where demanding determinism would silence the rule outright.
   For any other safe rule a second alternative is a genuine choice that
   the safe phase must not make, so such a rule applies only when it has
   exactly one. *)
fun safe_alternatives (rule : aesopRule.rule) node =
  (* Delayed, so that a rule which raises while producing its sequence at
     all is caught by the walk over that sequence. *)
  if #once rule then
    seq.delay (fn () => aesopTree.rule_results rule node)
  else
    case
      (aesopTree.unique_rule_result rule node
       handle HOL_ERR _ => NONE
            | Match => NONE)
    of
        NONE => seq.empty
      | SOME result => seq.result result

fun safe_phase max_rapps id rules tree =
  let
    val goal = aesopTree.goal tree id
    val node = aesopTree.child_node goal
    val has_dependencies =
      not (aesopTree.dependencies_empty (#deps goal))
    (* The tree is fixed for the whole scan, so its budget is decided once
       rather than once per rule. *)
    val at_rapp_limit =
      case max_rapps of
          NONE => false
        | SOME limit => aesopTree.rapp_count tree >= limit

    fun scan postponed [] = Deferred (List.rev postponed)
      | scan postponed (rule :: rest) =
          if #phase rule <> aesopRule.RSafe then
            scan postponed rest
          else
            consider rule rest postponed (safe_alternatives rule node)

    and consider rule rest postponed alternatives =
          case next_application alternatives of
              NONE => scan postponed rest
            | SOME (result, remaining) =>
                let
                  val (_, next) = result
                in
                  if not (aesopTree.changed node next) then
                    consider rule rest postponed remaining
                  else
                    let val data = application_data rule result
                    in
                      case admissible_forward goal rule data of
                          NONE => consider rule rest postponed remaining
                        | SOME added =>
                            let
                              val data' = data_with_forwarded data added
                            in
                              if
                                has_dependencies andalso
                                application_assigned goal data
                              then
                                consider rule rest (data' :: postponed)
                                  remaining
                              else if at_rapp_limit then CommitLimit tree
                              else
                                Committed
                                  (install_committed id data' tree)
                            end
                    end
                end
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

(* Building a ruleset retrieves candidates for the conclusion and for every
   assumption, so a goal expansion shares the one build across the phases
   whose inputs coincide.  [source] is a function of that input record, and
   the three inputs differ: normalisation sees the goal before it is
   normalised and always matches, the safe phase sees it afterwards and
   unifies once the goal has dependencies, and the unsafe cursor always
   unifies.  Normalisation leaving the goal alone is exactly [iterations =
   0], and the safe phase then agrees with it whenever it too matches. *)
fun phase_rules source initial_rules initial_iterations goal mode =
  if initial_iterations = 0 andalso mode = clasetUnify.Match then
    initial_rules
  else
    source (rule_input mode goal)

fun unsafe_cursor_rules source rules goal mode =
  #unsafe
    (if mode = clasetUnify.Unify then rules
     else source (rule_input clasetUnify.Unify goal))

fun next_safe_with include_irrelevant pop_goal
      (config as {max_depth, max_rapps, rules = source}) tree =
  case pop_goal tree of
      (NONE, remaining) => QueueEmpty remaining
    | (SOME id, remaining) =>
        let
          val initial_goal = aesopTree.goal remaining id
          val _ = trace 2
            (fn () => "expanding goal " ^ Int.toString id)
          val _ = trace_goal "candidate" remaining id
        in
          if #level initial_goal >= max_depth then
            DepthLimit {goal = id, tree = remaining}
          else
            let
              val initial_rules =
                source (rule_input clasetUnify.Match initial_goal)
            in
              case
                aesopNorm.normalise
                  {max_depth = max_depth, rules = #norm initial_rules}
                  id remaining
              of
                  aesopNorm.IterationLimit
                    {tree = limited, iterations, rule} =>
                      NormalisationLimit
                        {goal = id, tree = limited,
                         iterations = iterations, rule = rule}
                | aesopNorm.Complete {tree = normalised, iterations} =>
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
                          val mode = selected_mode goal
                          val rules =
                            phase_rules source initial_rules iterations
                              goal mode
                          val safe = aesopRule.safe_rules (#safe rules)
                        in
                          case safe_phase max_rapps id safe normalised of
                              Committed installed =>
                                next_safe_with include_irrelevant pop_goal
                                  config installed
                            | CommitLimit limited =>
                                raise SafeRappLimitReached limited
                            | Deferred postponed =>
                                ReadyForUnsafe
                                  {goal = id,
                                   tree =
                                     aesopTree.set_search_state id
                                       {safe_done = true,
                                        unsafe_cursor =
                                          unsafe_cursor_rules source
                                            rules goal mode,
                                        postponed = postponed}
                                       normalised}
                        end
                    end
            end
        end

fun next_safe_including_irrelevant {max_depth, rules} tree =
  next_safe_with true aesopTree.pop_goal_including_irrelevant
    {max_rapps = NONE, max_depth = max_depth, rules = rules}
    tree

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

fun safe_frontier tree =
  map
    (fn goal =>
      (#id goal,
       aesopTree.cgoal_under (aesopTree.active_store goal)
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
    val node = aesopTree.child_node goal

    fun prepare (result as (_, next)) =
      if not (aesopTree.changed node next) then NONE
      else
        let
          val data = application_data rule result
        in
          Option.map
            (fn added => data_with_forwarded data added)
            (admissible_forward goal rule data)
        end
  in
    List.mapPartial prepare
      (drain (aesopTree.rule_results rule node))
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
  | UnsafeRappSkipped of tree

datatype bounded_safe_outcome =
    BoundedSafe of next_outcome
  | BoundedSafeRappLimit of tree

fun bounded_safe_phase max_rapps max_depth rules tree =
  BoundedSafe
    (next_safe_with false aesopTree.pop_goal
      {max_depth = max_depth, max_rapps = SOME max_rapps,
       rules = rules} tree)
  handle SafeRappLimitReached limited =>
    BoundedSafeRappLimit limited

fun unsafe_phase {max_rapps, ...} id tree =
  let val goal = aesopTree.goal tree id
  in
    case choose_unsafe goal of
        NONE =>
          UnsafeContinue (aesopTree.exhaust_goal id tree)
      | SOME (candidate, unsafe, postponed) =>
          let
            val (name, offered) =
              case candidate of
                  Stored data =>
                    (#rule data ^ " (postponed)",
                     stored_application data)
                | Rule rule =>
                    (#name rule, unsafe_applications goal rule)
            val needed = length offered
            val _ =
              trace 2
                (fn () =>
                  "unsafe rule " ^ name ^ " produced " ^
                  Int.toString needed ^ " rapp(s)")
            (* The cap is global and the tree only grows, so a rule whose
               alternatives do not all fit now never fits later either.
               Installing a prefix of them would make the search silently
               incomplete in a way that depends on their order, so the rule
               is skipped here as inapplicable and the next candidate is
               tried.  The skip is reported, and the search blames the cap
               only if no rule closes the goal. *)
            val skipped =
              needed > 0 andalso
              aesopTree.rapp_count tree + needed > max_rapps
            val _ =
              if not skipped then ()
              else
                trace 2
                  (fn () =>
                    "unsafe rule " ^ name ^ " skipped: its " ^
                    Int.toString needed ^ " rapp(s) exceed the limit of " ^
                    Int.toString max_rapps)
            val applications = if skipped then [] else offered
            val extended = install_alternatives id applications tree
            val installed =
              aesopTree.set_search_state id
                {safe_done = #safe_done (aesopTree.goal extended id),
                 unsafe_cursor = unsafe, postponed = postponed}
                extended
            val current = aesopTree.goal installed id
            val queued =
              if #state current = aesopTree.Unknown andalso
                 candidates_remain installed id
              then aesopTree.enqueue_goal id installed
              else installed
          in
            if skipped then UnsafeRappSkipped queued
            else UnsafeContinue queued
          end
  end

fun safe_completion {max_depth, rules} tree =
  let
    fun complete current =
      case
        next_safe_with true aesopTree.pop_goal_including_irrelevant
          {max_depth = max_depth, max_rapps = NONE, rules = rules}
          current
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

(* The frontier is a whole second search, so do not force the thunk unless
   the trace that consumes it will actually print. *)
fun report_failure reason frontier =
  if not (traced 1) then ()
  else
    let
      val safe_goals = frontier ()
    in
      trace 1
        (fn () =>
          reason_string reason ^ "; " ^
          Int.toString (length safe_goals) ^ " safe goal(s)");
      List.app
        (fn (id, cgoal) =>
          trace 1
            (fn () =>
              "safe goal " ^ Int.toString id ^ ": " ^
              cgoal_string cgoal))
        safe_goals
    end

fun search
      (config as {max_rapps, max_depth} : aesop_config)
      rules initial =
  if max_rapps < 0 then
    raise ERR "search" "max_rapps must not be negative"
  else if max_depth < 0 then
    raise ERR "search" "max_depth must not be negative"
  else
    let
      (* [initial], not [tree]: the report is deliberately the safe-only
         frontier of the original goal, unpolluted by unsafe rapps and
         exhausted branches. *)
      fun failed reason tree =
        let
          fun frontier () =
            safe_frontier
              (safe_completion {max_depth = max_depth, rules = rules}
                 initial)
          val _ = report_failure reason frontier
        in
          SearchFailed
            {tree = tree, safe_goals = frontier, reason = reason}
        end

      (* An exhausted search that had to step around a limit did not
         exhaust the rules.  The rapp cap bounds the whole search where the
         depth limit bounds one branch, so it is reported first. *)
      fun exhausted_reason {depth_limited, rapp_limited} =
        if rapp_limited then RappLimitReached
        else if depth_limited then DepthLimitReached
        else SearchExhausted

      fun loop (limits as {depth_limited, rapp_limited}) tree =
        if
          #state (aesopTree.goal tree (aesopTree.root tree)) =
          aesopTree.Proved
        then
          (trace 1
             (fn () =>
               "search proved the root with " ^
               Int.toString (aesopTree.rapp_count tree) ^
               " rapp(s)");
           SearchProved tree)
        else
          case
            bounded_safe_phase max_rapps max_depth rules tree
          of
              BoundedSafeRappLimit limited =>
                failed RappLimitReached limited
            | BoundedSafe (QueueEmpty exhausted) =>
                if
                  #state
                    (aesopTree.goal exhausted
                      (aesopTree.root exhausted)) =
                  aesopTree.Proved
                then loop limits exhausted
                else failed (exhausted_reason limits) exhausted
            | BoundedSafe (DepthLimit {goal, tree = limited}) =>
                (trace 2
                   (fn () =>
                     "depth limit stopped goal " ^
                     Int.toString goal);
                 loop {depth_limited = true, rapp_limited = rapp_limited}
                   (aesopTree.exhaust_goal goal limited))
            | BoundedSafe
                (NormalisationLimit
                  {goal, tree = limited, iterations, rule}) =>
                (trace 2
                   (fn () =>
                     "normalisation limit stopped goal " ^
                     Int.toString goal ^ " after " ^
                     Int.toString iterations ^
                     " iteration(s), next rule " ^ rule);
                 loop {depth_limited = true, rapp_limited = rapp_limited}
                   (aesopTree.exhaust_goal goal limited))
            | BoundedSafe (ReadyForUnsafe {goal, tree = ready}) =>
                (case unsafe_phase config goal ready of
                     UnsafeContinue next => loop limits next
                   | UnsafeRappSkipped next =>
                       loop
                         {depth_limited = depth_limited,
                          rapp_limited = true}
                         next)
    in
      loop {depth_limited = false, rapp_limited = false} initial
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

(* A goal carrying its own proof, as opposed to one the tree proved through
   a copy of it made elsewhere.  Only the former can be descended into
   here: a goal proved solely by copy has no proved rule application, and
   its records are reached when the walk gets to the copy. *)
fun independently_proved tree id =
  let val current = aesopTree.goal tree id
  in
    #state current = aesopTree.Proved andalso
    (case #norm current of
         aesopTree.NormProved _ => true
       | _ =>
           List.exists
             (fn rid => #state (aesopTree.rapp tree rid) = aesopTree.Proved)
             (aesopTree.child_rapps tree id))
  end

(* A copied goal discharges the corresponding original sibling, but it is
   not a child emitted by the rule action that caused the copy.  First
   select the complete winning forest and record this redirection.  The
   later linearisation can then replay only real action children, in their
   original positional order. *)
fun winning_forest tree =
  let
    type selection = (gid, gid) Redblackmap.dict
    type rapp_selection = (gid, aesopTree.rid) Redblackmap.dict
    type requirements = (gid, aesopTree.rid) Redblackmap.dict
    val empty_selection : selection = Redblackmap.mkDict Int.compare
    val empty_rapp_selection : rapp_selection =
      Redblackmap.mkDict Int.compare
    val empty_requirements : requirements =
      Redblackmap.mkDict Int.compare

    fun add_path [] required = SOME required
      | add_path ((goal, rid) :: rest) required =
          (case Redblackmap.peek (required, goal) of
               NONE =>
                 add_path rest (Redblackmap.insert (required, goal, rid))
             | SOME rid' =>
                 if rid = rid' then add_path rest required else NONE)

    fun choose_supports _ [] required = SOME required
      | choose_supports supports_of (id :: rest) required =
          let
            fun choose [] = NONE
              | choose ((_, path) :: candidates) =
                  (case add_path path required of
                       SOME required' =>
                         (case choose_supports supports_of rest required' of
                              SOME result => SOME result
                            | NONE => choose candidates)
                     | NONE => choose candidates)
          in
            choose (supports_of id)
          end

    (* One obligation can be discharged more than once in the same tree:
       a goal may carry its own proof and also have a proved copy of it
       somewhere in the winning branch.  Both are genuine proofs of that
       single obligation, so replay takes exactly one of them -- the first
       the walk reaches -- and does not descend a second time.  Taking both
       would make [clasetMeta.absorb] fold two stores for one goal and
       linearise its records twice. *)
    fun select actual
      (accumulated as (selection, rapp_selection, stores, required)) =
      let
        val current = aesopTree.goal tree actual
        val original =
          case #copy_of current of
              NONE => actual
            | SOME id => id
      in
        if Option.isSome (Redblackmap.peek (selection, original)) then
          accumulated
        else
          let
            val selection' =
              Redblackmap.insert (selection, original, actual)
          in
            case #norm current of
                aesopTree.NormProved {store, ...} =>
                  (selection', rapp_selection, store :: stores, required)
              | _ =>
                  let
                    val rid =
                      case Redblackmap.peek (required, actual) of
                          NONE => proved_rapp tree actual
                        | SOME required_rid =>
                            if
                              #state (aesopTree.rapp tree required_rid) =
                                aesopTree.Proved andalso
                              List.exists
                                (fn child => child = required_rid)
                                (aesopTree.child_rapps tree actual)
                            then required_rid
                            else
                              raise ERR "extract"
                                ("a required copy-support application " ^
                                 "is not proved")
                    val application = aesopTree.rapp tree rid
                    val rapp_selection' =
                      Redblackmap.insert
                        (rapp_selection, actual, rid)
                    (* A cluster's goals are conjunctive, so every one of
                       them needs a proof in the forest.  The members
                       proved only by copy are picked up where the walk
                       meets the copy, which is itself a cluster goal of
                       some rapp below. *)
                    fun select_cluster
                      (cid,
                       accumulated as
                         (selection, rapp_selection, stores, required)) =
                      let
                        val cluster = aesopTree.cluster tree cid
                        val _ =
                          if #state cluster = aesopTree.Proved then ()
                          else
                            raise ERR "extract"
                              ("winning rule application contains " ^
                               "unproved cluster " ^ Int.toString cid)
                        val all_members = #goals cluster
                        val members =
                          List.filter (independently_proved tree)
                            all_members
                        val _ =
                          if null members then
                            raise ERR "extract"
                              ("proved cluster " ^ Int.toString cid ^
                               " has no independently proved goal")
                          else ()
                        val copy_members =
                          List.filter
                            (fn id =>
                              not (independently_proved tree id) andalso
                              not
                                (Option.isSome
                                  (Redblackmap.peek (selection, id))))
                            all_members
                        val required' =
                          case
                            choose_supports
                              (aesopTree.copy_supports tree)
                              copy_members required
                          of
                              SOME result => result
                            | NONE =>
                                raise ERR "extract"
                                  ("proved cluster " ^ Int.toString cid ^
                                   " has no compatible copy-support paths")
                        val prepared =
                          (selection, rapp_selection, stores, required')
                      in
                        List.foldl
                          (fn (id, current) => select id current)
                          prepared members
                      end
                  in
                    if null (#clusters application) then
                      (selection', rapp_selection',
                       #store application :: stores, required)
                    else
                      List.foldl select_cluster
                        (selection', rapp_selection', stores, required)
                        (#clusters application)
                  end
          end
      end

    val root = aesopTree.root tree
    val root_goal = aesopTree.goal tree root
    val _ =
      if #state root_goal = aesopTree.Proved then ()
      else raise ERR "extract" "the root goal is not proved"
  in
    case
      select root
        (empty_selection, empty_rapp_selection, [], empty_requirements)
    of
        (selection, rapp_selection, stores, _) =>
          (selection, rapp_selection, stores)
  end

fun selected_goal selection original =
  case Redblackmap.peek (selection, original) of
      SOME actual => actual
    | NONE =>
        raise ERR "extract"
          ("winning forest has no proof of goal " ^
           Int.toString original)

fun selected_rapp rapp_selection actual =
  case Redblackmap.peek (rapp_selection, actual) of
      SOME rid => rid
    | NONE =>
        raise ERR "extract"
          ("winning forest has no application for goal " ^
           Int.toString actual)

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
    val (selection, rapp_selection, final_stores) = winning_forest tree
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
                val rid = selected_rapp rapp_selection actual
                val application = aesopTree.rapp tree rid
                val with_application =
                  append_records (#records application) with_norm
              in
                List.foldl
                  (fn (child, accumulated) =>
                    linearise child (actual :: ancestors) accumulated)
                  with_application (aesopTree.direct_children tree rid)
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
  (* Every way replay can fail is an engine bug, so the diagnostic is
     deliberately a catch-all -- except for an interrupt, which is the
     user's and belongs to the proof they stopped, not to the engine. *)
  handle Portable.Interrupt => raise Portable.Interrupt
       | error =>
           raise ERR "REPLAY_TAC"
             ("kernel replay of a proved search tree failed; this is an " ^
              "aesop engine bug: " ^ Feedback.exn_to_string error)

end
