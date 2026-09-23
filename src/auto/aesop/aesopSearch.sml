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

datatype budget_outcome =
    SearchFinished of search_outcome
  | WorkLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

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

fun charge NONE _ = ()
  | charge (SOME budget) kind = searchBudget.charge budget kind

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

(* Engine steps keep their existing metering; rendered tactics and
   multi-step rules charge before forcing each alternative.  A yield
   then leaves the sequence at the same position. *)
fun charge_external_pull budget ({apply, ...} : aesopRule.rule) =
  case apply of
      aesopRule.EngineStep _ => ()
    | aesopRule.ContextualStep _ => ()
    | _ => charge budget searchBudget.Candidate

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
fun safe_alternatives ctxt budget (rule : aesopRule.rule) node =
  (* Delayed, so that a rule which raises while producing its sequence at
     all is caught by the walk over that sequence. *)
  if #once rule then
    seq.delay (fn () => aesopTree.rule_results_in ctxt rule node)
  else
    let
      val remaining =
        ref (seq.delay (fn () =>
          aesopTree.rule_results_in ctxt rule node))
      val first = ref (NONE :
        (clasetReplay.step_record list * clasetGoal.node) option)
      val decided = ref (NONE :
        (clasetReplay.step_record list * clasetGoal.node)
          option option)
      fun finish answer =
        (decided := SOME answer;
         case answer of
             SOME result => seq.result result
           | NONE => seq.empty)
      fun unique () =
        case !decided of
            SOME answer =>
              (case answer of
                   SOME result => seq.result result
                 | NONE => seq.empty)
          | NONE =>
              ((charge_external_pull budget rule;
                case seq.cases (!remaining) of
                    NONE => finish (!first)
                  | SOME (result, rest) =>
                      (remaining := rest;
                       case !first of
                           NONE => (first := SOME result; unique ())
                         | SOME _ => finish NONE))
               handle HOL_ERR _ => finish NONE
                    | Match => finish NONE)
    in
      seq.delay unique
    end

fun same_goal_context
      (previous : aesopTree.goal) (goal : aesopTree.goal) =
  #id previous = #id goal andalso
  Portable.pointer_eq
    (aesopTree.active_store previous,
     aesopTree.active_store goal) andalso
  clasetGoal.equal
    (aesopTree.child_node previous,
     aesopTree.child_node goal) andalso
  ListPair.allEq (fn (left, right) => Term.aconv left right)
    (#forwarded previous, #forwarded goal)

type safe_scan =
  {goal : aesopTree.goal,
   node : clasetGoal.node,
   registry_generation : int,
   rule_signature : (string * aesopRule.rphase * bool) list,
   remaining_rules : aesopRule.rule list ref,
   current :
     (aesopRule.rule *
      (clasetReplay.step_record list * clasetGoal.node) seq.seq)
       option ref,
   postponed : aesopTree.rapp_data list ref}

type safe_scan_cache =
  {scans : safe_scan list ref, active : bool ref}

fun empty_safe_scan_cache () : safe_scan_cache =
  {scans = ref [], active = ref false}

fun safe_rule_signature rules =
  map
    (fn ({name, phase, once, ...} : aesopRule.rule) =>
      (name, phase, once)) rules

fun new_safe_scan generation goal rules : safe_scan =
  {goal = goal, node = aesopTree.child_node goal,
   registry_generation = generation,
   rule_signature = safe_rule_signature rules,
   remaining_rules = ref rules, current = ref NONE,
   postponed = ref []}

fun forget_safe_scan (cache : safe_scan_cache) id =
  (#scans cache :=
     List.filter
       (fn ({goal, ...} : safe_scan) => #id goal <> id)
       (!(#scans cache));
   #active cache := false)

fun safe_phase ctxt budget (cache : safe_scan_cache)
      max_rapps id rules tree =
  let
    val goal = aesopTree.goal tree id
    val generation = aesopRule.registry_generation ()
    val rule_signature = safe_rule_signature rules
    val scan =
      case
        List.find
          (fn ({goal = previous,
                registry_generation = previous_generation,
                rule_signature = previous_rules,
                ...} : safe_scan) =>
            same_goal_context previous goal andalso
            previous_generation = generation andalso
            previous_rules = rule_signature)
          (!(#scans cache))
      of
          SOME saved => saved
        | NONE =>
            let val fresh = new_safe_scan generation goal rules
            in
              #scans cache :=
                fresh ::
                List.filter
                  (fn ({goal = previous, ...} : safe_scan) =>
                    #id previous <> id)
                  (!(#scans cache));
              fresh
            end
    val node = #node scan
    val has_dependencies =
      not (aesopTree.dependencies_empty (#deps goal))
    (* The tree is fixed for the whole scan, so its budget is decided once
       rather than once per rule. *)
    val at_rapp_limit =
      case max_rapps of
          NONE => false
        | SOME limit => aesopTree.rapp_count tree >= limit

    fun next_candidate () =
      case !(#current scan) of
          SOME (rule, alternatives) =>
            (case (if #once rule then
                     charge_external_pull budget rule else ();
                   next_application alternatives) of
                 NONE =>
                   (#current scan := NONE; next_candidate ())
               | SOME (result, remaining) =>
                   (#current scan := SOME (rule, remaining);
                    SOME (rule, result)))
        | NONE =>
            (case !(#remaining_rules scan) of
                 [] => NONE
               | rule :: rest =>
                   (#remaining_rules scan := rest;
                    if #phase rule = aesopRule.RSafe then
                      #current scan :=
                        SOME
                          (rule,
                           safe_alternatives ctxt budget rule node)
                    else ();
                    next_candidate ()))

    fun search () =
      (#active cache := true;
       case next_candidate () of
           NONE =>
             let
               val postponed = List.rev (!(#postponed scan))
               val _ = forget_safe_scan cache id
             in
               Deferred postponed
             end
         | SOME (rule, result as (_, next)) =>
             if not (aesopTree.changed node next) then search ()
             else
               let val data = application_data rule result
               in
                 case admissible_forward goal rule data of
                     NONE => search ()
                   | SOME added =>
                       let val data' = data_with_forwarded data added
                       in
                         if has_dependencies andalso
                            application_assigned goal data
                         then
                           (#postponed scan :=
                              data' :: !(#postponed scan);
                            search ())
                         else if at_rapp_limit then
                           (forget_safe_scan cache id;
                            CommitLimit tree)
                         else
                           (charge budget searchBudget.Application;
                            forget_safe_scan cache id;
                            Committed
                              (install_committed id data' tree))
                       end
               end)
  in
    search ()
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

fun next_safe_with ctxt include_irrelevant pop_goal
      (config as {max_depth, max_rapps, rules = source,
                  budget, safe_cache,
                  checkpoint_ready, checkpoint_progress}) tree =
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
                (case budget of
                     NONE => aesopNorm.normalise_in ctxt
                   | SOME meter =>
                       aesopNorm.normalise_budgeted_in ctxt meter)
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
                        next_safe_with ctxt include_irrelevant pop_goal
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
                          val _ = checkpoint_ready id normalised
                        in
                          case safe_phase ctxt budget safe_cache
                            max_rapps id safe
                            normalised of
                              Committed installed =>
                                (checkpoint_progress installed;
                                 next_safe_with ctxt include_irrelevant
                                   pop_goal config installed)
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

fun next_safe_including_irrelevant ctxt {max_depth, rules} tree =
  next_safe_with ctxt true aesopTree.pop_goal_including_irrelevant
    {max_rapps = NONE, max_depth = max_depth, rules = rules,
     budget = NONE, safe_cache = empty_safe_scan_cache (),
     checkpoint_ready = fn _ => fn _ => (),
     checkpoint_progress = fn _ => ()}
    tree

fun safe_saturate_in ctxt config tree =
  let
    fun saturate current =
      case next_safe_including_irrelevant ctxt config current of
          QueueEmpty saturated => SafeSaturated saturated
        | ReadyForUnsafe {tree = remaining, ...} =>
            saturate remaining
        | DepthLimit result => SafeDepthLimit result
        | NormalisationLimit result =>
            SafeNormalisationLimit result
  in
    saturate tree
  end

fun safe_saturate config tree =
  safe_saturate_in (Context.snapshot ()) config tree

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

type unsafe_scan =
  {goal : aesopTree.goal,
   rule : aesopRule.rule,
   node : clasetGoal.node,
   registry_generation : int,
   remaining : (clasetReplay.step_record list * clasetGoal.node)
     seq.seq ref,
   reversed : aesopTree.rapp_data list ref}

type scan_cache =
  {scans : unsafe_scan list ref, active : unsafe_scan option ref}

fun empty_scan_cache () : scan_cache =
  {scans = ref [], active = ref NONE}

fun new_unsafe_scan ctxt generation goal rule : unsafe_scan =
  let
    val node = aesopTree.child_node goal
  in
    {goal = goal, rule = rule, node = node,
     registry_generation = generation,
     remaining =
       ref (seq.delay (fn () =>
         aesopTree.rule_results_in ctxt rule node)),
     reversed = ref []}
  end

fun finish_unsafe_scan budget
      ({goal, rule, node, remaining, reversed, ...} : unsafe_scan) =
  let
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
    fun scan () =
      case (charge_external_pull budget rule;
            next_application (!remaining)) of
          NONE => List.rev (!reversed)
        | SOME (result, rest) =>
            (remaining := rest;
             (case prepare result of
                  NONE => ()
                | SOME data => reversed := data :: !reversed);
             scan ())
  in
    scan ()
  end

fun forget_unsafe_scan (cache : scan_cache) id =
  (#scans cache :=
     List.filter
       (fn ({goal, ...} : unsafe_scan) => #id goal <> id)
       (!(#scans cache));
   #active cache := NONE)

fun unsafe_applications ctxt budget (cache : scan_cache) goal rule =
  let
    val generation = aesopRule.registry_generation ()
    (* Restarted rule assembly makes a fresh closure, so pointer identity
       does not identify it.  The store, rendered node and tactic-registry
       generation identify a resumable rule scan. *)
    fun same_goal ({goal = previous, ...} : unsafe_scan) =
      #id previous = #id goal
    fun matches
          ({goal = previous_goal, rule = previous_rule,
            registry_generation = previous_generation, ...} :
           unsafe_scan) =
      same_goal_context previous_goal goal andalso
      previous_generation = generation andalso
      #name previous_rule = #name rule andalso
      #phase previous_rule = #phase rule andalso
      #once previous_rule = #once rule
    val scan =
      case List.find matches (!(#scans cache)) of
          SOME saved => saved
        | NONE =>
            let val fresh = new_unsafe_scan ctxt generation goal rule
            in
              #scans cache :=
                fresh :: List.filter (not o same_goal)
                  (!(#scans cache));
              fresh
            end
    val _ = #active cache := SOME scan
    val offered = finish_unsafe_scan budget scan
    val _ = forget_unsafe_scan cache (#id goal)
  in
    offered
  end
  handle HOL_ERR _ => (forget_unsafe_scan cache (#id goal); [])
       | Match => (forget_unsafe_scan cache (#id goal); [])

fun stored_application data =
  [data_with_phase data (aesopRule.RUnsafe postponed_percent)]

fun install_alternatives budget id data tree =
  let
    fun install (application, current) =
      let
        val _ = charge budget searchBudget.Application
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

fun bounded_safe_phase ctxt budget safe_cache
      checkpoint_ready checkpoint_progress
      max_rapps max_depth rules tree =
  BoundedSafe
    (next_safe_with ctxt false aesopTree.pop_goal
      {max_depth = max_depth, max_rapps = SOME max_rapps,
       rules = rules, budget = budget,
       safe_cache = safe_cache,
       checkpoint_ready = checkpoint_ready,
       checkpoint_progress = checkpoint_progress} tree)
  handle SafeRappLimitReached limited =>
    BoundedSafeRappLimit limited

fun unsafe_phase ctxt budget cache {max_rapps, ...} id tree =
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
                    (#name rule,
                     unsafe_applications ctxt budget cache goal rule)
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
            val extended =
              install_alternatives budget id applications tree
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

fun safe_completion ctxt budget {max_depth, rules} tree =
  let
    val safe_cache = empty_safe_scan_cache ()
    fun complete current =
      case
        next_safe_with ctxt true aesopTree.pop_goal_including_irrelevant
          {max_depth = max_depth, max_rapps = NONE,
           rules = rules, budget = budget,
           safe_cache = safe_cache,
           checkpoint_ready = fn _ => fn _ => (),
           checkpoint_progress = fn _ => ()}
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

type search_checkpoint =
  {tree : tree, depth_limited : bool, rapp_limited : bool}

type budget_session =
  {context : Context.t,
   budget : searchBudget.budget,
   config : aesop_config,
   rules : rule_source,
   registry_generation : int ref,
   initial : tree,
   checkpoint : search_checkpoint ref,
   cache : scan_cache,
   safe_cache : safe_scan_cache,
   finished : search_outcome option ref,
   terminal : bool ref}

datatype resume_outcome =
    ResumedFinished of search_outcome
  | ResumedYielded of
      {kind : searchBudget.kind, usage : searchBudget.usage,
       session : budget_session}
  | ResumedLimitReached of
      {kind : searchBudget.kind, usage : searchBudget.usage}

fun search_core_with ctxt budget
      (config as {max_rapps, max_depth} : aesop_config)
      rules initial checkpoint cache safe_cache =
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
              (safe_completion ctxt budget
                 {max_depth = max_depth, rules = rules}
                 initial)
          (* A bounded invocation must account for the failure report's
             second search before returning.  The ordinary entry point
             keeps its established lazy frontier behavior. *)
          val safe_goals =
            case budget of
                NONE => frontier
              | SOME _ =>
                  let val cached = frontier ()
                  in fn () => cached end
          val _ = report_failure reason safe_goals
        in
          SearchFailed
            {tree = tree, safe_goals = safe_goals, reason = reason}
        end

      (* An exhausted search that had to step around a limit did not
         exhaust the rules.  The rapp cap bounds the whole search where the
         depth limit bounds one branch, so it is reported first. *)
      fun exhausted_reason {depth_limited, rapp_limited} =
        if rapp_limited then RappLimitReached
        else if depth_limited then DepthLimitReached
        else SearchExhausted

      fun save {depth_limited, rapp_limited} tree =
        checkpoint :=
          {tree = tree, depth_limited = depth_limited,
           rapp_limited = rapp_limited}

      fun loop (limits as {depth_limited, rapp_limited}) tree =
        let val _ = save limits tree
        in
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
            bounded_safe_phase ctxt budget safe_cache
              (fn id => fn ready =>
                save limits (aesopTree.enqueue_goal id ready))
              (save limits)
              max_rapps max_depth rules tree
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
                let
                  (* The ready goal has been popped.  A suspended scan
                     resumes from this same goal/rule generation. *)
                  val _ =
                    save limits (aesopTree.enqueue_goal goal ready)
                in
                  case unsafe_phase ctxt budget cache config goal ready of
                      UnsafeContinue next => loop limits next
                    | UnsafeRappSkipped next =>
                        loop
                          {depth_limited = depth_limited,
                           rapp_limited = true}
                          next
                end
        end
      (* Rule applications are the engine's unit of work; charge the shared
         meter with the count the finished tree carries. *)
      fun charge tree =
        searchWork.note_rule_applications (aesopTree.rapp_count tree)
      val {tree = starting, depth_limited, rapp_limited} = !checkpoint
      val outcome =
        loop
          {depth_limited = depth_limited,
           rapp_limited = rapp_limited} starting
      val _ =
        case outcome of
            SearchProved tree => charge tree
          | SearchFailed {tree, ...} => charge tree
    in
      outcome
    end

fun search_core ctxt budget config rules initial =
  search_core_with ctxt budget config rules initial
    (ref
      {tree = initial, depth_limited = false,
       rapp_limited = false})
    (empty_scan_cache ()) (empty_safe_scan_cache ())

fun search_in ctxt config rules initial =
  search_core ctxt NONE config rules initial

fun search config rules initial =
  search_in (Context.snapshot ()) config rules initial

fun new_budget_session_in ctxt budget config make_rules initial :
      budget_session =
  {context = ctxt, budget = budget, config = config,
   rules = make_rules budget,
   registry_generation = ref (aesopRule.registry_generation ()),
   initial = initial,
   checkpoint =
     ref
       {tree = initial, depth_limited = false,
        rapp_limited = false},
   cache = empty_scan_cache (),
   safe_cache = empty_safe_scan_cache (),
   finished = ref NONE,
   terminal = ref false}

fun new_budget_session budget config make_rules initial =
  new_budget_session_in (Context.snapshot ()) budget config
    make_rules initial

fun resume_budget_session
      (session as {context, budget, config, rules, initial,
                   registry_generation,
                   checkpoint, cache, safe_cache,
                   finished, terminal} : budget_session) =
  (if !terminal then
     raise ERR "resume_budget_session"
       "a terminal work limit cannot be resumed"
   else case !finished of
       SOME outcome => ResumedFinished outcome
     | NONE =>
         let
           val current_generation =
             aesopRule.registry_generation ()
           val _ =
             if current_generation = !registry_generation then ()
             else
               (* Tree cursors also hold rules, so invalidate the whole
                  search state.  Keep the budget: repeated work is charged
                  rather than silently reset after a registry change. *)
               (registry_generation := current_generation;
                checkpoint :=
                  {tree = initial, depth_limited = false,
                   rapp_limited = false};
                #scans cache := [];
                #scans safe_cache := [];
                trace 2
                  (fn () =>
                    "registered tactic rules changed; " ^
                    "restarting budgeted search"))
           val _ = #active cache := NONE
           val _ = #active safe_cache := false
           val outcome =
             search_core_with context (SOME budget) config rules initial
               checkpoint cache safe_cache
           val _ = finished := SOME outcome
         in
           ResumedFinished outcome
         end)
  handle searchBudget.LimitReached (kind, usage) =>
    if kind = searchBudget.Candidate andalso
       (Option.isSome (!(#active cache)) orelse
        !(#active safe_cache))
    then
      ResumedYielded
        {kind = kind, usage = usage, session = session}
    else
      (terminal := true;
       ResumedLimitReached {kind = kind, usage = usage})

(* The original one-shot budgeted entry point keeps its result type.
   Callers that allocate more work use the session API above. *)
fun search_with_budget_in ctxt budget config make_rules initial =
  (case
     resume_budget_session
       (new_budget_session_in ctxt budget config make_rules initial)
   of
       ResumedFinished outcome => SearchFinished outcome
     | ResumedYielded {kind, usage, ...} =>
         WorkLimitReached {kind = kind, usage = usage}
     | ResumedLimitReached {kind, usage} =>
         WorkLimitReached {kind = kind, usage = usage})
  handle searchBudget.LimitReached (kind, usage) =>
    WorkLimitReached {kind = kind, usage = usage}

fun search_with_budget budget config make_rules initial =
  search_with_budget_in (Context.snapshot ()) budget config
    make_rules initial

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

    fun requirements_of items =
      List.foldl
        (fn ((goal,rid), required) =>
          Redblackmap.insert (required,goal,rid))
        empty_requirements items

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
                            aesopTree.select_copy_supports tree copy_members
                              (Redblackmap.listItems required)
                          of
                              SOME result => requirements_of result
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

fun REPLAY_TAC tree goal ctxt =
  let
    val grounded = extract tree
    val result as (goals, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal ctxt
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
