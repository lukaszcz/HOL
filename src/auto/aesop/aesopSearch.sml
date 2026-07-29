structure aesopSearch :> aesopSearch =
struct

open Abbrev HolKernel

type cgoal = clasetGoal.cgoal
type store = clasetMeta.store
type tree = aesopTree.tree
type gid = aesopTree.gid

type rule_source =
  {mode : clasetUnify.mode, cgoal : cgoal, store : store} ->
  aesopRule.ruleset

datatype next_outcome =
    QueueEmpty of tree
  | ReadyForUnsafe of {goal : gid, tree : tree}
  | NormalisationLimit of
      {goal : gid, tree : tree, iterations : int, rule : string}

datatype safe_outcome =
    SafeSaturated of tree
  | SafeNormalisationLimit of
      {goal : gid, tree : tree, iterations : int, rule : string}

datatype application =
    Inapplicable
  | Applied of aesopTree.rapp_data

datatype safe_phase =
    Committed of tree
  | Deferred of aesopTree.rapp_data list

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
              records = records, node = next}
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

fun set_forwarded_children added parent_forwarded result =
  let
    fun update (id, current) =
      if Option.isSome (#copy_of (aesopTree.goal current id)) then
        current
      else
        aesopTree.set_forwarded id
          (added :: parent_forwarded) current
  in
    List.foldl update (#tree result) (#goals result)
  end

fun install_committed id goal data added tree =
  let
    val installed = aesopTree.install_rapp id data tree
    val with_forward =
      case added of
          NONE => #tree installed
        | SOME hypothesis =>
            set_forwarded_children hypothesis (#forwarded goal) installed
  in
    with_forward
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
                         if
                           has_dependencies andalso
                           application_assigned goal data
                         then scan (data :: postponed) rest
                         else
                           Committed
                             (install_committed id goal data added tree))
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

fun next_safe (config as {max_depth, rules = source}) tree =
  case aesopTree.pop_goal tree of
      (NONE, remaining) => QueueEmpty remaining
    | (SOME id, remaining) =>
        let
          val initial_goal = aesopTree.goal remaining id
          val norm_rules =
            #norm (source (rule_input clasetUnify.Match initial_goal))
        in
          case
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
                    aesopTree.goal_irrelevant normalised id
                  then next_safe config normalised
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
                            next_safe config installed
                        | Deferred postponed =>
                            ReadyForUnsafe
                              {goal = id,
                               tree =
                                 prepare_unsafe id postponed source
                                   normalised}
                    end
                end
        end

fun safe_saturate config tree =
  let
    fun saturate current =
      case next_safe config current of
          QueueEmpty saturated => SafeSaturated saturated
        | ReadyForUnsafe {tree = remaining, ...} =>
            saturate remaining
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

end
