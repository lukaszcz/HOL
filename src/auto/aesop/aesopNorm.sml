structure aesopNorm :> aesopNorm =
struct

open Abbrev HolKernel

type tree = aesopTree.tree
type gid = aesopTree.gid
type rule = aesopRule.rule

datatype outcome =
    Complete of {tree : tree, iterations : int}
  | IterationLimit of
      {tree : tree, iterations : int, rule : string}

val ERR = mk_HOL_ERR "aesopNorm"

datatype application =
    Inapplicable
  | Applied of
      {record : clasetReplay.step_record, node : clasetGoal.node}

fun penalty ({phase = aesopRule.RNorm value, ...} : rule) = SOME value
  | penalty _ = NONE

fun ordered_rules rules =
  let
    val positioned =
      List.mapPartial
        (fn (index, rule) =>
          Option.map (fn value => (value, index, rule)) (penalty rule))
        (Lib.enumerate 0 rules)
    fun compare ((left, left_index, _), (right, right_index, _)) =
      case Int.compare (left, right) of
          EQUAL => Int.compare (left_index, right_index)
        | order => order
  in
    map #3 (Listsort.sort compare positioned)
  end

(* Metavariable identity, not term equality: a type binding respells a
   metavariable, and a respelling is not a new metavariable. *)
fun member_term candidate =
  List.exists
    (fn existing => clasetMeta.meta_compare (candidate, existing) = EQUAL)

fun member_type candidate =
  List.exists
    (fn existing => Type.compare (candidate, existing) = EQUAL)

fun new_binding created parent child =
  let
    val parent_bindings = clasetMeta.bindings parent
    val child_bindings = clasetMeta.bindings child
    fun new_term (meta, _) =
      not (member_term meta (map #1 (#terms parent_bindings))) andalso
      not (member_term meta (#terms created))
    fun new_type (tymeta, _) =
      not (member_type tymeta (map #1 (#types parent_bindings))) andalso
      not (member_type tymeta (#types created))
  in
    List.exists new_term (#terms child_bindings) orelse
    List.exists new_type (#types child_bindings)
  end

(* Normalisation rewrites a goal in place, so a norm rule must be
   deterministic and must not split the goal.  A [MultiStep] rule is a
   choice between its steps by construction, so it never normalises. *)
fun raw_application (rule : rule) node =
  case #apply rule of
      aesopRule.MultiStep _ => Inapplicable
    | _ =>
        (case aesopTree.unique_rule_result rule node of
             SOME ([record], next) =>
               if length (clasetGoal.goals next) > 1 then Inapplicable
               else Applied {record = record, node = next}
           | _ => Inapplicable)

fun application rule node =
  case raw_application rule node of
      Inapplicable => Inapplicable
    | Applied {record, node = next} =>
        if
          new_binding (clasetReplay.created_of record)
            (clasetGoal.store node) (clasetGoal.store next) orelse
          not (aesopTree.changed node next)
        then Inapplicable
        else Applied {record = record, node = next}
  handle HOL_ERR _ => Inapplicable
       | Match => Inapplicable

fun finish id reversed_records iterations node tree =
  let val records = List.rev reversed_records
  in
  case clasetGoal.goals node of
      [] =>
        Complete
          {tree =
             aesopTree.set_norm_proved id
               {records = records, store = clasetGoal.store node} tree,
           iterations = iterations}
    | [cgoal] =>
        Complete
          {tree =
             aesopTree.set_normalised id
               {records = records, cgoal = cgoal,
                store = clasetGoal.store node} tree,
           iterations = iterations}
    | _ =>
        raise ERR "finish" "a norm chain retained more than one goal"
  end

fun normalise {max_depth, rules} id tree =
  if max_depth < 0 then
    raise ERR "normalise" "max_depth must not be negative"
  else
    let
      val goal = aesopTree.goal tree id
      val ordered = ordered_rules rules

      fun scan original reversed_records iterations node [] =
            finish id reversed_records iterations node original
        | scan original reversed_records iterations node (rule :: rest) =
            (case application rule node of
                 Inapplicable =>
                   scan original reversed_records iterations node rest
               | Applied {record, node = next} =>
                   if iterations >= max_depth then
                     IterationLimit
                       {tree = original, iterations = iterations,
                        rule = #name rule}
                   else
                     let
                       val records' = record :: reversed_records
                       val iterations' = iterations + 1
                     in
                       if null (clasetGoal.goals next) then
                         finish id records' iterations' next original
                       else
                         scan original records' iterations' next ordered
                     end)
    in
      if aesopTree.is_normalised goal then
        Complete {tree = tree, iterations = 0}
      else
        scan tree [] 0 (aesopTree.goal_node goal) ordered
    end

end
