structure CPC_GraphResolvedConstructorBridge :>
  CPC_GraphResolvedConstructorBridge =
struct
  open SmtReplayGraph SmtReplayResolve SmtReplayProof SmtReplayRules
  structure G = SmtReplayGraph
  structure R = SmtReplayResolve
  structure P = SmtReplayProof
  structure Rules = SmtReplayRules
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphResolvedConstructorBridge"
  type assignment = {equation : G.node,variable : G.node,residue : G.node}
  datatype plan = Plan of
    {graph : G.graph,scope : G.scope,resolution : R.resolution,
     originals : G.node list,targets : G.node list,
     assignments : assignment list,roots : G.node list}
  fun active (Plan {graph,scope,resolution,...}) =
    R.validate graph scope resolution
  fun roots (plan as Plan {roots,...}) = (active plan;roots)
  fun sources (plan as Plan {originals,assignments,...}) =
    (active plan;originals @ List.map #equation assignments)
  fun orientation graph {equation,variable,residue} =
    case Rules.equality graph equation of SOME (left,right) =>
      if left = variable andalso right = residue then true
      else if right = variable andalso left = residue then false
      else raise ERR "orientation" "not the exact recorded assignment"
    | NONE => raise ERR "orientation" "assignment source is not equality"
  fun discover {graph,scope,resolution,originals,targets,assignments,
                template_limit,check_type} =
    let
      val _ = R.validate graph scope resolution
      val _ = if template_limit > 0 then () else
        raise ERR "discover" "nonpositive compact proof contract"
      val _ = List.app (fn node =>
        if R.node resolution node = node then () else
          raise ERR "discover" "an ordinary original Source would change")
        originals
      val _ = List.app (fn entry as {equation,variable,residue} =>
        (ignore (orientation graph entry);
         if R.is_assignment_source resolution equation andalso
             R.node resolution variable = R.node resolution residue then ()
         else raise ERR "discover" "unregistered assignment authority"))
        assignments
      val roots = originals @ List.map #equation assignments @ targets @
        List.map (R.node resolution) targets
      val nodes = G.block_reachable graph roots
      val _ = List.app (fn node =>
        if G.scope_visible graph scope (G.node_scope graph node) then ()
        else raise ERR "discover" "unavailable constructor owner") nodes
      val costs = List.mapPartial (fn node => case G.view graph node of
          G.Constant _ => SOME 5 | G.Application _ => SOME 7
        | _ => NONE) nodes
      val count = length costs + length originals + length assignments
      val context = List.foldl (fn (n,total) => total + IntInf.fromInt n)
        (IntInf.fromInt (length originals + length assignments)) costs +
        (if count = 0 then 1 else 3 * IntInf.fromInt (count-1))
      (* Constructor/source atoms are small names. A complete relation is
         name(old)=name(new), size5; context implication adds3. Both metrics
         agree before substitution. This includes prospective law ALPHA. *)
      val _ = if 3 + 2 * (context + 8) <=
          IntInf.fromInt template_limit then () else
        raise ERR "discover" "whole compact bridge law exceeds quota"
      val _ = List.app (check_type o G.type_of graph) nodes
      val _ = List.app (fn node =>
        if node = R.node resolution node then () else
          case G.view graph node of G.Application _ => ()
            | G.Variable (G.SolverFlexible,_) => ()
            | _ => raise ERR "discover"
                "changed binder or opaque leaf needs its checked adapter")
        (G.block_reachable graph targets)
      val _ = List.app (fn node =>
        if G.type_id graph node = G.type_id graph (R.node resolution node)
        then () else raise ERR "discover" "resolved constructor type changed")
        (G.block_reachable graph targets)
    in Plan {graph = graph,scope = scope,resolution = resolution,
      originals = originals,targets = targets,assignments = assignments,
      roots = roots} end
  fun assemble block (plan as Plan
      {graph,scope,resolution,assignments,originals,targets,...}) target =
    let
      val _ = active plan
      val _ = if P.scope block = scope andalso
          P.sources block = sources plan then () else
        raise ERR "assemble" "wrong block or source occurrence inventory"
      val _ = if List.exists (fn node => node = target) targets then () else
        raise ERR "assemble" "target was not discovered"
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun apply operation edges = P.compose block operation edges
      fun bridge node = case Redblackmap.peek (!memo,G.node_id node) of
          SOME edge => edge
        | NONE =>
          let val output = R.node resolution node
              val edge = if node = output then
                  apply (fn _ => Thm.REFL (P.name block node)) []
                else case G.view graph node of
                  G.Variable (G.SolverFlexible,_) =>
                    let
                      fun find [] _ = raise ERR "assemble"
                            "changed solver name lacks exact assignment"
                        | find ((entry as {variable,...}) :: rest) index =
                            if variable = node then (entry,index)
                            else find rest (index+1)
                      val (entry as {equation,residue,...},index) =
                        find assignments (length originals)
                      val forward = orientation graph entry
                      val relation = apply
                        (fn [constructor,fact] =>
                          let val law = Thm.EQ_MP constructor fact
                          in if forward then law else Thm.SYM law end
                          | _ => raise ERR "assemble" "assignment premises")
                        [P.constructor block equation,P.source block index]
                    in apply (fn [first,last] => Thm.TRANS first last
                        | _ => raise ERR "assemble" "residue premises")
                        [relation,bridge residue] end
                | G.Application (f,x) =>
                    apply (fn [original,left,right,resolved] =>
                      Thm.TRANS original
                        (Thm.TRANS (Thm.MK_COMB (left,right))
                          (Thm.SYM resolved))
                      | _ => raise ERR "assemble" "constructor premises")
                      [P.definition block node,bridge f,bridge x,
                       P.definition block output]
                | _ => raise ERR "assemble" "unsupported changed leaf"
              val _ = memo := Redblackmap.insert
                (!memo,G.node_id node,edge)
          in edge end
    in bridge target end
  fun original_fact block (plan as Plan {resolution,...})
      {target,normalized} =
    let val _ = active plan
        val output = R.node resolution target
        val _ = if Portable.pointer_eq
            (Thm.concl (P.theorem block normalized),P.name block output) then ()
          else raise ERR "original_fact" "wrong exact normalized proof"
    in P.compose block
      (fn [relation,fact] => Thm.EQ_MP (Thm.SYM relation) fact
        | _ => raise ERR "original_fact" "wrong proof premises")
      [assemble block plan target,normalized] end
end
