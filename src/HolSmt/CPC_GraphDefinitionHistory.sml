(* Actual retained equation hypotheses from staged ordinary producer origins.
   Closed post-transport laws do not exempt changed original Sources. *)
structure CPC_GraphDefinitionHistory :> CPC_GraphDefinitionHistory =
struct
  open SmtReplayGraph SmtReplaySource SmtLib_GraphProof SmtReplayRules
    CPC_GraphProofReplay
  structure G = SmtReplayGraph
  structure Q = SmtLib_GraphProof
  structure S = SmtReplaySource
  structure O = CPC_GraphProofReplay
  exception Adapter
  type preview =
    {owner : unit ref,revision : int,command : CPC_ProofParser.graph_command,
     origin : O.producer_origin,validate : unit -> unit,
     validate_committed : unit -> unit}
  type occurrence =
    {serial : int,revision : int,source : G.node,variable : G.node,
     residue : G.node,original_hypothesis : int,original_premises :
       {index : int,node : G.node,command_occurrence : int option} list}
  datatype history = History of
    {graph : G.graph,scope : G.scope,validate : unit -> unit,
     allocated : G.node list,original : G.node list,
     owner : unit ref option ref,last_revision : int ref,
     entries : (int,preview) Redblackmap.dict ref}
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphDefinitionHistory"
  fun new {packet,sources,validate} =
    let
      val graph = Q.graph packet val scope = Q.scope packet
      val _ = validate () val _ = G.validate_scope graph scope
      val original = S.assumption_nodes sources @ [S.denied_goal_node sources]
      val _ = List.app (fn node => ignore (G.type_of graph node)) original
      val allocated = List.map #node (Q.variables packet)
      val _ = List.app (fn node =>
        (if G.scope_visible graph scope (G.node_scope graph node) then () else
           raise ERR "new" "allocated solver descriptor is not live";
         case G.view graph node of G.Variable (G.SolverFlexible,_) => ()
           | _ => raise ERR "new" "allocated inventory changed its role"))
        allocated
    in History {graph = graph,scope = scope,validate = validate,
      allocated = allocated,original = original,owner = ref NONE,
      last_revision = ref 0,entries = ref (Redblackmap.mkDict Int.compare)} end
  fun active (History {graph,scope,validate,...}) =
    (validate ();G.validate_scope graph scope)
  fun allocated (history as History {allocated,...}) =
    (active history;allocated)
  fun capture (history as History
      {owner,last_revision,entries,...}) (entry : preview) =
    let
      val _ = active history val _ = #validate entry ()
      val _ = if #revision entry > !last_revision then () else
        raise ERR "capture" "stale producer revision"
      val _ = case !owner of NONE => owner := SOME (#owner entry)
        | SOME retained => if retained = #owner entry then () else
            raise ERR "capture" "producer belongs to another invocation"
      val serial = #serial (#origin entry)
      val _ = if Redblackmap.inDomain (!entries,serial) then
        raise ERR "capture" "repeated producer command occurrence" else ()
      val _ = entries := Redblackmap.insert (!entries,serial,entry)
    in last_revision := #revision entry end
  fun equations (history as History
      {graph,scope,allocated,original,entries,...}) requested =
    let
      val _ = active history
      fun member node nodes = List.exists (fn other => node = other) nodes
      fun selected {serial,variable} =
        let
          val entry = case Redblackmap.peek (!entries,serial) of
              SOME entry => entry
            | NONE => raise ERR "equations" "missing actual producer origin"
          val _ = #validate_committed entry ()
          val origin = #origin entry
          val source = #target origin
          val _ = if member variable allocated then () else
            raise ERR "equations" "definition lacks allocated solver permission"
          val _ = if G.scope_visible graph scope (G.node_scope graph variable)
              then () else raise ERR "equations" "definition captures scope"
          val (left,right) = #equation origin
          val _ = if SmtReplayRules.equality graph source = SOME (left,right)
              then () else raise ERR "equations" "stored orientation changed"
          val residue = if variable = left then right
            else if variable = right then left else
              raise ERR "equations" "selected name is not a stored endpoint"
          val deferred = case #deferred origin of SOME node => node
            | NONE => raise Adapter
          val index = case #actual_hypotheses origin of [index] => index
            | _ => raise Adapter
          val premise = List.nth (#premises origin,index)
          val _ = if deferred = source andalso #node premise = source andalso
              #command_occurrence premise = NONE andalso
              not (member source original) then () else
            raise ERR "equations" "definition is not exact original deferred Hyp"
          (* Every original Source stays rigid even when typed spellings
             overlap. Unknown Source FV metadata gives no freshness claim. *)
          val original_variables = List.concat (List.map (fn node =>
            case G.free_variable_nodes graph node of SOME nodes => nodes
              | NONE => raise Adapter)
            original)
          fun collision node = variable = node orelse
            (G.type_id graph variable = G.type_id graph node andalso
             #1 (Term.dest_var (G.representative graph variable)) =
             #1 (Term.dest_var (G.representative graph node)))
          val _ = if List.exists collision original_variables then
            raise ERR "equations" "solver definition changes original Source"
            else ()
          val _ = #validate_committed entry ()
        in {serial = serial,revision = #revision entry,source = source,
          variable = variable,residue = residue,original_hypothesis = index,
          original_premises = #premises origin} : occurrence end
    in List.map selected requested end
end
