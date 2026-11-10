(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphTheoremDiscovery :> SmtLib_GraphTheoremDiscovery =
struct
  structure G = SmtReplayGraph
  structure F = SmtLib_GraphSourcePortfolio
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphTheoremDiscovery"
  datatype discovery = Discovery of
    {graph : G.graph,scope : G.scope,facts : F.fact list,
     gaps : (G.node * string) list}
  exception BinderLaw
  fun active (Discovery {graph,scope,...}) = G.validate_scope graph scope
  fun facts (d as Discovery {facts,...}) = (active d;facts)
  fun gaps (d as Discovery {gaps,...}) = (active d;gaps)
  fun discover_internal records graph scope
      {roots,input_limit,template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val _ = if input_limit > 0 andalso template_limit > 0 then () else
        raise ERR "discover" "nonpositive original contract"
      val _ = List.app (fn root => List.app (fn metric =>
        case G.unfolded_nodes graph metric input_limit root of
          SOME count => if count <= input_limit then () else
            raise ERR "discover" "original input exceeds limit"
        | NONE => raise ERR "discover" "unknown original input metric")
        [G.RawNodes,G.BinderInclusiveNodes]) roots
      val reachable = G.block_reachable graph roots
      fun checked_type inspect value =
        let
          val _ = G.validate_scope graph scope
          val ty = inspect value
          val _ = G.validate_scope graph scope
          val _ = check_type ty
        in G.validate_scope graph scope end
      val _ = List.app (checked_type (G.type_of graph)) reachable
      val selected = ref (Redblackset.empty Int.compare)
      val laws = ref ([] : F.fact list)
      val missing = ref ([] : (G.node * string) list)
      fun admit term =
        let fun walk [] count = ()
              | walk (current :: rest) count =
                  if count >= template_limit then
                    raise ERR "discover" "selected stock law exceeds limit"
                  else if Term.is_comb current then
                    let val (f,x) = Term.dest_comb current in
                      walk (f :: x :: rest) (count+1) end
                  else if Term.is_var current orelse Term.is_const current then
                    walk rest (count+1)
                  else raise BinderLaw
        in walk [term] 0 end
      fun law head theorem =
        let
          val fact = case records of SOME catalogue =>
              (case List.find (fn plan => Portable.pointer_eq
                  (SmtReplayProof.closed_original plan,theorem)) catalogue of
                SOME plan => F.recorded_closed graph scope plan
              | NONE => raise BinderLaw)
            | NONE =>
              let
                val _ = admit (Thm.concl theorem)
                (* Rigid operands are not original Source assumptions. *)
                val variables = Term.free_vars (Thm.concl theorem)
                val _ = List.app (checked_type Term.type_of) variables
                val operands = List.map (G.variable graph scope G.RigidSource)
                  variables
              in F.closed graph scope
                {theorem = theorem,holes = variables,operands = operands,
                 template_limit = template_limit} end
        in laws := fact :: !laws end
        handle BinderLaw => missing := (head,
          "stock law requires checked binder and num-transfer recipe")
          :: !missing
      fun head node = case G.view graph node of G.Constant _ =>
          if Redblackset.member (!selected,G.node_id node) then () else
            let
              val _ = selected := Redblackset.add (!selected,G.node_id node)
              val theorems = if !SmtLib.include_theorems then
                SmtLib.graph_preprocessing_theorems_for_head
                  (G.representative graph node) else []
              val _ = List.app (law node) theorems
            in () end
        | _ => ()
      val _ = List.app head reachable
      val _ = G.validate_scope graph scope
    in Discovery {graph = graph,scope = scope,facts = List.rev (!laws),
      gaps = List.rev (!missing)} end
  fun discover graph scope args = discover_internal NONE graph scope args
  fun discover_recorded_laws graph scope
      {roots,input_limit,template_limit,check_type,records} =
    let
      val _ = G.validate_scope graph scope
      fun admit [] _ = ()
        | admit (plan :: rest) count =
            if count >= template_limit then
              raise ERR "discover" "record catalogue exceeds original limit"
            else (SmtReplayProof.validate_closed_fact graph scope
                    template_limit plan;
                  admit rest (count+1))
      val _ = if template_limit > 0 then () else
        raise ERR "discover" "nonpositive original template limit"
      val _ = admit records 0
    in discover_internal (SOME records) graph scope
      {roots = roots,input_limit = input_limit,
       template_limit = template_limit,check_type = check_type} end
end
