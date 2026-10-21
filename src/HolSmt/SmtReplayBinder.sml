(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayBinder :> SmtReplayBinder =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayResolve
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure R = SmtReplayResolve
  val ERR = Feedback.mk_HOL_ERR "SmtReplayBinder"
  fun indexed action items =
    ListPair.map action (List.tabulate (List.length items,fn i => i),items)
  type admission =
    {metric : G.metric,input_limit : int,output_limit : int,
     check_type : Type.hol_type -> unit,refuse : string -> unit}

  fun close_forall graph
      {parent_scope,scope,variables,body,block,edge,resolution,witnesses,
       admission = {metric,input_limit,output_limit,check_type,refuse},close} =
    let
      val _ = G.validate_scope graph parent_scope
      val _ = G.validate_scope graph scope
      val _ = ignore (P.name block body)
      val _ = if P.scope block = scope andalso not (List.null variables)
        then () else raise ERR "close_forall" "wrong or empty binder frame"
      val _ = if input_limit >= 0 andalso output_limit >= 0 then () else
        raise ERR "close_forall" "invalid binder admission limits"
      fun refusal reason = (refuse reason;
        raise ERR "close_forall" ("binder admission refused: " ^ reason))
      fun admitted operation limit node =
        case G.unfolded_nodes graph metric limit node of
          SOME size => if size <= limit then size else
            (refusal operation;raise Fail "unreachable binder refusal")
        | NONE => (refusal operation;raise Fail "unreachable binder refusal")
      val _ = if Type.compare (G.type_of graph body,Type.bool) = EQUAL then ()
        else raise ERR "close_forall" "non-Boolean binder body"
      val _ = List.app (fn node =>
        case G.view graph node of G.Variable (G.Bound,_) =>
            if G.scope_visible graph scope (G.node_scope graph node) then ()
            else raise ERR "close_forall" "bound variable escapes frame"
          | _ => raise ERR "close_forall" "binder is not a Bound node")
        variables
      val bound_ids = Redblackset.addList (Redblackset.empty Int.compare,
        List.map G.node_id variables)
      val _ = if Redblackset.numItems bound_ids = List.length variables then ()
        else raise ERR "close_forall" "duplicate binder variable"
      val parents = parent_scope :: List.map (G.node_scope graph)
        (List.take (variables,List.length variables-1))
      val _ = List.app (fn (variable,parent) =>
        if G.scope_visible graph (G.node_scope graph variable) parent then ()
        else raise ERR "close_forall" "binder frames are out of order")
        (ListPair.zip (variables,parents))
      val _ = ignore (admitted "binder input" input_limit body)
      val overhead = case metric of G.RawNodes => 3
        | G.BinderInclusiveNodes => 4
      val _ = if List.length variables <= output_limit div overhead then ()
        else refusal "binder output"
      val body_limit = output_limit - overhead * List.length variables
      val _ = ignore (admitted "binder output" body_limit body)

      val source_nodes = P.sources block
      val _ = case resolution of NONE => ()
        | SOME result => R.validate graph scope result
      fun assignment node = case resolution of NONE => false
        | SOME result => R.is_assignment_source result node
      val _ = List.app (fn node => case resolution of NONE => ()
        | SOME result => if assignment node orelse R.node result node = node
            then () else raise ERR "close_forall" "assignment changes source")
        source_nodes
      val _ = case resolution of NONE => ()
        | SOME result => if R.node result body = body then () else
            raise ERR "close_forall" "assignment changes binder body"

      (* Check source witness endpoints and their canonical hypotheses before
         realization. Metadata supplies eigenvariable absence; unknown is
         never treated as closed. No free-variable scan of a residue occurs. *)
      val buckets = 4093
      val hint = SmtReplayImport.pointer_bucket 4 buckets
      val source_index = Array.array (buckets,[])
      val _ = List.app (fn node => if assignment node then () else
        let val term = G.representative graph node val bucket = hint term in
          Array.update (source_index,bucket,
            (term,node) :: Array.sub (source_index,bucket)) end) source_nodes
      fun canonical hypothesis =
        case List.find (fn (term,_) => Portable.pointer_eq (term,hypothesis))
            (Array.sub (source_index,hint hypothesis)) of
          SOME (_,node) => node
        | NONE => raise ERR "close_forall" "noncanonical witness hypothesis"
      fun clean theorem =
        let val (oracles,_) = Tag.dest_tag (Thm.tag theorem) in
          List.all (fn tag => tag = "DISK_THM") oracles andalso
          List.null (Tag.axioms_of (Thm.tag theorem)) end
      val chosen = Vector.fromList (indexed (fn (index,node) =>
        if assignment node then NONE else
          case witnesses of NONE => NONE | SOME provide =>
            case provide (index,node) of NONE => NONE
              | SOME theorem =>
                  if Portable.pointer_eq
                      (Thm.concl theorem,G.representative graph node) andalso
                      clean theorem then SOME theorem else
                    raise ERR "close_forall" "invalid source witness")
        source_nodes)
      val hypotheses = List.concat (indexed (fn (index,node) =>
        if assignment node then [] else case Vector.sub (chosen,index) of
            NONE => [node]
          | SOME theorem => List.map canonical (Thm.hyp theorem)) source_nodes)
      val visited = ref (Redblackset.empty Int.compare)
      fun hypothesis node =
        if Redblackset.member (!visited,G.node_id node) then () else
          let
            val _ = visited := Redblackset.add (!visited,G.node_id node)
            val _ = ignore (admitted "binder hypothesis" input_limit node)
            val _ = ignore
              (admitted "binder output hypothesis" output_limit node)
          in case G.free_variable_nodes graph node of
              NONE => refusal "unknown binder hypothesis dependency"
            | SOME free => if List.exists (fn variable =>
                  Redblackset.member (bound_ids,G.node_id variable)) free then
                raise ERR "close_forall"
                  "eigenvariable remains in a hypothesis"
              else ()
          end
      val _ = List.app hypothesis hypotheses
      val types = ref (Redblackset.empty Int.compare)
      val _ = List.app (fn node =>
        let val id = G.type_id graph node in
          if Redblackset.member (!types,id) then () else
            (types := Redblackset.add (!types,id);
             check_type (G.type_of graph node))
        end) (G.block_reachable graph (body :: variables @ hypotheses))
      val _ = check_type Type.bool
      val operators = List.map (fn variable =>
        let
          val operator = Term.rator (boolSyntax.mk_forall
            (G.representative graph variable,boolSyntax.T))
          val _ = check_type (Term.type_of operator)
        in operator end) variables
      fun supplied (index,node) =
        if List.nth (source_nodes,index) = node then Vector.sub (chosen,index)
        else raise ERR "close_forall" "source occurrence changed"
      val theorem = case resolution of NONE =>
          P.realize_with_sources block body edge supplied
        | SOME result => P.realize_resolved_with_sources block result
            body edge supplied

      fun generalize (((variable,parent),operator),(body,theorem)) =
        let
          val term = G.representative graph variable
          val abstraction = G.abstraction graph parent output_limit
            (variable,body)
          val node = G.application graph parent
            (G.constant graph parent operator,abstraction)
          val proof = Thm.GEN term theorem
          (* Both endpoints are fully admitted small binder terms. *)
          val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl proof)
            (G.representative graph node)) proof
        in (node,exact) end
      val (node,theorem) = List.foldr generalize (body,theorem)
        (ListPair.zip (ListPair.zip (variables,parents),operators))
      val _ = close ()
      val _ = G.validate_scope graph parent_scope
    in {node = node,theorem = theorem} end
end
