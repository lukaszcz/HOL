(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplaySourceHypAdmission :> SmtReplaySourceHypAdmission =
struct
  open SmtReplayGraph SmtReplayBinder SmtReplayImport
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtReplaySourceHypAdmission"
  type view =
    {source : G.node,retained : Term.term,admitted : G.node,
     bridge : Thm.thm,free_variables : G.node list}
  datatype certificate = Certificate of
    {graph : G.graph,owner : G.scope,view : view,allow_bound : bool}
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end
  fun raw metric limit term = case metric of
      G.RawNodes => SmtReplayImport.bounded_raw_size limit term
    | G.BinderInclusiveNodes =>
        SmtReplayImport.bounded_binder_size limit term
  fun preflight graph scope
      {source,retained,admitted,bridge,free_variables}
      allow_bound
      ({metric,input_limit,output_limit,check_type,refuse} :
       SmtReplayBinder.admission) =
    let
      fun refusal label =
        (refuse label;raise ERR "admission" ("hypothesis admission: " ^ label))
      val _ = G.validate_scope graph scope
      val _ = if input_limit > 0 andalso output_limit > 0 then () else
        refusal "nonpositive hypothesis admission limits"
      val source_scope = G.node_scope graph source
      val _ = G.validate_scope graph source_scope
      val _ = if G.scope_visible graph scope source_scope andalso
          G.scope_visible graph scope (G.node_scope graph admitted) then ()
        else raise ERR "admission" "certificate endpoints escape their owner"
      val _ = if Portable.pointer_eq
          (retained,G.representative graph source) then () else
        raise ERR "admission" "original retained hypothesis pointer changed"
      fun source_size label limit = case raw metric limit retained of
          SOME _ => () | NONE => refusal label
      fun admitted_size label limit =
        case G.unfolded_nodes graph metric limit admitted of
          SOME size => if size <= limit then () else refusal label
        | NONE => refusal "unknown admitted hypothesis size"
      val _ = source_size "original hypothesis input" input_limit
      val _ = admitted_size "admitted hypothesis input" input_limit
      val _ = source_size "original hypothesis output" output_limit
      val _ = admitted_size "admitted hypothesis output" output_limit
      val law = Thm.concl bridge
      fun law_size label limit = case raw metric limit law of
          SOME _ => () | NONE => refusal label
      val _ = law_size "whole hypothesis bridge input" input_limit
      val _ = law_size "whole hypothesis bridge output" output_limit
      (* Only bounded original hypotheses enter actual type/FV traversal. *)
      fun types [] = ()
        | types (term :: rest) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 types (operator :: operand :: rest) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: rest) end
             else types rest)
      val _ = types [retained,law]
      val _ = List.app (check_type o G.type_of graph)
        (G.reachable graph [admitted])
      val _ = if Type.compare (G.type_of graph source,Type.bool) = EQUAL
          andalso Type.compare (G.type_of graph admitted,Type.bool) = EQUAL
        then () else raise ERR "admission" "hypothesis is not Boolean"
      fun bounded_variables [] _ = ()
        | bounded_variables (_ :: rest) count =
            if count >= input_limit then refusal "hypothesis variable count"
            else bounded_variables rest (count+1)
      val _ = bounded_variables free_variables 0
      fun owned variable =
        let
          val _ = case G.view graph variable of
              G.Variable (G.RigidSource,_) => ()
            | G.Variable (G.Bound,_) => if allow_bound then () else
                raise ERR "admission" "root hypothesis has a Bound variable"
            | _ => raise ERR "admission" "hypothesis variable is not canonical"
          val _ = check_type (G.type_of graph variable)
          val _ = if G.scope_visible graph scope
              (G.node_scope graph variable) andalso
              G.scope_visible graph source_scope
                (G.node_scope graph variable) then () else
            raise ERR "admission" "hypothesis variable escapes its Source"
        in G.representative graph variable end
      val variables = List.map owned free_variables
      val expected = Redblackset.addList
        (Redblackset.empty Int.compare,List.map G.node_id free_variables)
      val _ = if Redblackset.numItems expected = List.length variables then ()
        else raise ERR "admission" "duplicate hypothesis variable ID"
      fun distinct [] = ()
        | distinct (variable :: rest) =
            (if List.exists (Term.aconv variable) rest then
               raise ERR "admission" "ambiguous hypothesis variable spelling"
             else ();distinct rest)
      val _ = distinct variables
      val actual = Term.free_vars retained
      val _ = if List.length actual = List.length variables andalso
          List.all (fn variable =>
            List.exists (Term.aconv variable) variables) actual then () else
        raise ERR "admission" "original hypothesis typed FV set differs"
      val actual_nodes = case G.free_variable_nodes graph admitted of
          SOME nodes => nodes
        | NONE => raise ERR "admission" "unknown admitted hypothesis variables"
      val _ = List.app (fn node => ignore (owned node)) actual_nodes
      val ids = Redblackset.addList
        (Redblackset.empty Int.compare,List.map G.node_id actual_nodes)
      val _ = if Redblackset.equal (ids,expected) then () else
        raise ERR "admission" "hypothesis free-variable IDs differ"
      val _ = if List.null (Thm.hyp bridge) andalso clean bridge then () else
        raise ERR "admission" "hypothesis bridge is not closed and clean"
      val (left,right) = Term.dest_eq (Thm.concl bridge)
      val _ = if Portable.pointer_eq (left,retained) andalso
          Portable.pointer_eq (right,G.representative graph admitted)
        then () else raise ERR "admission" "bridge endpoints are not exact"
    in () end
  fun new graph scope {source,admitted,bridge,source_variables,
                       allow_bound,admission} =
    let
      val view = {source = source,retained = G.representative graph source,
        admitted = admitted,bridge = bridge,free_variables = source_variables}
      val _ = preflight graph scope view allow_bound admission
    in Certificate {graph = graph,owner = scope,view = view,
      allow_bound = allow_bound} end
  fun check (Certificate {graph,owner,view,allow_bound})
      {source,scope,variables,admission} =
    let
      val _ = G.validate_scope graph owner
      val _ = if source = #source view then () else
        raise ERR "check" "certificate names a different original Source"
      val _ = preflight graph scope view allow_bound admission
      val _ = List.app (fn variable =>
        (case G.view graph variable of G.Variable (G.Bound,_) => ()
          | _ => raise ERR "check" "annotation is not a Bound variable";
         if G.scope_visible graph scope (G.node_scope graph variable) then ()
           else raise ERR "check" "annotation escapes the consumer scope";
         #check_type admission (G.type_of graph variable);
         List.app (fn free =>
           if free = variable orelse not (Term.aconv
               (G.representative graph free)
               (G.representative graph variable)) then () else
             raise ERR "check" "distinct IDs alias an annotation variable")
           (#free_variables view))) variables
    in view end
end
