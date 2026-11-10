(* Narrow checked alignment reused at the actual staged worker boundary.
   Exact endpoint ownership plus kernel ALPHA supplies the transport proof. *)
structure CPC_GraphOwnedResult :> CPC_GraphOwnedResult =
struct
  open SmtReplayGraph SmtReplayImport SmtWordGraph CPC_Proof
  structure G = SmtReplayGraph
  exception Adapter
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphOwnedResult"
  fun align {graph,scope,ordinary_limit,target,theorem,located,premises} =
    let
      val _ = G.validate_scope graph scope
      val _ = if ordinary_limit > 0 then () else
        raise ERR "align" "nonpositive original caller quota"
      val actual = Thm.concl theorem
      val expected = G.representative graph target
      val reported = #term (located : CPC_Proof.located_term)
      val hypotheses = Thm.hyp theorem
      val antecedents = List.map (#term : CPC_Proof.located_term -> Term.term)
        premises @ hypotheses
      val original_law = List.foldr boolSyntax.mk_imp actual antecedents
      val aligned_law = List.foldr boolSyntax.mk_imp expected antecedents
      val alpha_law = boolSyntax.mk_eq (actual,expected)
      fun whole term = if Option.isSome
          (SmtReplayImport.bounded_raw_size ordinary_limit term) andalso
          Option.isSome
          (SmtReplayImport.bounded_binder_size ordinary_limit term) then ()
        else raise Adapter
      (* Complete original/aligned conditional and equality propositions
         precede type/FV/alpha work even at custom caller limits. *)
      val _ = List.app whole (actual :: expected :: reported :: antecedents @
        [original_law,aligned_law,alpha_law])
      val _ = if Portable.pointer_eq (reported,expected) then () else
        raise ERR "align" "reported endpoint is not the retained target"
      fun visible node =
        if G.scope_visible graph scope (G.node_scope graph node) then () else
          raise ERR "align" "result captures an unavailable owned ID"
      val _ = visible target
      val variables = case G.free_variable_nodes graph target of
          SOME nodes => nodes | NONE => raise Adapter
      val _ = List.app (fn node =>
        (visible node;case G.view graph node of
            G.Variable (G.RigidSource,_) => ()
          | G.Variable (G.SolverFlexible,_) => ()
          | _ => raise Adapter)) variables
      val admission = SmtWordGraph.new_type_admission ()
      fun bounded_type ty =
        let fun visit [] _ = ()
              | visit (ty :: rest) count =
                  if count >= ordinary_limit then raise Adapter else
                    visit ((if Type.is_vartype ty then [] else
                      #2 (Type.dest_type ty)) @ rest) (count+1)
        in visit [ty] 0 end
      fun inspect [] = ()
        | inspect (term :: rest) =
            (bounded_type (Term.type_of term);
             SmtWordGraph.admit_primitive_type admission (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 inspect (operator :: operand :: rest) end
             else if Term.is_abs term then
               let val (binder,body) = Term.dest_abs term in
                 inspect (binder :: body :: rest) end
             else inspect rest)
      val _ = inspect (actual :: expected :: reported :: antecedents @
        [original_law,aligned_law,alpha_law])
        handle Conv.UNCHANGED => raise Adapter
      val names = List.map (G.representative graph) variables
      fun same_variables term =
        let val free = Term.free_vars term in
          length free = length names andalso
          List.all (fn name => List.exists (Term.aconv name) free) names andalso
          List.all (fn name => List.exists (Term.aconv name) names) free end
      val _ = if same_variables actual andalso same_variables reported then ()
        else raise ERR "align" "result changed exact owned free-ID inventory"
      val _ = Library.check_oracle_tags "CPC_GraphOwnedResult" "align" theorem
      val aligned = Thm.EQ_MP (Thm.ALPHA actual expected) theorem
      val retained = Thm.hyp aligned
      fun member term terms = List.exists
        (fn value => Portable.pointer_eq (term,value)) terms
      val _ = if length retained = length hypotheses andalso
          List.all (fn term => member term retained) hypotheses andalso
          List.all (fn term => member term hypotheses) retained then () else
        raise ERR "align" "alignment changed canonical actual Hyp"
      val _ = G.validate_scope graph scope
    in (aligned,{term = expected,provenance = #provenance located}) end
end
