structure SmtLib_GraphGuardedCarrierCancel
  :> SmtLib_GraphGuardedCarrierCancel =
struct
  open SmtReplayGraph SmtReplayBinder SmtReplayProof SmtReplaySource
    SmtReplayImport SmtLib_GraphNumGuardedArithmetic
    SmtLib_GraphPreprocessDerived Drule
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure D = SmtLib_GraphPreprocessDerived
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphGuardedCarrierCancel"
  exception Unsupported
  datatype conversion = Conversion of
    {source : G.node,target : G.node,equality : G.node,theorem : Thm.thm,
     premise : G.node,operand : G.node}
  type options =
    {graph : G.graph,scope : G.scope,admission : SmtReplayBinder.admission,
     template_limit : int}
  fun source (Conversion {source,...}) = source
  fun target (Conversion {target,...}) = target
  fun equality (Conversion {equality,...}) = equality
  fun theorem (Conversion {theorem,...}) = theorem
  fun premise (Conversion {premise,...}) = premise
  fun operand (Conversion {operand,...}) = operand
  datatype work = Visit of G.node | Finish of G.node * G.node * G.node
  fun discover ({graph,scope,admission,template_limit} : options)
      {body,operand} =
    let
      val {metric,input_limit,output_limit,check_type,refuse} = admission
      fun reject text =
        (refuse text;raise ERR "discover" ("guarded cancel: " ^ text))
      val _ = G.validate_scope graph scope
      fun visible node =
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then () else
           raise ERR "discover" "owned input escapes active local frame")
      val _ = List.app visible [body,operand]
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          template_limit > 0 then () else reject "nonpositive contract"
      fun count limit term = case metric of G.RawNodes =>
          SmtReplayImport.bounded_raw_size limit term
        | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit term
      fun admit label limit term = case count limit term of SOME size => size
        | NONE => (reject label;raise Fail "unreachable")
      fun types [] = ()
        | types (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (left,right) = Term.dest_comb term in
                 types (left :: right :: pending) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 types (variable :: body :: pending) end
             else types pending)
      fun run operator guard consequent universal =
        let
          val actual = G.representative graph body
          val input_count = admit "whole local body input" input_limit actual
          val fixed = if universal then boolTheory.IMP_CONG
            else boolTheory.AND_CONG
          val fixed_count = admit "whole fixed conditional congruence law"
            template_limit (Thm.concl fixed)
          (* A conservative complete specialization bound also covers every
             local congruence, DISCH, body equality and final proposition
             ALPHA. It may require ordinary compatibility continuation. *)
          val _ = if fixed_count > 0 andalso
              input_count <= output_limit div fixed_count then () else
            reject "whole conditional specialization/ALPHA law"
          val negative_false = boolSyntax.mk_neg boolSyntax.F
          val _ = ignore (admit "whole closed denied-F source schema"
            template_limit negative_false)
          val _ = ignore (admit "whole denied-F proposition ALPHA law"
            output_limit (boolSyntax.mk_eq (negative_false,negative_false)))
          val _ = types [actual,Thm.concl fixed,negative_false]
          val owned = case G.free_variable_nodes graph body of SOME nodes =>
              nodes | NONE => raise ERR "discover" "unknown local free IDs"
          val _ = List.app visible owned
          val _ = List.app (fn node => case G.view graph node of
              G.Variable (G.RigidSource,_) => ()
            | G.Variable (G.Bound,_) => ()
            | _ => raise ERR "discover" "unowned local free-variable kind")
            owned
          val free = Term.free_vars actual
          val _ = if List.length free = List.length owned andalso
              List.all (fn variable => List.exists (fn node =>
                Term.aconv variable (G.representative graph node)) owned) free
            then () else raise ERR "discover" "inexact local free-ID coverage"
          val producer = SmtLib_GraphNumGuardedArithmetic.create graph scope
            {template_limit = template_limit,check_type = check_type}
          val cancel = #cancel producer operand
          val _ = if #premise cancel = guard then () else raise Unsupported
          val equation = #target cancel
          val (old,replacement) = case G.view graph equation of
              G.Application (left,right) =>
                (case G.view graph left of G.Application (_,left) =>
                    (left,right)
                  | _ => raise ERR "discover" "changed cancellation equality")
            | _ => raise ERR "discover" "changed cancellation target"
          val _ = if replacement = operand then () else
            raise ERR "discover" "cancellation changed exact operand ID"
          val local_nodes = G.block_reachable graph [consequent]
          val _ = if List.exists (fn node => node = old) local_nodes andalso
              List.all (fn node => case G.view graph node of
                G.AdmittedBinder _ => false | G.OpaqueRetained => false
              | _ => true) local_nodes then () else raise Unsupported
          val context = D.discover graph scope
            {goal = ([G.representative graph guard],
                      boolSyntax.F),
             import_limit = input_limit,revisit = false,
             check_type = check_type,conversion = fn _ => NONE,
             facts = [],rules = [#rule cancel]}
          val _ = if S.assumption_nodes (D.original_sources context) = [guard]
            then () else raise ERR "discover" "local guard Source ID changed"
          val block = P.freeze graph {scope = scope,roots = D.roots context,
            sources = D.source_nodes context,template_limit = template_limit}
          val edge = case D.assembler context block equation of SOME edge =>
              edge | NONE => raise ERR "discover" "missing guarded derivation"
          val denied = S.denied_goal_node (D.original_sources context)
          val expected_false = G.representative graph denied
          val _ = ignore (admit "actual whole denied-F ALPHA law"
            output_limit (boolSyntax.mk_eq (negative_false,expected_false)))
          val not_false = Thm.NOT_INTRO
            (Thm.DISCH boolSyntax.F (Thm.ASSUME boolSyntax.F))
          val not_false = Thm.EQ_MP
            (Thm.ALPHA (Thm.concl not_false) expected_false) not_false
          (* This closed theorem proves an already recorded exact Source.
             P checks its endpoint, tags and canonical hypothesis membership;
             the actual nonnegative guard remains the sole surviving Hyp. *)
          val cancellation = P.realize_with_sources block equation edge
            (fn (_,node) => if node = denied then SOME not_false else NONE)
          val _ = if case Thm.hyp cancellation of [hypothesis] =>
                Portable.pointer_eq (hypothesis,G.representative graph guard)
              | _ => false then () else
            raise ERR "discover" "derived guard is not the original premise"
          val memo = ref (Redblackmap.mkDict Int.compare)
          fun required node = Redblackmap.find (!memo,G.node_id node)
          fun save node value = memo := Redblackmap.insert
            (!memo,G.node_id node,value)
          fun loop [] = ()
            | loop (Visit node :: pending) =
                if Option.isSome (Redblackmap.peek (!memo,G.node_id node)) then
                  loop pending
                else if node = old then
                  (save node (replacement,cancellation);loop pending)
                else (visible node;
                  case G.view graph node of G.Application (left,right) =>
                    loop (Visit left :: Visit right ::
                      Finish (node,left,right) :: pending)
                  | G.AdmittedBinder _ => raise Unsupported
                  | G.OpaqueRetained => raise Unsupported
                  | _ => (save node
                      (node,Thm.REFL (G.representative graph node));
                      loop pending))
            | loop (Finish (node,left,right) :: pending) =
                let val (left_node,left_proof) = required left
                    val (right_node,right_proof) = required right
                    val target = G.application graph scope
                      (left_node,right_node)
                in save node (target,Thm.MK_COMB (left_proof,right_proof));
                  loop pending end
          val _ = loop [Visit consequent]
          val (changed,proof) = required consequent
          val conditional = Thm.DISCH (G.representative graph guard) proof
          val law = Drule.SPECL
            [G.representative graph guard,G.representative graph guard,
             G.representative graph consequent,G.representative graph changed]
            fixed
          val _ = ignore (admit "actual specialized congruence law"
            output_limit (Thm.concl law))
          val unchanged = Thm.REFL (G.representative graph guard)
          val premises = if universal then Thm.CONJ unchanged conditional else
            Thm.CONJ (Thm.DISCH (G.representative graph consequent) unchanged)
              conditional
          val theorem = Thm.MP law premises
          val target = G.application graph scope
            (G.application graph scope (operator,guard),changed)
          val equality = G.application graph scope
            (G.application graph scope
              (G.constant graph scope (Term.inst
                (Type.match_type (Term.type_of boolSyntax.equality)
                  (boolSyntax.list_mk_fun ([Type.bool,Type.bool],Type.bool)))
                boolSyntax.equality),body),target)
          val expected = G.representative graph equality
          val _ = ignore (admit "actual final conditional body equality"
            output_limit expected)
          val theorem = Thm.EQ_MP
            (Thm.ALPHA (Thm.concl theorem) expected) theorem
          val (tags,_) = Tag.dest_tag (Thm.tag theorem)
          val _ = if null (Thm.hyp theorem) andalso
              List.all (fn tag => tag = "DISK_THM") tags andalso
              null (Tag.axioms_of (Thm.tag theorem)) then () else
            raise ERR "discover" "conditional transport is not a checked law"
        in SOME (Conversion {source = body,target = target,
          equality = equality,theorem = theorem,premise = guard,
          operand = operand}) end
    in case G.view graph body of G.Application (left,consequent) =>
        (case G.view graph left of G.Application (operator,guard) =>
           (case G.view graph operator of G.Constant _ =>
              let val term = G.representative graph operator
                  val implication = Term.same_const term boolSyntax.implication
                  val conjunction = Term.same_const term boolSyntax.conjunction
              in if implication orelse conjunction then
                  run operator guard consequent implication else NONE end
            | _ => NONE)
         | _ => NONE)
      | _ => NONE
    end handle Unsupported => NONE
end
