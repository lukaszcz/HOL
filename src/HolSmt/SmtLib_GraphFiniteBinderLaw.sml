(* No binder is inferred from a Q view or a caller-supplied node label. *)
structure SmtLib_GraphFiniteBinderLaw :> SmtLib_GraphFiniteBinderLaw =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure F = SmtLib_GraphFiniteQueryTransport
  structure A = SmtReplayFocusAdmission
  structure Scope = SmtReplayOwnedScopeReceipt
  structure L = SmtReplayOwnedLambda
  structure Law = SmtLib_GraphConditionalLambdaLaw
  structure P = SmtReplayProof
  structure D = SmtLib_GraphFiniteLawDAG
  structure Opening = SmtLib_GraphCheckedOpening
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphFiniteBinderLaw"
  datatype result = Needs of F.requirement list
    | Conditional of {fact:P.closed_fact,condition:G.node,source:G.node,
                      target:G.node,evidence:V.fact list}
    | Unconditional of L.canonical_policy_conversion
  datatype nested_result = NestedNeeds of F.requirement list
    | NestedLaw of {binding:F.nested_binding,law:F.body_binding}
  datatype location = Located of
      {frame:Scope.receipt,scope:G.scope,admission:A.policy_focus}
    | OpeningNeeded of F.requirement

  val promote =
    let val proposition = Term.mk_var ("finite_body_closed",Type.bool)
    in Thm.DISCH proposition
      (Thm.DISCH boolSyntax.T (Thm.ASSUME proposition)) end

  fun execute_internal nested condition_closed work plan
      {validation,profiles} =
    ((let
      val description = W.with_step work (fn () =>
        let val saved = F.body_description_with_policy_for work plan
            val _ = V.current_facts_with_policy_for work validation
        in saved end)
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val root_frame = Scope.root_with_policy work
      fun expected scope =
        {graph=graph,scope=scope,sources=sources,work=work}
      val first = W.with_step work (fn () =>
        A.current_query_with_policy work validation (#position description))
      fun unopened scope focus =
        let val actual = A.describe_with_policy_for (expected scope) focus
            val source = G.cached_opened_view graph scope (#node actual)
            val _ = G.validate_opened_view graph scope (#node actual) source
        in OpeningNeeded (F.CheckedOpening
          {original={scope=scope,node= #node actual},
           opened={scope=scope,node= #node source}}) end
      fun open_focus frame scope focus =
        let
          val actual = A.describe_with_policy_for (expected scope) focus
          val source = G.cached_opened_view graph scope (#node actual)
          val _ = G.validate_opened_view graph scope (#node actual) source
          val _ = case G.view graph (#node source) of G.AdmittedBinder _ => ()
            | _ => raise ERR "execute_nested"
                "registered target is not an admitted binder"
          val checked = Opening.bridge_generated_with_policy work
            {frame=frame,original= #node actual,opened= #node source,
             native_contract= #contract description,profiles=profiles,
             ordinal= #ordinal description,
             check_type=F.body_check_type_with_policy_for work plan}
          val next = A.generated_scoped_with_policy (expected scope) focus
            (#generated checked)
        in (next,#generated checked) end
      fun walk frame scope focus [] =
            Located {frame=frame,scope=scope,admission=focus}
        | walk frame scope focus (step::rest) = case step of
            F.FunctionChild =>
              let val (left,_) =
                    A.application_children_with_policy (expected scope) focus
              in walk frame scope left rest end
          | F.ArgumentChild =>
              let val (_,right) =
                    A.application_children_with_policy (expected scope) focus
              in walk frame scope right rest end
          | F.BinderBody =>
              let val actual = A.describe_with_policy_for
                    (expected scope) focus
              in case G.view graph (#node actual) of
                  G.OpaqueRetained =>
                    (case nested of NONE => unopened scope focus
                     | SOME _ =>
                         let val (next,_) = open_focus frame scope focus
                         in walk frame scope next (step::rest) end)
                | _ =>
                    let val inner = Scope.body_with_policy work frame
                          (#child actual)
                        val next = A.binder_body_with_policy
                          (expected scope) focus
                        val owner = Scope.description_with_policy_for work
                          inner
                    in walk inner (#scope owner) next rest end
              end
      val located = walk root_frame root first (#path description)
    in case located of OpeningNeeded reason => (Needs [reason],NONE)
      | Located {frame,scope,admission} =>
        let val actual = A.describe_with_policy_for (expected scope) admission
            val (actual,admission,opening) = case nested of NONE =>
                (actual,admission,NONE)
              | SOME _ => if #node actual<> #node (#binder description) andalso
                    #node actual= #node (#original description) then
                  let val (next,proof) = open_focus frame scope admission
                  in (A.describe_with_policy_for (expected scope) next,
                      next,SOME proof) end
                else (actual,admission,NONE)
        in if #node actual<> #node (#binder description) then
            if #node actual= #node (#original description) then
              (case unopened scope admission of OpeningNeeded reason =>
                 (Needs [reason],NONE)
               | _ => raise ERR "execute" "unreachable path")
            else raise ERR "execute" "different retained binder path"
          else
            let
              val body_frame = Scope.body_with_policy work frame
                (#child actual)
              val programme = case nested of NONE =>
                  F.realize_body_with_policy work plan
                    {validation=validation,root_frame=root_frame,
                     parent_frame=frame,body_frame=body_frame,
                     admission=admission,profiles=profiles}
                | SOME bindings => F.realize_body_with_nested_with_policy
                    work plan {validation=validation,root_frame=root_frame,
                      parent_frame=frame,body_frame=body_frame,
                      admission=admission,profiles=profiles,bindings=bindings}
            in case programme of F.BodyNeeds pending => (Needs pending,NONE)
              | F.BodyLaw {fact,condition,evidence,...} =>
                let
                  val (fact,condition) = if condition_closed andalso
                      not (Option.isSome condition) then
                    let
                      val (context,conditional,truth) = W.with_step work
                        (fn () =>
                        let
                          val context =
                            D.create_with_condition_frame_with_policy work
                              {frame=body_frame,condition_frame=root_frame,
                               native_contract= #contract description,
                               profiles=profiles,
                               ordinal= #ordinal description,
                               check_type=
                                 F.body_check_type_with_policy_for work plan}
                          val closed = V.scoped_recorded_closed_with_policy
                            work body_frame fact
                          val actual = D.of_closed_with_policy work context
                            closed
                          val equation = #target
                            (D.description_with_policy_for work context actual)
                          val truth = G.constant graph root boolSyntax.T
                          val tautology = D.evidence_with_policy work context
                            truth
                          val law = D.schema_with_policy work context
                            {theorem=promote,premises=[equation,truth],
                             target=equation}
                          val conditional = D.apply_with_policy work context
                            {law=law,premises=[actual,tautology],
                             target=equation}
                        in (context,conditional,truth) end)
                      val promoted = D.realize_with_policy work context
                        conditional
                    in (promoted,SOME truth) end
                    else (fact,condition)
                  val ordinal = W.with_step work (fn () =>
                    W.unused_policy_ordinal work
                      {role=W.ClosedRecord,minimum= #ordinal description})
                  val request:L.policy_request =
                    {graph=graph,scope=scope,sources=sources,work=work,
                     ordinal=ordinal,admission=admission,body_fact=fact,
                     native_contract= #contract description,profiles=profiles,
                     check_type=F.body_check_type_with_policy_for work plan}
                in case condition of NONE =>
                    (Unconditional (L.execute_canonical_with_policy
                      (L.prepare_canonical_admitted_with_policy request)),NONE)
                  | SOME antecedent =>
                    let
                      val converted = L.execute_conditional_with_policy
                        (L.prepare_conditional_admitted_with_policy request)
                      val ports = L.endpoints_conditional_with_policy_for
                        {graph=graph,caller=scope,scope=scope,sources=sources,
                         work=work} converted
                      val _ = if #condition ports=antecedent then () else
                        raise ERR "execute" "conditional body premise changed"
                      val recording = Law.record_receipt_with_policy work
                        {frame=frame,native_contract= #contract description,
                         conversion=converted,profiles=profiles,
                         ordinal= #ordinal description,
                         check_type=
                           F.body_check_type_with_policy_for work plan}
                      val _ = F.retain_recorded_with_policy work plan recording
                      val actual = W.with_step work (fn () =>
                        Law.recorded_with_policy_for work recording)
                      val fact = #fact actual
                      val held = case nested of NONE => NONE
                        | SOME _ =>
                          let
                            (* Root query opening can already have moved
                               the actual focus to the admitted binder.
                               Retain a genuine scoped opening receipt for
                               its original slot after the body succeeds;
                               an unfinished body performs no new proof. *)
                            val opening = case opening of SOME _ => opening
                              | NONE =>
                                if #node (#original description)=
                                    #node (#binder description) then NONE
                                else SOME (#generated
                                  (Opening.bridge_generated_with_policy work
                                    {frame=frame,
                                     original= #node (#original description),
                                     opened= #node (#binder description),
                                     native_contract= #contract description,
                                     profiles=profiles,
                                     ordinal= #ordinal description,
                                     check_type=
                                       F.body_check_type_with_policy_for
                                         work plan}))
                          in SOME (F.seal_nested_with_policy work plan
                            {recording=recording,evidence=evidence,
                             opening=opening}) end
                    in (Conditional {fact=fact,condition=antecedent,
                      source= #source ports,target= #target ports,
                      evidence=evidence},held) end
                end
            end
        end
    end) handle primary => (W.close work;raise primary))
  fun execute_with_policy work plan input =
    #1 (execute_internal NONE false work plan input)
  fun execute_conditioned_with_policy work plan input =
    #1 (execute_internal NONE true work plan input)

  fun execute_nested_conditioned_with_policy work plan
      {validation,profiles,bindings} =
    case execute_internal (SOME bindings) true work plan
        {validation=validation,profiles=profiles} of
      (Needs pending,_) => NestedNeeds pending
    | (Conditional {fact,condition,source,target,evidence},SOME binding) =>
        NestedLaw {binding=binding,
          law={plan=plan,fact=fact,condition=condition,source=source,
               target=target,evidence=evidence}}
    | _ => raise ERR "execute_nested" "missing genuine conditioned body law"
end
