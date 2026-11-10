(* Authentic finite scoped syntax. No theorem or closure permission. *)
signature SmtReplayOwnedScopedValueSyntax =
sig
  type plan
  type syntax=SmtLib_GraphParserValue.proof_term
  datatype requirement = NativeOpening of syntax
  datatype preparation = Prepared of plan | Needs of requirement list
  (* Outside an action. The context has already authenticated the actual
     enclosing Bind and classified its entire child command queue. This
     pass admits the exact expanded binder-free child syntax before any
     native body construction. It retains names and a metadata-only N
     freeze plan, not a theorem, scoped result, or a callback certificate. *)
  val prepare : SmtReplayInvocationWork.portfolio ->
    SmtReplayOwnedScopedValueContext.context -> preparation
  (* SAME caller-owned action; expected Work precedes held backing. The
     returned shapes/Type inventory are DATA. The sealed programme owner
     must finish all rule/Hyp/closing portfolios before callbacks/native
     execution. In particular no caller may label this syntax Ready. *)
  val data_for : SmtReplayInvocationWork.portfolio -> plan ->
    {context:SmtReplayOwnedScopedValueContext.context,
     body:syntax,body_profile:SmtReplayNamedContext.profile,
     key:syntax -> int,name:syntax -> Term.term,
     profile:syntax -> SmtReplayNamedContext.profile,
     semantic:syntax -> SmtReplayGraph.node,
     view:syntax -> syntax SmtReplayNamedContext.view,
     reachable:syntax list,cells:SmtReplayValueInterpretation.cell list,
     type_ports:Type.hol_type list,
     freeze:syntax SmtReplayNamedContext.freeze_plan}
end
