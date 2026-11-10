(* Source proposal: explicitly chosen original int-bag occurrences only. *)
structure SmtLib_GraphIntBagPortfolio :> SmtLib_GraphIntBagPortfolio =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure P = SmtReplayProof
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure B = SmtLib_GraphIntBagCarrier
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphIntBagPortfolio"
  type choice = {view : G.source,law : P.closed_fact}
  fun prepare graph scope sources
      {admission : SmtReplayBinder.admission,template_limit,assumptions,
       goal,scope_opened} =
    let
      val epoch = Type.type_epoch ()
      fun active () =
        (G.validate_scope graph scope;
         if Type.type_epoch () = epoch then () else
           raise ERR "prepare" "original type admission epoch changed")
      val _ = active ()
      val {metric,input_limit,output_limit,check_type,refuse} = admission
      fun policy ty = (active ();check_type ty;active ())
      fun observed child = (active ();scope_opened child;active ())
      val guarded_admission =
        {metric = metric,input_limit = input_limit,output_limit = output_limit,
         check_type = policy,refuse = refuse}
      val _ = if G.root_scope graph = G.root_scope (S.owning_graph sources)
          andalso scope = S.owning_scope sources then () else
        raise ERR "prepare" "different original Source owner"
      val originals = S.assumption_nodes sources
      val length = List.length originals
      val _ = if template_limit > 0 andalso
          length < template_limit then () else
        raise ERR "prepare" "original occurrence portfolio exceeds cap"
      (* All supplied indices/views/laws are checked before conversion,
         including duplicate and unused caller rows. No ID-only lookup. *)
      val chosen = ref (Redblackmap.mkDict Int.compare)
      val selections = ref (Redblackmap.mkDict Int.compare :
        (int,G.node * choice) Redblackmap.dict)
      fun same_choice ({view = left,law = a} : choice)
          ({view = right,law = b} : choice) =
        #node left = #node right andalso
        Portable.pointer_eq (#original left,#original right) andalso
        Portable.pointer_eq (#bridge left,#bridge right) andalso
        Portable.pointer_eq (a,b)
      fun register node (choice as {view,law} : choice) =
        (active ();G.validate_opened_view graph scope node view;
         P.validate_closed_fact graph scope template_limit law;
         case Redblackmap.peek (!selections,G.node_id node) of
           NONE => selections := Redblackmap.insert
             (!selections,G.node_id node,(node,choice))
         | SOME (held,old) =>
             if held = node andalso same_choice old choice then () else
               raise ERR "prepare" "conflicting same-source conversion choice")
      val remaining = ref (template_limit-length-1)
      val _ = List.app (fn (index,{view,law} : choice) =>
        (active ();
         if !remaining > 0 then remaining := !remaining-1 else
           raise ERR "prepare" "choice incidences exceed original cap";
         if index >= 0 andalso index < length andalso
             not (Redblackmap.inDomain (!chosen,index)) then () else
           raise ERR "prepare" "duplicate or foreign occurrence index";
         register (List.nth (originals,index)) {view = view,law = law};
         chosen := Redblackmap.insert (!chosen,index,{view = view,law = law})))
        assumptions
      val denied = S.denied_goal_node sources
      val goal_node = case G.view graph denied of
          G.Application (_,node) => node
        | _ => raise ERR "prepare" "original denial is not negation"
      val _ = case goal of NONE => () | SOME choice => register goal_node choice
      type result = {source : G.node,target : G.node,theorem : Thm.thm}
      val converted = ref (Redblackmap.mkDict Int.compare :
        (int,G.node * choice * result) Redblackmap.dict)
      fun convert node (choice as {view,law} : choice) =
        (active ();G.validate_opened_view graph scope node view;
         P.validate_closed_fact graph scope template_limit law;
         case Redblackmap.peek (!converted,G.node_id node) of
           SOME (held,old,result) =>
             if held = node andalso same_choice old choice then result else
               raise ERR "prepare" "conversion memo identity differs"
         | NONE =>
             let val result = SmtLib_GraphIntBagCarrier.convert
                   {graph = graph,scope = scope,original = node,view = view,
                    law = law,admission = guarded_admission,
                    template_limit = template_limit,
                    scope_opened = observed}
                 val _ = active ()
                 val _ = G.validate_opened_view graph scope node view
                 val _ = P.validate_closed_fact graph scope template_limit law
                 val _ = if #source result = node then () else
                   raise ERR "prepare" "memo conversion original differs"
                 val _ = converted := Redblackmap.insert
                   (!converted,G.node_id node,(node,choice,result))
             in result end)
      fun record node view target theorem =
        let val target_view = G.record_opened_view graph scope
              template_limit target
        in P.record_conversion graph scope
          {source = node,source_view = view,target = target,
           target_view = target_view,theorem = theorem,
           template_limit = template_limit,check_type = policy}
        end
      fun assertion (index,node) =
        let val fact = F.original graph scope sources index
        in case Redblackmap.peek (!chosen,index) of NONE => fact
          | SOME (choice as {view,...}) =>
              let val result = convert node choice
                  val plan = record node view (#target result) (#theorem result)
              in F.binder_transport graph scope plan fact end end
      val facts = List.map assertion (ListPair.zip
        (List.tabulate (length,Lib.I),originals))
      val denied_fact = F.original graph scope sources length
      val (processed_goal,denied_fact) = case goal of
          NONE => (goal_node,denied_fact)
        | SOME choice =>
            let val result = convert goal_node choice
                val negative = G.constant graph scope boolSyntax.negation
                val target = G.application graph scope
                  (negative,#target result)
                (* The sole AP_TERM sees the already bounded whole local
                   conversion; source syntax discovery remains prerequisite. *)
                val denied_view = G.record_opened_view graph scope
                  template_limit denied
                val target_view = G.record_opened_view graph scope
                  template_limit target
                val _ = G.validate_opened_view graph scope denied denied_view
                val _ = G.validate_opened_view graph scope target target_view
                (* Admit BOTH actual endpoint syntax envelopes before AP_TERM
                   or aconv/ALPHA, even though original cached metrics may
                   remain opaque/unknown. No caller semantic view is used. *)
                val _ = List.app (fn metric =>
                  let val available = ref (template_limit-3)
                  in List.app (fn node =>
                    case G.unfolded_nodes graph metric template_limit node of
                      SOME count => if count <= !available then
                          available := !available-count else
                        raise ERR "prepare" "denial conversion exceeds cap"
                    | NONE => raise ERR "prepare" "unknown denial syntax")
                    [#node denied_view,#node target_view] end)
                  [G.RawNodes,G.BinderInclusiveNodes]
                val _ = active ()
                val eq = Thm.AP_TERM boolSyntax.negation (#theorem result)
                val _ = active ()
                val (left,right) = boolSyntax.dest_eq (Thm.concl eq)
                val _ = if Term.aconv left (G.representative graph denied)
                    andalso Term.aconv right (G.representative graph target)
                  then () else raise ERR "prepare" "denial endpoints differ"
                val eq = Thm.TRANS
                  (Thm.ALPHA (G.representative graph denied) left)
                  (Thm.TRANS eq
                    (Thm.ALPHA right (G.representative graph target)))
                val plan = record denied denied_view target eq
            in (#target result,F.binder_transport graph scope plan denied_fact)
            end
      val portfolio = F.validate graph scope sources
        {assumptions = facts,goal = processed_goal,denied = denied_fact,
         template_limit = template_limit}
    in GP.from_portfolio portfolio end
end
