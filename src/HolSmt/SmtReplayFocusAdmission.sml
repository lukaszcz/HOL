structure SmtReplayFocusAdmission :> SmtReplayFocusAdmission =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure V = SmtLib_GraphSourcePortfolio
  val _ = SmtReplayProof.validate_closed_fact
  val _ = SmtReplayInvocationWork.original_sources
  val _ = SmtReplaySource.goal_source
  val _ = SmtLib_GraphNumericRuleMatch.instance_condition_for
  val ERR = Feedback.mk_HOL_ERR "SmtReplayFocusAdmission"
  datatype category = Original | Generated | Auxiliary
  type expected =
    {graph : G.graph,scope : G.scope,sources : S.sources,work : W.portfolio}
  type owner =
    {graph : G.graph,root : G.scope,sources : S.sources,work : W.portfolio,
     limits : W.limits,epoch : int}
  datatype focus = Focus of
    {owner : owner,traversal : G.scope,caller : G.scope,
     child : G.closure_child,node : G.node,category : category,
     (* Private provenance-only Original flag; not caller supplied. *)
     occurrence : int,goal : bool,compact : bool,guard : unit -> unit}
  fun protect work operation =
    operation () handle primary => (W.close work;raise primary)
  fun owner_of (Focus {owner,...}) = owner
  fun work_of focus = #work (owner_of focus)
  fun cap ({limits,...} : owner) Original = #input_limit limits
    | cap {limits,...} Generated = #output_limit limits
    | cap {limits,...} Auxiliary = #template_limit limits
  fun active (focus as Focus
      {owner = owner as {graph,root,sources,work,limits,epoch},
       traversal,caller,child,node,category,goal,compact,guard,...}) =
    protect work (fn () =>
      (W.validate work graph root sources limits;
       G.validate_scope graph traversal;G.validate_scope graph caller;
       if Type.type_epoch () = epoch then () else
         raise ERR "active" "original Type epoch changed";
       guard ();
       if G.closure_child_node graph caller child = node andalso
           G.scope_visible graph traversal (G.node_scope graph node)
         then () else raise ERR "active" "held canonical path changed";
       if compact orelse (goal andalso category = Original) then () else
       List.app (fn metric =>
         case G.unfolded_nodes graph metric (cap owner category) node of
             SOME n => if n <= cap owner category then () else
               raise ERR "active" "focus exceeds original category cap"
           | NONE => raise ERR "active" "focus lacks complete cached metric")
         [G.RawNodes,G.BinderInclusiveNodes]))
  (* Compare private held owner fields before activating a supplied focus.
     Failure retires EXPECTED Work only, never a foreign held invocation. *)
  fun validate_for {graph,scope,sources,work} (held as Focus
      {owner = owner,traversal,...}) =
    protect work (fn () =>
      let val limits = W.semantic_limits work
          val root = S.owning_scope sources
          val _ = W.validate work graph root sources limits
          val _ = G.validate_scope graph scope
          val _ = if Portable.pointer_eq (graph,#graph owner) andalso
              scope = traversal andalso root = #root owner andalso
              Portable.pointer_eq (sources,#sources owner) andalso
              Portable.pointer_eq (work,#work owner) then () else
            raise ERR "validate_for" "different expected focus owner/frame"
      in active held end)
  fun describe_for expected (held as Focus
      {owner,node,child,category,occurrence,...}) =
    (validate_for expected held;
     {node = node,child = child,category = category,
      source_limit = cap owner category,occurrence = occurrence})
  fun invoke focus operation =
    (active focus;let val answer = operation () in active focus;answer end)
  fun spend focus amount =
    (active focus;W.spend (work_of focus) amount;active focus)

  fun initial work {occurrence,view} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val _ = if occurrence >= 0 then () else
          raise ERR "initial" "negative original occurrence"
        fun select [] _ = raise ERR "initial" "absent original occurrence"
          | select (source::rest) i =
              (W.spend work 1;if i = 0 then source else select rest (i-1))
        val source = select (S.reconciliation_sources sources) occurrence
        fun registered () =
          G.validate_opened_view graph root (#node source) view
        val _ = registered ()
        val node = #node view
        val child = G.closure_root graph root node
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = node,
           category = Original,occurrence = occurrence,goal = false,
           compact = false,
           guard = registered}
        val _ = active result
    in result end)

  (* This path does NOT claim an opened recipe when NONE is supplied.
     Original positive DAGs/residues are provenance DATA; only applicable
     operation producers admit their local realized syntax. *)
  fun initial_goal work {view} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val original = S.goal_source sources
        fun retained () =
          let val saved = S.goal_source sources
          in if #node saved = #node original andalso
              Portable.pointer_eq (#original saved,#original original) andalso
              Portable.pointer_eq (#bridge saved,#bridge original) then () else
            raise ERR "initial_goal" "retained positive Source changed" end
        fun registered () = (retained ();
          case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened)
        val _ = registered ()
        val node = case view of NONE => #node original
          | SOME opened => #node opened
        val child = G.closure_root graph root node
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = node,
           category = Original,occurrence = ~1,goal = true,compact = false,
           guard = registered}
        val _ = active result
    in result end)

  (* A genuine ordered assumption, not the denial or a caller category.
     NONE retains original import DATA only; SOME is its registered view.
     Applicable local producers admit syntax. No whole-assumption bound. *)
  fun initial_assumption work {occurrence,view} =
    W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val _ = if occurrence >= 1 then () else
          raise ERR "initial_assumption" "not an original assumption index"
        fun select [] _ = raise ERR "initial_assumption"
              "absent original assumption"
          | select (source::rest) i =
              (W.spend work 1;if i = 0 then source else select rest (i-1))
        val original = select (S.reconciliation_sources sources) occurrence
        fun registered () =
          (* Opaque S retains this immutable occurrence portfolio. SAME
             W/S identity is rechecked; guards do not rerun selection. *)
          let val _ = W.validate work graph root sources limits
          in case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened end
        val _ = registered ()
        val current = case view of NONE => #node original
          | SOME opened => #node opened
        val child = G.closure_root graph root current
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = current,
           category = Original,occurrence = occurrence,goal = true,
           compact = false,
           guard = registered}
        val _ = active result
    in result end)

  (* Private genuine fixed-selector provenance, never a caller cap or
     ordinary Source ordinal. Actual recording template is retained. *)
  fun initial_condition work {instance,index} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val data = SmtLib_GraphNumericRuleMatch.instance_condition_for
          work instance index
        val traversal = #traversal data val node = #node data
        val child = #child data
        fun registered () =
          let val held = SmtLib_GraphNumericRuleMatch.instance_condition_for
                work instance index
          in if #node held=node andalso #traversal held=traversal then () else
            raise ERR "initial_condition" "instantiated antecedent changed"
          end
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph=graph,root=root,sources=sources,work=work,
                    limits=limits,epoch=Type.type_epoch ()},
           traversal=traversal,caller=traversal,child=child,node=node,
           category=Generated,occurrence= ~3,goal=false,compact=false,
           guard=registered}
        val _ = active result
    in result end)

  fun initial_auxiliary work {law} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val expected =
          {graph = graph,scope = root,sources = sources,work = work}
        val data = SmtLib_GraphSelectedAuxiliary.describe_for expected law
        val current = #node (#opened data)
        fun registered () =
          SmtLib_GraphSelectedAuxiliary.validate_for expected law
        val child = G.closure_root graph root current
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = current,
           category = Auxiliary,occurrence = ~2,goal = false,
           compact = false,
           guard = registered}
        val _ = active result
    in result end)

  (* Normalize to the actual traversal frame but retain BOTH the incoming
     canonical handle path and its original caller; no raw child guess. *)
  fun descend (parent as Focus {owner,category,occurrence,goal,compact,...})
      traversal incoming_caller incoming extra result_category =
    let val graph = #graph owner
        val _ = spend parent 1
        val node = invoke parent
          (fn () => G.closure_child_node graph incoming_caller incoming)
        val child = invoke parent
          (fn () => G.closure_root graph traversal node)
        fun guard () =
          (active parent;
           ignore (G.closure_child_node graph incoming_caller incoming);
           extra ())
        val _ = spend parent 1
        val result = Focus
          {owner = owner,traversal = traversal,caller = traversal,
           child = child,node = node,category = result_category,
           occurrence = occurrence,goal = goal,compact = compact,guard = guard}
        val _ = active result
    in result end
  fun application_children (expected as {work,...} : expected)
      (parent as Focus {owner,caller,child,traversal,category,...}) =
    protect work (fn () =>
      (validate_for expected parent;W.with_step work (fn () =>
        let val graph = #graph owner val _ = spend parent 1
            val (left,right) = invoke parent (fn () =>
              G.closure_application_children graph caller child)
        in (descend parent traversal caller left (fn () => ()) category,
            descend parent traversal caller right (fn () => ()) category)
        end)))
  fun binder_body (expected as {work,...} : expected)
      (parent as Focus {owner,caller,child,category,...}) =
    protect work (fn () =>
      (validate_for expected parent;W.with_step work (fn () =>
        let val graph = #graph owner val _ = spend parent 1
            val closure = invoke parent
              (fn () => G.closure_child_binder graph caller child)
            val data = invoke parent
              (fn () => G.binder_closure_data graph caller closure)
            val body = invoke parent
              (fn () => G.binder_closure_body graph caller closure)
            fun backing () =
              ignore (G.binder_closure_data graph caller closure)
        in descend parent (#body_frame data) caller body backing category end)))

  val eq_id = #Name (Term.dest_thy_constid boolSyntax.equality)
  fun equality_sides focus node =
    let val graph = #graph (owner_of focus)
        fun view n = (spend focus 1;invoke focus (fn () => G.view graph n))
        val (partial,right) = case view node of G.Application pair => pair
          | _ => raise ERR "generated" "evidence is not an equality"
        val (head,left) = case view partial of G.Application pair => pair
          | _ => raise ERR "generated" "evidence is not an equality spine"
        val id = case view head of G.Constant id => id
          | _ => raise ERR "generated" "evidence has no equality constructor"
        val _ = if Term.uptodate_term boolSyntax.equality then () else
          raise ERR "generated" "fixed equality constructor retired"
        fun text {Thy,Name} =
          IntInf.fromInt (String.size Thy) + IntInf.fromInt (String.size Name)
        val _ = spend focus 1
        val amount = 1 + text (KernelSig.name_of_id id) +
          text (KernelSig.name_of_id eq_id)
        val _ = if amount <= IntInf.fromInt (W.work_limit (work_of focus))
            then spend focus (IntInf.toInt amount) else
          raise ERR "generated" "equality identity work exceeds original cap"
        val _ = if KernelSig.id_compare (id,eq_id) = EQUAL then () else
          raise ERR "generated" "not the actual equality constructor"
        val _ = if invoke focus (fn () => G.type_id graph left) =
            invoke focus (fn () => G.type_id graph right) then () else
          raise ERR "generated" "equality endpoint types differ"
    in (left,right) end
  fun generated (expected as {work,...} : expected)
      (parent as Focus {owner,node,traversal,...}) fact =
    protect work (fn () =>
      (validate_for expected parent;W.with_step work (fn () =>
        let val graph = #graph owner
            val limit = #template_limit (#limits owner)
            fun evidence () =
              P.validate_closed_fact graph traversal limit fact
            val _ = spend parent 1
            val _ = invoke parent evidence
            val equality = invoke parent (fn () => P.closed_node fact)
            val (left,right) = equality_sides parent equality
            val _ = if left = node then () else
              raise ERR "generated" "evidence source is not this exact focus"
            val incoming = invoke parent
              (fn () => G.closure_root graph traversal right)
        in descend parent traversal traversal incoming evidence Generated end)))
  fun generated_compact (expected as {work,...} : expected)
      (parent as Focus {owner,node,traversal,occurrence,goal,...}) receipt =
    protect work (fn () =>
      (validate_for expected parent;W.with_step work (fn () =>
        let
          fun evidence () =
            let val data =
                  SmtReplayOwnedLargeProofCore.conversion_description_for
                    work receipt
            in if Portable.pointer_eq (#graph data,#graph owner) andalso
                #scope data = traversal andalso
                Portable.pointer_eq (#sources data,#sources owner) andalso
                #source data = node then () else
              raise ERR "generated_compact" "different compact result owner"
            end
          val _ = evidence ()
          val data = SmtReplayOwnedLargeProofCore.conversion_description_for
            work receipt
          val _ = spend parent 1
          val incoming = G.closure_root (#graph owner) traversal (#target data)
          val result = Focus {owner = owner,traversal = traversal,
            caller = traversal,child = incoming,node = #target data,
            category = Generated,occurrence = occurrence,goal = goal,
            compact = true,guard = fn () => (active parent;evidence ())}
          val _ = active result
        in result end)))

  structure RP = SmtReplayResourcePolicy
  type pf_owner =
    {graph : G.graph,root : G.scope,sources : S.sources,work : W.portfolio,
     limits : RP.semantic_policy,epoch : int}
  datatype current_query_position = CurrentGoal
    | CurrentAssumption of IntInf.int
  type current_query_origin =
    {validation:V.validation,position:current_query_position,
     assumptions:V.fact list,selected:V.fact option,denied:V.fact,
     node:G.node,symbols:int}
  datatype pf_metric = PlainMetric | ScopedMetric of
    {capture:G.profiled_metric,profiles:G.policy_opaque_profile list}
    | CurrentQueryMetric of current_query_origin
  fun current_projection work
      ({validation,position,assumptions,selected,denied,node,symbols}:
        current_query_origin) =
    let
      val current=V.current_facts_with_policy_for work validation
      val _=if Portable.pointer_eq (assumptions,#assumptions current) andalso
          Portable.pointer_eq (denied,#denied current) then () else
        raise ERR "current_query_with_policy" "retained query facts changed"
      val endpoint=case (position,selected) of
          (CurrentGoal,NONE)=> #goal current
        | (CurrentAssumption _,SOME fact)=>V.endpoint fact
        | _=>raise ERR "current_query_with_policy"
            "different retained current query position"
      val _=if endpoint=node then () else
        raise ERR "current_query_with_policy" "current query endpoint changed"
    in if Term.term_epoch ()=symbols then () else
      raise ERR "current_query_with_policy" "current query Term epoch changed"
    end
  datatype policy_focus = PolicyFocus of
    {pf_owner : pf_owner,traversal : G.scope,caller : G.scope,
     child : G.closure_child,node : G.node,category : category,
     (* Private provenance-only Original flag; not caller supplied. *)
     occurrence : IntInf.int,goal : bool,compact : bool,metric : pf_metric,
     guard : unit -> unit}
  fun pf_protect work operation =
    operation () handle primary => (W.close work;raise primary)
  fun pf_owner_of (PolicyFocus {pf_owner,...}) = pf_owner
  fun pf_work item = #work (pf_owner_of item)
  fun pf_cap ({limits,...} : pf_owner) Original = #input_limit limits
    | pf_cap {limits,...} Generated = #output_limit limits
    | pf_cap {limits,...} Auxiliary = #template_limit limits
  fun pf_active (item as PolicyFocus
      {pf_owner = pf_owner as {graph,root,sources,work,limits,epoch},
       traversal,caller,child,node,category,goal,compact,metric,guard,...}) =
    pf_protect work (fn () =>
      (W.validate_policy work graph root sources limits;
       G.validate_scope graph traversal;G.validate_scope graph caller;
       if Type.type_epoch () = epoch then () else
         raise ERR "pf_active" "original Type epoch changed";
       (case metric of CurrentQueryMetric origin=>
          current_projection work origin | _=>());
       guard ();
       if G.closure_child_node graph caller child = node andalso
           G.scope_visible graph traversal (G.node_scope graph node)
         then () else raise ERR "pf_active" "held canonical path changed";
       if compact orelse (goal andalso category = Original) then () else
       case metric of ScopedMetric {capture,...} =>
         let val data=G.profiled_metric_data graph traversal capture
             val maximum=pf_cap pf_owner category
         in if #node data=node andalso RP.allows maximum (#raw data)
             andalso RP.allows maximum (#inc data) then () else
           raise ERR "pf_active" "different or excessive scoped metric"
         end
       | CurrentQueryMetric _ => ()
       | PlainMetric => List.app (fn metric =>
         case G.unfolded_nodes_with_policy graph metric (pf_cap pf_owner
           category) node of
             SOME n => if RP.allows (pf_cap pf_owner category) n then () else
               raise ERR "pf_active" "focus exceeds original category cap"
           | NONE => raise ERR "pf_active"
             "focus lacks complete cached metric")
         [G.RawNodes,G.BinderInclusiveNodes]))
  (* Compare private held pf_owner fields before activating a supplied item.
     Failure retires EXPECTED Work only, never a foreign held invocation. *)
  fun validate_with_policy_for {graph,scope,sources,work} (held as PolicyFocus
      {pf_owner = pf_owner,traversal,...}) =
    pf_protect work (fn () =>
      let val limits = W.semantic_policy work
          val root = S.owning_scope sources
          val _ = W.validate_policy work graph root sources limits
          val _ = G.validate_scope graph scope
          val _ = if Portable.pointer_eq (graph,#graph pf_owner) andalso
              scope = traversal andalso root = #root pf_owner andalso
              Portable.pointer_eq (sources,#sources pf_owner) andalso
              Portable.pointer_eq (work,#work pf_owner) then () else
            raise ERR "validate_with_policy_for"
              "different expected focus owner/frame"
      in pf_active held end)
  fun describe_with_policy_for expected (held as PolicyFocus
      {pf_owner,node,child,category,occurrence,...}) =
    (validate_with_policy_for expected held;
     {node = node,child = child,category = category,
      source_limit = pf_cap pf_owner category,occurrence = occurrence})
  fun pf_invoke item operation =
    (pf_active item;let val answer = operation () in pf_active item;answer end)
  fun pf_spend item amount =
    (pf_active item;W.spend_policy (pf_work item) amount;pf_active item)

  fun initial_with_policy work {occurrence,view} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_policy work
        val _ = W.validate_policy work graph root sources limits
        val _ = if occurrence >= 0 then () else
          raise ERR "initial_with_policy" "negative original occurrence"
        fun select [] _ = raise ERR "initial_with_policy"
          "absent original occurrence"
          | select (source::rest) i =
              (W.spend_policy work 1;if i = 0 then source else select rest
                (i-1))
        val source = select (S.reconciliation_sources sources) occurrence
        fun registered () =
          G.validate_opened_view graph root (#node source) view
        val _ = registered ()
        val node = #node view
        val child = G.closure_root graph root node
        val _ = W.spend_policy work 1
        val result = PolicyFocus
          {pf_owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = node,
           category = Original,occurrence = occurrence,goal = false,
           compact = false,
           metric=PlainMetric,
           guard = registered}
        val _ = pf_active result
    in result end)

  (* This path does NOT claim an opened recipe when NONE is supplied.
     Original positive DAGs/residues are provenance DATA; only applicable
     operation producers admit their local realized syntax. *)
  fun initial_goal_with_policy work {view} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_policy work
        val _ = W.validate_policy work graph root sources limits
        val original = S.goal_source sources
        fun retained () =
          let val saved = S.goal_source sources
          in if #node saved = #node original andalso
              Portable.pointer_eq (#original saved,#original original) andalso
              Portable.pointer_eq (#bridge saved,#bridge original) then () else
            raise ERR "initial_goal_with_policy"
              "retained positive Source changed" end
        fun registered () = (retained ();
          case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened)
        val _ = registered ()
        val node = case view of NONE => #node original
          | SOME opened => #node opened
        val child = G.closure_root graph root node
        val _ = W.spend_policy work 1
        val result = PolicyFocus
          {pf_owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = node,
           category = Original,occurrence = ~1,goal = true,compact = false,
           metric=PlainMetric,
           guard = registered}
        val _ = pf_active result
    in result end)

  (* A genuine ordered assumption, not the denial or a caller category.
     NONE retains original import DATA only; SOME is its registered view.
     Applicable local producers admit syntax. No whole-assumption bound. *)
  fun initial_assumption_with_policy work {occurrence,view} =
    W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_policy work
        val _ = W.validate_policy work graph root sources limits
        val _ = if occurrence >= 1 then () else
          raise ERR "initial_assumption_with_policy"
            "not an original assumption index"
        fun select [] _ = raise ERR "initial_assumption_with_policy"
              "absent original assumption"
          | select (source::rest) i =
              (W.spend_policy work 1;if i = 0 then source else select rest
                (i-1))
        val original = select (S.reconciliation_sources sources) occurrence
        fun registered () =
          (* Opaque S retains this immutable occurrence portfolio. SAME
             W/S identity is rechecked; guards do not rerun selection. *)
          let val _ = W.validate_policy work graph root sources limits
          in case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened end
        val _ = registered ()
        val current = case view of NONE => #node original
          | SOME opened => #node opened
        val child = G.closure_root graph root current
        val _ = W.spend_policy work 1
        val result = PolicyFocus
          {pf_owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = child,node = current,
           category = Original,occurrence = occurrence,goal = true,
           compact = false,
           metric=PlainMetric,
           guard = registered}
        val _ = pf_active result
    in result end)

  (* Normalize to the actual traversal frame but retain BOTH the incoming
     canonical handle path and its original caller; no raw child guess. *)
  fun pf_descend_metric (parent as PolicyFocus
    {pf_owner,category,occurrence,goal,compact,...})
      traversal incoming_caller incoming extra result_category metric =
    let val graph = #graph pf_owner
        val _ = pf_spend parent 1
        val node = pf_invoke parent
          (fn () => G.closure_child_node graph incoming_caller incoming)
        val child = pf_invoke parent
          (fn () => G.closure_root graph traversal node)
        fun guard () =
          (pf_active parent;
           ignore (G.closure_child_node graph incoming_caller incoming);
           extra ())
        val _ = pf_spend parent 1
        val result = PolicyFocus
          {pf_owner = pf_owner,traversal = traversal,caller = traversal,
           child = child,node = node,category = result_category,
           occurrence = occurrence,goal = goal,compact = compact,
           metric = metric,guard = guard}
        val _ = pf_active result
    in result end
  (* Child captures use the actual checked closure frame. A root metric
     never supplies authority for another node or body frame. *)
  fun pf_descend (parent as PolicyFocus {metric,...})
      traversal incoming_caller incoming extra result_category =
    let val graph= #graph (pf_owner_of parent)
        val child_metric=case metric of PlainMetric=>PlainMetric
          | CurrentQueryMetric origin=>CurrentQueryMetric origin
          | ScopedMetric {profiles,...}=>
              let val node=pf_invoke parent (fn()=>
                    G.closure_child_node graph incoming_caller incoming)
                  val _=pf_spend parent 1
                  val capture=pf_invoke parent (fn()=>
                    G.prepare_scoped_profiled_metric graph traversal
                      {node=node,profiles=profiles})
              in ScopedMetric {capture=capture,profiles=profiles} end
    in pf_descend_metric parent traversal incoming_caller incoming extra
      result_category child_metric end
  fun application_children_with_policy (expected as {work,...} : expected)
      (parent as PolicyFocus {pf_owner,caller,child,traversal,category,...}) =
    pf_protect work (fn () =>
      (validate_with_policy_for expected parent;W.with_step work (fn () =>
        let val graph = #graph pf_owner val _ = pf_spend parent 1
            val (left,right) = pf_invoke parent (fn () =>
              G.closure_application_children graph caller child)
        in (pf_descend parent traversal caller left (fn () => ()) category,
            pf_descend parent traversal caller right (fn () => ()) category)
        end)))
  fun binder_body_with_policy (expected as {work,...} : expected)
      (parent as PolicyFocus {pf_owner,caller,child,category,...}) =
    pf_protect work (fn () =>
      (validate_with_policy_for expected parent;W.with_step work (fn () =>
        let val graph = #graph pf_owner val _ = pf_spend parent 1
            val closure = pf_invoke parent
              (fn () => G.closure_child_binder graph caller child)
            val data = pf_invoke parent
              (fn () => G.binder_closure_data graph caller closure)
            val body = pf_invoke parent
              (fn () => G.binder_closure_body graph caller closure)
            fun backing () =
              ignore (G.binder_closure_data graph caller closure)
        in pf_descend parent (#body_frame data) caller body backing category
          end)))

  val pf_eq_id = #Name (Term.dest_thy_constid boolSyntax.equality)
  fun pf_equality_sides item node =
    let val graph = #graph (pf_owner_of item)
        fun view n = (pf_spend item 1;pf_invoke item (fn () => G.view graph n))
        val (partial,right) = case view node of G.Application pair => pair
          | _ => raise ERR "generated_with_policy"
            "evidence is not an equality"
        val (head,left) = case view partial of G.Application pair => pair
          | _ => raise ERR "generated_with_policy"
            "evidence is not an equality spine"
        val id = case view head of G.Constant id => id
          | _ => raise ERR "generated_with_policy"
            "evidence has no equality constructor"
        val _ = if Term.uptodate_term boolSyntax.equality then () else
          raise ERR "generated_with_policy"
            "fixed equality constructor retired"
        fun text {Thy,Name} =
          IntInf.fromInt (String.size Thy) + IntInf.fromInt (String.size Name)
        val _ = pf_spend item 1
        val amount = 1 + text (KernelSig.name_of_id id) +
          text (KernelSig.name_of_id pf_eq_id)
        val _ = if RP.allows (W.remaining_policy (pf_work item)) amount
            then pf_spend item amount else
          raise ERR "generated_with_policy"
            "equality identity work exceeds original cap"
        val _ = if KernelSig.id_compare (id,pf_eq_id) = EQUAL then () else
          raise ERR "generated_with_policy"
            "not the actual equality constructor"
        val _ = if pf_invoke item (fn () => G.type_id graph left) =
            pf_invoke item (fn () => G.type_id graph right) then () else
          raise ERR "generated_with_policy" "equality endpoint types differ"
    in (left,right) end
  fun generated_with_policy (expected as {work,...} : expected)
      (parent as PolicyFocus {pf_owner,node,traversal,...}) fact =
    pf_protect work (fn () =>
      (validate_with_policy_for expected parent;W.with_step work (fn () =>
        let val graph = #graph pf_owner
            val limit = #template_limit (#limits pf_owner)
            fun evidence () =
              P.validate_closed_fact_with_policy graph traversal limit fact
            val _ = pf_spend parent 1
            val _ = pf_invoke parent evidence
            val equality = pf_invoke parent (fn () => P.closed_node fact)
            val (left,right) = pf_equality_sides parent equality
            val _ = if left = node then () else
              raise ERR "generated_with_policy"
                "evidence source is not this exact focus"
            val incoming = pf_invoke parent
              (fn () => G.closure_root graph traversal right)
        in pf_descend parent traversal traversal incoming evidence Generated
          end)))
  (* A genuine lazy fixed-law owner is the producer, not caller theorem or
     arbitrary node DATA. Fill its cache outside our own Work action. *)
  fun initial_law_with_policy work {owner,natural,universal} =
    pf_protect work (fn () =>
    let
      val fact = SmtLib_CarrierLaws.get_with_policy_for work owner
        {natural=natural,universal=universal}
    in W.with_step work (fn () =>
      let val sources = W.original_sources work
          val graph = S.owning_graph sources
          val root = S.owning_scope sources
          val limits = W.semantic_policy work
          fun registered () =
            (SmtLib_CarrierLaws.validate_with_policy_for work owner;
             P.validate_closed_fact_with_policy graph root
               (#template_limit limits) fact)
          val _ = W.validate_policy work graph root sources limits
          val _ = registered ()
          val current = P.closed_node fact
          val child = G.closure_root graph root current
          val _ = W.spend_policy work 1
          val result = PolicyFocus
            {pf_owner={graph=graph,root=root,sources=sources,
              work=work,limits=limits,epoch=Type.type_epoch ()},
             traversal=root,caller=root,child=child,node=current,
             category=Auxiliary,occurrence= ~2,goal=false,compact=false,
           metric=PlainMetric,
             guard=registered}
          val _ = pf_active result
      in result end)
    end)

  (* Only a receipt from the selected law's actual policy producer; no old
     finite receipt cast and no theorem/node tuple supplied by the caller. *)
  fun initial_auxiliary_with_policy work {law} = W.with_step work (fn () =>
    let val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val limits=W.semantic_policy work
        val expected={graph=graph,scope=root,sources=sources,work=work}
        val data=SmtLib_GraphSelectedAuxiliary.describe_with_policy_for
          expected law
        val current= #node (#opened data)
        fun registered ()=
          SmtLib_GraphSelectedAuxiliary.validate_with_policy_for expected law
        val _=W.validate_policy work graph root sources limits
        val child=G.closure_root graph root current
        val _=W.spend_policy work 1
        val result=PolicyFocus
          {pf_owner={graph=graph,root=root,sources=sources,work=work,
                     limits=limits,epoch=Type.type_epoch ()},
           traversal=root,caller=root,child=child,node=current,
           category=Auxiliary,occurrence= ~2,goal=false,compact=false,
           metric=PlainMetric,
           guard=registered}
        val _=pf_active result
    in result end)

  (* Only the actual policy matcher instance can supply a generated
     antecedent. Neither a raw theorem nor an old finite instance is cast. *)
  fun initial_condition_with_policy work {instance,index} =
    W.with_step work (fn () =>
    let val sources=W.original_sources work
        val graph=S.owning_graph sources val root=S.owning_scope sources
        val limits=W.semantic_policy work
        val _=W.validate_policy work graph root sources limits
        val
          data=SmtLib_GraphNumericRuleMatch.instance_condition_with_policy_for
          work instance index
        val traversal= #traversal data val node= #node data
        val child= #child data
        fun registered ()=
          let val held=
                SmtLib_GraphNumericRuleMatch.instance_condition_with_policy_for
                  work instance index
          in if #node held=node andalso #traversal held=traversal then () else
            raise ERR "initial_condition_with_policy"
              "instantiated antecedent changed" end
        val _=W.spend_policy work 1
        val result=PolicyFocus
          {pf_owner={graph=graph,root=root,sources=sources,work=work,
                     limits=limits,epoch=Type.type_epoch ()},
           traversal=traversal,caller=traversal,child=child,node=node,
           category=Generated,occurrence= ~3,goal=false,compact=false,
           metric=PlainMetric,
           guard=registered}
        val _=pf_active result
    in result end)

  (* Only P's genuine same-production fact/RHS join supplies this evidence.
     Check expected Work/Source/frame before activating that backing. *)
  fun generated_scoped_with_policy (expected as {work,...} : expected)
      (parent as PolicyFocus {pf_owner,node,traversal,...}) saved =
    pf_protect work (fn()=>
      (validate_with_policy_for expected parent;W.with_step work (fn()=>
      let val graph= #graph pf_owner
          val maximum= #template_limit (#limits pf_owner)
          val _=pf_spend parent 1
          fun evidence ()=ignore
            (P.scoped_generated_equality_for graph traversal maximum saved)
          val data=pf_invoke parent (fn()=>
            P.scoped_generated_equality_for graph traversal maximum saved)
          val equality=pf_invoke parent (fn()=>P.closed_node (#fact data))
          val(left,right)=pf_equality_sides parent equality
          val _=if left=node andalso left= #source data andalso
              right= #target data then () else
            raise ERR "generated_scoped_with_policy"
              "different actual equality source or target"
          val incoming=pf_invoke parent
            (fn()=>G.closure_root graph traversal right)
      in pf_descend_metric parent traversal traversal incoming evidence
        Generated (ScopedMetric
          {capture= #metric data,profiles= #profiles data}) end)))

  (* This exact validated projection defers size admission; it does not
     claim compact-constructor provenance or a whole-query native bound.
     Every native consumer must quote its actual operands using the existing
     Generated/output contract, including bodies and surviving hypotheses. *)
  fun current_query_with_policy work validation position =
    pf_protect work (fn()=>
    let
      val current=V.current_facts_with_policy_for work validation
      val sources=W.original_sources work
      val graph=S.owning_graph sources val root=S.owning_scope sources
      val limits=W.semantic_policy work
      val _=W.validate_policy work graph root sources limits
      val (node,selected,occurrence,goal)=case position of
          CurrentGoal=>(#goal current,NONE,~1,true)
        | CurrentAssumption index=>
          let
            val _=if index>=0 then () else
              raise ERR "current_query_with_policy"
                "negative current assumption occurrence"
            fun seek [] _=raise ERR "current_query_with_policy"
                  "current assumption occurrence absent"
              | seek (fact::rest) remaining=
                (W.spend_policy work 1;
                 if remaining=0 then fact else seek rest (remaining-1))
            val fact=seek (#assumptions current) index
          in (V.endpoint fact,SOME fact,index,false) end
      val origin:current_query_origin=
        {validation=validation,position=position,
         assumptions= #assumptions current,selected=selected,
         denied= #denied current,node=node,symbols=Term.term_epoch ()}
      val child=G.closure_root graph root node
      val _=W.spend_policy work 1
      val result=PolicyFocus
        {pf_owner={graph=graph,root=root,sources=sources,work=work,
                   limits=limits,epoch=Type.type_epoch ()},
         traversal=root,caller=root,child=child,node=node,
         category=Generated,occurrence=occurrence,goal=goal,compact=false,
         metric=CurrentQueryMetric origin,guard=fn()=>()}
      val _=pf_active result
    in result end)
end
