structure SmtReplayOwnedTransport :> SmtReplayOwnedTransport =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure B = SmtReplayRecordedBeta
  structure C = SmtLib_GraphCarrierRoot
  structure L = SmtReplayOwnedLambda
  structure A = SmtReplayOwnedAlpha
  structure Q = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  val _ = SmtReplayOwnedLambda.prepare_admitted
  val _ = SmtReplayOwnedLambda.prepare
  val _ = SmtReplayOwnedAlpha.same_inside
  val _ = SmtReplaySource.goal_source
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedTransport"
  datatype provenance = OriginalOccurrence | OriginalDescendant
                      | GeneratedResult | GeneratedDescendant
                      | OriginalPositiveGoal | PositiveGoalDescendant
                      | UnopenedPositiveGoal | UnopenedGoalDescendant
                      | UnopenedOriginalOccurrence
                      | UnopenedOriginalDescendant
                      | ClosedAuxiliaryRoot | ClosedAuxiliaryDescendant
  type owner =
    {graph : G.graph,root : G.scope,sources : S.sources,
     work : W.portfolio,limits : W.limits,epoch : int}
  datatype focus = Focus of
    {owner : owner,traversal : G.scope,caller : G.scope,
     child : G.closure_child,node : G.node,
     original : G.source,opened : G.source,root_ordinal : int,
     provenance : provenance,goal_unopened : bool,
     guards : (unit -> unit) list,
     validated : IntInf.int ref}
  datatype conversion = Conversion of
    {initial : focus,target : focus,theorem : Thm.thm,
     guard : unit -> unit}
  datatype state = Ready | Running | Complete | Retired
  type footprint =
    {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int,ty : IntInf.int}
  datatype application_plan = ApplicationPlan of
    {parent : focus,old_left : focus,old_right : focus,
     new_left : focus,new_right : focus,left : conversion option,
     right : conversion option,policy : Type.hol_type -> unit,
     types : Type.hol_type list,result_types : Type.hol_type list,
     ordinal : int,state : state ref}

  fun owner_of (Focus {owner,...}) = owner
  fun work_of f = #work (owner_of f)
  fun protected work operation =
    operation () handle primary => (W.close work;raise primary)
  (* Validation follows a retained DAG. Visit each completed receipt once
     within this pure guard walk; a subsequent guard starts a new generation.
     No policy callback runs inside a walk, so retirement and epoch changes
     are checked again after every callback. Marks are private metadata and
     confer no work entitlement or admission. *)
  val validation_generation = ref (0 : IntInf.int)
  val validation_depth = ref 0
  fun validate_once seen operation =
    let
      val _ = if !validation_depth = 0 then
        validation_generation := !validation_generation + 1 else ()
      val generation = !validation_generation
      val _ = validation_depth := !validation_depth + 1
      fun leave () = validation_depth := !validation_depth - 1
    in
      ((if !seen = generation then () else
          (operation ();seen := generation));
       leave ())
      handle primary => (leave ();raise primary)
    end
  fun validation_guard operation =
    let val seen = ref (~1 : IntInf.int)
    in fn () => validate_once seen operation end

  fun active (Focus {owner = {graph,root,sources,work,limits,epoch},
                     traversal,caller,child,node,guards,validated,...}) =
    protected work (fn () => validate_once validated (fn () =>
      (W.validate work graph root sources limits;
       G.validate_scope graph traversal;G.validate_scope graph caller;
       List.app (fn guard => guard ()) guards;
       if Type.type_epoch () = epoch andalso
           G.closure_child_node graph caller child = node andalso
           G.scope_visible graph traversal (G.node_scope graph node)
         then () else raise ERR "active" "focus/frame/epoch changed")))
  fun invoke focus operation = protected (work_of focus) (fn () =>
    (active focus;let val value = operation () val _ = active focus
                  in value end))
  fun spend focus amount =
    (active focus;W.spend (work_of focus) amount;active focus)
  fun same_owner f g =
    let val a = owner_of f val b = owner_of g
    in Portable.pointer_eq (#graph a,#graph b) andalso #root a = #root b
       andalso Portable.pointer_eq (#sources a,#sources b) andalso
       Portable.pointer_eq (#work a,#work b) andalso #epoch a = #epoch b
    end
  fun require_owner expected other =
    protected (work_of expected) (fn () =>
      (active expected;
       if same_owner expected other then active other else
         raise ERR "owner" "different original invocation"))
  fun description_for {graph,scope,sources,work}
      (focus as Focus {owner,traversal,node,provenance,root_ordinal,...}) =
    protected work (fn () =>
      if Portable.pointer_eq (graph,#graph owner) andalso
          scope = traversal andalso
          Portable.pointer_eq (sources,#sources owner) andalso
          Portable.pointer_eq (work,#work owner) then
        (active focus;
         {node = node,scope = traversal,provenance = provenance,
          occurrence = if root_ordinal >= 0 then SOME root_ordinal else NONE})
      else raise ERR "description_for" "different original owner/frame")
  fun node (f as Focus {node,...}) = (active f;node)
  fun scope (f as Focus {traversal,...}) = (active f;traversal)
  fun child (f as Focus {child,...}) = (active f;child)
  fun provenance (f as Focus {provenance,...}) = (active f;provenance)
  fun original_occurrence (f as Focus {root_ordinal,...}) =
    protected (work_of f) (fn () =>
      (active f;if root_ordinal >= 0 then root_ordinal else
        raise ERR "original_occurrence" "positive Goal is not a Source slot"))
  fun root_sources (f as Focus
      {original,opened,goal_unopened,provenance,...}) =
    protected (work_of f) (fn () =>
      (active f;if goal_unopened then raise ERR "root_sources"
          (case provenance of
              UnopenedOriginalOccurrence =>
                "unopened assumption Source has no opened view"
            | UnopenedOriginalDescendant =>
                "unopened assumption Source has no opened view"
            | _ => "unopened positive Source has no opened view")
       else {original = original,opened = opened}))

  (* Every derived focus keeps the incoming path guard, then normalizes its
     own handle to the actual traversal frame. It does not infer body frames
     from node_scope of constants or adopt a first source_anchor. *)
  fun descend (parent as Focus
      {owner,original,opened,root_ordinal,goal_unopened,...})
      traversal incoming_caller incoming extras provenance =
    let val graph = #graph owner
        val _ = active parent
        val current = G.closure_child_node graph incoming_caller incoming
        val root = G.closure_root graph traversal current
        val result = Focus
          {owner = owner,traversal = traversal,caller = traversal,
           child = root,node = current,original = original,opened = opened,
           root_ordinal = root_ordinal,
           provenance = provenance,goal_unopened = goal_unopened,
           guards = (fn () => active parent) ::
             (fn () => ignore (G.closure_child_node graph
               incoming_caller incoming)) :: extras,
           validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end
  fun at_node parent traversal current guards =
    let val graph = #graph (owner_of parent)
        val root = invoke parent
          (fn () => G.closure_root graph traversal current)
    in descend parent traversal traversal root guards GeneratedResult end
  fun descendant parent = case provenance parent of
      OriginalOccurrence => OriginalDescendant
    | OriginalDescendant => OriginalDescendant
    | OriginalPositiveGoal => PositiveGoalDescendant
    | PositiveGoalDescendant => PositiveGoalDescendant
    | UnopenedPositiveGoal => UnopenedGoalDescendant
    | UnopenedGoalDescendant => UnopenedGoalDescendant
    | UnopenedOriginalOccurrence => UnopenedOriginalDescendant
    | UnopenedOriginalDescendant => UnopenedOriginalDescendant
    | ClosedAuxiliaryRoot => ClosedAuxiliaryDescendant
    | ClosedAuxiliaryDescendant => ClosedAuxiliaryDescendant
    | _ => GeneratedDescendant

  fun start work {occurrence,view} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val _ = if occurrence >= 0 then () else
          raise ERR "start" "negative original occurrence"
        fun select [] _ = raise ERR "start" "absent original occurrence"
          | select (item::rest) n =
              (W.spend work 1;if n = 0 then item else select rest (n-1))
        val original = select (S.reconciliation_sources sources) occurrence
        fun registered () =
          (W.validate work graph root sources limits;
           G.validate_opened_view graph root (#node original) view)
        val _ = registered ()
        val current = #node view
        val _ = List.app (fn metric =>
          (W.spend work 1;
           case G.unfolded_nodes graph metric (#input_limit limits) current of
               SOME count => if count <= #input_limit limits then () else
                 raise ERR "start" "initial canonical Source exceeds input cap"
             | NONE => raise ERR "start"
                 "initial Source needs rich admission"))
          [G.RawNodes,G.BinderInclusiveNodes]
        val root_child = G.closure_root graph root current
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = root_child,node = current,
           original = original,opened = view,root_ordinal = occurrence,
           provenance = OriginalOccurrence,goal_unopened = false,
           guards = [registered],validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end)
  fun start_goal work {view} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val original = S.goal_source sources
        fun registered () =
          let val saved = S.goal_source sources
              val _ = W.validate work graph root sources limits
              val _ = if #node saved = #node original andalso
                  Portable.pointer_eq (#original saved,#original original)
                  andalso Portable.pointer_eq (#bridge saved,#bridge original)
                then () else raise ERR "start_goal" "positive Source changed"
          in case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened end
        val _ = registered ()
        val opened = case view of NONE => original | SOME saved => saved
        val current = #node opened
        val root_child = G.closure_root graph root current
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = root_child,node = current,
           original = original,opened = opened,root_ordinal = ~1,
           provenance = (case view of NONE => UnopenedPositiveGoal
             | SOME _ => OriginalPositiveGoal),
           goal_unopened = (case view of NONE => true | SOME _ => false),
           guards = [registered],validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end)
  (* The supplied ordinal must name a retained assumption (>=1).
     The option selects genuine opened syntax or explicitly unopened DATA,
     never a caller category/cap override. SAME Work owns the action. *)
  fun start_assumption work {occurrence,view} =
    W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
        val _ = if occurrence >= 1 then () else
          raise ERR "start_assumption" "not an original assumption index"
        fun select [] _ = raise ERR "start_assumption"
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
        val opened = case view of NONE => original | SOME saved => saved
        val current = #node opened
        val root_child = G.closure_root graph root current
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = root_child,node = current,
           original = original,opened = opened,root_ordinal = occurrence,
           provenance = (case view of NONE => UnopenedOriginalOccurrence
             | SOME _ => OriginalOccurrence),
           goal_unopened = (case view of NONE => true | SOME _ => false),
           guards = [registered],validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end)

  (* A checked selected stock-law receipt is not an ordinary Source slot.
     Its whole import/opened and P evidence were admitted by the SAME W. *)
  fun start_auxiliary work {law} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val expected =
          {graph = graph,scope = root,sources = sources,work = work}
        val data = SmtLib_GraphSelectedAuxiliary.describe_for expected law
        val original = #imported data val opened = #opened data
        fun registered () =
          SmtLib_GraphSelectedAuxiliary.validate_for expected law
        val current = #node opened
        val root_child = G.closure_root graph root current
        val _ = W.spend work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits = limits,epoch = Type.type_epoch ()},
           traversal = root,caller = root,child = root_child,node = current,
           original = original,opened = opened,root_ordinal = ~2,
           provenance = ClosedAuxiliaryRoot,goal_unopened = false,
           guards = [registered],validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end)

  fun application_children (parent as Focus {caller,child,...}) =
    let val graph = #graph (owner_of parent)
        val pair = invoke parent
          (fn () => G.closure_application_children graph caller child)
        val traversal = scope parent
    in (descend parent traversal caller (#1 pair) [] (descendant parent),
        descend parent traversal caller (#2 pair) [] (descendant parent)) end
  fun binder_body (parent as Focus {caller,child,...}) =
    let val graph = #graph (owner_of parent)
        val closure = invoke parent
          (fn () => G.closure_child_binder graph caller child)
        val data = invoke parent
          (fn () => G.binder_closure_data graph caller closure)
        val body = invoke parent
          (fn () => G.binder_closure_body graph caller closure)
        fun held () = ignore (G.binder_closure_data graph caller closure)
    in descend parent (#body_frame data) caller body [held]
      (descendant parent) end

  fun clean theorem =
    null (Thm.hyp theorem) andalso null (Tag.axioms_of (Thm.tag theorem))
    andalso List.all (fn oracle => oracle = "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag theorem)))
  fun check_endpoints initial target theorem =
    let val graph = #graph (owner_of initial)
        val _ = require_owner initial target
        val _ = if scope initial = scope target then () else
          raise ERR "endpoints" "different traversal frame"
        val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
    in if clean theorem andalso Portable.pointer_eq
          (left,G.representative graph (node initial)) andalso
          Portable.pointer_eq (right,G.representative graph (node target))
          andalso G.type_id graph (node initial) =
            G.type_id graph (node target) then () else
         raise ERR "endpoints" "unclean or changed canonical endpoints" end
  fun checked (initial,target,theorem,backing) =
    let val guard = validation_guard (fn () =>
          (active initial;active target;backing ();
           check_endpoints initial target theorem))
        val _ = guard ()
    in Conversion {initial = initial,target = target,theorem = theorem,
                   guard = guard} end
  fun validate (Conversion {initial,guard,...}) =
    protected (work_of initial) guard
  fun endpoints (c as Conversion {initial,target,theorem,...}) =
    (validate c;{source = node initial,target = node target,theorem = theorem})
  (* This typed pure projection has no callback argument or retained
     cache. Expected ownership of BOTH endpoints is compared before any
     conversion/foreign backing activation. A successful validate already
     checks every held path, exact theorem endpoint, Hyp/tag and frame. *)
  fun conversion_description_for {graph,scope,sources,work}
      (converted as Conversion
        {initial = Focus {owner = first,traversal = left_scope,
                          node = left,...},
         target = Focus {owner = last,traversal = right_scope,
                         node = right,...},...}) =
    protected work (fn () =>
      if Portable.pointer_eq (graph,#graph first) andalso
          Portable.pointer_eq (graph,#graph last) andalso
          Portable.pointer_eq (sources,#sources first) andalso
          Portable.pointer_eq (sources,#sources last) andalso
          Portable.pointer_eq (work,#work first) andalso
          Portable.pointer_eq (work,#work last) andalso
          left_scope = scope andalso right_scope = scope then
        (validate converted;{source = left,target = right,scope = scope})
      else raise ERR "conversion_description_for"
        "different expected conversion owner/frame")

  fun target_focus (c as Conversion {target,...}) = (validate c;target)
  fun initial_focus (c as Conversion {initial,...}) = (validate c;initial)
  (* Pure owner projection: NEVER activate a foreign receipt to identify it. *)
  fun peek_initial (Conversion {initial,...}) = initial
  fun expected focus =
    let val owner = owner_of focus
    in {graph = #graph owner,scope = scope focus,sources = #sources owner,
        work = #work owner} end

  fun adopt_beta focus receipt = W.with_step (work_of focus) (fn () =>
    let fun backing () = B.validate_for (expected focus) receipt
        val _ = backing ()  (* BEFORE receipt endpoint/theorem getters *)
        val {source,target,theorem} = B.endpoints receipt
        val _ = if source = node focus then () else
          raise ERR "adopt_beta" "different owned source focus"
        val result = at_node focus (scope focus) target [backing]
    in checked (focus,result,theorem,backing) end)
  fun adopt_carrier focus receipt = W.with_step (work_of focus) (fn () =>
    let fun backing () = C.validate_for (expected focus) receipt
        val _ = backing ()  (* BEFORE receipt endpoint/theorem getters *)
        val {source,target,theorem} = C.endpoints receipt
        val _ = if source = node focus then () else
          raise ERR "adopt_carrier" "different owned source focus"
        val result = at_node focus (scope focus) target [backing]
    in checked (focus,result,theorem,backing) end)

  fun adopt_compact focus receipt = W.with_step (work_of focus) (fn () =>
    let val owner = owner_of focus
        fun checked_description () =
          let val data = SmtReplayOwnedLargeProofCore.conversion_description_for
                (#work owner) receipt
          in if Portable.pointer_eq (#graph data,#graph owner) andalso
              #scope data = scope focus andalso
              Portable.pointer_eq (#sources data,#sources owner) andalso
              #source data = node focus then data else
            raise ERR "adopt_compact" "different result source/owner/frame" end
        (* The SAME backing is reachable through both the target focus
           and conversion. Share only within the existing callback-free
           validation walk, never across independent getters/callbacks. *)
        val backing = validation_guard (fn () =>
          ignore (checked_description ()))
        val data = checked_description ()
        val theorem = SmtReplayOwnedLargeProofCore.theorem_for
          (#work owner) receipt
        (* No callback intervenes; reuse this locally checked description. *)
        val result = at_node focus (scope focus) (#target data) [backing]
    in checked (focus,result,theorem,backing) end)

  fun adopt_realized_lambda focus receipt =
    W.with_step (work_of focus) (fn () =>
    let val owner = owner_of focus
        val backing = validation_guard (fn () =>
          let val data = SmtReplayOwnedRealizedLambda.conversion_description_for
                (#work owner) receipt
          in if Portable.pointer_eq (#graph data,#graph owner) andalso
              #root data = #root owner andalso #scope data = scope focus andalso
              Portable.pointer_eq (#sources data,#sources owner) andalso
              #source data = node focus then () else
            raise ERR "adopt_realized_lambda" "different source/owner/frame"
          end)
        val _ = backing ()
        val data = SmtReplayOwnedRealizedLambda.conversion_description_for
          (#work owner) receipt
        val theorem = SmtReplayOwnedRealizedLambda.theorem_for
          (#work owner) receipt
        val _ = backing ()
        val target = at_node focus (scope focus) (#target data) [backing]
    in checked (focus,target,theorem,backing) end)

  (* Full repeated syntax/type footprints; memo shares discovery, never
     occurrence sums. Private closure/map/name costs remain unclosed. *)
  fun inventory (focus as Focus {traversal,...}) roots =
    let val _ = active focus
        val work = work_of focus
        (* This complete inventory has no user callbacks. Fence it once,
           not around every paid type/node/memo operation. The returned
           guard still checks every retained path at policy boundaries. *)
        fun invoke _ action = action ()
        fun spend _ amount = W.spend work amount
        fun scope _ = traversal
        val graph = #graph (owner_of focus)
        val limits = #limits (owner_of focus)
        val maximum = Int.max (#input_limit limits,
          Int.max (#output_limit limits,#template_limit limits))
        val ceiling = IntInf.fromInt (W.work_limit (work_of focus))
        fun plus a b = IntInf.min (ceiling+1,a+b)
        val types = ref ([] : Type.hol_type list)
        val held = ref ([] : (G.scope * G.closure_child) list)
        val opaque = ref ([] : G.opaque_profile list)
        val memo = ref ([] : (G.node * footprint) list)
        fun weight ty =
          let fun walk [] n = n
                | walk (pending::more) n =
                  (spend focus 1;case pending of [] => walk more n
                   | current::rest =>
                     let val next = plus n 1
                         val _ = if next <= ceiling then () else
                           raise ERR "inventory" "type footprint exceeds Work"
                     in if invoke focus (fn () => Type.is_vartype current)
                        then walk (rest::more) next
                        else walk ((invoke focus
                          (fn () => #2 (Type.dest_type current)))::rest::more)
                          next end)
          in walk [[ty]] 0 end
        fun annotation current =
          let val ty = invoke focus (fn () => G.type_of graph current)
              val count = weight ty val _ = spend focus 1
              val _ = types := ty :: !types
          in count end
        fun lookup current [] = NONE
          | lookup current ((old,value)::rest) =
              (spend focus 1;if current = old then SOME value
               else lookup current rest)
        fun visit caller child =
          let val _ = spend focus 1
              val current = invoke focus
                (fn () => G.closure_child_node graph caller child)
              val _ = held := (caller,child) :: !held
          in case lookup current (!memo) of SOME value => value
           | NONE =>
            let val kind = invoke focus (fn () => G.view graph current)
                val profile = case kind of G.OpaqueRetained =>
                    invoke focus (fn () => G.opaque_profile_for graph
                      (scope focus) current)
                  | _ => NONE
                val ty = case profile of SOME held =>
                    #ty (invoke focus (fn () => G.opaque_profile_data graph
                      (scope focus) held))
                  | NONE => annotation current
                val value : footprint = case kind of
                    G.Application _ =>
                      let val (f,x) = invoke focus (fn () =>
                            G.closure_application_children graph caller child)
                          val a = visit caller f val b = visit caller x
                      in {raw = plus 1 (plus (#raw a) (#raw b)),
                          inc = plus 1 (plus (#inc a) (#inc b)),
                          ann = plus ty (plus (#ann a) (#ann b)),ty = ty}
                      end
                  | G.AdmittedBinder _ =>
                      let val binder = invoke focus (fn () =>
                            G.closure_child_binder graph caller child)
                          val d = invoke focus (fn () =>
                            G.binder_closure_data graph caller binder)
                          val bt = annotation (#binder d)
                          val b = visit caller (invoke focus (fn () =>
                            G.binder_closure_body graph caller binder))
                      in {raw = plus 1 (#raw b),inc = plus 2 (#inc b),
                          ann = plus ty (plus bt (#ann b)),ty = ty} end
                  | G.OpaqueRetained => (case profile of NONE =>
                      raise ERR "inventory"
                        "unrecorded opaque annotation portfolio"
                    | SOME held =>
                      let val data = invoke focus
                            (fn () => G.opaque_profile_data graph
                              (scope focus) held)
                          val _ = spend focus 1
                          val _ = opaque := held :: !opaque
                          val _ = List.app (fn ty =>
                            (spend focus 1;types := ty :: !types)) (#types data)
                      in {raw = IntInf.fromInt (#raw data),
                          inc = IntInf.fromInt (#inc data),
                          ann = #ann data,ty = #ty data} end)
                  | _ => {raw = 1,inc = 1,ann = ty,ty = ty}
                val _ = spend focus 1
                val _ = memo := (current,value) :: !memo
            in value end end
        fun root current =
          let val _ = List.app (fn metric =>
                (spend focus 1;case invoke focus (fn () =>
                    G.unfolded_nodes graph metric maximum current) of
                    SOME count => if count <= maximum then () else
                      raise ERR "inventory" "cached syntax exceeds caps"
                  | NONE => raise ERR "inventory" "unknown cached syntax"))
                [G.RawNodes,G.BinderInclusiveNodes]
          in visit (scope focus) (invoke focus
            (fn () => G.closure_root graph (scope focus) current)) end
        val values = List.map root roots
        fun guard () =
          (active focus;List.app (fn (caller,child) =>
            ignore (G.closure_child_node graph caller child)) (!held);
           List.app (fn profile => ignore (G.opaque_profile_data graph
             traversal profile)) (!opaque))
    in (values,!types,guard) end

  (* Only the internal quoted role changes the node bound. Both paths
     retain the original Work debit; semantic result and checked evidence
     are separate portfolios, never a caller scalar-cap override. *)
  datatype quoted_role = SemanticResult | ClosedEquation of footprint
  fun reserve_role role focus ordinal target proofs =
    let val owner = owner_of focus val limits = #limits owner
        val ceiling = IntInf.fromInt (W.work_limit (#work owner))
        fun plus a b = IntInf.min (ceiling+1,a+b)
        fun bound label maximum (value : footprint) =
          if #raw value <= IntInf.fromInt maximum andalso
              #inc value <= IntInf.fromInt maximum then () else
            raise ERR "reserve" (label ^ " exceeds original semantic cap")
        val _ = case role of SemanticResult =>
            bound "target" (#output_limit limits) target
          | ClosedEquation result =>
            (bound "target" (#output_limit limits) result;
             bound "closed equality" (#template_limit limits) target)
        val _ = List.app (bound "proof" (#template_limit limits)) proofs
        val amount = List.foldl (fn (value : footprint,total) =>
          plus total (plus (#raw value) (plus (#inc value) (#ann value))))
          (plus (#raw target) (plus (#inc target) (#ann target))) proofs
        val _ = if ordinal >= 0 andalso amount > 0 andalso amount <= ceiling
          then () else raise ERR "reserve" "malformed/exhausted footprint"
        val token = W.reserve (#work owner)
          {role = W.LocalCarrier,ordinal = ordinal,
           amount = IntInf.toInt amount}
    in W.consume (#work owner) token (IntInf.toInt amount) end
  fun reserve focus ordinal target proofs =
    reserve_role SemanticResult focus ordinal target proofs
  fun equation (a : footprint) (b : footprint) : footprint =
    {raw = 3 + #raw a + #raw b,inc = 3 + #inc a + #inc b,
     ann = 6 + 3 * #ty a + #ann a + #ann b,ty = 1}
  fun policies focus guard types result_types ordinal future_count policy =
    let
        fun count [] n = n
          | count (_::rest) n = (spend focus 1;count rest (n+1))
        val count_types = count types 0
        val count_results = count result_types 0
        val amount = IntInf.fromInt count_types +
          11 * IntInf.fromInt count_results + IntInf.fromInt future_count
        val _ = if amount > 0 andalso
            amount <= IntInf.fromInt (W.work_limit (work_of focus)) then ()
          else raise ERR "policies" "policy/render portfolio exceeds Work"
        val work = work_of focus
        val token = W.reserve work
          {role = W.FactAssembly,ordinal = ordinal,
           amount = IntInf.toInt amount}
        fun consume amount = (active focus;W.consume work token amount)
        fun call ty =
          (active focus;guard ();consume 1;
           policy ty;active focus;guard ())
        (* Render only the fixed prospective equality shell AFTER reserving
           its full annotation portfolio. Type internals remain unclosed. *)
        fun render result_type =
          let val _ = consume 4
              val inner = invoke focus
                (fn () => Type.mk_type ("fun",[result_type,Type.bool]))
              val _ = consume 4
              val outer = invoke focus
                (fn () => Type.mk_type ("fun",[result_type,inner]))
          in [Type.bool,inner,outer] end
        val generated = List.map render result_types
        val _ = List.app call types
        val _ = List.app (List.app call) generated
    in call end

  fun compose {first,second,ordinal,check_type} =
    let val initial = peek_initial first
        val work = work_of initial
    in protected work (fn () =>
      let val next = peek_initial second
          val _ = require_owner initial next
          val _ = validate first
          val _ = validate second
          val middle = target_focus first val target = target_focus second
          fun guard () = (validate first;validate second)
      in W.with_step work (fn () =>
      let val _ = guard ()
          val _ = if node middle = node next andalso
              scope initial = scope next then () else
            raise ERR "compose" "different exact middle node/frame"
          val (sizes,types,held) = inventory initial
            [node initial,node target]
          val (a,b) = case sizes of [a,b] => (a,b)
            | _ => raise ERR "compose" "internal size portfolio"
          val _ = reserve initial ordinal b [equation a b]
          fun all () = (guard ();held ())
          val graph = #graph (owner_of initial)
          val _ = policies initial all types
            [G.type_of graph (node initial)] ordinal 0 check_type
          val theorem = invoke initial (fn () => Thm.TRANS
            (#theorem (endpoints first)) (#theorem (endpoints second)))
          val _ = all ()
      in checked (initial,target,theorem,all) end) end) end

  fun prepare_application {parent,left,right,ordinal,check_type} =
    W.with_step (work_of parent) (fn () =>
    let val (old_left,old_right) = application_children parent
        fun chosen old NONE = old
          | chosen old (SOME converted) =
              let val initial = peek_initial converted
                  val _ = require_owner parent initial
                  val _ = validate converted
                  val _ = if node old = node initial andalso
                      scope old = scope initial then () else
                    raise ERR "application" "different immediate child"
              in target_focus converted end
        val new_left = chosen old_left left
        val new_right = chosen old_right right
        val graph = #graph (owner_of parent)
        val _ = if G.type_id graph (node old_left) =
            G.type_id graph (node new_left) andalso
            G.type_id graph (node old_right) =
            G.type_id graph (node new_right) then () else
          raise ERR "application" "child conversion type changed"
        val (sizes,types,guard) = inventory parent
          [node parent,node new_left,node new_right]
        val (old,f,x) = case sizes of [a,b,c] => (a,b,c)
          | _ => raise ERR "application" "internal size portfolio"
        val target : footprint =
          {raw = 1 + #raw f + #raw x,inc = 1 + #inc f + #inc x,
           ann = #ty old + #ann f + #ann x,ty = #ty old}
        (* MK_COMB, source ALPHA, target ALPHA and BOTH TRANS results. *)
        val reflexivities =
          (case left of NONE => [equation f f] | SOME _ => []) @
          (case right of NONE => [equation x x] | SOME _ => [])
        val _ = reserve parent ordinal target
          ([equation old target,equation old old,equation target target,
            equation old target,equation old target] @ reflexivities)
        val _ = guard ()
        val guarded_policy = fn ty =>
          (guard ();check_type ty;guard ())
    in ApplicationPlan {parent = parent,old_left = old_left,
      old_right = old_right,new_left = new_left,new_right = new_right,
      left = left,right = right,policy = guarded_policy,types = types,
      result_types = G.type_of graph (node parent) ::
        ((case left of NONE => [G.type_of graph (node new_left)]
          | SOME _ => []) @
         (case right of NONE => [G.type_of graph (node new_right)]
          | SOME _ => [])),ordinal = ordinal,state = ref Ready} end)

  fun execute_application (ApplicationPlan
      {parent,old_left,old_right,new_left,new_right,left,right,
       policy,types,result_types,ordinal,state}) =
    let val work = work_of parent val graph = #graph (owner_of parent)
        fun guard () =
          (active parent;active old_left;active old_right;
           active new_left;active new_right;
           List.app (fn item => case item of NONE => ()
             | SOME converted => validate converted) [left,right])
        fun proof old NONE = invoke parent
              (fn () => Thm.REFL (G.representative graph (node old)))
          | proof old (SOME converted) =
              (validate converted;#theorem (endpoints converted))
        fun immediate label term a b =
          let val (f,x) = Term.dest_comb term
          in if Portable.pointer_eq
              (f,G.representative graph (node a)) andalso
              Portable.pointer_eq (x,G.representative graph (node b)) then ()
             else raise ERR "application" (label ^ " child pointer changed")
          end
    in W.with_step work (fn () =>
      ((guard ();case !state of Ready => state := Running
        | _ => raise ERR "application" "plan is one shot");
       let val _ = policies parent guard types result_types ordinal 0 policy
           val target_node = invoke parent (fn () => G.application graph
             (scope parent) (node new_left,node new_right))
           val target = at_node parent (scope parent) target_node [guard]
           val theorem = invoke parent
             (fn () => Thm.MK_COMB (proof old_left left,proof old_right right))
           val (a,b) = boolSyntax.dest_eq (Thm.concl theorem)
           (* Kernel MK_COMB rebuilds OUTER applications. Authenticate the
              exact immediate children, never demand fresh outer pointers. *)
           val _ = immediate "source" a old_left old_right
           val _ = immediate "target" b new_left new_right
           val align_left = invoke parent (fn () => Thm.ALPHA
             (G.representative graph (node parent)) a)
           val align_right = invoke parent (fn () => Thm.ALPHA b
             (G.representative graph target_node))
           val tail = invoke parent (fn () => Thm.TRANS theorem align_right)
           val complete = invoke parent (fn () => Thm.TRANS align_left tail)
           val _ = guard () val _ = state := Complete
       in checked (parent,target,complete,guard) end)
      handle primary => (state := Retired;W.close work;raise primary)) end

  fun closed_fact converted {ordinal,check_type} =
    let val initial = initial_focus converted
        val target = target_focus converted
        val work = work_of initial val graph = #graph (owner_of initial)
        val limits = #limits (owner_of initial)
    in W.with_step work (fn () =>
      let val _ = validate converted
          val (sizes,types,held) = inventory initial
            [node initial,node target]
          val (a,b) = case sizes of [a,b] => (a,b)
            | _ => raise ERR "closed_fact" "internal size portfolio"
          val equality = equation a b
          val _ = reserve_role (ClosedEquation b) initial ordinal equality [equality]
          fun guard () = (validate converted;held ())
          (* The future P type-policy portfolio has at most every held
             unique annotation node plus the THREE new equality nodes.
             Inventory includes binder VARIABLE annotations too. Reserve
             this incidence ceiling before the FIRST supplied policy. *)
          fun policy_count [] n = n
            | policy_count (_::rest) n =
                (spend initial 1;policy_count rest (n+1))
          val future_count = policy_count types 3
          val policy = policies initial guard types
            [G.type_of graph (node initial)] ordinal future_count check_type
          val theorem = #theorem (endpoints converted)
          val operator = Term.rator (Term.rator (Thm.concl theorem))
          val head = invoke initial
            (fn () => G.constant graph (scope initial) operator)
          val partial = invoke initial (fn () => G.application graph
            (scope initial) (head,node initial))
          val equality_node = invoke initial (fn () => G.application graph
            (scope initial) (partial,node target))
          val result = invoke initial (fn () => P.record_closed graph
            (scope initial) {node = equality_node,theorem = theorem,
              template_limit = #template_limit limits,check_type = policy})
          val _ = guard ()
      in result end) end

  fun closed_fact_for expected converted request =
    protected (#work expected) (fn () =>
      (ignore (description_for expected (peek_initial converted));
       closed_fact converted request))

  fun lift_lambda {parent,body,record_ordinal,lift_ordinal,check_type} =
    protected (work_of parent) (fn () =>
    let val initial = peek_initial body
        val _ = require_owner parent initial
        val _ = validate body
        val graph = #graph (owner_of parent)
        val Focus {caller,child,...} = parent
        val closure = invoke parent
          (fn () => G.closure_child_binder graph caller child)
        val captured = invoke parent
          (fn () => G.binder_closure_data graph caller closure)
        val _ = if node initial = #body captured andalso
            scope initial = #body_frame captured then () else
          raise ERR "lambda" "different owned body node/frame"
        fun guard () = (active parent;validate body)
        fun policy ty = (guard ();check_type ty;guard ())
        val evidence = closed_fact body
          {ordinal = record_ordinal,check_type = policy}
        val _ = guard ()
        val owner = owner_of parent
        val result = L.execute (L.prepare
          {graph = graph,caller = caller,scope = scope parent,
           sources = #sources owner,work = #work owner,ordinal = lift_ordinal,
           binder = closure,body_fact = evidence,check_type = policy})
        fun backing () =
          (guard ();L.validate_for
            {graph = graph,caller = caller,scope = scope parent,
             sources = #sources owner,work = #work owner} result)
        val _ = backing ()
        val {source,target,theorem} = L.endpoints result
        val _ = if source = node parent then () else
          raise ERR "lambda" "different lambda source"
        val focus = at_node parent (scope parent) target [backing]
    in checked (parent,focus,theorem,backing) end)

  fun lift_lambda_admitted
      {parent,admission,body,record_ordinal,lift_ordinal,check_type} =
    protected (work_of parent) (fn () =>
    let val _ = active parent
        val owner = owner_of parent
        val graph = #graph owner
        val expected : Q.expected =
          {graph = graph,scope = scope parent,sources = #sources owner,
           work = #work owner}
        val d = Q.describe_for expected admission
        val expected_category = case provenance parent of
            OriginalOccurrence => Q.Original
          | OriginalDescendant => Q.Original
          | OriginalPositiveGoal => Q.Original
          | PositiveGoalDescendant => Q.Original
          | UnopenedPositiveGoal => Q.Original
          | UnopenedGoalDescendant => Q.Original
          | UnopenedOriginalOccurrence => Q.Original
          | UnopenedOriginalDescendant => Q.Original
          | ClosedAuxiliaryRoot => Q.Auxiliary
          | ClosedAuxiliaryDescendant => Q.Auxiliary
          | _ => Q.Generated
        (* Private lineage ordinal, not the public Source-index getter.
           -1 agrees with lower Goal DATA and confers no P.Source slot. *)
        val Focus {root_ordinal = held_ordinal,...} = parent
        val _ = if #node d = node parent andalso
            #category d = expected_category andalso
            #occurrence d = held_ordinal then () else
          raise ERR "lambda_admitted" "different parent admission provenance"
        val initial = peek_initial body
        val _ = require_owner parent initial
        val _ = validate body
        val graph = #graph (owner_of parent)
        val Focus {caller,child,...} = parent
        val closure = invoke parent
          (fn () => G.closure_child_binder graph caller child)
        val captured = invoke parent
          (fn () => G.binder_closure_data graph caller closure)
        val _ = if node initial = #body captured andalso
            scope initial = #body_frame captured then () else
          raise ERR "lambda" "different owned body node/frame"
        val admitted_closure = invoke parent (fn () =>
          G.closure_child_binder graph (scope parent) (#child d))
        val admitted_data = invoke parent (fn () =>
          G.binder_closure_data graph (scope parent) admitted_closure)
        val _ = if #node admitted_data = #node captured andalso
            #binder admitted_data = #binder captured andalso
            #body admitted_data = #body captured andalso
            #body_frame admitted_data = #body_frame captured andalso
            #binder_frame admitted_data = #binder_frame captured andalso
            #declaring_scope admitted_data = #declaring_scope captured andalso
            #node_frame admitted_data = #node_frame captured then () else
          raise ERR "lambda_admitted" "different genuine binder path"
        fun guard () =
          (active parent;Q.validate_for expected admission;validate body)
        fun policy ty = (guard ();check_type ty;guard ())
        val evidence = closed_fact body
          {ordinal = record_ordinal,check_type = policy}
        val _ = guard ()
        val owner = owner_of parent
        val result = L.execute (L.prepare_admitted
          {graph = graph,scope = scope parent,
           sources = #sources owner,work = #work owner,ordinal = lift_ordinal,
           admission = admission,body_fact = evidence,check_type = policy})
        fun backing () =
          (guard ();L.validate_for
            {graph = graph,caller = scope parent,scope = scope parent,
             sources = #sources owner,work = #work owner} result)
        val _ = backing ()
        val {source,target,theorem} = L.endpoints result
        val _ = if source = node parent then () else
          raise ERR "lambda" "different lambda source"
        val focus = at_node parent (scope parent) target [backing]
    in checked (parent,focus,theorem,backing) end)

  fun alpha_changed converted =
    let val initial = initial_focus converted
        val target = target_focus converted
        val work = work_of initial
    in W.with_step work (fn () =>
      let val _ = validate converted
          val answer = A.same_inside work
            {caller = scope initial,traversal = scope initial,
             left = child initial,right = child target}
          val _ = validate converted
      in not answer end) end

  (* Authentic lower focus determines the source role; its semantic
     evidence is not previous Work credit. The comparison itself debits
     SAME Work before Term.aconv and retains all lifetime guards. *)
  fun alpha_changed_admitted {conversion,admission} =
    let val initial = initial_focus conversion
        val target = target_focus conversion
        val work = work_of initial val owner = owner_of initial
        val Focus {root_ordinal,...} = initial
    in W.with_step work (fn () =>
      let val _ = validate conversion
          val data = Q.describe_for
            {graph = #graph owner,scope = scope initial,
             sources = #sources owner,work = work} admission
          val _ = if #node data = node initial andalso
              #occurrence data = root_ordinal then () else
            raise ERR "alpha_changed_admitted" "different initial receipt"
          val kind = provenance initial
          val matching = case (kind,#category data) of
              (OriginalOccurrence,Q.Original) => true
            | (OriginalDescendant,Q.Original) => true
            | (OriginalPositiveGoal,Q.Original) => true
            | (PositiveGoalDescendant,Q.Original) => true
            | (ClosedAuxiliaryRoot,Q.Auxiliary) => true
            | (ClosedAuxiliaryDescendant,Q.Auxiliary) => true
            | (GeneratedResult,Q.Generated) => true
            | (GeneratedDescendant,Q.Generated) => true
            | _ => false
          val _ = if matching then () else raise ERR "alpha_changed_admitted"
            "different original/generated source role"
          val answer = A.same_admitted_inside work
            {caller = scope initial,traversal = scope initial,
             left = child initial,right = child target,admission = admission}
          val _ = validate conversion
      in not answer end) end

  fun restore_original converted {ordinal,check_type} =
    let val initial = peek_initial converted
        val work = work_of initial
    in protected work (fn () => W.with_step work (fn () =>
      let val _ = validate converted
          val Focus {owner,original,opened,root_ordinal,
                     provenance,...} = initial
          val graph = #graph owner val root = #root owner
          val _ = if provenance = OriginalOccurrence andalso
              scope initial = root andalso node initial = #node opened then ()
            else raise ERR "restore_original" "not an initial root occurrence"
          fun occurrence [] _ = raise ERR "restore_original"
                "original occurrence disappeared"
            | occurrence (first::rest) n =
                (spend initial 1;if n = 0 then first
                 else occurrence rest (n-1))
          val held = occurrence (S.reconciliation_sources (#sources owner))
            root_ordinal
          val _ = if #node held = #node original andalso
              Portable.pointer_eq (#original held,#original original) andalso
              Portable.pointer_eq (#bridge held,#bridge original) then () else
            raise ERR "restore_original" "different original Source occurrence"
          val _ = G.validate_opened_view graph root (#node original) opened
          val target = target_focus converted
          val (sizes,types,portfolio) = inventory initial
            [node initial,node target]
          val (a,b) = case sizes of [a,b] => (a,b)
            | _ => raise ERR "restore_original" "internal size portfolio"
          (* S.import and the registered opened recipe use ALPHA/REFL/
             MK_COMB only: the full raw/inclusive/type profile is preserved.
             Do NOT decode a possibly opaque raw original to obtain a quote.
             The TWO new TRANS results each have the old+target profile. *)
          val _ = reserve initial ordinal b [equation a b,equation a b]
          fun guard () =
            (validate converted;portfolio ();
             G.validate_opened_view graph root (#node original) opened)
          val _ = policies initial guard types
            [G.type_of graph (node initial)] ordinal 0 check_type
          fun bridge theorem left right =
            let val (x,y) = boolSyntax.dest_eq (Thm.concl theorem)
            in if clean theorem andalso Portable.pointer_eq (x,left) andalso
                Portable.pointer_eq (y,right) then () else
                 raise ERR "restore_original" "held bridge endpoint changed"
            end
          val _ = guard ()
          val _ = bridge (#bridge original) (#original original)
            (G.representative graph (#node original))
          val _ = bridge (#bridge opened)
            (G.representative graph (#node original))
            (G.representative graph (node initial))
          val tail = invoke initial (fn () => Thm.TRANS (#bridge opened)
            (#theorem (endpoints converted)))
          val result = invoke initial
            (fn () => Thm.TRANS (#bridge original) tail)
          val _ = guard ()
          val _ = bridge result (#original original)
            (G.representative graph (node target))
      in result end)) end

  (* ROOT-only checked canonical Source transport for the existing GP/F
     binder row. Raw USER source restoration remains the separate API. *)
  fun source_conversion converted {ordinal,check_type} =
    let val initial = peek_initial converted val work = work_of initial
    in protected work (fn () => W.with_step work (fn () =>
      let
        val _ = validate converted
        val Focus {owner,original,opened,root_ordinal,provenance,...} = initial
        val graph = #graph owner val root = #root owner
        val limits = #limits owner
        val _ = if provenance = OriginalOccurrence andalso
            scope initial = root andalso node initial = #node opened then ()
          else raise ERR "source_conversion" "not an initial root occurrence"
        fun occurrence [] _ = raise ERR "source_conversion"
              "original occurrence disappeared"
          | occurrence (first::rest) n =
              (spend initial 1;if n = 0 then first
               else occurrence rest (n-1))
        fun original_guard () =
          let val held = occurrence
                (S.reconciliation_sources (#sources owner)) root_ordinal
          in if #node held = #node original andalso
              Portable.pointer_eq (#original held,#original original) andalso
              Portable.pointer_eq (#bridge held,#bridge original) then
                G.validate_opened_view graph root (#node original) opened
            else raise ERR "source_conversion" "original Source changed"
          end
        val _ = original_guard ()
        val target = target_focus converted
        val (sizes,types,held) = inventory initial
          [node initial,node target]
        val (a,b) = case sizes of [a,b] => (a,b)
          | _ => raise ERR "source_conversion" "internal size portfolio"
        val _ = if G.type_id graph (#node original) =
            G.type_id graph (node initial) andalso
            Type.compare (G.type_of graph (node initial),Type.bool) = EQUAL
          then () else raise ERR "source_conversion" "non-Boolean Source"
        (* Existing held operands: opened alpha bridge aa and owned ab.
           New operations: target REFL bb and one canonical Source TRANS ab.
           No raw original.bridge participates in this canonical result. *)
        val _ = reserve initial ordinal b
          [equation a a,equation a b,equation b b,equation a b]
        val identity = invoke initial (fn () =>
          G.plan_identity_closure_view graph root (#template_limit limits)
            {target = child target,retain = [child initial]})
        val published = ref (NONE : G.source option)
        fun guard () =
          (validate converted;held ();original_guard ();
           case !published of NONE =>
             ignore (G.identity_closure_view_node identity)
           | SOME view => G.validate_opened_view graph root (node target) view)
        (* Quote the EXACT existing P.record_conversion forest before any
           supplied policy. Its unique G.reachable includes binder VARIABLE
           nodes. Borrow argument spines; no unadmitted Args @ rest here.
           G.reachable/private Type implementation work remains unclosed. *)
        val reachable = invoke initial (fn () => G.reachable graph
          [node initial,node target])
        val remaining = ref (#template_limit limits)
        fun type_walk pending =
          (spend initial 1;case pending of [] => () | spine::more =>
            (spend initial 1;case spine of [] => type_walk more
             | ty::rest =>
               let val _ = if !remaining > 0 then
                     remaining := !remaining-1 else
                     raise ERR "source_conversion" "P type forest exceeds cap"
                   val _ = spend initial 1
               in if invoke initial (fn () => Type.is_vartype ty) then
                    (spend initial 1;type_walk (rest::more))
                  else let val args = invoke initial
                        (fn () => #2 (Type.dest_type ty))
                           val _ = spend initial 2
                       in type_walk (args::rest::more) end end))
        fun forecast [] count = count
          | forecast (current::rest) count =
              (spend initial 1;guard ();
               type_walk [[invoke initial (fn () => G.type_of graph current)]];
               forecast rest (count+1))
        val future_count = forecast reachable 0
        val policy = policies initial guard types
          [G.type_of graph (node initial)] ordinal future_count check_type
        fun bridge theorem left right =
          let val (x,y) = boolSyntax.dest_eq (Thm.concl theorem)
          in if clean theorem andalso Portable.pointer_eq (x,left) andalso
              Portable.pointer_eq (y,right) then () else
            raise ERR "source_conversion" "held exact bridge changed" end
        val _ = guard ()
        val _ = bridge (#bridge opened)
          (G.representative graph (#node original))
          (G.representative graph (node initial))
        val target_view = invoke initial
          (fn () => G.execute_identity_closure_view identity)
        val _ = published := SOME target_view
        val _ = guard ()
        val theorem = invoke initial (fn () => Thm.TRANS (#bridge opened)
          (#theorem (endpoints converted)))
        val _ = bridge theorem (G.representative graph (#node original))
          (G.representative graph (node target))
        val result = invoke initial (fn () => P.record_conversion graph root
          {source = #node original,source_view = opened,
           target = node target,target_view = target_view,theorem = theorem,
           template_limit = #template_limit limits,check_type = policy})
        val _ = guard ()
        val _ = P.validate_conversion graph root
          (#template_limit limits) result
      in result end)) end

  (* A fixed negation closure, AFTER owned positive-Goal traversal. It does
     not create a traversal focus with a larger input/output syntax limit. *)
  fun denial_conversion converted {denial_view,ordinal,check_type} =
    let val initial = peek_initial converted val work = work_of initial
    in protected work (fn () => W.with_step work (fn () =>
      let
        val _ = validate converted
        val Focus {owner,original,opened,provenance,...} = initial
        val graph = #graph owner val root = #root owner
        val sources = #sources owner val limits = #limits owner
        val _ = if provenance = OriginalPositiveGoal andalso
            scope initial = root then () else raise ERR "denial_conversion"
              "requires owned opened positive Goal root"
        val saved = S.goal_source sources
        val _ = if #node saved = #node original andalso
            Portable.pointer_eq (#original saved,#original original) andalso
            Portable.pointer_eq (#bridge saved,#bridge original) then () else
          raise ERR "denial_conversion" "different retained positive Goal"
        val _ = spend initial 1
        val denied = case S.reconciliation_sources sources of first::_ => first
          | [] => raise ERR "denial_conversion" "original denial absent"
        fun registered () =
          (G.validate_opened_view graph root (#node original) opened;
           G.validate_opened_view graph root (#node denied) denial_view)
        val _ = registered ()
        val old_child = invoke initial
          (fn () => G.closure_root graph root (#node denial_view))
        val target = target_focus converted
        val (sizes,types,held) = inventory initial
          [node initial,node target,#node denial_view]
        val (a,b,old_negative) = case sizes of [a,b,c] => (a,b,c)
          | _ => raise ERR "denial_conversion" "internal portfolio"
        fun negated (value : footprint) : footprint =
          {raw = #raw value+2,inc = #inc value+2,
           ann = #ann value+4,ty = 1}
        val na = negated a val nb = negated b
        val _ = if #raw na = #raw old_negative andalso
            #inc na = #inc old_negative andalso
            #ann na = #ann old_negative then () else
          raise ERR "denial_conversion" "retained negation profile differs"
        val _ = if Type.compare (G.type_of graph (node initial),Type.bool)
            = EQUAL then () else raise ERR "denial_conversion" "Goal not Bool"
        val head = case G.view graph (#node denied) of G.Application (f,_) => f
          | _ => raise ERR "denial_conversion" "retained denial not wrapper"
        val _ = spend initial 1
        val _ = if Term.uptodate_term boolSyntax.negation then () else
          raise ERR "denial_conversion" "fixed negation retired"
        val head_term = G.representative graph head
        val _ = case G.view graph head of G.Constant _ => ()
          | _ => raise ERR "denial_conversion" "fixed wrapper head changed"
        val _ = if Term.same_const head_term boolSyntax.negation then () else
          raise ERR "denial_conversion" "not fixed Boolean negation"
        (* Two held Goal bridges, owned equation, two Goal TRANS results,
           held denial bridge and SYM, AP_TERM, input ALPHA, two prefix
           TRANS, output ALPHA, final TRANS, identity REFL, old view bridge.
           Each is quoted with repeated endpoints; nothing is refunded. *)
        val _ = spend initial 15 (* copied footprint portfolio incidence *)
        val proofs = [equation a a,equation a a,equation a b,
          equation a a,equation a b,equation na na,equation na na,
          equation na nb,equation na na,equation na nb,equation na nb,
          equation nb nb,equation na nb,equation nb nb,equation na na]
        val ceiling = IntInf.fromInt (W.work_limit work)
        fun plus x y = IntInf.min (ceiling+1,x+y)
        fun shape (value : footprint) =
          if #raw value <= IntInf.fromInt (#template_limit limits) andalso
              #inc value <= IntInf.fromInt (#template_limit limits) then ()
          else raise ERR "denial_conversion" "wrapper proof exceeds template"
        val _ = shape nb val _ = List.app shape proofs
        fun extent (value : footprint) =
          plus (#raw value) (plus (#inc value) (#ann value))
        val amount = List.foldl (fn (value,total) => plus (extent value) total)
          (extent nb) proofs
        val _ = if ordinal >= 0 andalso amount > 0 andalso amount <= ceiling
          then () else raise ERR "denial_conversion" "wrapper Work exhausted"
        val token = W.reserve work {role = W.GoalDenial,ordinal = ordinal,
          amount = IntInf.toInt amount}
        val _ = W.consume work token (IntInf.toInt amount)
        val _ = spend initial 1
        val published = ref (NONE : G.source option)
        fun guard () =
          (validate converted;held ();registered ();
           ignore (G.closure_child_node graph root old_child);
           if Term.uptodate_term boolSyntax.negation then () else
             raise ERR "denial_conversion" "fixed negation retired";
           case !published of NONE => () | SOME view =>
             G.validate_opened_view graph root (#node view) view)
        (* Existing P forest plus ONE prospective wrapper-node Bool. The
           extra node is a conservative reservation if G.application hits;
           this is not a whole private-map/allocation or parity claim. *)
        val reachable = invoke initial (fn () => G.reachable graph
          [#node denial_view,node target,head])
        val _ = spend initial 1
        val remaining = ref (#template_limit limits)
        fun walk pending =
          (spend initial 1;case pending of [] => () | spine::more =>
            (spend initial 1;case spine of [] => walk more | ty::rest =>
              let val _ = if !remaining > 0 then remaining := !remaining-1
                    else raise ERR "denial_conversion" "P type forest cap"
              in if invoke initial (fn () => Type.is_vartype ty) then
                   walk (rest::more)
                 else let val args = invoke initial
                        (fn () => #2 (Type.dest_type ty))
                      in walk (args::rest::more) end end))
        fun forecast [] count = count
          | forecast (n::rest) count =
              (guard ();walk [[invoke initial (fn () => G.type_of graph n)]];
               forecast rest (count+1))
        val future = forecast reachable 0
        val _ = walk [[Type.bool]]
        val _ = spend initial (length proofs)
        val headers = List.map (fn _ => Type.bool) proofs
        val policy = policies initial guard types headers ordinal (future+1)
          check_type
        val _ = guard ()
        val negative = invoke initial
          (fn () => G.application graph root (head,node target))
        val new_child = invoke initial
          (fn () => G.closure_root graph root negative)
        val identity = invoke initial (fn () =>
          G.plan_identity_closure_view graph root (#template_limit limits)
            {target = new_child,retain = [child initial,old_child]})
        fun bridge theorem left right =
          let val (l,r) = boolSyntax.dest_eq (Thm.concl theorem)
          in if clean theorem andalso Portable.pointer_eq (l,left) andalso
              Portable.pointer_eq (r,right) then () else
            raise ERR "denial_conversion" "changed exact bridge" end
        (* Both outer constructors have the SAME admitted immediate child.
           No independent expanded original-body comparison is permitted. *)
        fun outer left right =
          let val (lf,lx) = Term.dest_comb left
              val (rf,rx) = Term.dest_comb right
              val _ = if Term.same_const lf boolSyntax.negation andalso
                  Term.same_const rf boolSyntax.negation andalso
                  Portable.pointer_eq (lx,rx) then () else
                raise ERR "denial_conversion" "wrapper child/head differs"
          in invoke initial (fn () => Thm.ALPHA left right) end
        val _ = bridge (#bridge original) (#original original)
          (G.representative graph (#node original))
        val _ = bridge (#bridge opened)
          (G.representative graph (#node original))
          (G.representative graph (node initial))
        val _ = bridge (#bridge denied) (#original denied)
          (G.representative graph (#node denied))
        val (denied_head,denied_body) = Term.dest_comb (#original denied)
        val _ = if Term.same_const denied_head boolSyntax.negation andalso
            Portable.pointer_eq (denied_body,#original original) then () else
          raise ERR "denial_conversion" "not original fixed Goal denial"
        val first = invoke initial (fn () => Thm.TRANS
          (#bridge original) (#bridge opened))
        val goal = invoke initial (fn () => Thm.TRANS first
          (#theorem (endpoints converted)))
        val _ = bridge goal (#original original)
          (G.representative graph (node target))
        val lifted = invoke initial
          (fn () => Thm.AP_TERM boolSyntax.negation goal)
        val (left,right) = boolSyntax.dest_eq (Thm.concl lifted)
        val input_alignment = outer (#original denied) left
        val output_alignment = outer right
          (G.representative graph negative)
        val prefix = invoke initial (fn () => Thm.SYM (#bridge denied))
        val middle = invoke initial
          (fn () => Thm.TRANS input_alignment lifted)
        val raw = invoke initial (fn () => Thm.TRANS prefix middle)
        val theorem = invoke initial
          (fn () => Thm.TRANS raw output_alignment)
        val _ = bridge theorem (G.representative graph (#node denied))
          (G.representative graph negative)
        val target_view = invoke initial
          (fn () => G.execute_identity_closure_view identity)
        val _ = published := SOME target_view
        val result = invoke initial (fn () => P.record_conversion graph root
          {source = #node denied,source_view = denial_view,target = negative,
           target_view = target_view,theorem = theorem,
           template_limit = #template_limit limits,check_type = policy})
        val _ = guard ()
        val _ = P.validate_conversion graph root (#template_limit limits) result
      in result end)) end
  (* Policy transport is distinct from the old finite focus/conversion.
         Native ceilings come only from the actual retained caller contract. *)
      structure NativePolicyTransport =
      struct
        structure RP = SmtReplayResourcePolicy
        structure NC = SmtReplayNativeContract
        type owner =
          {graph:G.graph,root:G.scope,sources:S.sources,work:W.portfolio,
           limits:W.limits,policy_limits:RP.semantic_policy,epoch:int,
           native_contract:NC.contract,native_data:NC.limits,
       profiles:G.policy_opaque_profile list}
        datatype focus = Focus of
          {owner:owner,traversal:G.scope,caller:G.scope,
           child:G.closure_child,node:G.node,original:G.source,opened:G.source,
           root_ordinal:IntInf.int,provenance:provenance,goal_unopened:bool,
           guards:(unit->unit) list,validated:IntInf.int ref}
        datatype conversion = Conversion of
          {initial:focus,target:focus,theorem:Thm.thm,guard:unit->unit}
        datatype application_plan = ApplicationPlan of
          {parent:focus,old_left:focus,old_right:focus,
           new_left:focus,new_right:focus,left:conversion option,
           right:conversion option,policy:Type.hol_type -> unit,
           types:Type.hol_type list,result_types:Type.hol_type list,
           ordinal:int,state:state ref}
      fun owner_of (Focus {owner,...}) = owner
  fun work_of f = #work (owner_of f)
  fun protected work operation =
    operation () handle primary => (W.close work;raise primary)
  fun active (Focus {owner =
    {graph,root,sources,work,limits,policy_limits,epoch,
                               native_contract,native_data,profiles},
                     traversal,caller,child,node,guards,validated,...}) =
    protected work (fn () => validate_once validated (fn () =>
      (W.validate_policy work graph root sources policy_limits;
       NC.validate_for work native_contract;
       G.validate_scope graph traversal;G.validate_scope graph caller;
       List.app (fn guard => guard ()) guards;
       if Type.type_epoch () = epoch andalso
           G.closure_child_node graph caller child = node andalso
           G.scope_visible graph traversal (G.node_scope graph node)
         then () else raise ERR "active" "focus/frame/epoch changed")))
  fun invoke focus operation = protected (work_of focus) (fn () =>
    (active focus;let val value = operation () val _ = active focus
                  in value end))
  fun spend focus amount =
    (active focus;W.spend_policy (work_of focus) (IntInf.fromInt amount);active
      focus)
  fun same_owner f g =
    let val a = owner_of f val b = owner_of g
    in Portable.pointer_eq (#graph a,#graph b) andalso #root a = #root b
       andalso Portable.pointer_eq (#sources a,#sources b) andalso
       Portable.pointer_eq (#work a,#work b) andalso #epoch a = #epoch b
         andalso
       Portable.pointer_eq (#native_contract a,#native_contract b)
       andalso #native_data a = #native_data b
    end
  fun require_owner expected other =
    protected (work_of expected) (fn () =>
      (active expected;
       if same_owner expected other then active other else
         raise ERR "owner" "different original invocation"))
  fun description_for {graph,scope,sources,work}
      (focus as Focus {owner,traversal,node,provenance,root_ordinal,...}) =
    protected work (fn () =>
      if Portable.pointer_eq (graph,#graph owner) andalso
          scope = traversal andalso
          Portable.pointer_eq (sources,#sources owner) andalso
          Portable.pointer_eq (work,#work owner) then
        (active focus;
         {node = node,scope = traversal,provenance = provenance,
          occurrence = if root_ordinal >= 0 then SOME root_ordinal else NONE})
      else raise ERR "description_for" "different original owner/frame")
  fun node (f as Focus {node,...}) = (active f;node)
  fun scope (f as Focus {traversal,...}) = (active f;traversal)
  fun child (f as Focus {child,...}) = (active f;child)
  fun provenance (f as Focus {provenance,...}) = (active f;provenance)
  fun original_occurrence (f as Focus {root_ordinal,...}) =
    protected (work_of f) (fn () =>
      (active f;if root_ordinal >= 0 then root_ordinal else
        raise ERR "original_occurrence" "positive Goal is not a Source slot"))
  fun root_sources (f as Focus
      {original,opened,goal_unopened,provenance,...}) =
    protected (work_of f) (fn () =>
      (active f;if goal_unopened then raise ERR "root_sources"
          (case provenance of
              UnopenedOriginalOccurrence =>
                "unopened assumption Source has no opened view"
            | UnopenedOriginalDescendant =>
                "unopened assumption Source has no opened view"
            | _ => "unopened positive Source has no opened view")
       else {original = original,opened = opened}))

  (* Every derived focus keeps the incoming path guard, then normalizes its
     own handle to the actual traversal frame. It does not infer body frames
     from node_scope of constants or adopt a first source_anchor. *)
  fun descend (parent as Focus
      {owner,original,opened,root_ordinal,goal_unopened,...})
      traversal incoming_caller incoming extras provenance =
    let val graph = #graph owner
        val _ = active parent
        val current = G.closure_child_node graph incoming_caller incoming
        val root = G.closure_root graph traversal current
        val result = Focus
          {owner = owner,traversal = traversal,caller = traversal,
           child = root,node = current,original = original,opened = opened,
           root_ordinal = root_ordinal,
           provenance = provenance,goal_unopened = goal_unopened,
           guards = (fn () => active parent) ::
             (fn () => ignore (G.closure_child_node graph
               incoming_caller incoming)) :: extras,
           validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end
  fun at_node parent traversal current guards =
    let val graph = #graph (owner_of parent)
        val root = invoke parent
          (fn () => G.closure_root graph traversal current)
    in descend parent traversal traversal root guards GeneratedResult end
  fun descendant parent = case provenance parent of
      OriginalOccurrence => OriginalDescendant
    | OriginalDescendant => OriginalDescendant
    | OriginalPositiveGoal => PositiveGoalDescendant
    | PositiveGoalDescendant => PositiveGoalDescendant
    | UnopenedPositiveGoal => UnopenedGoalDescendant
    | UnopenedGoalDescendant => UnopenedGoalDescendant
    | UnopenedOriginalOccurrence => UnopenedOriginalDescendant
    | UnopenedOriginalDescendant => UnopenedOriginalDescendant
    | ClosedAuxiliaryRoot => ClosedAuxiliaryDescendant
    | ClosedAuxiliaryDescendant => ClosedAuxiliaryDescendant
    | _ => GeneratedDescendant

  fun start_goal work {view,native_contract,profiles} = W.with_step work (fn ()
    =>
    let val native=NC.for_work work native_contract
        val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = #semantic_limits native
        val policy_limits = W.semantic_policy work
        val _ = W.validate_policy work graph root sources policy_limits
        val original = S.goal_source sources
        fun registered () =
          let val saved = S.goal_source sources
              val _ = W.validate_policy work graph root sources policy_limits
              val _ = if #node saved = #node original andalso
                  Portable.pointer_eq (#original saved,#original original)
                  andalso Portable.pointer_eq (#bridge saved,#bridge original)
                then () else raise ERR "start_goal" "positive Source changed"
          in case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened end
        val _ = registered ()
        val opened = case view of NONE => original | SOME saved => saved
        val current = #node opened
        val root_child = G.closure_root graph root current
        val _ = W.spend_policy work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits=limits,policy_limits=policy_limits,
                    native_contract=native_contract,native_data=native,
                    profiles=profiles,
                    epoch=Type.type_epoch ()},
           traversal = root,caller = root,child = root_child,node = current,
           original = original,opened = opened,root_ordinal = ~1,
           provenance = (case view of NONE => UnopenedPositiveGoal
             | SOME _ => OriginalPositiveGoal),
           goal_unopened = (case view of NONE => true | SOME _ => false),
           guards = [registered],validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end)
  (* The supplied ordinal must name a retained assumption (>=1).
     The option selects genuine opened syntax or explicitly unopened DATA,
     never a caller category/cap override. SAME Work owns the action. *)
  fun start_assumption work {occurrence,view,native_contract,profiles} =
    W.with_step work (fn () =>
    let val native=NC.for_work work native_contract
        val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = #semantic_limits native
        val policy_limits = W.semantic_policy work
        val _ = W.validate_policy work graph root sources policy_limits
        val _ = if occurrence >= 1 then () else
          raise ERR "start_assumption" "not an original assumption index"
        fun select [] (_:IntInf.int) = raise ERR "start_assumption"
              "absent original assumption"
          | select (source::rest) i =
              (W.spend_policy work 1;if i = 0 then source else select rest
                (i-1))
        val original = select (S.reconciliation_sources sources) occurrence
        fun registered () =
          (* Opaque S retains this immutable occurrence portfolio. SAME
             W/S identity is rechecked; guards do not rerun selection. *)
          let val _ = W.validate_policy work graph root sources policy_limits
          in case view of NONE => () | SOME opened =>
            G.validate_opened_view graph root (#node original) opened end
        val _ = registered ()
        val opened = case view of NONE => original | SOME saved => saved
        val current = #node opened
        val root_child = G.closure_root graph root current
        val _ = W.spend_policy work 1
        val result = Focus
          {owner = {graph = graph,root = root,sources = sources,work = work,
                    limits=limits,policy_limits=policy_limits,
                    native_contract=native_contract,native_data=native,
                    profiles=profiles,
                    epoch=Type.type_epoch ()},
           traversal = root,caller = root,child = root_child,node = current,
           original = original,opened = opened,root_ordinal = occurrence,
           provenance = (case view of NONE => UnopenedOriginalOccurrence
             | SOME _ => OriginalOccurrence),
           goal_unopened = (case view of NONE => true | SOME _ => false),
           guards = [registered],validated = ref (~1 : IntInf.int)}
        val _ = active result
    in result end)

  fun application_children (parent as Focus {caller,child,...}) =
    let val graph = #graph (owner_of parent)
        val pair = invoke parent
          (fn () => G.closure_application_children graph caller child)
        val traversal = scope parent
    in (descend parent traversal caller (#1 pair) [] (descendant parent),
        descend parent traversal caller (#2 pair) [] (descendant parent)) end
  fun binder_body (parent as Focus {caller,child,...}) =
    let val graph = #graph (owner_of parent)
        val closure = invoke parent
          (fn () => G.closure_child_binder graph caller child)
        val data = invoke parent
          (fn () => G.binder_closure_data graph caller closure)
        val body = invoke parent
          (fn () => G.binder_closure_body graph caller closure)
        fun held () = ignore (G.binder_closure_data graph caller closure)
    in descend parent (#body_frame data) caller body [held]
      (descendant parent) end

  fun clean theorem =
    null (Thm.hyp theorem) andalso null (Tag.axioms_of (Thm.tag theorem))
    andalso List.all (fn oracle => oracle = "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag theorem)))
  fun check_endpoints initial target theorem =
    let val graph = #graph (owner_of initial)
        val _ = require_owner initial target
        val _ = if scope initial = scope target then () else
          raise ERR "endpoints" "different traversal frame"
        val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
    in if clean theorem andalso Portable.pointer_eq
          (left,G.representative graph (node initial)) andalso
          Portable.pointer_eq (right,G.representative graph (node target))
          andalso G.type_id graph (node initial) =
            G.type_id graph (node target) then () else
         raise ERR "endpoints" "unclean or changed canonical endpoints" end
  fun checked (initial,target,theorem,backing) =
    let val guard = validation_guard (fn () =>
          (active initial;active target;backing ();
           check_endpoints initial target theorem))
        val _ = guard ()
    in Conversion {initial = initial,target = target,theorem = theorem,
                   guard = guard} end
  fun validate (Conversion {initial,guard,...}) =
    protected (work_of initial) guard
  fun endpoints (c as Conversion {initial,target,theorem,...}) =
    (validate c;{source = node initial,target = node target,theorem = theorem})
  (* This typed pure projection has no callback argument or retained
     cache. Expected ownership of BOTH endpoints is compared before any
     conversion/foreign backing activation. A successful validate already
     checks every held path, exact theorem endpoint, Hyp/tag and frame. *)
  fun conversion_description_for {graph,scope,sources,work}
      (converted as Conversion
        {initial = Focus {owner = first,traversal = left_scope,
                          node = left,...},
         target = Focus {owner = last,traversal = right_scope,
                         node = right,...},...}) =
    protected work (fn () =>
      if Portable.pointer_eq (graph,#graph first) andalso
          Portable.pointer_eq (graph,#graph last) andalso
          Portable.pointer_eq (sources,#sources first) andalso
          Portable.pointer_eq (sources,#sources last) andalso
          Portable.pointer_eq (work,#work first) andalso
          Portable.pointer_eq (work,#work last) andalso
          left_scope = scope andalso right_scope = scope then
        (validate converted;{source = left,target = right,scope = scope})
      else raise ERR "conversion_description_for"
        "different expected conversion owner/frame")

  fun target_focus (c as Conversion {target,...}) = (validate c;target)
  fun initial_focus (c as Conversion {initial,...}) = (validate c;initial)
  (* Pure owner projection: NEVER activate a foreign receipt to identify it. *)
  fun peek_initial (Conversion {initial,...}) = initial
  fun expected focus =
    let val owner = owner_of focus
    in {graph = #graph owner,scope = scope focus,sources = #sources owner,
        work = #work owner} end

  fun adopt_beta focus receipt = W.with_step (work_of focus) (fn () =>
    let fun backing () = B.validate_with_policy_for (expected focus) receipt
        val _ = backing ()  (* BEFORE receipt endpoint/theorem getters *)
        val {source,target,theorem} = B.endpoints_with_policy receipt
        val _ = if source = node focus then () else
          raise ERR "adopt_beta" "different owned source focus"
        val result = at_node focus (scope focus) target [backing]
    in checked (focus,result,theorem,backing) end)
  fun profile_for focus frame current =
    let val owner=owner_of focus
        fun seek [] = NONE
          | seek (held::rest) =
              let val _=spend focus 1
                  val data=invoke focus (fn()=>
                    G.opaque_profile_data_with_policy (#graph owner)
                      frame held)
              in if #node data=current then SOME held else seek rest end
    in seek (#profiles owner) end

  fun inventory focus roots =
    let val graph = #graph (owner_of focus)
        val limits = #limits (owner_of focus)
        val maximum = Int.max (#input_limit limits,
          Int.max (#output_limit limits,#template_limit limits))
        val ceiling = IntInf.fromInt (#type_work_limit (#native_data (owner_of
          focus)))
        fun plus a b = IntInf.min (ceiling+1,a+b)
        val types = ref ([] : Type.hol_type list)
        val held = ref ([] : (G.scope * G.closure_child) list)
        val opaque = ref ([] : (G.scope * G.policy_opaque_profile) list)
        val memo = ref ([] : (G.node * footprint) list)
        fun weight ty =
          let fun walk [] n = n
                | walk (pending::more) n =
                  (spend focus 1;case pending of [] => walk more n
                   | current::rest =>
                     let val next = plus n 1
                         val _ = if next <= ceiling then () else
                           raise ERR "inventory" "type footprint exceeds Work"
                     in if invoke focus (fn () => Type.is_vartype current)
                        then walk (rest::more) next
                        else walk ((invoke focus
                          (fn () => #2 (Type.dest_type current)))::rest::more)
                          next end)
          in walk [[ty]] 0 end
        fun annotation current =
          let val ty = invoke focus (fn () => G.type_of graph current)
              val count = weight ty val _ = spend focus 1
              val _ = types := ty :: !types
          in count end
        fun lookup current [] = NONE
          | lookup current ((old,value)::rest) =
              (spend focus 1;if current = old then SOME value
               else lookup current rest)
        fun visit caller requester child =
          let val _ = spend focus 1
              val current = invoke focus
                (fn () => G.closure_child_node graph caller child)
              val _ = held := (caller,child) :: !held
          in case lookup current (!memo) of SOME value => value
           | NONE =>
            let val kind = invoke focus (fn () => G.view graph current)
                val profile = case kind of G.OpaqueRetained =>
                    profile_for focus requester current
                  | _ => NONE
                val ty = case profile of SOME held =>
                    #ty (invoke focus (fn () =>
                      G.opaque_profile_data_with_policy graph
                      requester held))
                  | NONE => annotation current
                val value : footprint = case kind of
                    G.Application _ =>
                      let val (f,x) = invoke focus (fn () =>
                            G.closure_application_children graph caller child)
                          val a = visit caller requester f
                          val b = visit caller requester x
                      in {raw = plus 1 (plus (#raw a) (#raw b)),
                          inc = plus 1 (plus (#inc a) (#inc b)),
                          ann = plus ty (plus (#ann a) (#ann b)),ty = ty}
                      end
                  | G.AdmittedBinder _ =>
                      let val binder = invoke focus (fn () =>
                            G.closure_child_binder graph caller child)
                          val d = invoke focus (fn () =>
                            G.binder_closure_data graph caller binder)
                          val bt = annotation (#binder d)
                          val b = visit caller (#body_frame d) (invoke focus
                            (fn () =>
                            G.binder_closure_body graph caller binder))
                      in {raw = plus 1 (#raw b),inc = plus 2 (#inc b),
                          ann = plus ty (plus bt (#ann b)),ty = ty} end
                  | G.OpaqueRetained => (case profile of NONE =>
                      raise ERR "inventory"
                        "unrecorded opaque annotation portfolio"
                    | SOME held =>
                      let val data = invoke focus
                            (fn () => G.opaque_profile_data_with_policy graph
                              requester held)
                          val _ = spend focus 1
                          val _ = opaque := (requester,held) :: !opaque
                          val _ = List.app (fn ty =>
                            (spend focus 1;types := ty :: !types)) (#types
                              data)
                      in {raw = #raw data,
                          inc = #inc data,
                          ann = #ann data,ty = #ty data} end)
                  | _ => {raw = 1,inc = 1,ann = ty,ty = ty}
                val _ = spend focus 1
                val _ = memo := (current,value) :: !memo
            in value end end
        val captures = ref ([]:G.profiled_metric list)
        fun root current =
          let
            val capture=invoke focus (fn()=>G.prepare_profiled_metric graph
              (scope focus)
              {node=current,profiles= #profiles (owner_of focus)})
            val data=invoke focus (fn()=>G.profiled_metric_data graph
              (scope focus) capture)
            val _=spend focus 2
            val _=if #raw data<=IntInf.fromInt maximum andalso
                #inc data<=IntInf.fromInt maximum then () else
              raise ERR "inventory" "cached syntax exceeds caps"
            val _=captures:=capture:: !captures
          in visit (scope focus) (scope focus) (invoke focus
            (fn () => G.closure_root graph (scope focus) current)) end
        val values = List.map root roots
        fun guard () =
          (active focus;
           List.app (fn capture=>ignore (G.profiled_metric_data graph
             (scope focus) capture)) (!captures);
           List.app (fn (caller,child) =>
            ignore (G.closure_child_node graph caller child)) (!held);
           List.app (fn (requester,profile) => ignore
             (G.opaque_profile_data_with_policy graph requester profile))
             (!opaque))
    in (values,!types,guard) end

  (* Only the internal quoted role changes the node bound. Both paths
     retain the original Work debit; semantic result and checked evidence
     are separate portfolios, never a caller scalar-cap override. *)
  datatype quoted_role = SemanticResult | ClosedEquation of footprint
  fun reserve_role role focus ordinal target proofs =
    let val owner = owner_of focus val limits = #limits owner
        val ceiling = IntInf.fromInt (#type_work_limit (#native_data owner))
        fun plus a b = IntInf.min (ceiling+1,a+b)
        val policy_limits= #policy_limits owner
        fun bound label maximum policy (value : footprint) =
          if #raw value <= IntInf.fromInt maximum andalso
              #inc value <= IntInf.fromInt maximum andalso
              RP.allows policy (#raw value) andalso
              RP.allows policy (#inc value) then () else
            raise ERR "reserve" (label ^ " exceeds original semantic cap")
        val _ = case role of SemanticResult =>
            bound "target" (#output_limit limits)
              (#output_limit policy_limits) target
          | ClosedEquation result =>
            (bound "target" (#output_limit limits)
               (#output_limit policy_limits) result;
             bound "closed equality" (#template_limit limits)
               (#template_limit policy_limits) target)
        val _ = List.app (bound "proof" (#template_limit limits)
          (#template_limit policy_limits)) proofs
        val amount = List.foldl (fn (value : footprint,total) =>
          plus total (plus (#raw value) (plus (#inc value) (#ann value))))
          (plus (#raw target) (plus (#inc target) (#ann target))) proofs
        val _ = if ordinal >= 0 andalso amount > 0 andalso amount <= ceiling
          then () else raise ERR "reserve" "malformed/exhausted footprint"
        val token = W.reserve_policy (#work owner)
          {role = W.LocalCarrier,ordinal = ordinal,
           amount = amount}
    in W.consume_policy (#work owner) token amount end
  fun reserve focus ordinal target proofs =
    reserve_role SemanticResult focus ordinal target proofs
  fun equation (a : footprint) (b : footprint) : footprint =
    {raw = 3 + #raw a + #raw b,inc = 3 + #inc a + #inc b,
     ann = 6 + 3 * #ty a + #ann a + #ann b,ty = 1}
  fun policies focus guard types result_types ordinal future_count policy =
    let
        fun count [] n = n
          | count (_::rest) n = (spend focus 1;count rest (n+1))
        val count_types = count types 0
        val count_results = count result_types 0
        val amount = IntInf.fromInt count_types +
          11 * IntInf.fromInt count_results + IntInf.fromInt future_count
        val _ = if amount > 0 andalso
            amount <= IntInf.fromInt (#type_work_limit (#native_data (owner_of
              focus))) then ()
          else raise ERR "policies" "policy/render portfolio exceeds Work"
        val work = work_of focus
        val token = W.reserve_policy work
          {role = W.FactAssembly,ordinal = ordinal,
           amount = amount}
        fun consume amount = (active focus;W.consume_policy work token
          (IntInf.fromInt amount))
        fun call ty =
          (active focus;guard ();consume 1;
           policy ty;active focus;guard ())
        (* Render only the fixed prospective equality shell AFTER reserving
           its full annotation portfolio. Type internals remain unclosed. *)
        fun render result_type =
          let val _ = consume 4
              val inner = invoke focus
                (fn () => Type.mk_type ("fun",[result_type,Type.bool]))
              val _ = consume 4
              val outer = invoke focus
                (fn () => Type.mk_type ("fun",[result_type,inner]))
          in [Type.bool,inner,outer] end
        val generated = List.map render result_types
        val _ = List.app call types
        val _ = List.app (List.app call) generated
    in call end

  (* Quote the actual P callback forest: unique graph annotations followed
     by genuine opaque-profile Type roots. Separate root captures may repeat
     a shared profile; that is conservative, never a missing occurrence. *)
  fun future_type_forest focus backing roots prospective =
    let val owner=owner_of focus val graph= #graph owner
        val frame=scope focus
        val captures=List.map (fn node=>invoke focus (fn()=>
          G.prepare_profiled_metric graph frame
            {node=node,profiles= #profiles owner})) roots
        fun guard ()=
          (backing ();List.app (fn capture=>ignore
            (G.profiled_metric_data graph frame capture)) captures)
        val nodes=invoke focus (fn()=>G.reachable graph roots)
        val extra=List.concat (List.map (fn capture=>
          #types (invoke focus (fn()=>
            G.profiled_metric_data graph frame capture))) captures)
        val remaining=ref (#template_limit (#limits owner))
        fun walk []=()
          | walk (pending::more)=
              (spend focus 1;case pending of []=>walk more | ty::rest=>
                let val _=if !remaining>0 then remaining:= !remaining-1
                      else raise ERR "future_type_forest"
                        "P type forest exceeds native template"
                in if invoke focus (fn()=>Type.is_vartype ty) then
                     walk (rest::more)
                   else let val args=invoke focus
                         (fn()=> #2 (Type.dest_type ty))
                        in walk (args::rest::more) end end)
        fun count_types [] n=n
          | count_types (ty::rest) n=
              (spend focus 1;guard ();walk [[ty]];count_types rest (n+1))
        fun count_nodes [] n=n
          | count_nodes (node::rest) n=
              (spend focus 1;guard ();
               walk [[invoke focus (fn()=>G.type_of graph node)]];
               count_nodes rest (n+1))
        (* These are the admitted fixed equality shell's three new graph
           annotation roots, not a count of arbitrary expanded syntax. *)
        val total=count_types extra (count_nodes nodes prospective)
        val _=guard ()
    in (total,guard) end

  fun compose {first,second,ordinal,check_type} =
    let val initial = peek_initial first
        val work = work_of initial
    in protected work (fn () =>
      let val next = peek_initial second
          val _ = require_owner initial next
          val _ = validate first
          val _ = validate second
          val middle = target_focus first val target = target_focus second
          fun guard () = (validate first;validate second)
      in W.with_step work (fn () =>
      let val _ = guard ()
          val _ = if node middle = node next andalso
              scope initial = scope next then () else
            raise ERR "compose" "different exact middle node/frame"
          val (sizes,types,held) = inventory initial
            [node initial,node target]
          val (a,b) = case sizes of [a,b] => (a,b)
            | _ => raise ERR "compose" "internal size portfolio"
          val _ = reserve initial ordinal b [equation a b]
          fun all () = (guard ();held ())
          val graph = #graph (owner_of initial)
          val _ = policies initial all types
            [G.type_of graph (node initial)] ordinal 0 check_type
          val theorem = invoke initial (fn () => Thm.TRANS
            (#theorem (endpoints first)) (#theorem (endpoints second)))
          val _ = all ()
      in checked (initial,target,theorem,all) end) end) end

  fun prepare_application {parent,left,right,ordinal,check_type} =
    W.with_step (work_of parent) (fn () =>
    let val (old_left,old_right) = application_children parent
        fun chosen old NONE = old
          | chosen old (SOME converted) =
              let val initial = peek_initial converted
                  val _ = require_owner parent initial
                  val _ = validate converted
                  val _ = if node old = node initial andalso
                      scope old = scope initial then () else
                    raise ERR "application" "different immediate child"
              in target_focus converted end
        val new_left = chosen old_left left
        val new_right = chosen old_right right
        val graph = #graph (owner_of parent)
        val _ = if G.type_id graph (node old_left) =
            G.type_id graph (node new_left) andalso
            G.type_id graph (node old_right) =
            G.type_id graph (node new_right) then () else
          raise ERR "application" "child conversion type changed"
        val (sizes,types,guard) = inventory parent
          [node parent,node new_left,node new_right]
        val (old,f,x) = case sizes of [a,b,c] => (a,b,c)
          | _ => raise ERR "application" "internal size portfolio"
        val target : footprint =
          {raw = 1 + #raw f + #raw x,inc = 1 + #inc f + #inc x,
           ann = #ty old + #ann f + #ann x,ty = #ty old}
        (* MK_COMB, source ALPHA, target ALPHA and BOTH TRANS results. *)
        val reflexivities =
          (case left of NONE => [equation f f] | SOME _ => []) @
          (case right of NONE => [equation x x] | SOME _ => [])
        val _ = reserve parent ordinal target
          ([equation old target,equation old old,equation target target,
            equation old target,equation old target] @ reflexivities)
        val _ = guard ()
        val guarded_policy = fn ty =>
          (guard ();check_type ty;guard ())
    in ApplicationPlan {parent = parent,old_left = old_left,
      old_right = old_right,new_left = new_left,new_right = new_right,
      left = left,right = right,policy = guarded_policy,types = types,
      result_types = G.type_of graph (node parent) ::
        ((case left of NONE => [G.type_of graph (node new_left)]
          | SOME _ => []) @
         (case right of NONE => [G.type_of graph (node new_right)]
          | SOME _ => [])),ordinal = ordinal,state = ref Ready} end)

  fun execute_application (ApplicationPlan
      {parent,old_left,old_right,new_left,new_right,left,right,
       policy,types,result_types,ordinal,state}) =
    let val work = work_of parent val graph = #graph (owner_of parent)
        fun guard () =
          (active parent;active old_left;active old_right;
           active new_left;active new_right;
           List.app (fn item => case item of NONE => ()
             | SOME converted => validate converted) [left,right])
        fun proof old NONE = invoke parent
              (fn () => Thm.REFL (G.representative graph (node old)))
          | proof old (SOME converted) =
              (validate converted;#theorem (endpoints converted))
        fun immediate label term a b =
          let val (f,x) = Term.dest_comb term
          in if Portable.pointer_eq
              (f,G.representative graph (node a)) andalso
              Portable.pointer_eq (x,G.representative graph (node b)) then ()
             else raise ERR "application" (label ^ " child pointer changed")
          end
    in W.with_step work (fn () =>
      ((guard ();case !state of Ready => state := Running
        | _ => raise ERR "application" "plan is one shot");
       let val _ = policies parent guard types result_types ordinal 0 policy
           val target_node = invoke parent (fn () => G.application graph
             (scope parent) (node new_left,node new_right))
           val target = at_node parent (scope parent) target_node [guard]
           val theorem = invoke parent
             (fn () => Thm.MK_COMB (proof old_left left,proof old_right right))
           val (a,b) = boolSyntax.dest_eq (Thm.concl theorem)
           (* Kernel MK_COMB rebuilds OUTER applications. Authenticate the
              exact immediate children, never demand fresh outer pointers. *)
           val _ = immediate "source" a old_left old_right
           val _ = immediate "target" b new_left new_right
           val align_left = invoke parent (fn () => Thm.ALPHA
             (G.representative graph (node parent)) a)
           val align_right = invoke parent (fn () => Thm.ALPHA b
             (G.representative graph target_node))
           val tail = invoke parent (fn () => Thm.TRANS theorem align_right)
           val complete = invoke parent (fn () => Thm.TRANS align_left tail)
           val _ = guard () val _ = state := Complete
       in checked (parent,target,complete,guard) end)
      handle primary => (state := Retired;W.close work;raise primary)) end

  fun closed_fact converted {ordinal,check_type} =
    let val initial = initial_focus converted
        val target = target_focus converted
        val work = work_of initial val graph = #graph (owner_of initial)
        val limits = #limits (owner_of initial)
    in W.with_step work (fn () =>
      let val _ = validate converted
          val (sizes,types,held) = inventory initial
            [node initial,node target]
          val (a,b) = case sizes of [a,b] => (a,b)
            | _ => raise ERR "closed_fact" "internal size portfolio"
          val equality = equation a b
          val _ = reserve_role (ClosedEquation b) initial ordinal equality
            [equality]
          fun guard () = (validate converted;held ())
          (* The future P type-policy portfolio has at most every held
             unique annotation node plus the THREE new equality nodes.
             Inventory includes binder VARIABLE annotations too. Reserve
             this incidence ceiling before the FIRST supplied policy. *)
          val (future_count,extra_guard)=future_type_forest initial guard
            [node initial,node target] 3
          fun all ()=(guard ();extra_guard ())
          val policy = policies initial all types
            [G.type_of graph (node initial)] ordinal future_count check_type
          val theorem = #theorem (endpoints converted)
          val operator = Term.rator (Term.rator (Thm.concl theorem))
          val head = invoke initial
            (fn () => G.constant graph (scope initial) operator)
          val partial = invoke initial (fn () => G.application graph
            (scope initial) (head,node initial))
          val equality_node = invoke initial (fn () => G.application graph
            (scope initial) (partial,node target))
          val result = invoke initial (fn () =>
            P.record_closed_with_policy_profiles graph
            (scope initial) {node = equality_node,theorem = theorem,
              template_limit = #template_limit (#policy_limits (owner_of
                initial)),
              check_type=policy,profiles= #profiles (owner_of initial)})
          val _ = all ()
      in result end) end

  fun closed_fact_for expected converted request =
    protected (#work expected) (fn () =>
      (ignore (description_for expected (peek_initial converted));
       closed_fact converted request))

  (* Lambda consumes a genuine registered whole import/opened pair. A
     generic closed equality does not establish that association. Quote the
     actual equality and both import/opening bridges before either producer;
     metadata policy never replaces the finite caller's native admission. *)
  fun closed_fact_from_import converted {ordinal,check_type} =
    let val initial=peek_initial converted val work=work_of initial
    in protected work (fn()=>W.with_step work (fn()=>
      let val _=validate converted
          val target=target_focus converted val owner=owner_of initial
          val graph= #graph owner val frame=scope initial
          val (sizes,types,held)=inventory initial
            [node initial,node target]
          val (a,b)=case sizes of [a,b]=>(a,b)
            | _=>raise ERR "closed_fact_from_import" "internal portfolio"
          val equality=equation a b
          val bridge=equation equality equality
          val _=reserve_role (ClosedEquation b) initial ordinal equality
            [equality,bridge,bridge]
          val theorem= #theorem (endpoints converted)
          val original=Thm.concl theorem
          fun original_guard ()=(validate converted;held ())
          val _=original_guard ()
          val plan=invoke initial (fn()=>G.plan_import_with_policy graph frame
            (RP.from_int (#import_limit (#native_data owner))) original)
          val import_types=invoke initial (fn()=>
            G.import_types_with_policy plan)
          val remaining=ref (#type_work_limit (#native_data owner))
          fun admit_types []=()
            | admit_types (pending::more)=
                (spend initial 1;case pending of []=>admit_types more
                 | ty::rest=>
                   let val _=if !remaining>0 then remaining:= !remaining-1
                         else raise ERR "closed_fact_from_import"
                           "import Type portfolio exceeds native contract"
                   in if invoke initial (fn()=>Type.is_vartype ty) then
                        admit_types (rest::more)
                      else let val args=invoke initial
                            (fn()=> #2 (Type.dest_type ty))
                           in admit_types (args::rest::more) end end)
          val _=admit_types [import_types]
          val _=original_guard ()
          val imported=invoke initial (fn()=>
            G.execute_import_with_policy plan)
          val opened=invoke initial (fn()=>G.record_opened_view_with_policy
            graph frame (RP.from_int (#template_limit (#limits owner)))
            (#node imported))
          fun association ()=
            let val (first,second)=G.imported_opened_source graph frame
                  original (#node opened)
            in if #node first= #node imported andalso
                #node second= #node opened andalso
                Portable.pointer_eq (#bridge first,#bridge imported)
                andalso Portable.pointer_eq (#bridge second,#bridge opened)
              then () else raise ERR "closed_fact_from_import"
                "registered whole import/opened pair changed" end
          fun guard ()=(original_guard ();association ())
          val _=guard ()
          val (actual,opened_types,opened_guard)=inventory initial
            [#node opened]
          val actual=case actual of [value]=>value
            | _=>raise ERR "closed_fact_from_import" "opened portfolio"
          val _=reserve_role (ClosedEquation b) initial ordinal actual
            [equation actual actual]
          val (future,extra_guard)=future_type_forest initial guard
            [#node opened] 0
          fun all ()=(guard ();opened_guard ();extra_guard ())
          val policy=policies initial all (types @ opened_types)
            [G.type_of graph (node initial)] ordinal future check_type
          val result=invoke initial (fn()=>
            P.record_closed_from_import_with_policy_profiles graph frame
              {node= #node opened,theorem=theorem,
               template_limit= #template_limit (#policy_limits owner),
               check_type=policy,profiles= #profiles owner})
          val _=all ()
      in result end)) end

  fun closed_fact_from_import_for expected converted request=
    protected (#work expected) (fn()=>
      (ignore (conversion_description_for expected converted);
       closed_fact_from_import converted request))

  fun lift_lambda_admitted
      {parent,admission,body,record_ordinal,lift_ordinal,check_type} =
    protected (work_of parent) (fn () =>
    let val _ = active parent
        val owner = owner_of parent
        val graph = #graph owner
        val expected : Q.expected =
          {graph = graph,scope = scope parent,sources = #sources owner,
           work = #work owner}
        val d = Q.describe_with_policy_for expected admission
        val expected_category = case provenance parent of
            OriginalOccurrence => Q.Original
          | OriginalDescendant => Q.Original
          | OriginalPositiveGoal => Q.Original
          | PositiveGoalDescendant => Q.Original
          | UnopenedPositiveGoal => Q.Original
          | UnopenedGoalDescendant => Q.Original
          | UnopenedOriginalOccurrence => Q.Original
          | UnopenedOriginalDescendant => Q.Original
          | ClosedAuxiliaryRoot => Q.Auxiliary
          | ClosedAuxiliaryDescendant => Q.Auxiliary
          | _ => Q.Generated
        (* Private lineage ordinal, not the public Source-index getter.
           -1 agrees with lower Goal DATA and confers no P.Source slot. *)
        val Focus {root_ordinal = held_ordinal,...} = parent
        val _ = if #node d = node parent andalso
            #category d = expected_category andalso
            #occurrence d = held_ordinal then () else
          raise ERR "lambda_admitted" "different parent admission provenance"
        val initial = peek_initial body
        val _ = require_owner parent initial
        val _ = validate body
        val graph = #graph (owner_of parent)
        val Focus {caller,child,...} = parent
        val closure = invoke parent
          (fn () => G.closure_child_binder graph caller child)
        val captured = invoke parent
          (fn () => G.binder_closure_data graph caller closure)
        val _ = if node initial = #body captured andalso
            scope initial = #body_frame captured then () else
          raise ERR "lambda" "different owned body node/frame"
        val admitted_closure = invoke parent (fn () =>
          G.closure_child_binder graph (scope parent) (#child d))
        val admitted_data = invoke parent (fn () =>
          G.binder_closure_data graph (scope parent) admitted_closure)
        val _ = if #node admitted_data = #node captured andalso
            #binder admitted_data = #binder captured andalso
            #body admitted_data = #body captured andalso
            #body_frame admitted_data = #body_frame captured andalso
            #binder_frame admitted_data = #binder_frame captured andalso
            #declaring_scope admitted_data = #declaring_scope captured andalso
            #node_frame admitted_data = #node_frame captured then () else
          raise ERR "lambda_admitted" "different genuine binder path"
        fun guard () =
          (active parent;Q.validate_with_policy_for expected admission;validate
            body)
        fun policy ty = (guard ();check_type ty;guard ())
        val evidence = closed_fact_from_import body
          {ordinal = record_ordinal,check_type = policy}
        val _ = guard ()
        val owner = owner_of parent
        val result = L.execute_with_policy (L.prepare_admitted_with_policy
          {graph = graph,scope = scope parent,
           sources = #sources owner,work = #work owner,ordinal = lift_ordinal,
           admission=admission,body_fact=evidence,
           native_contract= #native_contract owner,
           profiles= #profiles owner,check_type=policy})
        fun backing () =
          (guard ();L.validate_with_policy_for
            {graph = graph,caller = scope parent,scope = scope parent,
             sources = #sources owner,work = #work owner} result)
        val _ = backing ()
        val {source,target,theorem}=L.endpoints_with_policy_for
          {graph=graph,caller=scope parent,scope=scope parent,
           sources= #sources owner,work= #work owner} result
        val _ = if source = node parent then () else
          raise ERR "lambda" "different lambda source"
        val focus = at_node parent (scope parent) target [backing]
    in checked (parent,focus,theorem,backing) end)

  (* Authentic lower focus determines the source role; its semantic
     evidence is not previous Work credit. The comparison itself debits
     SAME Work before Term.aconv and retains all lifetime guards. *)
  fun alpha_changed_admitted {conversion,admission} =
    let val initial = initial_focus conversion
        val target = target_focus conversion
        val work = work_of initial val owner = owner_of initial
        val Focus {root_ordinal,...} = initial
    in W.with_step work (fn () =>
      let val _ = validate conversion
          val data = Q.describe_with_policy_for
            {graph = #graph owner,scope = scope initial,
             sources = #sources owner,work = work} admission
          val _ = if #node data = node initial andalso
              #occurrence data = root_ordinal then () else
            raise ERR "alpha_changed_admitted" "different initial receipt"
          val kind = provenance initial
          val matching = case (kind,#category data) of
              (OriginalOccurrence,Q.Original) => true
            | (OriginalDescendant,Q.Original) => true
            | (OriginalPositiveGoal,Q.Original) => true
            | (PositiveGoalDescendant,Q.Original) => true
            | (ClosedAuxiliaryRoot,Q.Auxiliary) => true
            | (ClosedAuxiliaryDescendant,Q.Auxiliary) => true
            | (GeneratedResult,Q.Generated) => true
            | (GeneratedDescendant,Q.Generated) => true
            | _ => false
          val _ = if matching then () else raise ERR "alpha_changed_admitted"
            "different original/generated source role"
          val answer = A.same_admitted_inside_with_policy work
            {caller = scope initial,traversal = scope initial,
             left=child initial,right=child target,admission=admission,
             native_contract= #native_contract owner,
             profiles= #profiles owner}
          val _ = validate conversion
      in not answer end) end

  fun source_conversion converted {ordinal,check_type} =
    let val initial = peek_initial converted val work = work_of initial
    in protected work (fn () => W.with_step work (fn () =>
      let
        val _ = validate converted
        val Focus {owner,original,opened,root_ordinal,provenance,...} = initial
        val graph = #graph owner val root = #root owner
        val limits = #limits owner
        val _ = if provenance = OriginalOccurrence andalso
            scope initial = root andalso node initial = #node opened then ()
          else raise ERR "source_conversion" "not an initial root occurrence"
        fun occurrence [] (_:IntInf.int) = raise ERR "source_conversion"
              "original occurrence disappeared"
          | occurrence (first::rest) n =
              (spend initial 1;if n = 0 then first
               else occurrence rest (n-1))
        fun original_guard () =
          let val held = occurrence
                (S.reconciliation_sources (#sources owner)) root_ordinal
          in if #node held = #node original andalso
              Portable.pointer_eq (#original held,#original original) andalso
              Portable.pointer_eq (#bridge held,#bridge original) then
                G.validate_opened_view graph root (#node original) opened
            else raise ERR "source_conversion" "original Source changed"
          end
        val _ = original_guard ()
        val target = target_focus converted
        val (sizes,types,held) = inventory initial
          [node initial,node target]
        val (a,b) = case sizes of [a,b] => (a,b)
          | _ => raise ERR "source_conversion" "internal size portfolio"
        val _ = if G.type_id graph (#node original) =
            G.type_id graph (node initial) andalso
            Type.compare (G.type_of graph (node initial),Type.bool) = EQUAL
          then () else raise ERR "source_conversion" "non-Boolean Source"
        (* Existing held operands: opened alpha bridge aa and owned ab.
           New operations: target REFL bb and one canonical Source TRANS ab.
           No raw original.bridge participates in this canonical result. *)
        val _ = reserve initial ordinal b
          [equation a a,equation a b,equation b b,equation a b]
        val identity = invoke initial (fn () =>
          G.plan_identity_closure_view_with_policy graph root
            (RP.from_int (#template_limit limits))
            {target=child target,retain=[child initial],
             profiles= #profiles owner})
        val published = ref (NONE : G.source option)
        fun guard () =
          (validate converted;held ();original_guard ();
           case !published of NONE =>
             ignore (G.identity_closure_view_node identity)
           | SOME view => G.validate_opened_view graph root (node target) view)
        (* Quote the EXACT existing P.record_conversion forest before any
           supplied policy. Its unique G.reachable includes binder VARIABLE
           nodes. Borrow argument spines; no unadmitted Args @ rest here.
           G.reachable/private Type implementation work remains unclosed. *)
        val reachable = invoke initial (fn () => G.reachable graph
          [node initial,node target])
        (* P captures the source and target profiles in this exact order.
           Their retained Type roots supplement graph reachability; neither
           vector is replaced with a caller count or old int registry. *)
        val extra_captures=List.map (fn current=>invoke initial (fn()=>
          G.prepare_profiled_metric graph root
            {node=current,profiles= #profiles owner}))
          [node initial,node target]
        fun extra_types ()=List.concat (List.map (fn capture=>
          #types (invoke initial (fn()=>
            G.profiled_metric_data graph root capture))) extra_captures)
        val profile_types=extra_types ()
        val remaining = ref (#template_limit limits)
        fun type_walk pending =
          (spend initial 1;case pending of [] => () | spine::more =>
            (spend initial 1;case spine of [] => type_walk more
             | ty::rest =>
               let val _ = if !remaining > 0 then
                     remaining := !remaining-1 else
                     raise ERR "source_conversion" "P type forest exceeds cap"
                   val _ = spend initial 1
               in if invoke initial (fn () => Type.is_vartype ty) then
                    (spend initial 1;type_walk (rest::more))
                  else let val args = invoke initial
                        (fn () => #2 (Type.dest_type ty))
                           val _ = spend initial 2
                       in type_walk (args::rest::more) end end))
        fun forecast [] count = count
          | forecast (current::rest) count =
              (spend initial 1;guard ();
               type_walk [[invoke initial (fn () => G.type_of graph current)]];
               forecast rest (count+1))
        fun forecast_extra [] count = count
          | forecast_extra (ty::rest) count =
              (spend initial 1;guard ();type_walk [[ty]];
               forecast_extra rest (count+1))
        val future_count = forecast_extra profile_types (forecast reachable 0)
        fun complete_guard () =
          (guard ();List.app (fn capture=>
            ignore (G.profiled_metric_data graph root capture)) extra_captures)
        val policy = policies initial complete_guard types
          [G.type_of graph (node initial)] ordinal future_count check_type
        fun bridge theorem left right =
          let val (x,y) = boolSyntax.dest_eq (Thm.concl theorem)
          in if clean theorem andalso Portable.pointer_eq (x,left) andalso
              Portable.pointer_eq (y,right) then () else
            raise ERR "source_conversion" "held exact bridge changed" end
        val _ = complete_guard ()
        val _ = bridge (#bridge opened)
          (G.representative graph (#node original))
          (G.representative graph (node initial))
        val target_view = invoke initial
          (fn () => G.execute_identity_closure_view identity)
        val _ = published := SOME target_view
        val _ = complete_guard ()
        val theorem = invoke initial (fn () => Thm.TRANS (#bridge opened)
          (#theorem (endpoints converted)))
        val _ = bridge theorem (G.representative graph (#node original))
          (G.representative graph (node target))
        val result = invoke initial (fn () =>
          P.record_conversion_with_policy_profiles graph root
          {source = #node original,source_view = opened,
           target = node target,target_view = target_view,theorem = theorem,
           template_limit= #template_limit (#policy_limits owner),
           check_type=policy,profiles= #profiles owner})
        val _ = complete_guard ()
        val _ = P.validate_conversion_with_policy graph root
          (#template_limit (#policy_limits owner)) result
      in result end)) end

  (* A fixed negation closure, AFTER owned positive-Goal traversal. It does
     not create a traversal focus with a larger input/output syntax limit. *)
  fun denial_conversion converted {denial_view,ordinal,check_type} =
    let val initial = peek_initial converted val work = work_of initial
    in protected work (fn () => W.with_step work (fn () =>
      let
        val _ = validate converted
        val Focus {owner,original,opened,provenance,...} = initial
        val graph = #graph owner val root = #root owner
        val sources = #sources owner val limits = #limits owner
        val _ = if provenance = OriginalPositiveGoal andalso
            scope initial = root then () else raise ERR "denial_conversion"
              "requires owned opened positive Goal root"
        val saved = S.goal_source sources
        val _ = if #node saved = #node original andalso
            Portable.pointer_eq (#original saved,#original original) andalso
            Portable.pointer_eq (#bridge saved,#bridge original) then () else
          raise ERR "denial_conversion" "different retained positive Goal"
        val _ = spend initial 1
        val denied = case S.reconciliation_sources sources of first::_ => first
          | [] => raise ERR "denial_conversion" "original denial absent"
        fun registered () =
          (G.validate_opened_view graph root (#node original) opened;
           G.validate_opened_view graph root (#node denied) denial_view)
        val _ = registered ()
        val old_child = invoke initial
          (fn () => G.closure_root graph root (#node denial_view))
        val target = target_focus converted
        val (sizes,types,held) = inventory initial
          [node initial,node target,#node denial_view]
        val (a,b,old_negative) = case sizes of [a,b,c] => (a,b,c)
          | _ => raise ERR "denial_conversion" "internal portfolio"
        fun negated (value : footprint) : footprint =
          {raw = #raw value+2,inc = #inc value+2,
           ann = #ann value+4,ty = 1}
        val na = negated a val nb = negated b
        val _ = if #raw na = #raw old_negative andalso
            #inc na = #inc old_negative andalso
            #ann na = #ann old_negative then () else
          raise ERR "denial_conversion" "retained negation profile differs"
        val _ = if Type.compare (G.type_of graph (node initial),Type.bool)
            = EQUAL then () else raise ERR "denial_conversion" "Goal not Bool"
        val head = case G.view graph (#node denied) of G.Application (f,_) => f
          | _ => raise ERR "denial_conversion" "retained denial not wrapper"
        val _ = spend initial 1
        val _ = if Term.uptodate_term boolSyntax.negation then () else
          raise ERR "denial_conversion" "fixed negation retired"
        val head_term = G.representative graph head
        val _ = case G.view graph head of G.Constant _ => ()
          | _ => raise ERR "denial_conversion" "fixed wrapper head changed"
        val _ = if Term.same_const head_term boolSyntax.negation then () else
          raise ERR "denial_conversion" "not fixed Boolean negation"
        (* Two held Goal bridges, owned equation, two Goal TRANS results,
           held denial bridge and SYM, AP_TERM, input ALPHA, two prefix
           TRANS, output ALPHA, final TRANS, identity REFL, old view bridge.
           Each is quoted with repeated endpoints; nothing is refunded. *)
        val _ = spend initial 15 (* copied footprint portfolio incidence *)
        val proofs = [equation a a,equation a a,equation a b,
          equation a a,equation a b,equation na na,equation na na,
          equation na nb,equation na na,equation na nb,equation na nb,
          equation nb nb,equation na nb,equation nb nb,equation na na]
        val ceiling = IntInf.fromInt (#type_work_limit (#native_data owner))
        fun plus x y = IntInf.min (ceiling+1,x+y)
        fun shape (value : footprint) =
          if #raw value <= IntInf.fromInt (#template_limit limits) andalso
              #inc value <= IntInf.fromInt (#template_limit limits) then ()
          else raise ERR "denial_conversion" "wrapper proof exceeds template"
        val _ = shape nb val _ = List.app shape proofs
        val _=List.app (fn (value:footprint)=>
          if RP.allows (#template_limit (#policy_limits owner)) (#raw value)
              andalso RP.allows (#template_limit (#policy_limits owner))
                (#inc value) then () else raise ERR "denial_conversion"
                  "wrapper exceeds metadata template") (nb::proofs)
        fun extent (value : footprint) =
          plus (#raw value) (plus (#inc value) (#ann value))
        val amount = List.foldl (fn (value,total) => plus (extent value) total)
          (extent nb) proofs
        val _ = if ordinal >= 0 andalso amount > 0 andalso amount <= ceiling
          then () else raise ERR "denial_conversion" "wrapper Work exhausted"
        val token = W.reserve_policy work {role = W.GoalDenial,ordinal =
          ordinal,
          amount = amount}
        val _ = W.consume_policy work token amount
        val _ = spend initial 1
        val published = ref (NONE : G.source option)
        fun guard () =
          (validate converted;held ();registered ();
           ignore (G.closure_child_node graph root old_child);
           if Term.uptodate_term boolSyntax.negation then () else
             raise ERR "denial_conversion" "fixed negation retired";
           case !published of NONE => () | SOME view =>
             G.validate_opened_view graph root (#node view) view)
        (* Quote the actual P forest plus the prospective Boolean wrapper
           annotation before callbacks. Authentic profile roots supplement
           graph reachability and retain their own fresh guards. *)
        val (future,extra_guard)=future_type_forest initial guard
          [#node denial_view,node target,head] 1
        fun all ()=(guard ();extra_guard ())
        val _ = spend initial (length proofs)
        val headers = List.map (fn _ => Type.bool) proofs
        val policy = policies initial all types headers ordinal future
          check_type
        val _ = all ()
        val negative = invoke initial
          (fn () => G.application graph root (head,node target))
        val new_child = invoke initial
          (fn () => G.closure_root graph root negative)
        val identity = invoke initial (fn () =>
          G.plan_identity_closure_view_with_policy graph root
            (RP.from_int (#template_limit limits))
            {target=new_child,retain=[child initial,old_child],
             profiles= #profiles owner})
        fun bridge theorem left right =
          let val (l,r) = boolSyntax.dest_eq (Thm.concl theorem)
          in if clean theorem andalso Portable.pointer_eq (l,left) andalso
              Portable.pointer_eq (r,right) then () else
            raise ERR "denial_conversion" "changed exact bridge" end
        (* Both outer constructors have the SAME admitted immediate child.
           No independent expanded original-body comparison is permitted. *)
        fun outer left right =
          let val (lf,lx) = Term.dest_comb left
              val (rf,rx) = Term.dest_comb right
              val _ = if Term.same_const lf boolSyntax.negation andalso
                  Term.same_const rf boolSyntax.negation andalso
                  Portable.pointer_eq (lx,rx) then () else
                raise ERR "denial_conversion" "wrapper child/head differs"
          in invoke initial (fn () => Thm.ALPHA left right) end
        val _ = bridge (#bridge original) (#original original)
          (G.representative graph (#node original))
        val _ = bridge (#bridge opened)
          (G.representative graph (#node original))
          (G.representative graph (node initial))
        val _ = bridge (#bridge denied) (#original denied)
          (G.representative graph (#node denied))
        val (denied_head,denied_body) = Term.dest_comb (#original denied)
        val _ = if Term.same_const denied_head boolSyntax.negation andalso
            Portable.pointer_eq (denied_body,#original original) then () else
          raise ERR "denial_conversion" "not original fixed Goal denial"
        val first = invoke initial (fn () => Thm.TRANS
          (#bridge original) (#bridge opened))
        val goal = invoke initial (fn () => Thm.TRANS first
          (#theorem (endpoints converted)))
        val _ = bridge goal (#original original)
          (G.representative graph (node target))
        val lifted = invoke initial
          (fn () => Thm.AP_TERM boolSyntax.negation goal)
        val (left,right) = boolSyntax.dest_eq (Thm.concl lifted)
        val input_alignment = outer (#original denied) left
        val output_alignment = outer right
          (G.representative graph negative)
        val prefix = invoke initial (fn () => Thm.SYM (#bridge denied))
        val middle = invoke initial
          (fn () => Thm.TRANS input_alignment lifted)
        val raw = invoke initial (fn () => Thm.TRANS prefix middle)
        val theorem = invoke initial
          (fn () => Thm.TRANS raw output_alignment)
        val _ = bridge theorem (G.representative graph (#node denied))
          (G.representative graph negative)
        val target_view = invoke initial
          (fn () => G.execute_identity_closure_view identity)
        val _ = published := SOME target_view
        val result = invoke initial (fn () =>
          P.record_conversion_with_policy_profiles graph root
          {source = #node denied,source_view = denial_view,target = negative,
           target_view = target_view,theorem = theorem,
           template_limit= #template_limit (#policy_limits owner),
           check_type=policy,profiles= #profiles owner})
        val _ = all ()
        val _ = P.validate_conversion_with_policy graph root
          (#template_limit (#policy_limits owner)) result
      in result end)) end
  end
  type policy_focus = NativePolicyTransport.focus
  type policy_conversion = NativePolicyTransport.conversion
  val start_goal_with_policy = NativePolicyTransport.start_goal
  val start_assumption_with_policy = NativePolicyTransport.start_assumption
  val description_with_policy_for = NativePolicyTransport.description_for
  val node_with_policy = NativePolicyTransport.node
  val scope_with_policy = NativePolicyTransport.scope
  val child_with_policy = NativePolicyTransport.child
  val application_children_with_policy =
    NativePolicyTransport.application_children
  val binder_body_with_policy = NativePolicyTransport.binder_body
  val adopt_beta_with_policy = NativePolicyTransport.adopt_beta
  val target_focus_with_policy = NativePolicyTransport.target_focus
  val endpoints_with_policy = NativePolicyTransport.endpoints
  val conversion_description_with_policy_for =
    NativePolicyTransport.conversion_description_for
  val source_conversion_with_policy = NativePolicyTransport.source_conversion
  type policy_application_plan = NativePolicyTransport.application_plan
  val compose_with_policy = NativePolicyTransport.compose
  val prepare_application_with_policy =
    NativePolicyTransport.prepare_application
  val execute_application_with_policy =
    NativePolicyTransport.execute_application
  val closed_fact_with_policy = NativePolicyTransport.closed_fact
  val closed_fact_with_policy_for = NativePolicyTransport.closed_fact_for
  val closed_fact_from_import_with_policy_for =
    NativePolicyTransport.closed_fact_from_import_for
  val lift_lambda_admitted_with_policy =
    NativePolicyTransport.lift_lambda_admitted
  val denial_conversion_with_policy =
    NativePolicyTransport.denial_conversion
  val alpha_changed_admitted_with_policy =
    NativePolicyTransport.alpha_changed_admitted
  (* Same native portfolios as ordinary publication; metric acquisition
     follows actual checked binder frames and authentic retained profiles. *)
  structure ScopedPolicyPublication =
  struct
    open NativePolicyTransport
  fun inventory focus roots =
    let val graph = #graph (owner_of focus)
        val limits = #limits (owner_of focus)
        val maximum = Int.max (#input_limit limits,
          Int.max (#output_limit limits,#template_limit limits))
        val ceiling = IntInf.fromInt (#type_work_limit (#native_data (owner_of
          focus)))
        fun plus a b = IntInf.min (ceiling+1,a+b)
        val types = ref ([] : Type.hol_type list)
        val held = ref ([] : (G.scope * G.closure_child) list)
        val opaque = ref ([] : (G.scope * G.policy_opaque_profile) list)
        val memo = ref ([] : (G.node * footprint) list)
        fun weight ty =
          let fun walk [] n = n
                | walk (pending::more) n =
                  (spend focus 1;case pending of [] => walk more n
                   | current::rest =>
                     let val next = plus n 1
                         val _ = if next <= ceiling then () else
                           raise ERR "inventory" "type footprint exceeds Work"
                     in if invoke focus (fn () => Type.is_vartype current)
                        then walk (rest::more) next
                        else walk ((invoke focus
                          (fn () => #2 (Type.dest_type current)))::rest::more)
                          next end)
          in walk [[ty]] 0 end
        fun annotation current =
          let val ty = invoke focus (fn () => G.type_of graph current)
              val count = weight ty val _ = spend focus 1
              val _ = types := ty :: !types
          in count end
        fun lookup current [] = NONE
          | lookup current ((old,value)::rest) =
              (spend focus 1;if current = old then SOME value
               else lookup current rest)
        fun visit caller requester child =
          let val _ = spend focus 1
              val current = invoke focus
                (fn () => G.closure_child_node graph caller child)
              val _ = held := (caller,child) :: !held
          in case lookup current (!memo) of SOME value => value
           | NONE =>
            let val kind = invoke focus (fn () => G.view graph current)
                val profile = case kind of G.OpaqueRetained =>
                    profile_for focus requester current
                  | _ => NONE
                val ty = case profile of SOME held =>
                    #ty (invoke focus (fn () =>
                      G.opaque_profile_data_with_policy graph
                      requester held))
                  | NONE => annotation current
                val value : footprint = case kind of
                    G.Application _ =>
                      let val (f,x) = invoke focus (fn () =>
                            G.closure_application_children graph caller child)
                          val a = visit caller requester f
                          val b = visit caller requester x
                      in {raw = plus 1 (plus (#raw a) (#raw b)),
                          inc = plus 1 (plus (#inc a) (#inc b)),
                          ann = plus ty (plus (#ann a) (#ann b)),ty = ty}
                      end
                  | G.AdmittedBinder _ =>
                      let val binder = invoke focus (fn () =>
                            G.closure_child_binder graph caller child)
                          val d = invoke focus (fn () =>
                            G.binder_closure_data graph caller binder)
                          val bt = annotation (#binder d)
                          val b = visit caller (#body_frame d) (invoke focus
                            (fn () =>
                            G.binder_closure_body graph caller binder))
                      in {raw = plus 1 (#raw b),inc = plus 2 (#inc b),
                          ann = plus ty (plus bt (#ann b)),ty = ty} end
                  | G.OpaqueRetained => (case profile of NONE =>
                      raise ERR "inventory"
                        "unrecorded opaque annotation portfolio"
                    | SOME held =>
                      let val data = invoke focus
                            (fn () => G.opaque_profile_data_with_policy graph
                              requester held)
                          val _ = spend focus 1
                          val _ = opaque := (requester,held) :: !opaque
                          val _ = List.app (fn ty =>
                            (spend focus 1;types := ty :: !types)) (#types
                              data)
                      in {raw = #raw data,
                          inc = #inc data,
                          ann = #ann data,ty = #ty data} end)
                  | _ => {raw = 1,inc = 1,ann = ty,ty = ty}
                val _ = spend focus 1
                val _ = memo := (current,value) :: !memo
            in value end end
        val captures = ref ([]:G.profiled_metric list)
        fun root current =
          let
            val capture=invoke focus (fn()=>
              G.prepare_scoped_profiled_metric graph (scope focus)
              {node=current,profiles= #profiles (owner_of focus)})
            val data=invoke focus (fn()=>G.profiled_metric_data graph
              (scope focus) capture)
            val _=spend focus 2
            val _=if #raw data<=IntInf.fromInt maximum andalso
                #inc data<=IntInf.fromInt maximum then () else
              raise ERR "inventory" "cached syntax exceeds caps"
            val _=captures:=capture:: !captures
          in visit (scope focus) (scope focus) (invoke focus
            (fn () => G.closure_root graph (scope focus) current)) end
        val values = List.map root roots
        fun guard () =
          (active focus;
           List.app (fn capture=>ignore (G.profiled_metric_data graph
             (scope focus) capture)) (!captures);
           List.app (fn (caller,child) =>
            ignore (G.closure_child_node graph caller child)) (!held);
           List.app (fn (requester,profile) => ignore
             (G.opaque_profile_data_with_policy graph requester profile))
             (!opaque))
    in (values,!types,guard) end

  fun future_type_forest focus backing roots prospective =
    let val owner=owner_of focus val graph= #graph owner
        val frame=scope focus
        val captures=List.map (fn node=>invoke focus (fn()=>
          G.prepare_scoped_profiled_metric graph frame
            {node=node,profiles= #profiles owner})) roots
        fun guard ()=
          (backing ();List.app (fn capture=>ignore
            (G.profiled_metric_data graph frame capture)) captures)
        val nodes=invoke focus (fn()=>G.reachable graph roots)
        val extra=List.concat (List.map (fn capture=>
          #types (invoke focus (fn()=>
            G.profiled_metric_data graph frame capture))) captures)
        val remaining=ref (#template_limit (#limits owner))
        fun walk []=()
          | walk (pending::more)=
              (spend focus 1;case pending of []=>walk more | ty::rest=>
                let val _=if !remaining>0 then remaining:= !remaining-1
                      else raise ERR "future_type_forest"
                        "P type forest exceeds native template"
                in if invoke focus (fn()=>Type.is_vartype ty) then
                     walk (rest::more)
                   else let val args=invoke focus
                         (fn()=> #2 (Type.dest_type ty))
                        in walk (args::rest::more) end end)
        fun count_types [] n=n
          | count_types (ty::rest) n=
              (spend focus 1;guard ();walk [[ty]];count_types rest (n+1))
        fun count_nodes [] n=n
          | count_nodes (node::rest) n=
              (spend focus 1;guard ();
               walk [[invoke focus (fn()=>G.type_of graph node)]];
               count_nodes rest (n+1))
        (* These are the admitted fixed equality shell's three new graph
           annotation roots, not a count of arbitrary expanded syntax. *)
        val total=count_types extra (count_nodes nodes prospective)
        val _=guard ()
    in (total,guard) end

  fun generated_equality converted {ordinal,check_type} =
    let val initial = initial_focus converted
        val target = target_focus converted
        val work = work_of initial val graph = #graph (owner_of initial)
        val limits = #limits (owner_of initial)
    in W.with_step work (fn () =>
      let val _ = validate converted
          val (sizes,types,held) = inventory initial
            [node initial,node target]
          val (a,b) = case sizes of [a,b] => (a,b)
            | _ => raise ERR "closed_fact" "internal size portfolio"
          val equality = equation a b
          val _ = reserve_role (ClosedEquation b) initial ordinal equality
            [equality]
          fun guard () = (validate converted;held ())
          (* The future P type-policy portfolio has at most every held
             unique annotation node plus the THREE new equality nodes.
             Inventory includes binder VARIABLE annotations too. Reserve
             this incidence ceiling before the FIRST supplied policy. *)
          val (future_count,extra_guard)=future_type_forest initial guard
            [node initial,node target] 3
          fun all ()=(guard ();extra_guard ())
          val policy = policies initial all types
            [G.type_of graph (node initial)] ordinal future_count check_type
          val theorem = #theorem (endpoints converted)
          val operator = Term.rator (Term.rator (Thm.concl theorem))
          val head = invoke initial
            (fn () => G.constant graph (scope initial) operator)
          val partial = invoke initial (fn () => G.application graph
            (scope initial) (head,node initial))
          val equality_node = invoke initial (fn () => G.application graph
            (scope initial) (partial,node target))
          val result = invoke initial (fn () =>
            P.record_generated_equality_with_policy_scoped_profiles graph
            (scope initial) {node = equality_node,theorem = theorem,
              template_limit = #template_limit (#policy_limits (owner_of
                initial)),
              check_type=policy,profiles= #profiles (owner_of initial)})
          val _ = all ()
      in result end) end

  fun generated_equality_for expected converted request =
    protected (#work expected) (fn () =>
      (ignore (description_for expected (peek_initial converted));
       generated_equality converted request))

  fun closed_fact converted request =
    let val saved=generated_equality converted request
        val initial=peek_initial converted
        val owner=owner_of initial
    in #fact (P.scoped_generated_equality_for (#graph owner) (scope initial)
      (#template_limit (#policy_limits owner)) saved) end
  end
  val closed_generated_equality_with_policy_for =
    ScopedPolicyPublication.generated_equality_for
  (* Actual canonical body equality; no import/reopening changes child IDs.
     All finite Lambda admission and expected owner checks remain actual. *)
  structure CanonicalPolicyTransport =
  struct
    open NativePolicyTransport
  fun lift_lambda_canonical_admitted
      {parent,admission,body,record_ordinal,lift_ordinal,check_type} =
    protected (work_of parent) (fn () =>
    let val _ = active parent
        val owner = owner_of parent
        val graph = #graph owner
        val expected : Q.expected =
          {graph = graph,scope = scope parent,sources = #sources owner,
           work = #work owner}
        val d = Q.describe_with_policy_for expected admission
        val expected_category = case provenance parent of
            OriginalOccurrence => Q.Original
          | OriginalDescendant => Q.Original
          | OriginalPositiveGoal => Q.Original
          | PositiveGoalDescendant => Q.Original
          | UnopenedPositiveGoal => Q.Original
          | UnopenedGoalDescendant => Q.Original
          | UnopenedOriginalOccurrence => Q.Original
          | UnopenedOriginalDescendant => Q.Original
          | ClosedAuxiliaryRoot => Q.Auxiliary
          | ClosedAuxiliaryDescendant => Q.Auxiliary
          | _ => Q.Generated
        (* Private lineage ordinal, not the public Source-index getter.
           -1 agrees with lower Goal DATA and confers no P.Source slot. *)
        val Focus {root_ordinal = held_ordinal,...} = parent
        val _ = if #node d = node parent andalso
            #category d = expected_category andalso
            #occurrence d = held_ordinal then () else
          raise ERR "lambda_admitted" "different parent admission provenance"
        val initial = peek_initial body
        val _ = require_owner parent initial
        val _ = validate body
        val graph = #graph (owner_of parent)
        val Focus {caller,child,...} = parent
        val closure = invoke parent
          (fn () => G.closure_child_binder graph caller child)
        val captured = invoke parent
          (fn () => G.binder_closure_data graph caller closure)
        val _ = if node initial = #body captured andalso
            scope initial = #body_frame captured then () else
          raise ERR "lambda" "different owned body node/frame"
        val admitted_closure = invoke parent (fn () =>
          G.closure_child_binder graph (scope parent) (#child d))
        val admitted_data = invoke parent (fn () =>
          G.binder_closure_data graph (scope parent) admitted_closure)
        val _ = if #node admitted_data = #node captured andalso
            #binder admitted_data = #binder captured andalso
            #body admitted_data = #body captured andalso
            #body_frame admitted_data = #body_frame captured andalso
            #binder_frame admitted_data = #binder_frame captured andalso
            #declaring_scope admitted_data = #declaring_scope captured andalso
            #node_frame admitted_data = #node_frame captured then () else
          raise ERR "lambda_admitted" "different genuine binder path"
        fun guard () =
          (active parent;Q.validate_with_policy_for expected admission;validate
            body)
        fun policy ty = (guard ();check_type ty;guard ())
        val evidence = ScopedPolicyPublication.closed_fact body
          {ordinal = record_ordinal,check_type = policy}
        val _ = guard ()
        val owner = owner_of parent
        val plan = L.prepare_canonical_admitted_with_policy
          {graph = graph,scope = scope parent,
           sources = #sources owner,work = #work owner,ordinal = lift_ordinal,
           admission=admission,body_fact=evidence,
           native_contract= #native_contract owner,
           profiles= #profiles owner,check_type=policy}
        val result = L.execute_canonical_with_policy plan
        fun backing () =
          (guard ();L.validate_canonical_with_policy_for
            {graph = graph,caller = scope parent,scope = scope parent,
             sources = #sources owner,work = #work owner} result)
        val _ = backing ()
        val {source,target,theorem}=L.endpoints_canonical_with_policy_for
          {graph=graph,caller=scope parent,scope=scope parent,
           sources= #sources owner,work= #work owner} result
        val _ = if source = node parent then () else
          raise ERR "lambda" "different lambda source"
        val focus = at_node parent (scope parent) target [backing]
    in checked (parent,focus,theorem,backing) end)

  end
  val lift_lambda_canonical_admitted_with_policy =
    CanonicalPolicyTransport.lift_lambda_canonical_admitted
  (* Adopt only the genuine profiled fixed-law programme result. The receipt
     authenticates both endpoints and proof before any payload is extracted. *)
  fun adopt_profiled_carrier_with_policy focus receipt =
    NativePolicyTransport.protected
      (NativePolicyTransport.work_of focus) (fn()=>
    W.with_step (NativePolicyTransport.work_of focus) (fn()=>
      let open NativePolicyTransport
          fun backing ()=C.validate_profiled_with_policy_for
            (expected focus) receipt
          val _=backing ()
          val {source,target,theorem}=C.endpoints_profiled_with_policy_for
            (expected focus) receipt
          val _=if source=node focus then () else
            raise ERR "adopt_profiled_carrier_with_policy"
              "different actual carrier source"
          val result=at_node focus (scope focus) target [backing]
      in checked(focus,result,theorem,backing) end))
  (* Preserve the actual signed private lineage, including selected auxiliary
     -2 through generated descendants. Expected owner precedes projection. *)
  fun original_lineage_with_policy_for expected focus=
    NativePolicyTransport.protected (#work expected) (fn()=>
      (ignore(NativePolicyTransport.description_for expected focus);
       let val NativePolicyTransport.Focus{root_ordinal,...}=focus
       in root_ordinal end))
  fun start_auxiliary_native_with_policy work
      {law,native_contract,profiles}=
    NativePolicyTransport.protected work (fn()=>W.with_step work (fn()=>
      let val native=SmtReplayNativeContract.for_work work native_contract
          val sources=W.original_sources work
          val graph=S.owning_graph sources val root=S.owning_scope sources
          val policy_limits=W.semantic_policy work
          val expected={graph=graph,scope=root,sources=sources,work=work}
          fun registered ()=
            if Portable.pointer_eq(native_contract,
                SmtLib_GraphSelectedAuxiliary.native_contract_with_policy_for
                  expected law)then ()else
              raise ERR "start_auxiliary_native_with_policy"
                "different actual selected native contract"
          val _=registered()
          val data=SmtLib_GraphSelectedAuxiliary.describe_with_policy_for
            expected law
          val original= #imported data val opened= #opened data
          val current= #node opened
          val child=G.closure_root graph root current
          val _=W.spend_policy work 1
          val result=NativePolicyTransport.Focus
            {owner={graph=graph,root=root,sources=sources,work=work,
              limits= #semantic_limits native,policy_limits=policy_limits,
              epoch=Type.type_epoch(),native_contract=native_contract,
              native_data=native,profiles=profiles},
             traversal=root,caller=root,child=child,node=current,
             original=original,opened=opened,root_ordinal= ~2,
             provenance=ClosedAuxiliaryRoot,goal_unopened=false,
             guards=[registered],validated=ref(~1:IntInf.int)}
          val _=NativePolicyTransport.active result
      in result end))

  (* This is an actual REFL on the genuine selected schema, not an
     identity assertion or a borrowed existing proof. Admit its complete
     realized input/equality/Type portfolio before policy or theorem mint. *)
  fun identity_auxiliary_with_policy_for expected_request focus
      {ordinal,check_type}=
    NativePolicyTransport.protected (#work expected_request) (fn()=>
      (ignore(NativePolicyTransport.description_for expected_request focus);
       W.with_step (#work expected_request) (fn()=>
       let open NativePolicyTransport
           val owner=owner_of focus val graph= #graph owner
           val _=if provenance focus=ClosedAuxiliaryRoot andalso
               original_lineage_with_policy_for expected_request focus= ~2 then ()else
             raise ERR "identity_auxiliary" "not a genuine auxiliary root"
           val limits= #limits owner
           val metadata= #template_limit(#policy_limits owner)
           val(values,types,held)=ScopedPolicyPublication.inventory focus
             [node focus]
           val input=case values of [value]=>value|_=>
             raise ERR "identity_auxiliary" "internal singleton portfolio"
           val equality=equation input input
           fun admit cap (value:footprint)=
             if #raw value<=IntInf.fromInt cap andalso
                 #inc value<=IntInf.fromInt cap then ()else
               raise ERR "identity_auxiliary" "native schema exceeds cap"
           val _=admit (#template_limit limits) input
           val _=admit (#template_limit limits) equality
           val _=admit (#output_limit limits) equality
           val _=if RP.allows metadata (#raw equality)andalso
               RP.allows metadata (#inc equality)then ()else
             raise ERR "identity_auxiliary" "metadata template exceeds cap"
           fun extent(value:footprint)= #raw value+ #inc value+ #ann value
           val amount=extent input+extent equality
           val _=if ordinal>=0 andalso amount>0 andalso
               amount<=IntInf.fromInt(#type_work_limit(#native_data owner))
               then ()else raise ERR "identity_auxiliary"
                 "native Type portfolio exceeds caller cap"
           val token=W.reserve_policy (#work owner)
             {role=W.LocalCarrier,ordinal=ordinal,amount=amount}
           val _=W.consume_policy (#work owner)token amount
           fun guard ()=(active focus;held())
           val _=policies focus guard types
             [G.type_of graph(node focus)]ordinal 0 check_type
           val theorem=invoke focus
             (fn()=>Thm.REFL(G.representative graph(node focus)))
           val _=guard()
       in checked(focus,focus,theorem,guard)end)))
  structure PolicyTransportCore=SmtReplayOwnedLargeProofCore
  (* Actual expected focus precedes Core's held backing. The opaque result
     supplies its own proof/endpoints; no theorem/node pair is adopted. *)
  fun adopt_core_with_policy_for expected_request focus receipt=
    NativePolicyTransport.protected (#work expected_request) (fn()=>
      (ignore(NativePolicyTransport.description_for expected_request focus);
       W.with_step (#work expected_request) (fn()=>
       let val owner=NativePolicyTransport.owner_of focus
           val work= #work owner
           fun backing ()=
             let val contract=
                   PolicyTransportCore.native_contract_with_policy_for
                     work receipt
                 val _=if Portable.pointer_eq
                     (contract,#native_contract owner)then ()else
                   raise ERR "adopt_core_with_policy_for"
                     "different actual Core native contract"
                 val data=
                   PolicyTransportCore.conversion_description_with_policy_for
                     work receipt
             in if Portable.pointer_eq(#graph data,#graph owner)andalso
                 #root data= #root owner andalso
                 #scope data=NativePolicyTransport.scope focus andalso
                 Portable.pointer_eq(#sources data,#sources owner)andalso
                 #source data=NativePolicyTransport.node focus
                 then ()else raise ERR "adopt_core_with_policy_for"
                   "different actual Core source/owner/frame/contract"end
           val _=backing()
           val data=
             PolicyTransportCore.conversion_description_with_policy_for
               work receipt
           val theorem=PolicyTransportCore.theorem_with_policy_for
             work receipt
           val _=backing()
           val target=NativePolicyTransport.at_node focus
             (NativePolicyTransport.scope focus)(#target data)[backing]
       in NativePolicyTransport.checked(focus,target,theorem,backing)end)))

  (* Owner-first actual token projection, used by genuine typed receivers.
     It grants no native operation, new ordinal, or Work credit. *)
  fun native_contract_conversion_with_policy_for expected_request converted=
    NativePolicyTransport.protected (#work expected_request) (fn()=>
      (ignore(NativePolicyTransport.conversion_description_for
         expected_request converted);
       let val NativePolicyTransport.Conversion{initial,...}=converted
       in #native_contract(NativePolicyTransport.owner_of initial)end))
  (* Borrow the exact original/view ports of an ORIGINAL root focus. This
     does not assert an opened view for NONE, nor admit a native operation. *)
  fun root_sources_with_policy_for expected_request focus=
    NativePolicyTransport.protected (#work expected_request)(fn()=>
      (ignore(NativePolicyTransport.description_for expected_request focus);
       let val NativePolicyTransport.Focus
             {owner,traversal,node,original,opened,provenance,
              goal_unopened,...}=focus
           val _=if traversal= #root owner andalso
               (case provenance of OriginalOccurrence=>true
                | OriginalPositiveGoal=>true|UnopenedPositiveGoal=>true
                | UnopenedOriginalOccurrence=>true|_=>false)then ()else
             raise ERR "root_sources_with_policy_for"
               "expected actual original root focus"
           val _=if node= #node opened then ()else
             raise ERR "root_sources_with_policy_for"
               "original root focus changed"
       in {original=original,view=if goal_unopened then NONE else SOME opened}
       end))

end
