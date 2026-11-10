(* SAME invocation, manual nonoverlapping local leaves, compact ancestors.
   Nominal term/type quotation only; private map/symbol/kernel costs
   unclosed. *)
structure SmtReplayOwnedRawCompactApplication :>
    SmtReplayOwnedRawCompactApplication =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure D = SmtReplayOwnedTransport
  structure P = SmtReplayProof
  structure C = SmtReplayCanonGraph
  val _ = SmtReplayGraph.discovered_alpha
  val _ = SmtReplayProof.record_typed_conversion
  val _ = SmtReplayCanonGraph.graph_conversion_with_conversions
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedRawCompactApplication"
  type owner = {graph : G.graph,scope : G.scope,sources : S.sources,
                work : W.portfolio}
  datatype plan = Plan of {owner : owner,focus : D.focus,index : int,
    conversion : C.graph_conversion,leaves : P.closed_conversion list,
    receipts : G.discovered_alpha list,held : D.focus list,
    epoch : int,symbols : int}
  fun protected work action = action ()
    handle primary => (W.close work;raise primary)
  fun same (a : owner) (b : owner) =
    Portable.pointer_eq (#graph a,#graph b) andalso #scope a = #scope b andalso
    Portable.pointer_eq (#sources a,#sources b) andalso
    Portable.pointer_eq (#work a,#work b)
  fun active ({graph,scope,sources,work} : owner) epoch symbols =
    (W.validate work graph scope sources (W.semantic_limits work);
     if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
       then () else raise ERR "active" "kernel epoch changed")

  fun prepare work {source,leaves,check_type} = protected work (fn () =>
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources val scope = S.owning_scope sources
      val owner = {graph = graph,scope = scope,sources = sources,work = work}
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val limits = W.semantic_limits work val cap = #template_limit limits
      val backing = ref (fn () => ())
      fun guard () = (active owner epoch symbols;
        ignore (D.description_for owner source);(!backing) ())
      val _ = guard ()
      val description = D.description_for owner source
      val root_pair = D.root_sources source
      val (raw,index,positive) = case #provenance description of
          D.OriginalOccurrence =>
            let val ordinal = D.original_occurrence source
                val n = List.length (S.assumption_nodes sources)
                val index = if ordinal = 0 then n else ordinal-1
                val original =
                  List.nth (S.reconciliation_sources sources,ordinal)
                val _ = if G.node_id (#node original) =
                    G.node_id (#node (#original root_pair)) andalso
                    Portable.pointer_eq (#bridge original,
                      #bridge (#original root_pair)) then () else
                  raise ERR "prepare" "original Source row differs"
            in (#node original,index,false) end
        | D.OriginalPositiveGoal =>
            let val original = S.goal_source sources
                val _ = if #node original = #node (#original root_pair) andalso
                    Portable.pointer_eq (#bridge original,
                      #bridge (#original root_pair)) then () else
                  raise ERR "prepare" "positive Goal origin differs"
            in (#node original,List.length (S.assumption_nodes sources),true)
            end
        | _ => raise ERR "prepare" "not an opened original root occurrence"
      fun policy ty = (guard ();check_type ty;guard ())
      fun observe () = (guard ();W.spend work 1;guard ())
      (* Every paired incoming focus is held even when raw IDs share a DAG.
         Applications are actual canonical RAW constructors, not user-term
         body incidence. No descent through an opaque raw binder is issued. *)
      val paired = ref ([] : (G.node * D.focus) list)
      val held = ref ([] : D.focus list)
      val seen = ref (Redblackmap.mkDict Int.compare)
      val _ = W.with_step work (fn () =>
        let
          fun visit raw focus =
            let val _ = observe ()
                val data = D.description_for owner focus
                val view = G.cached_opened_view graph scope raw
                val _ = if #node view = #node data then () else
                  raise ERR "prepare" "raw/rich child correspondence differs"
                val _ = held := focus :: !held
            in case Redblackmap.peek (!seen,G.node_id raw) of SOME () => ()
              | NONE =>
                (seen := Redblackmap.insert (!seen,G.node_id raw,());
                 paired := (raw,focus) :: !paired;
                 case G.view graph raw of G.Application (f,x) =>
                     let val (left,right) = D.application_children focus
                     in visit f left;visit x right end
                   | _ => ())
            end
        in visit raw source end)
      fun plus a b = if a > cap orelse b > cap-a then
          raise ERR "prepare" "local proof portfolio exceeds original template"
        else a+b
      fun type_size ty =
        let val _ = observe ()
        in if Type.is_vartype ty then 1 else
          let val {Args,...} = Type.dest_thy_type ty
              fun args [] total = total
                | args (next::rest) total =
                    (observe ();args rest (plus total (type_size next)))
          in args Args 1 end end
      type profile = {raw : int,inc : int,ann : int}
      val profiles = ref (Redblackmap.mkDict Int.compare)
      val types = ref ([] : Type.hol_type list)
      fun profile child : profile =
        let val _ = observe ()
            val node = G.closure_child_node graph scope child
        in case Redblackmap.peek (!profiles,G.node_id node) of SOME data => data
          | NONE =>
            let val ty = G.type_of graph node val annotation = type_size ty
                val _ = types := ty :: !types
                val data : profile = case G.view graph node of
                    G.Application _ =>
                      let val (f,x) = G.closure_application_children
                            graph scope child
                          val a = profile f val b = profile x
                      in {raw = plus 1 (plus (#raw a) (#raw b)),
                        inc = plus 1 (plus (#inc a) (#inc b)),
                        ann = plus annotation (plus (#ann a) (#ann b))} end
                  | G.AdmittedBinder _ =>
                      let val binder = G.closure_child_binder graph scope child
                          val data = G.binder_closure_data graph scope binder
                          val bound_type = G.type_of graph (#binder data)
                          val bound_size = type_size bound_type
                          val _ = types := bound_type :: !types
                          val b = profile (G.binder_closure_body
                            graph scope binder)
                      in {raw = plus 1 (#raw b),inc = plus 2 (#inc b),
                        ann = plus annotation (plus bound_size (#ann b))} end
                  | G.OpaqueRetained => raise ERR "prepare"
                      "missing complete local annotation recipe"
                  | _ => {raw = 1,inc = 1,ann = annotation}
                val _ = profiles := Redblackmap.insert
                  (!profiles,G.node_id node,data)
            in data end
        end
      fun equality (a : profile) (b : profile) ty_size : profile =
        {raw = plus 3 (plus (#raw a) (#raw b)),
         inc = plus 3 (plus (#inc a) (#inc b)),
         ann = plus 6 (plus (plus ty_size (plus ty_size ty_size))
           (plus (#ann a) (#ann b)))}
      fun remaining () = W.work_limit work - #charged (W.audit work)
      (* Guard the complete original rich discovery lifetime without imposing
         a new unfolded semantic limit on the enclosing application DAG. *)
      val root_receipt = W.with_step work (fn () =>
        let val receipt = G.discovered_alpha graph scope (remaining ()) raw
            val data = G.discovered_alpha_data graph scope receipt
            val _ = W.spend work (#visits data)
        in receipt end)
      val receipts = ref [root_receipt]
      val _ = backing := (fn () =>
        (List.app (fn focus => ignore (D.description_for owner focus)) (!held);
         List.app (G.validate_discovered_alpha graph scope) (!receipts)))
      val typed = ref ([] : P.closed_conversion list)
      val used_sources = ref ([] : G.node list)
      fun record [] = ()
        | record ((ordinal,converted)::rest) =
          let
            val _ = guard ()
            val endpoints = D.conversion_description_for owner converted
            val local_source = #source endpoints val target = #target endpoints
            (* D owns its pre-existing quote/record action; no nested action. *)
            val fact = D.closed_fact_for owner converted
              {ordinal = ordinal,check_type = policy}
            val _ = guard ()
            val aliases = W.with_step work (fn () =>
              let fun pick [] result = result
                    | pick ((raw,focus)::more) result =
                      (observe ();if #node (D.description_for owner focus) =
                          local_source then pick more (raw::result)
                       else pick more result)
                  val result = pick (!paired) []
                  val _ = if null result then
                    raise ERR "prepare" "local rewrite was not reached"
                    else ()
              in result end)
            fun alias raw = W.with_step work (fn () =>
              let
                val _ = observe ()
                val _ = if List.exists (fn node =>
                    (observe ();node = raw)) (!used_sources) then
                    raise ERR "prepare" "duplicate or overlapping local source"
                  else ()
                val receipt = G.discovered_alpha graph scope (remaining ()) raw
                val data = G.discovered_alpha_data graph scope receipt
                val _ = W.spend work (#visits data)
                val source_view = #source data
                val _ = if #node source_view = local_source then () else
                  raise ERR "prepare" "local Alpha source differs"
                val target_child = G.closure_root graph scope target
                val left = profile (#annotation data)
                val right = profile target_child
                val _ = if #raw right <= #output_limit limits andalso
                    #inc right <= #output_limit limits then () else
                  raise ERR "prepare" "local target exceeds original output"
                val ty_size = type_size (G.type_of graph local_source)
                (* Exact equality grammar: Alpha bridge, held local theorem,
                   TRANS result and identity REFL. TWO copies of the source
                   profile are retained where the actual operand has them. *)
                val operand_quotes = [equality left left ty_size,
                  equality left right ty_size,equality left right ty_size,
                  equality right right ty_size]
                (* Work is the ORIGINAL remaining ledger, not the semantic
                   template ceiling or a fresh sum-of-portfolios cutoff. *)
                val _ = List.app (fn (item : profile) =>
                  (W.spend work (#inc item);W.spend work (#ann item)))
                  operand_quotes
                val identity_plan = G.plan_identity_closure_view graph scope cap
                  {target = target_child,retain = [#annotation data]}
                val _ = P.validate_closed_fact graph scope cap fact
                val _ = List.app policy (!types)
                val _ = guard ()
                val _ = G.validate_discovered_alpha graph scope receipt
                val target_view = G.execute_identity_closure_view identity_plan
                val _ = guard ()
                val theorem = Thm.TRANS (#bridge source_view)
                  (P.closed_original fact)
                val _ = guard ()
                val conversion = P.record_typed_conversion graph scope
                  {source = raw,source_view = source_view,target = target,
                   target_view = target_view,theorem = theorem,
                   template_limit = cap,check_type = policy}
                val _ = guard ()
                val _ = G.validate_discovered_alpha graph scope receipt
                val _ = receipts := receipt :: !receipts
                val _ = typed := conversion :: !typed
                val _ = used_sources := raw :: !used_sources
              in () end)
            val _ = List.app alias aliases
          in record rest end
      val _ = record leaves
      val conversion = W.with_step work (fn () =>
        let
          val root = if positive then
              let val denied = S.denied_goal_node sources
                  val (head,operand) = case G.view graph denied of
                      G.Application pair => pair
                    | _ => raise ERR "prepare" "denial is not fixed negation"
                  val _ = if operand = raw andalso
                      Term.same_const (G.representative graph head)
                        boolSyntax.negation then () else
                    raise ERR "prepare" "original denied Goal head differs"
              in denied end else raw
          val used = ref ([] : G.node list)
          fun propose node =
            let fun seek [] = NONE
                  | seek (plan::rest) =
                    (observe ();if P.conversion_source plan = node then
                       (used := node :: !used;SOME plan) else seek rest)
            in seek (!typed) end
          val result = C.graph_conversion_with_conversions graph scope
            {template_limit = cap,revisit = false,propose = propose,
             observe = observe} root
          val _ = List.app (fn plan =>
            if List.exists (fn node => (observe ();
                node = P.conversion_source plan)) (!used) then () else
              raise ERR "prepare" "overlapping local witness not used") (!typed)
          val _ = guard ()
        in result end)
    in Plan {owner = owner,focus = source,index = index,conversion = conversion,
      leaves = !typed,receipts = !receipts,held = !held,
      epoch = epoch,symbols = symbols} end)

  fun checked expected (plan as Plan
      {owner,focus,index,conversion,leaves,receipts,held,epoch,symbols}) =
    protected (#work expected) (fn () =>
      (active expected (Type.type_epoch ()) (Term.term_epoch ());
       if same expected owner then () else
         raise ERR "checked" "different original invocation";
       active owner epoch symbols;
       ignore (D.description_for owner focus);
       List.app (fn item => ignore (D.description_for owner item)) held;
       List.app (G.validate_discovered_alpha (#graph owner) (#scope owner))
         receipts;
       List.app (P.validate_conversion (#graph owner) (#scope owner)
         (#template_limit (W.semantic_limits (#work owner)))) leaves;
       active owner epoch symbols;plan))
  fun graph_conversion_for expected plan =
    let val Plan {conversion,...} = checked expected plan in conversion end
  fun source_index_for expected plan =
    let val Plan {index,...} = checked expected plan in index end
end
