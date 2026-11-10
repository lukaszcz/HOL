structure SmtReplayOwnedCompactApplication :>
    SmtReplayOwnedCompactApplication =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure D = SmtReplayOwnedTransport
  structure P = SmtReplayProof
  structure C = SmtReplayCanonGraph
  val _ = SmtReplayOwnedTransport.closed_fact_for
  val _ = SmtReplayCanonGraph.graph_conversion_with_closed
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedCompactApplication"
  type owner = {graph : G.graph,scope : G.scope,sources : S.sources,
                work : W.portfolio}
  datatype plan = Plan of
    {owner : owner,source : D.focus,conversion : C.graph_conversion,
     leaves : (G.node * P.closed_fact) list,epoch : int}
  fun protected work action = action ()
    handle primary => (W.close work;raise primary)
  fun active ({graph,scope,sources,work} : owner) epoch =
    (W.validate work graph scope sources (W.semantic_limits work);
     if Type.type_epoch () = epoch then () else
       raise ERR "active" "type epoch changed")
  fun same (a : owner) (b : owner) =
    Portable.pointer_eq (#graph a,#graph b) andalso #scope a = #scope b
      andalso Portable.pointer_eq (#sources a,#sources b) andalso
      Portable.pointer_eq (#work a,#work b)
  fun prepare work {source,leaves,check_type} = protected work (fn () =>
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources
      val scope = S.owning_scope sources
      val owner = {graph = graph,scope = scope,sources = sources,work = work}
      val epoch = Type.type_epoch ()
      val limit = #template_limit (W.semantic_limits work)
      fun guard () =
        (active owner epoch;ignore (D.description_for owner source))
      val _ = guard ()
      val root = #node (D.description_for owner source)
      fun policy ty = (guard ();check_type ty;guard ())
      (* Each leaf owns a separate existing D action. No enclosing W action
         nests closed_fact's quote/record operation. Its source may be num
         or function typed: the checked equality itself is Boolean. *)
      fun record [] held = List.rev held
        | record ((ordinal,converted)::rest) held =
          let
            val _ = guard ()
            val fact = D.closed_fact_for owner converted
              {ordinal = ordinal,check_type = policy}
            val _ = guard ()
            val eq = P.closed_node fact
            val (partial,_) = case G.view graph eq of G.Application pair => pair
              | _ => raise ERR "prepare" "owned fact is not equality"
            val (_,left) = case G.view graph partial of
                G.Application pair => pair
              | _ => raise ERR "prepare" "owned fact is not equality"
            fun conflict [] = false
              | conflict ((node,_)::more) =
                  (W.spend work 1;node = left orelse conflict more)
            val _ = W.with_step work (fn () =>
              (guard ();if conflict held then
                raise ERR "prepare" "duplicate local rewrite source"
               else W.spend work 1))
          in record rest ((left,fact)::held) end
      val recorded = record leaves []
      val used = ref ([] : G.node list)
      val conversion = W.with_step work (fn () =>
        let
          fun observe () = (guard ();W.spend work 1;guard ())
          fun propose node =
            let fun seek [] = NONE
                  | seek ((left,fact)::rest) =
                    (observe ();if node = left then
                      (observe ();used := node :: !used;SOME fact)
                     else seek rest)
            in guard ();seek recorded end
          val converted = C.graph_conversion_with_closed graph scope
            {template_limit = limit,revisit = false,
             propose = propose,observe = observe} root
          (* Overlapping leaves whose parent no longer matches after its
             children changed are not silently discarded. This finite
             independent-leaf portfolio declines that ambiguous ordering. *)
          fun was_used node [] = false
            | was_used node (current::rest) =
                (observe ();node = current orelse was_used node rest)
          val _ = List.app (fn (node,_) =>
            if was_used node (!used) then () else
              raise ERR "prepare" "local rewrite was not reached") recorded
          val _ = guard ()
        in converted end)
    in Plan {owner = owner,source = source,conversion = conversion,
      leaves = recorded,epoch = epoch} end)
  fun graph_conversion_for expected
      (Plan {owner,source,conversion,leaves,epoch}) =
    protected (#work expected) (fn () =>
      (active expected (Type.type_epoch ());
       if same expected owner then () else
         raise ERR "graph_conversion_for" "different original invocation";
       active owner epoch;ignore (D.description_for owner source);
       List.app (fn (_,fact) => P.validate_closed_fact (#graph owner)
         (#scope owner) (#template_limit (W.semantic_limits (#work owner)))
         fact) leaves;
       active owner epoch;conversion))
end
