(* Reuse the genuine alpha-leaf and named congruence proof programmes. *)
structure SmtLib_GraphCheckedOpening :> SmtLib_GraphCheckedOpening =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure Scope = SmtReplayOwnedScopeReceipt
  structure NC = SmtReplayNativeContract
  structure P = SmtReplayProof
  structure C = SmtReplayCanonGraph
  structure Core = SmtReplayOwnedLargeProofCore
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphCheckedOpening"
  datatype task = Visit of G.node * G.node
    | Join of {original:G.node,opened:G.node,
               left:G.node * G.node,right:G.node * G.node}
  fun compare_pair ((a,b),(c,d)) =
    case Int.compare (a,c) of EQUAL => Int.compare (b,d) | order => order

  fun bridge_internal finish work
      {frame,original,opened,native_contract,profiles,ordinal,check_type} =
    ((let
      val owner = Scope.description_with_policy_for work frame
      val graph = #graph owner val scope = #scope owner
      val root = #root owner val sources = #sources owner
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val _ = NC.validate_for work native_contract
      fun guard () =
        let
          val current = Scope.description_with_policy_for work frame
          val _ = NC.validate_for work native_contract
        in if Portable.pointer_eq (#graph current,graph) andalso
            #root current=root andalso #scope current=scope andalso
            Portable.pointer_eq (#sources current,sources) andalso
            Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
          then () else raise ERR "bridge" "original owner or epoch changed"
        end
      fun registered (left,right) =
        let
          val _ = guard ()
          val source = G.cached_opened_view graph scope left
          val _ = G.validate_opened_view graph scope left source
          val _ = if #node source=right then () else
            raise ERR "bridge" "different registered opening endpoint"
          val _ = ignore (G.closure_root graph scope left)
          val _ = ignore (G.closure_root graph scope right)
        in source end
      fun action compute = W.with_step work (fn () =>
        let fun observe () = (guard ();W.spend_policy work 1)
            val _ = guard () val result = compute observe
            val _ = guard ()
        in result end)
      fun keep recipe =
        (C.validate_conversion_for work recipe;recipe)
      fun cut fact =
        let
          val saved = P.closed_fact_cut_with_policy_for work
            {frame=frame,fact=fact}
        in action (fn observe => keep
          (C.graph_closed_fact_cut_with_policy work
            {cut=saved,observe=observe})) end
      fun close recipe =
        let
          val _ = guard ()
          val actual_ordinal = action (fn observe =>
            (observe ();W.unused_policy_ordinal work
              {role=W.FinalFreeze,minimum=ordinal}))
          val result = Core.execute_with_policy work
            (Core.prepare_in_scope_with_policy work
              {frame=frame,conversion=recipe,ordinal=actual_ordinal,
               native_contract=native_contract,profiles=profiles,
               check_type=check_type})
          val actual = Core.conversion_description_with_policy_for work result
          val contract = Core.native_contract_with_policy_for work result
          val _ = if Portable.pointer_eq (contract,native_contract) andalso
              Portable.pointer_eq (#graph actual,graph) andalso
              Portable.pointer_eq (#sources actual,sources) andalso
              #root actual=root andalso #scope actual=scope andalso
              #source actual=C.graph_source recipe andalso
              #target actual=C.graph_result recipe then () else
            raise ERR "bridge" "different actual compact realization"
          val _ = guard ()
        in result end
      fun closed_cut recipe =
        let val result = close recipe
            val fact = P.completed_policy_source_realization_closed_fact_for
              work
              (Core.realization_with_policy_for work result)
        in cut fact end
      fun binder left right source =
        let
          val alpha = action (fn observe =>
            G.carrier_alpha_for_with_policy graph scope
              {original=left,source=source,step=observe})
          val capture = action (fn observe =>
            (observe ();G.prepare_scoped_profiled_metric graph scope
              {node=right,profiles=profiles}))
          val _ = ignore
            (G.alpha_metric_data_with_policy graph scope alpha capture)
          val plan = P.prepare_alpha_leaf_with_policy work
            {frame=frame,alpha=alpha,capture=capture,
             native_contract=native_contract,check_type=check_type}
          val fact = P.execute_alpha_leaf_with_policy work plan
          val _ = guard ()
        in cut fact end
      val memo = ref (Redblackmap.mkDict compare_pair)
      fun key (left,right) = (G.node_id left,G.node_id right)
      fun save pair recipe = action (fn observe =>
        (observe ();ignore (registered pair);keep recipe;
         if C.graph_source recipe= #1 pair andalso
             C.graph_result recipe= #2 pair then
           memo := Redblackmap.insert (!memo,key pair,recipe)
         else raise ERR "bridge" "checked child endpoints differ"))
      fun lookup pair = action (fn observe =>
        (observe ();ignore (registered pair);
         case Redblackmap.peek (!memo,key pair) of
           NONE => NONE | SOME recipe => SOME (keep recipe)))
      fun saved pair = case lookup pair of SOME recipe => recipe
        | NONE => raise ERR "bridge" "missing completed child proof"
      fun run [] = saved (original,opened)
        | run (Visit (pair as (left,right))::rest) =
            (case lookup pair of SOME _ => run rest
             | NONE =>
               let val source = action (fn observe =>
                     (observe ();registered pair))
               in if left=right then
                   let val recipe = action (fn observe => keep
                         (C.graph_identity graph scope
                           {observe=observe} left))
                   in save pair recipe;run rest end
                 else case (G.view graph left,G.view graph right) of
                     (G.Application (f,x),G.Application (g,y)) =>
                       run (Visit (f,g)::Visit (x,y)::
                         Join {original=left,opened=right,
                               left=(f,g),right=(x,y)}::rest)
                   | (G.OpaqueRetained,G.AdmittedBinder _) =>
                       (save pair (binder left right source);run rest)
                   | _ => raise ERR "bridge"
                       "registered opening has unsupported changed shape"
               end)
        | run (Join {original=left,opened=right,
                     left=operator,right=operand}::rest) =
            let
              val a = saved operator val b = saved operand
              val recipe = action (fn observe => keep
                (C.graph_application graph scope
                  {source=left,left=a,right=b,observe=observe}))
              val _ = if C.graph_result recipe=right then () else
                raise ERR "bridge" "congruence differs from registered view"
              val recipe = closed_cut recipe
              val _ = save (left,right) recipe
            in run rest end
      val recipe = run [Visit (original,opened)]
      val result = close recipe
      val conversion = Core.conversion_with_policy_for work result
      val _ = P.validate_conversion_for work conversion
      val _ = if P.conversion_source conversion=original andalso
          P.conversion_target conversion=opened then () else
        raise ERR "bridge" "final checked endpoints differ"
      val _ = guard ()
    in finish result conversion end)
     handle primary => (W.close work;raise primary))

  fun bridge_with_policy work input =
    bridge_internal (fn _ => fn conversion => conversion) work input

  fun bridge_generated_with_policy work
      (input as {profiles,frame,native_contract,...}) =
    bridge_internal (fn result => fn conversion =>
      let val generated = W.with_step work (fn () =>
            (ignore (Scope.description_with_policy_for work frame);
             NC.validate_for work native_contract;W.spend_policy work 1;
             P.policy_source_realization_generated_equality_for work
               (Core.realization_with_policy_for work result)
               {profiles=profiles}))
      in {conversion=conversion,generated=generated} end)
      work input
end
