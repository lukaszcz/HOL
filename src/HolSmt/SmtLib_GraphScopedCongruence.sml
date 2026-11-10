(* Structural compatibility is DATA; only the existing executor proves it. *)
structure SmtLib_GraphScopedCongruence :> SmtLib_GraphScopedCongruence =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure Scope = SmtReplayOwnedScopeReceipt
  structure NC = SmtReplayNativeContract
  structure P = SmtReplayProof
  structure C = SmtReplayCanonGraph
  structure Core = SmtReplayOwnedLargeProofCore
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphScopedCongruence"
  type pair = G.node * G.node
  datatype row = Identity | Application of pair * pair
  type item =
    {pair:pair,left:G.closure_child,right:G.closure_child,row:row}
  datatype plan = Plan of
    {work:W.portfolio,frame:Scope.receipt,native_contract:NC.contract,
     profiles:G.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit,epoch:int,symbols:int,
     source:G.node,target:G.node,items:item list}
  datatype preparation = DifferentShape | Prepared of plan
  datatype task = Visit of pair | Join of item
  fun compare_pair pay ((a,b),(c,d)) =
    (pay ();case Int.compare (a,c) of
       EQUAL => (pay ();Int.compare (b,d)) | order => order)
  fun pair_key (left,right) = (G.node_id left,G.node_id right)

  fun prepare_with_policy work
      {frame,source,target,native_contract,profiles,ordinal,check_type} =
    ((let
      val owner = Scope.description_with_policy_for work frame
      val graph = #graph owner val scope = #scope owner
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val _ = NC.validate_for work native_contract
      fun guard () =
        (ignore (Scope.description_with_policy_for work frame);
         NC.validate_for work native_contract;
         if epoch=Type.type_epoch () andalso symbols=Term.term_epoch ()
         then () else raise ERR "prepare" "declaration lifetime changed")
      val result = W.with_step work (fn () =>
        let
          fun tick () = (guard ();W.spend_policy work 1)
          val seen = ref (Redblackset.empty (compare_pair tick))
          val ordered = ref ([]:item list)
          fun add (item:item) =
            (tick ();seen := Redblackset.add (!seen,pair_key (#pair item));
             tick ();
             ordered := item:: !ordered)
          fun scan [] = (tick ();true)
            | scan (Join item::rest) = (add item;scan rest)
            | scan (Visit (pair as (left,right))::rest) =
              let
                val _ = tick ()
                val a = G.closure_root graph scope left
                val b = G.closure_root graph scope right
                val _ = tick ()
              in if Redblackset.member (!seen,pair_key pair) then scan rest
                else if left=right then
                  (add {pair=pair,left=a,right=b,row=Identity};scan rest)
                else if G.type_id graph left<>G.type_id graph right then false
                else case (G.view graph left,G.view graph right) of
                    (G.Application (f,x),G.Application (g,y)) =>
                      if G.node_scope graph right<>scope then false else
                      (tick ();tick ();tick ();
                       scan (Visit (f,g)::Visit (x,y)::
                        Join {pair=pair,left=a,right=b,
                          row=Application ((f,g),(x,y))}::rest))
                  | _ => false
              end
          val _ = tick ()
          val compatible = scan [Visit (source,target)]
          fun reverse [] result = (tick ();result)
            | reverse (item::rest) result =
                (tick ();tick ();reverse rest (item::result))
          val _ = guard ()
        in if compatible then SOME (reverse (!ordered) []) else NONE end)
    in case result of NONE => DifferentShape
      | SOME items => Prepared (Plan
          {work=work,frame=frame,native_contract=native_contract,
           profiles=profiles,ordinal=ordinal,check_type=check_type,
           epoch=epoch,symbols=symbols,source=source,target=target,
           items=items})
    end) handle primary => (W.close work;raise primary))

  fun execute_with_policy expected
      (Plan {work,frame,native_contract,profiles,ordinal,check_type,
             epoch,symbols,source,target,items}) =
    ((let
      val _ = if Portable.pointer_eq (expected,work) then () else
        raise ERR "execute" "different expected Work"
      val owner = Scope.description_with_policy_for work frame
      val graph = #graph owner val scope = #scope owner
      fun guard () =
        (ignore (Scope.description_with_policy_for work frame);
         NC.validate_for work native_contract;
         if epoch=Type.type_epoch () andalso symbols=Term.term_epoch ()
         then () else raise ERR "execute" "declaration lifetime changed")
      fun action compute = W.with_step work (fn () =>
        let fun observe () = (guard ();W.spend_policy work 1)
            val _ = guard () val result = compute observe
            val _ = guard ()
        in result end)
      fun endpoints ({pair=(left,right),left=a,right=b,...}:item) =
        (guard ();
         if G.closure_child_node graph scope a=left andalso
             G.closure_child_node graph scope b=right then () else
           raise ERR "execute" "different retained closure endpoints")
      fun close recipe =
        let
          val actual = action (fn observe =>
            (observe ();C.validate_conversion_for work recipe;
             W.unused_policy_ordinal work
               {role=W.FinalFreeze,minimum=ordinal}))
          val result = Core.execute_with_policy work
            (Core.prepare_in_scope_with_policy work
              {frame=frame,conversion=recipe,ordinal=actual,
               native_contract=native_contract,profiles=profiles,
               check_type=check_type})
          val description = Core.conversion_description_with_policy_for work
            result
          val contract = Core.native_contract_with_policy_for work result
          val _ = if Portable.pointer_eq (contract,native_contract) andalso
              Portable.pointer_eq (#graph description,graph) andalso
              Portable.pointer_eq (#sources description,#sources owner)
              andalso #root description= #root owner andalso
              #scope description=scope andalso
              #source description=C.graph_source recipe andalso
              #target description=C.graph_result recipe then () else
            raise ERR "execute" "different actual compact realization"
        in P.completed_policy_source_realization_closed_fact_for work
          (Core.realization_with_policy_for work result) end
      fun cut fact =
        let val saved = P.closed_fact_cut_with_policy_for work
              {frame=frame,fact=fact}
        in action (fn observe =>
          C.graph_closed_fact_cut_with_policy work
            {cut=saved,observe=observe}) end
      val memo = ref (Redblackmap.mkDict
        (compare_pair (fn () => (guard ();W.spend_policy work 1))) :
        (int * int,C.graph_conversion * P.closed_fact option) Redblackmap.dict)
      fun saved pair = action (fn observe =>
        (observe ();
         ignore (G.closure_root graph scope (#1 pair));
         ignore (G.closure_root graph scope (#2 pair));
         case Redblackmap.peek (!memo,pair_key pair) of
           NONE => raise ERR "execute" "missing completed child proof"
         | SOME (recipe,fact) =>
             (C.validate_conversion_for work recipe;(recipe,fact))))
      fun build (item as {pair=(left,right),row,...}:item) =
        let
          val _ = action (fn observe => (observe ();endpoints item))
          val (recipe,fact) = case row of Identity =>
              (action (fn observe => C.graph_identity graph scope
                {observe=observe} left),NONE)
            | Application (operator,operand) =>
                let val (a,_) = saved operator val (b,_) = saved operand
                    val recipe = action (fn observe =>
                      C.graph_application graph scope
                        {source=left,left=a,right=b,observe=observe})
                    val _ = if C.graph_result recipe=right then () else
                      raise ERR "execute" "different actual target application"
                    val fact = close recipe
                in (cut fact,SOME fact) end
          val _ = action (fn observe =>
            (observe ();endpoints item;C.validate_conversion_for work recipe;
             memo := Redblackmap.insert (!memo,pair_key (left,right),
               (recipe,fact))))
        in () end
      val _ = List.app build items
      val (recipe,finished) = saved (source,target)
      val fact = case finished of SOME result => result | NONE => close recipe
      val _ = P.validate_closed_fact_in_scope_with_policy_for work
        {frame=frame,fact=fact}
      val _ = guard ()
    in fact end) handle primary => (W.close expected;raise primary))
end
