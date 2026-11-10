structure SmtReplayOwnedAlpha :> SmtReplayOwnedAlpha =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure F = SmtReplayFocusAdmission
  val _ = SmtReplayFocusAdmission.describe_for
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedAlpha"
  type footprint =
    {raw : IntInf.int,inclusive : IntInf.int,
     annotations : IntInf.int,type_bytes : IntInf.int}

  datatype comparison_role = OutputPair | AdmittedSource of F.focus
  fun compare_inside role work {caller,traversal,left,right} =
    let
      val _ = W.spend work 0
      val sources = W.original_sources work
      val graph = S.owning_graph sources
      val owner = S.owning_scope sources
      val limits = W.semantic_limits work
      val epoch = Type.type_epoch ()
      fun tick () = W.spend work 1
      fun source_guard () = case role of OutputPair => ()
        | AdmittedSource admission =>
          let val _ = tick ()
              val data = F.describe_for
                {graph = graph,scope = traversal,sources = sources,work = work}
                admission
              val _ = tick ()
              val current = G.closure_child_node graph caller left
          in if #node data = current then () else
            raise ERR "same_admitted_inside" "different exact source receipt"
          end
      fun source_cap () = case role of OutputPair => #output_limit limits
        | AdmittedSource admission =>
          let val _ = tick ()
              val data = F.describe_for
                {graph = graph,scope = traversal,sources = sources,work = work}
                admission
          in #source_limit data end
      fun owner_guard () =
        (W.validate work graph owner sources limits;
         G.validate_scope graph caller;G.validate_scope graph traversal;
         if G.scope_visible graph caller owner andalso
             G.scope_visible graph traversal caller andalso
             Type.type_epoch () = epoch then () else
           raise ERR "same_inside" "owner, traversal or epoch differs";
         source_guard ())
      fun root_guard child =
        let val _ = tick ()
            val node = G.closure_child_node graph caller child
            val _ = tick () val frame = G.node_scope graph node
            val _ = tick ()
        in if G.scope_visible graph traversal frame then () else
          raise ERR "same_inside" "root outside active traversal frame" end
      val _ = owner_guard ()
      val _ = root_guard left val _ = root_guard right
      val left_cap = source_cap ()
      val right_cap = #output_limit limits
      val node_cap = IntInf.fromInt (Int.max (left_cap,right_cap))
      val nominal_cap = IntInf.fromInt (W.work_limit work)
      fun plus cap a b =
        if a > cap orelse b > cap-a then cap+1 else a+b
      val _ = tick () val memo = ref ([] : (G.node * footprint) list)
      val _ = tick () val held = ref ([] : G.closure_child list)
      val profiles = ref ([] : G.opaque_profile list)
      val _ = tick ()
      val type_memo = ref ([] :
        (Type.hol_type * (IntInf.int * IntInf.int)) list)
      fun cached equal key pending =
        (tick ();case pending of [] => NONE | (old,value)::rest =>
          (tick ();if equal (key,old) then (tick ();SOME value)
           else cached equal key rest))
      fun text_bytes text =
        let val _ = tick () val size = String.size text
            fun loop i =
              (tick ();if i = size then () else
                (tick ();ignore (String.sub (text,i));loop (i+1)))
            val _ = loop 0
        in IntInf.fromInt size end
      fun type_size ty =
        case cached Portable.pointer_eq ty (!type_memo) of
          SOME size => size
        | NONE =>
          let
            val cap = IntInf.fromInt (#template_limit limits)
            fun visit pending count bytes =
              (tick ();case pending of [] => (tick ();(count,bytes))
               | terms::more =>
                 (tick ();case terms of [] => visit more count bytes
                  | current::rest =>
                    let val next = plus cap count 1 val _ = tick ()
                        val _ = if next <= cap then () else
                          raise ERR "same_inside" "type exceeds original cap"
                        val _ = tick ()
                    in if Type.is_vartype current then
                        let val _ = tick ()
                            val n = text_bytes (Type.dest_vartype current)
                            val _ = tick ()
                        in visit (rest::more) next
                             (plus nominal_cap bytes n) end
                       else
                        let val _ = tick ()
                            val {Thy,Tyop,Args} = Type.dest_thy_typeid current
                            val _ = tick () val name = KernelSig.name_of Tyop
                            val n = plus nominal_cap (text_bytes Thy)
                              (text_bytes name)
                            val _ = tick () val _ = tick ()
                        in visit (Args::rest::more) next
                             (plus nominal_cap bytes n) end
                    end))
            val _ = tick () val _ = tick ()
            val size = visit [[ty]] 0 0
            val _ = tick () val _ = tick () val _ = tick ()
            val _ = type_memo := (ty,size) :: !type_memo
          in size end
      fun admitted cap node metric =
        (tick ();case G.unfolded_nodes graph metric cap
            node of
          SOME n => if n > 0 andalso n <= cap
            then IntInf.fromInt n else
              raise ERR "same_inside"
                (case role of OutputPair => "syntax exceeds original output cap"
                   | AdmittedSource _ => "syntax exceeds original role cap")
        | NONE => raise ERR "same_inside" "unknown syntax metric")
      fun annotation node =
        let val _ = tick () val ty = G.type_of graph node
        in type_size ty end
      fun visit cap child =
        let
          val _ = tick () val node = G.closure_child_node graph caller child
          (* Each incoming handle is checked before a memo hit. Its exact
             parent path and rehome backing are retained for the final check. *)
          val _ = tick () val _ = tick () val _ = held := child :: !held
          val raw = admitted cap node G.RawNodes
          val inclusive = admitted cap node G.BinderInclusiveNodes
        in case cached (op =) node (!memo) of SOME value => value
         | NONE =>
           let
             val (ty,bytes) = annotation node
             val _ = tick ()
             val value : footprint = case G.view graph node of
                 G.Application _ =>
                   let val _ = tick ()
                       val (l,r) = G.closure_application_children graph caller
                         child
                       val a = visit cap l val b = visit cap r val _ = tick ()
                   in {raw = plus node_cap 1
                         (plus node_cap (#raw a) (#raw b)),
                       inclusive = plus node_cap 1
                         (plus node_cap (#inclusive a) (#inclusive b)),
                       annotations = plus nominal_cap ty
                         (plus nominal_cap (#annotations a) (#annotations b)),
                       type_bytes = plus nominal_cap bytes
                         (plus nominal_cap (#type_bytes a) (#type_bytes b))}
                   end
               | G.AdmittedBinder _ =>
                   let val _ = tick ()
                       val closure = G.closure_child_binder graph caller child
                       val _ = tick ()
                       val data = G.binder_closure_data graph caller closure
                       val _ = admitted cap (#binder data) G.RawNodes
                       val _ = admitted cap (#binder data) G.BinderInclusiveNodes
                       val _ = tick ()
                       val (variable_ty,variable_bytes) =
                         annotation (#binder data)
                       val _ = tick ()
                       val body = visit cap (G.binder_closure_body graph caller
                         closure)
                       val _ = tick ()
                   in {raw = plus node_cap 1 (#raw body),
                       inclusive = plus node_cap 2 (#inclusive body),
                       annotations = plus nominal_cap ty
                         (plus nominal_cap variable_ty (#annotations body)),
                       type_bytes = plus nominal_cap bytes
                         (plus nominal_cap variable_bytes (#type_bytes body))}
                   end
               | G.OpaqueRetained =>
                   let val _ = tick ()
                       val profile = case G.opaque_profile_for graph traversal
                           node of SOME held => held | NONE =>
                         raise ERR "same_inside"
                           "opaque syntax has no complete annotation inventory"
                       val _ = tick ()
                       val data = G.opaque_profile_data graph traversal profile
                       val _ = tick ()
                       val _ = profiles := profile :: !profiles
                   in {raw = IntInf.fromInt (#raw data),
                       inclusive = IntInf.fromInt (#inc data),
                       annotations = #ann data,type_bytes = #type_bytes data}
                   end
               | _ => (tick ();{raw = 1,inclusive = 1,annotations = ty,
                                 type_bytes = bytes})
             val _ = tick () val _ = tick ()
             val _ = if #raw value = raw andalso
                 #inclusive value = inclusive then () else
               raise ERR "same_inside" "annotation syntax metric differs"
             val _ = tick () val _ = tick () val _ = tick ()
             val _ = memo := (node,value) :: !memo
           in value end
        end
      val a = visit left_cap left val b = visit right_cap right
      (* The debit is the complete repeated canonical syntax/type portfolio,
         including binder VARIABLE annotations. It is a nominal admission,
         not a bound on G getter internals or Term.aconv's kernel algorithm. *)
      fun nominal value = plus nominal_cap (#inclusive (value : footprint))
        (plus nominal_cap (#annotations value) (#type_bytes value))
      val amount = plus nominal_cap (nominal a) (nominal b)
      val _ = if amount <= IntInf.fromInt
          (W.work_limit work - #charged (W.audit work)) then () else
        raise ERR "same_inside" "original cumulative work exhausted"
      val _ = W.spend work (IntInf.toInt amount)
      fun retained pending =
        (tick ();case pending of [] => () | child::rest =>
          (tick ();ignore (G.closure_child_node graph caller child);
           retained rest))
      fun retained_profiles () = List.app (fn profile =>
        (tick ();ignore (G.opaque_profile_data graph traversal profile)))
        (!profiles)
      val _ = retained (!held) val _ = retained_profiles ()
      val _ = owner_guard ()
      val _ = root_guard left val _ = root_guard right
      val _ = tick () val l = G.closure_child_node graph caller left
      val _ = tick () val r = G.closure_child_node graph caller right
      val _ = tick () val lterm = G.representative graph l
      val _ = tick () val rterm = G.representative graph r
      val _ = tick ()
      val answer = Term.aconv lterm rterm
      val _ = owner_guard () val _ = retained (!held)
      val _ = retained_profiles ()
      val _ = root_guard left val _ = root_guard right
      val _ = W.spend work 0
    in answer end
    handle primary => (W.close work;raise primary)
  (* The old API retains its BOTH-output policy. No raw caller cap enters
     the admitted comparison: only a SAME-owner opaque focus supplies the
     original/generated source role; target always keeps original output. *)
  fun same_inside work request = compare_inside OutputPair work request
  fun same_admitted_inside work {caller,traversal,left,right,admission} =
    compare_inside (AdmittedSource admission) work
      {caller = caller,traversal = traversal,left = left,right = right}
  structure RP=SmtReplayResourcePolicy
  structure NC=SmtReplayNativeContract
  datatype policy_comparison_role = PolicyOutputPair | PolicyAdmittedSource of
    F.policy_focus
  fun pa_compare_inside role work
      {caller,traversal,left,right,native_contract,profiles=available_profiles} =
    let
      val native=NC.for_work work native_contract
      val _ = W.spend_policy work 0
      val sources = W.original_sources work
      val graph = S.owning_graph sources
      val owner = S.owning_scope sources
      val limits = #semantic_limits native
      val policy_limits=W.semantic_policy work
      val native_used=ref (0:IntInf.int)
      val epoch = Type.type_epoch ()
      fun debit amount =
        if amount>=0 andalso !native_used+amount<=
            IntInf.fromInt (#type_work_limit native) then
          (W.spend_policy work amount;native_used:= !native_used+amount)
        else raise ERR "same_inside_with_policy"
          "native equality planning allowance exhausted"
      fun tick () = debit 1
      fun source_guard () = case role of PolicyOutputPair => ()
        | PolicyAdmittedSource admission =>
          let val _ = tick ()
              val data = F.describe_with_policy_for
                {graph = graph,scope = traversal,sources = sources,work = work}
                admission
              val _ = tick ()
              val current = G.closure_child_node graph caller left
          in if #node data = current then () else
            raise ERR "same_admitted_inside_with_policy"
              "different exact source receipt"
          end
      fun source_cap () = case role of PolicyOutputPair => #output_limit limits
        | PolicyAdmittedSource admission =>
          let val _ = tick ()
              val data = F.describe_with_policy_for
                {graph = graph,scope = traversal,sources = sources,work = work}
                admission
          in case #category data of F.Original=> #input_limit limits
            | F.Generated=> #output_limit limits
            | F.Auxiliary=> #template_limit limits end
      fun source_policy () = case role of
          PolicyOutputPair=> #output_limit policy_limits
        | PolicyAdmittedSource admission=>
            #source_limit (F.describe_with_policy_for
              {graph=graph,scope=traversal,sources=sources,work=work}
              admission)
      fun owner_guard () =
        (NC.validate_for work native_contract;
         W.validate_policy work graph owner sources policy_limits;
         G.validate_scope graph caller;G.validate_scope graph traversal;
         if G.scope_visible graph caller owner andalso
             G.scope_visible graph traversal caller andalso
             Type.type_epoch () = epoch then () else
           raise ERR "same_inside_with_policy"
             "owner, traversal or epoch differs";
         source_guard ())
      fun root_guard child =
        let val _ = tick ()
            val node = G.closure_child_node graph caller child
            val _ = tick () val frame = G.node_scope graph node
            val _ = tick ()
        in if G.scope_visible graph traversal frame then () else
          raise ERR "same_inside_with_policy"
            "root outside active traversal frame" end
      val _ = owner_guard ()
      val _ = root_guard left val _ = root_guard right
      val left_cap = source_cap ()
      val right_cap = #output_limit limits
      val node_cap = IntInf.fromInt (Int.max (left_cap,right_cap))
      val nominal_cap = IntInf.fromInt (#type_work_limit native)
      fun plus cap a b =
        if a > cap orelse b > cap-a then cap+1 else a+b
      val _ = tick () val memo = ref ([] : (G.node * footprint) list)
      val _ = tick () val held = ref ([] : G.closure_child list)
      val held_profiles = ref ([] : (G.scope*G.policy_opaque_profile) list)
      val _ = tick ()
      val type_memo = ref ([] :
        (Type.hol_type * (IntInf.int * IntInf.int)) list)
      fun cached equal key pending =
        (tick ();case pending of [] => NONE | (old,value)::rest =>
          (tick ();if equal (key,old) then (tick ();SOME value)
           else cached equal key rest))
      fun text_bytes text =
        let val _ = tick () val size = String.size text
            fun loop i =
              (tick ();if i = size then () else
                (tick ();ignore (String.sub (text,i));loop (i+1)))
            val _ = loop 0
        in IntInf.fromInt size end
      fun type_size ty =
        case cached Portable.pointer_eq ty (!type_memo) of
          SOME size => size
        | NONE =>
          let
            val cap = IntInf.fromInt (#template_limit limits)
            fun visit pending count bytes =
              (tick ();case pending of [] => (tick ();(count,bytes))
               | terms::more =>
                 (tick ();case terms of [] => visit more count bytes
                  | current::rest =>
                    let val next = plus cap count 1 val _ = tick ()
                        val _ = if next <= cap then () else
                          raise ERR "same_inside_with_policy"
                            "type exceeds original cap"
                        val _ = tick ()
                    in if Type.is_vartype current then
                        let val _ = tick ()
                            val n = text_bytes (Type.dest_vartype current)
                            val _ = tick ()
                        in visit (rest::more) next
                             (plus nominal_cap bytes n) end
                       else
                        let val _ = tick ()
                            val {Thy,Tyop,Args} = Type.dest_thy_typeid current
                            val _ = tick () val name = KernelSig.name_of Tyop
                            val n = plus nominal_cap (text_bytes Thy)
                              (text_bytes name)
                            val _ = tick () val _ = tick ()
                        in visit (Args::rest::more) next
                             (plus nominal_cap bytes n) end
                    end))
            val _ = tick () val _ = tick ()
            val size = visit [[ty]] 0 0
            val _ = tick () val _ = tick () val _ = tick ()
            val _ = type_memo := (ty,size) :: !type_memo
          in size end
      fun admitted cap node metric =
        let val _=tick ()
            val fixed=G.node_scope graph node
            val plan=G.prepare_profiled_metric graph fixed
              {node=node,profiles=available_profiles}
            val data=G.profiled_metric_data graph fixed plan
            val n=case metric of G.RawNodes=> #raw data
              | G.BinderInclusiveNodes=> #inc data
        in if n>0 andalso n<=IntInf.fromInt cap then n else
          raise ERR "same_inside_with_policy" "native syntax exceeds role cap"
        end
      fun annotation node =
        let val _ = tick () val ty = G.type_of graph node
        in type_size ty end
      fun visit cap metadata child =
        let
          val _ = tick () val node = G.closure_child_node graph caller child
          (* Each incoming handle is checked before a memo hit. Its exact
             parent path and rehome backing are retained for the final check.
               *)
          val _ = tick () val _ = tick () val _ = held := child :: !held
          val raw = admitted cap node G.RawNodes
          val inclusive = admitted cap node G.BinderInclusiveNodes
          val _=if RP.allows metadata raw andalso RP.allows metadata inclusive
            then () else raise ERR "same_inside_with_policy"
              "metadata syntax exceeds role cap"
        in case cached (op =) node (!memo) of SOME value => value
         | NONE =>
           let
             val (ty,bytes) = annotation node
             val _ = tick ()
             val value : footprint = case G.view graph node of
                 G.Application _ =>
                   let val _ = tick ()
                       val (l,r) = G.closure_application_children graph caller
                         child
                       val a = visit cap metadata l val b = visit cap metadata
                         r val _ = tick ()
                   in {raw = plus node_cap 1
                         (plus node_cap (#raw a) (#raw b)),
                       inclusive = plus node_cap 1
                         (plus node_cap (#inclusive a) (#inclusive b)),
                       annotations = plus nominal_cap ty
                         (plus nominal_cap (#annotations a) (#annotations b)),
                       type_bytes = plus nominal_cap bytes
                         (plus nominal_cap (#type_bytes a) (#type_bytes b))}
                   end
               | G.AdmittedBinder _ =>
                   let val _ = tick ()
                       val closure = G.closure_child_binder graph caller child
                       val _ = tick ()
                       val data = G.binder_closure_data graph caller closure
                       val _ = admitted cap (#binder data) G.RawNodes
                       val _ = admitted cap (#binder data)
                         G.BinderInclusiveNodes
                       val _ = tick ()
                       val (variable_ty,variable_bytes) =
                         annotation (#binder data)
                       val _ = tick ()
                       val body = visit cap metadata (G.binder_closure_body
                         graph caller
                         closure)
                       val _ = tick ()
                   in {raw = plus node_cap 1 (#raw body),
                       inclusive = plus node_cap 2 (#inclusive body),
                       annotations = plus nominal_cap ty
                         (plus nominal_cap variable_ty (#annotations body)),
                       type_bytes = plus nominal_cap bytes
                         (plus nominal_cap variable_bytes (#type_bytes body))}
                   end
               | G.OpaqueRetained =>
                   let val _ = tick ()
                       fun find [] = raise ERR "same_inside_with_policy"
                             "opaque syntax has no genuine policy profile"
                         | find (profile::rest) =
                             let val _=tick ()
                                 val d=G.opaque_profile_data_with_policy
                                   graph (G.node_scope graph node) profile
                             in if #node d=node then profile else find rest end
                       val profile=find available_profiles
                       val _ = tick ()
                       val data = G.opaque_profile_data_with_policy graph
                         (G.node_scope graph node) profile
                       val _ = tick ()
                       val _ = held_profiles := (G.node_scope graph
                         node,profile) :: !held_profiles
                   in {raw = #raw data,
                       inclusive = #inc data,
                       annotations = #ann data,type_bytes = #type_bytes data}
                   end
               | _ => (tick ();{raw = 1,inclusive = 1,annotations = ty,
                                 type_bytes = bytes})
             val _ = tick () val _ = tick ()
             val _ = if #raw value = raw andalso
                 #inclusive value = inclusive then () else
               raise ERR "same_inside_with_policy"
                 "annotation syntax metric differs"
             val _ = tick () val _ = tick () val _ = tick ()
             val _ = memo := (node,value) :: !memo
           in value end
        end
      val a = visit left_cap (source_policy ()) left
      val b = visit right_cap (#output_limit policy_limits) right
      (* The debit is the complete repeated canonical syntax/type portfolio,
         including binder VARIABLE annotations. It is a nominal admission,
         not a bound on G getter internals or Term.aconv's kernel algorithm. *)
      fun nominal value = plus nominal_cap (#inclusive (value : footprint))
        (plus nominal_cap (#annotations value) (#type_bytes value))
      val amount = plus nominal_cap (nominal a) (nominal b)
      val _ = if RP.allows (W.remaining_policy work) amount then () else
        raise ERR "same_inside_with_policy"
          "original cumulative work exhausted"
      val _ = debit amount
      fun retained pending =
        (tick ();case pending of [] => () | child::rest =>
          (tick ();ignore (G.closure_child_node graph caller child);
           retained rest))
      fun retained_profiles () = List.app (fn (fixed,profile) =>
        (tick ();ignore (G.opaque_profile_data_with_policy graph fixed
          profile)))
        (!held_profiles)
      val _ = retained (!held) val _ = retained_profiles ()
      val _ = owner_guard ()
      val _ = root_guard left val _ = root_guard right
      val _ = tick () val l = G.closure_child_node graph caller left
      val _ = tick () val r = G.closure_child_node graph caller right
      val _ = tick () val lterm = G.representative graph l
      val _ = tick () val rterm = G.representative graph r
      val _ = tick ()
      val answer = Term.aconv lterm rterm
      val _ = owner_guard () val _ = retained (!held)
      val _ = retained_profiles ()
      val _ = root_guard left val _ = root_guard right
      val _ = W.spend_policy work 0
    in answer end
    handle primary => (W.close work;raise primary)
  (* The old API retains its BOTH-output policy. No raw caller cap enters
     the admitted comparison: only a SAME-owner opaque focus supplies the
     original/generated source role; target always keeps original output. *)
  fun same_inside_with_policy work request = pa_compare_inside
    PolicyOutputPair work request
  fun same_admitted_inside_with_policy work
      {caller,traversal,left,right,admission,native_contract,profiles} =
    pa_compare_inside (PolicyAdmittedSource admission) work
      {caller=caller,traversal=traversal,left=left,right=right,
       native_contract=native_contract,profiles=profiles}

end
