(* Compile-checked intermediate plumbing, not a mixed-engine implementation.
   The mixed compiler supplies both native reducers over its existing index. *)
functor Task08Cutovers (I : Task08API) =
struct
  open I
  type mixed_projection_inputs =
    {ordinary_native : Traverse.reducer, configured_native : T.reducer,
     dprocs : Traverse.reducer list, travrules : Travrules.travrules,
     relation : Term.term, limit : int option}
  fun ordinary_projection
      ({ordinary_native,dprocs,travrules,relation,limit,...}
       : mixed_projection_inputs) : Traverse.traverse_data =
    {rewriters=[ordinary_native],dprocs=dprocs,travrules=travrules,
     relation=relation,limit=limit}
  fun private_configured_projection
      ({configured_native,dprocs,travrules,relation,limit,...}
       : mixed_projection_inputs) config : T.xtraverse_data =
    ({rewriters=[configured_native],dprocs=map T.lift dprocs,
      travrules=travrules,relation=relation,limit=limit},config)
  (* TASK_11 needs no extended constructor in ordinary Traverse. *)
  fun private_refresh inputs config facts =
    T.XTRAVERSE (private_configured_projection inputs config) facts
  val ordinary_direct_constructor = Cond_rewr.COND_REWR_CONV
  (* The paired constructor now requires the explicit extension import. *)
  val initial_paired_constructor = Cond_rewrExt.COND_REWR_CONVS
  val initial_threaded_factory = TravrulesExt.mk_threaded_travrules
  val initial_threaded_opening = OpeningExt.THREADED_CONGPROC
  val extension_paired_constructor = C.COND_REWR_CONVS
  val extension_threaded_factory :
      Travrules.preorder list -> Thm.thm list -> Travrules.travrules =
    R.mk_threaded_travrules
  val extension_opening_factory :
      ({Rinst : Term.term,arg : Term.term} -> Thm.thm) ->
      Thm.thm -> Opening.congproc = O.THREADED_CONGPROC
  (* TASK_15 restores plain fragment elements. If the still-mixed compiler
     needs slots, attach them only at installation; TASK_16 deletes this. *)
  type plain_rules = (KernelSig.kernelname option * Thm.thm) list
  fun temporary_install_slots (rules : plain_rules) =
    ListPair.zip (List.tabulate (length rules,fn n => n),rules)
  fun stage15_install install (rules : plain_rules) =
    install (temporary_install_slots rules)
end
