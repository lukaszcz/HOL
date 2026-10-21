(* These functors are elaborated, not applied to fake engine stubs.
   Each body must work for every implementation of the proposed signature. *)
functor Task08Clients (I : Task08API) =
struct
  open I
  fun install_opaque ss r = S.++ (ss,S.dproc_ss (T.lift r))
  fun install_configured ss data =
    S.++ (ss,S.dproc_ss (T.CONFIG_REDUCER data))
  fun projections ss facts =
    (T.TRAVERSE (S.traversedata_for_ss ss) facts,
     T.XTRAVERSE (S.xtraversedata_for_ss ss) facts)
  fun configured_congruence ss public_frag rel facts =
    G.CONGRUENCE_SIMP_CONV rel
      (G.mk_congset [G.lift_fragment public_frag]) ss facts
  fun source_runtime ss facts policy config =
    let
      val (ss,args) = S.prepare_rewrite_arguments ss facts
      val bundle = S.prepare_rewrite_bundle ss args
      val rules = S.rewrite_bundle_rules bundle
      val views = List.concat
        (map (fn (th,handles) => map (fn h => (h,th)) handles) rules)
      val invocation = S.install_rewrite_bundle bundle views ss
    in
      S.GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND policy {safe=false}
        config invocation bundle []
    end
  fun tracked_recipe ordinary_reducer steps =
    Default.build
      {seed=fn () => install_opaque Bool.bool_ss ordinary_reducer,
       steps=steps}
  fun typed_window update tac arg = Default.with_updates update tac arg
  val congruence_shape : O.congproc -> Opening.congproc = fn x => x
  val travrule_shape : R.travrules -> Travrules.travrules = fn x => x
  val preorder_shape : R.preorder -> Travrules.preorder = fn x => x
  fun named_at_application name goal =
    case S.lookup_named_frag name of
        NONE => raise Fail ("missing extension fragment: " ^ name)
      | SOME frag => S.SIMP_TAC (S.++ (Pure.pure_ss,frag)) [] goal
end
