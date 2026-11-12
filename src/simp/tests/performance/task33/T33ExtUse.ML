(* The explicit extension objects of T33Ext: tracked simpsets, rewrite
   views, bundles and projections; kernel checks, then discard cycles. *)
local
  open HolKernel boolLib
  structure C = T33
  structure X = simpExtLib
  fun rules tag i = List.tabulate (4, fn j => let
    val s = "t33_" ^ tag ^ Int.toString i ^ "_" ^ Int.toString j
  in ASSUME (mk_eq (mk_var (s ^ "a", bool), mk_var (s ^ "b", bool))) end)
  fun first rs = lhs (concl (hd rs))
  fun tracked rs = X.mk_simpset [X.rewrites rs]
  fun view ss = let
    val h = hd (X.rewrite_source_handles ss)
  in X.++ (ss, X.rewrite_views [(h, #2 (X.source_rewrite h))]) end
  fun bundle ss rs = X.install_rewrite_bundle
    (X.prepare_rewrite_bundle ss rs) [] ss
  fun conv ss rs = fn () => ignore (X.SIMP_CONV ss [] (first rs))
  val kinds =
    [("noop", fn _ => fn () => ()),
     ("ext_tracked", fn i => let val rs = rules "et" i in
        conv (tracked rs) rs end),
     ("ext_views", fn i => let val rs = rules "ev" i in
        conv (view (tracked rs)) rs end),
     ("ext_bundle", fn i => let val rs = rules "eb" i in
        conv (bundle X.empty_ss rs) rs end),
     ("ext_projection", fn i => let
        val ss = tracked (rules "ep" i)
        val td = X.traversedata_for_ss ss
      in C.hold td end),
     ("ext_xprojection", fn i => let
        val ss = tracked (rules "ex" i)
        val td = X.xtraversedata_for_ss ss
      in C.hold td end)]
  fun proof label ss rs = let
    val rw = hd rs
    val th = X.SIMP_CONV ss [] (lhs (concl rw))
  in C.check label (C.same (th, rw)) (Parse.thm_to_string th) end
  val m = C.need_int "T33_M" 1
in
  val _ = let val rs = rules "c" 0 in
    proof "ext tracked" (tracked rs) rs;
    proof "ext views" (view (tracked rs)) rs;
    proof "ext bundle" (bundle X.empty_ss rs) rs end
  val _ = C.live "ext.start"
  val _ = List.app (C.release m) kinds
end
