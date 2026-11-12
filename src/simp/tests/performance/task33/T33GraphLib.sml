(* Retained graph words by object kind and size (the CoreGraph and
   MatrixSupport.storage method): anchored PolyML.objSize over equal-arity
   roots, so the shared base and the inputs cancel.  Not bytes, RSS or
   allocation.  Rules are assumed equations over fresh variables, so no
   theory state grows.

   objSize also counts code reachable through closures and the global state
   they reach.  Every tuple therefore carries code0, built and used once per
   process from one unrelated rule, so that rows count per-object data
   only; the step records compare the 0 -> 1 step with the 1 -> 10 step per
   object.

   Per size: PolyML.shareCommonData on the anchor inputs, the anchors (the
   canonical pre-anchor: the inputs are fully shared, so it does not depend
   on how Poly/ML's own sharing pass fell), then the objects, then the rows
   as built, the anchors again (they must not move), PolyML.shareCommonData
   on one tuple of every root, and the rows again as canonical rows.
   Poly/ML's own sharing pass is timing-driven and cannot be switched off,
   so the as-built rows are comparable only when no pass ran inside the
   window (the share counts say), and the canonical rows are deterministic.
   Retention into the shared base moves the canonical post-anchor away from
   the canonical pre-anchor, whatever passes ran.

   T33_GRAPH_EXTRA puts extra data inside the measured object (a control):
   one extra rewrite per rule in every simpset, and in every closure a
   captured list of one cons per rule.  The cells rows check the unit (cons
   3 words, reference 2). *)
structure T33GraphLib =
struct
  open HolKernel boolLib simpLib

  val default_sizes = [0, 1, 10, 100, 1000, 10000]
  fun sizes () = case T33.env "T33_SIZES" of
      NONE => default_sizes
    | SOME s => map (fn x => case Int.fromString x of
                              SOME n => n | NONE => raise Fail "T33_SIZES")
                    (String.tokens (fn c => c = #",") s)

  fun rule i = ASSUME (mk_eq (mk_var ("t33_g" ^ Int.toString i, bool), T))
  (* Integers that no other list in the image shares a tail with, so that
     sharing cannot merge the cells and extra data with anything else; the
     extra data (the control) uses another range than the cells' integers,
     so the two lists cannot merge with each other either. *)
  fun uniq i = 1000003 * (i + 17)
  fun uniqx i = uniq (i + 100000000)
  fun xrule i = ASSUME (mk_eq (mk_var ("t33_x" ^ Int.toString i, bool), T))

  (* The code anchor: every kind of object once, from one unrelated rule. *)
  fun code0 () = let
    val r0 = ASSUME (mk_eq (mk_var ("t33_c0", bool), T))
    val lhs0 = lhs (concl r0)
    val base = pureSimps.pure_ss
    val f0 = rewrites [r0]
    val ss0 = base ++ f0
    val cv0 = SIMP_CONV base []
    val tac0 = SIMP_TAC base []
    val td0 = traversedata_for_ss base
    val cs0 = congLib.mk_congset [congLib.csfrag_rewrites [r0]]
    val cc0 = congLib.CONGRUENCE_EQ_SIMP_CONV cs0 base []
    val nm = {Thy = "bool", Name = "t33_c0"}
    val ex0 = (base ++ rewrites_with_names [(nm, r0)]) -* ["t33_c0"]
    val rm0 = remove_ssfrags ["t33_frag"]
                (base ++ named_rewrites "t33_frag" [r0])
    val roots = (f0, ss0, merge_ss [f0], boolSimps.bool_ss ++ f0, cv0, tac0,
                 td0, cc0, ex0, rm0)
    fun use conv = ignore (Conv.QCONV conv lhs0) handle HOL_ERR _ => ()
  in
    use (SIMP_CONV ss0 []); use (SIMP_CONV ex0 []); use (SIMP_CONV rm0 []);
    use (Traverse.TRAVERSE td0 []); use cc0;
    ignore (T33.solve (SIMP_TAC ss0 []) ([concl r0], lhs0));
    roots
  end

  (* /proc/self/clear_refs "5" resets VmHWM to the current RSS. *)
  fun reset () = let val out = TextIO.openOut "/proc/self/clear_refs" in
    TextIO.output (out, "5"); TextIO.closeOut out; true end
    handle _ => false
  fun status () = RuntimeMetrics.procStatus ()
  val slack = 65536

  (* A reset is verified only if the write succeeded, VmHWM was above VmRSS
     by more than the slack before it (so there was something to reset), and
     VmHWM is within the slack of VmRSS right after it. *)
  fun verified ok b a = ok andalso
    (case (b, a) of
       ((SOME r0, SOME h0), (SOME r1, SOME h1)) =>
         h0 - r0 > LargeInt.fromInt slack andalso
         LargeInt.abs (h1 - r1) <= LargeInt.fromInt slack
     | _ => false)
  fun window ok (r0, h0) (r1, h1) (r2, h2) =
    T33.jo [("reset_ok", T33.jb ok),
            ("rss_before", T33.jopt T33.jn r0),
            ("hwm_before", T33.jopt T33.jn h0),
            ("rss_reset", T33.jopt T33.jn r1),
            ("hwm_reset", T33.jopt T33.jn h1),
            ("rss_after", T33.jopt T33.jn r2),
            ("hwm_after", T33.jopt T33.jn h2),
            ("status", T33.js (if verified ok (r0, h0) (r1, h1) andalso
                                  isSome r2 andalso isSome h2
                               then "ok" else "unsupported"))]

  fun show th = Parse.thm_to_string th
  fun same_ev (th, expect) = (T33.same (th, expect), show th)
  fun all_ev tag xs = (List.all #1 xs,
    "n=" ^ tag ^ " " ^ String.concatWith "; " (map #2 xs))
  (* The closure keeps the extra data alive (the control). *)
  fun carry extra f =
    if T33.graph_extra then (fn x => (ignore (length extra); f x)) else f

  fun at_size c0 n = let
    val tag = Int.toString n
    (* inputs *)
    val rs = List.tabulate (n, rule)
    val xf = if T33.graph_extra
             then SOME (rewrites (List.tabulate (n, xrule))) else NONE
    val extra = if T33.graph_extra then List.tabulate (n, uniqx) else []
    fun plus ss = case xf of NONE => ss | SOME x => ss ++ x
    val base = pureSimps.pure_ss
    val bs = boolSimps.bool_ss
    val f = rewrites rs
    val pss = base ++ f
    val names = List.tabulate (n, fn i => {Thy = "bool", Name = T33.rname i})
    val named = rewrites_with_names (ListPair.zip (names, rs))
    val ints = List.tabulate (n, uniq)
    val refs = List.tabulate (n, fn i => ref (uniq i))
    val e = ([] : int list)
    (* the anchors, before any measured object exists *)
    val anchor_rows =
      [("fragment", fn () => PolyML.objSize (c0, base, rs, base)),
       ("compiled", fn () => PolyML.objSize (c0, base, f, base)),
       ("compiled_bool", fn () => PolyML.objSize (c0, bs, f, bs)),
       ("merge", fn () => PolyML.objSize (c0, base, f, base)),
       ("projection", fn () => PolyML.objSize (c0, pss, pss, pss)),
       ("conversion", fn () => PolyML.objSize (c0, pss, pss, pss)),
       ("tactic", fn () => PolyML.objSize (c0, pss, pss, pss)),
       ("exclusion", fn () => PolyML.objSize (c0, base, named, base)),
       ("removed", fn () => PolyML.objSize (c0, base, rs, base)),
       ("cong", fn () => PolyML.objSize (c0, base, rs, base)),
       ("cells_cons", fn () => PolyML.objSize (c0, e)),
       ("cells_ref", fn () => PolyML.objSize (c0, e))]
    fun anchors () = map (fn (_, a) => a ()) anchor_rows
    (* on fully shared inputs: one sharing call need not reach the fixed
       point, so the inputs are shared until the anchors stop changing *)
    fun shared prev tries = let
      val _ = PolyML.shareCommonData (c0, base, bs, rs, f, pss, named, e)
      val _ = List.app (fn _ => PolyML.fullGC ()) [1, 2, 3]
      val now = anchors ()
    in if now = prev orelse tries <= 0 then now else shared now (tries - 1)
    end
    val pre = shared (anchors ()) 8
    val share_start = T33.share ()
    (* the measured objects, in the build peak window *)
    val st0 = status ()
    val reset_ok = reset ()
    val reset1 = status ()
    val merged = merge_ss (f :: (case xf of NONE => [] | SOME x => [x]))
    val fragx = case xf of NONE => f | SOME x => merge_ss [f, x]
    val pssx = plus pss
    val bss = bs ++ f
    val bssx = plus bss
    val td = traversedata_for_ss pssx
    val cv = carry extra (SIMP_CONV pss [])
    val tac = carry extra (SIMP_TAC pss [])
    val excluded = List.tabulate (n div 10, T33.rname)
    val ex = plus ((base ++ named) -* excluded)
    val removed = plus (remove_ssfrags ["t33_frag"]
                          (base ++ named_rewrites "t33_frag" rs))
    val cs = congLib.mk_congset [congLib.csfrag_rewrites rs]
    val cc = carry extra (congLib.CONGRUENCE_EQ_SIMP_CONV cs base [])
    val union_rows =
      [fn () => PolyML.objSize (c0, base, rs, fragx),
       fn () => PolyML.objSize (c0, base, f, pssx),
       fn () => PolyML.objSize (c0, bs, f, bssx),
       fn () => PolyML.objSize (c0, base, f, merged),
       fn () => PolyML.objSize (c0, pss, pss, td),
       fn () => PolyML.objSize (c0, pss, pss, cv),
       fn () => PolyML.objSize (c0, pss, pss, tac),
       fn () => PolyML.objSize (c0, base, named, ex),
       fn () => PolyML.objSize (c0, base, rs, removed),
       fn () => PolyML.objSize (c0, base, rs, cc),
       fn () => PolyML.objSize (c0, ints),
       fn () => PolyML.objSize (c0, refs)]
    fun unions () = map (fn u => u ()) union_rows
    (* kernel checks, each carrying the printed theorems as evidence *)
    val ends = if n = 0 then [] else [hd rs, List.last rs]
    fun refl_ok conv tm = same_ev (Conv.QCONV conv tm, REFL tm)
    fun proof1 conv rw = same_ev (Conv.QCONV conv (lhs (concl rw)), rw)
    fun proof conv = all_ev tag (map (proof1 conv) ends)
    fun tproof t = all_ev tag (map (fn rw => let
      val th = T33.solve t ([concl rw], lhs (concl rw))
    in (aconv (concl th) (lhs (concl rw)) andalso
        HOLset.equal (hypset th, hypset rw), show th) end) ends)
    fun chk label (ok, ev) = T33.check (label ^ " " ^ tag) ok ev
    val k = n div 10
    val exconv = SIMP_CONV ex []
    val rmconv = SIMP_CONV removed []
    val nf = length (frag_rewrites f)
    val nm = length (frag_rewrites merged)
    val _ = chk "fragment"
      (nf = n andalso nm = (if isSome xf then 2 * n else n),
       "n=" ^ tag ^ " fragment " ^ Int.toString nf ^ " merged " ^
       Int.toString nm)
    val _ = chk "compiled" (all_ev tag
      ((if n = 0 then [refl_ok cv T] else []) @ map (proof1 cv) ends))
    val _ = chk "compiled_bool" (proof (SIMP_CONV bssx []))
    val _ = chk "merge" (proof (SIMP_CONV (base ++ merged) []))
    val _ = chk "projection" (proof (Traverse.TRAVERSE td []))
    val _ = chk "tactic" (tproof tac)
    val _ = chk "exclusion"
      (all_ev tag ((if k = 0 then [] else
                    [refl_ok exconv (lhs (concl (hd rs)))]) @
                   (if n - 1 < k then [] else
                    [proof1 exconv (List.last rs)])))
    val _ = chk "removed"
      (all_ev tag (if n = 0 then [] else
                   [refl_ok rmconv (lhs (concl (hd rs)))]))
    val _ = chk "cong" (proof cc)
    val st2 = status ()
    (* the rows, in their own window: as built, then canonical *)
    val reset2_ok = reset ()
    val reset2 = status ()
    val _ = PolyML.fullGC ()
    val built = unions ()
    val share_union = T33.share ()
    val post = anchors ()
    val share_built = T33.share ()
    val _ = PolyML.shareCommonData
      (c0, base, bs, rs, f, pss, pssx, bss, bssx, merged, fragx, td, cv, tac,
       named, ex, removed, cs, cc, extra, xf, ints, refs)
    val share_shared = T33.share ()
    val canon_pre = anchors ()
    val canon = unions ()
    val canon_post = anchors ()
    val share_canon = T33.share ()
    val rows_end = status ()
    fun row (label, a, ap, u, ca, cap, cu) = T33.emit "graph"
      [("graph", T33.js label), ("n", T33.ji n), ("anchor", T33.ji a),
       ("anchor_post", T33.ji ap), ("union", T33.ji u),
       ("words", T33.ji (u - a)), ("share", T33.ji share_union),
       ("canon_anchor", T33.ji ca), ("canon_anchor_post", T33.ji cap),
       ("canon_union", T33.ji cu), ("canon_words", T33.ji (cu - ca)),
       ("canon_share", T33.ji share_canon)]
    val labels = map #1 anchor_rows
    val _ = ListPair.app (fn (l, (a, (ap, (u, (ca, (cap, cu)))))) =>
                            row (l, a, ap, u, ca, cap, cu))
      (labels, ListPair.zip (pre, ListPair.zip (post,
         ListPair.zip (built, ListPair.zip (canon_pre,
           ListPair.zip (canon_post, canon))))))
    val keep = [T33.hold pss, T33.hold bssx, T33.hold merged, T33.hold td,
                T33.hold cv, T33.hold tac, T33.hold ex, T33.hold removed,
                T33.hold cc, T33.hold rs, T33.hold extra]
    val _ = T33.live ("graph." ^ tag)
    val _ = List.app (fn u => u ()) keep
  in
    T33.emit "phase"
      [("n", T33.ji n), ("share_start", T33.ji share_start),
       ("share_built", T33.ji share_built),
       ("share_shared", T33.ji share_shared),
       ("share_canon", T33.ji share_canon),
       ("build", window reset_ok st0 reset1 st2),
       ("rows", window reset2_ok st2 reset2 rows_end)];
    (n, ListPair.zip (labels, ListPair.zip (ListPair.map op- (built, pre),
                                            ListPair.map op- (canon,
                                                              canon_pre))))
  end

  (* The 0 -> 1 step and the 1 -> 10 step per object of every row, as built
     and canonical: equal when the rows count per-object data only. *)
  fun steps results = let
    fun at n = List.find (fn (m, _) => m = n) results
    fun words n label sel = case at n of
        NONE => NONE
      | SOME (_, rows) => Option.map (fn (_, p) => sel p)
                            (List.find (fn (l, _) => l = label) rows)
    fun emit_step mode sel (label, _) =
      case (words 0 label sel, words 1 label sel, words 10 label sel) of
          (SOME w0, SOME w1, SOME w10) =>
            T33.emit "step"
              [("graph", T33.js label), ("mode", T33.js mode),
               ("first", T33.ji (w1 - w0)), ("rest", T33.ji (w10 - w1)),
               ("span", T33.ji 9)]
        | _ => ()
  in
    case at 0 of
        NONE => ()
      | SOME (_, rows) =>
          (List.app (emit_step "built" #1) rows;
           List.app (emit_step "canonical" #2) rows)
  end

  fun run () = let
    val c0 = code0 ()
    (* The first size of a process runs kernel and printing code for the
       first time, which changes the reach of the anchors by a few words
       (a first-use effect, seen as a moved anchor at the first size and
       not run to run the same): one unrecorded run of size 0 first. *)
    val _ = T33.quietly (fn () => at_size c0 0)
    val _ = T33.live "start"
    val results = map (at_size c0) (sizes ())
  in
    steps results; T33.live "end"; ()
  end
end
