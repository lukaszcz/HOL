open HolKernel Parse boolLib simpLib splitLib
open testutils boolSimps

val failcount = ref 0
val _ = diemode := Remember failcount

val _ = Portable.catch_SIGINT()

(* earlier versions of the simplifier would go into an infinite loop on
   terms of this form. *)
val const_term = ``(ARB : bool -> bool) ((ARB : bool -> bool) ARB)``
val test_term = ``^const_term /\ x /\ y``

val _ = tprint "AC looping (if test appears to hang, it has failed)"
val _ = let
  fun kont result1 =
      let
        fun test2P th2 =
            aconv (rhs (concl (Exn.release result1))) (rhs (concl th2))
      in
        (tprint "Permuted AC arguments";
         require (check_result test2P)
                 (QCONV (SIMP_CONV bool_ss [AC CONJ_COMM CONJ_ASSOC]))
                 test_term)
      end
in
  require_msgk (check_result (K true)) (fn _ => HOLPP.add_string "")
               (QCONV (SIMP_CONV bool_ss [AC CONJ_ASSOC CONJ_COMM]))
               kont
               test_term
end

fun infloop_protect msg check f x =
    (tprint msg; require (check_result check) f x)

(* test bounded simplification *)
fun test3P th = aconv (rhs (concl th)) ``P(f (g (x:'a):'a) : 'a):bool``
val _ =
    infloop_protect
      "Bounded rewrites (if test appears to hang, it has failed)"
      test3P
      (QCONV (SIMP_CONV bool_ss
                        [Once (Q.ASSUME `x:'a = f (y:'a)`),
                         Q.ASSUME `y:'a = g (x:'a)`]))
      ``P (x:'a) : bool``

(* test abbreviations in tactics *)
fun test4P (sgs, vfn) =
    length sgs = 1 andalso
    (let val (asms, gl) = hd sgs
     in
       aconv gl ``Q (f (x:'a) : 'b) : bool`` andalso
       length asms = 1 andalso
       aconv (hd asms) ``P (f (x:'a) : 'b) : bool``
     end)

val _ =
    infloop_protect
      "Abbreviations + ASM_SIMP_TAC"
      test4P
      (VALID (ASM_SIMP_TAC bool_ss [markerSyntax.Abbr`y`]))
      ([``Abbrev (y:'b = f (x : 'a))``, ``P (y:'b) : bool``],
       ``Q (y:'b) : bool``)

(* test that bounded rewrites get applied to both branches, and also that
   the bound on the rewrite allows it to apply at all (normally it wouldn't)
*)
val goal5 = ``(x:'a = y) <=> (y = x)``
val test5P =
    infloop_protect
        "Bounded rewrites branch, and bypass permutative loop check"
        (fn (sgs, vf) => null sgs andalso let
                           val th = vf []
                         in
                           aconv (concl th) goal5 andalso null (hyp th)
                         end)
        (fn g => (EQ_TAC THEN STRIP_TAC THEN
                  SIMP_TAC bool_ss [Once EQ_SYM_EQ] THEN
                  POP_ASSUM ACCEPT_TAC) g)
        ([], goal5)

(* test that being a bounded rewrite overrides detection of loops in
   mk_rewrites code *)
val _ = let
  open boolSimps
  val rwt_th = ASSUME ``!x:'a. (f:'a -> 'b) x = if P x then z
                                     else let x = g x in f x``
  val Pa_th = ASSUME ``P (a:'a) : bool``
  fun doit t = (QCONV (SIMP_CONV bool_ss [Pa_th, Once rwt_th]) t,
                QCONV (SIMP_CONV bool_ss [Pa_th, rwt_th]) t)
  fun check (th1, th2) =
      aconv (rhs (concl th1)) ``z:'b`` andalso length (hyp th1) = 2 andalso
      aconv (rhs (concl th2)) ``f (a:'a):'b``
in
  infloop_protect
      "Bounded rewrites override mk_rewrites loop check"
      check
      doit
      ``f (a:'a) : 'b``
end

(* test that loop detection doesn't trigger on bound variables *)
val _ =
    convtest ("Loop detection doesn't trigger on bound variable",
              SIMP_CONV boolSimps.bool_ss
                        [ASSUME “a:'a = (\a:'a b:'b. a) x y”],
              “f(a:'a) = z:'c”,
              “f(x:'a) = z:'c”);

(* test that a bounded rewrite on a variable gets a chance to fire at all *)
val _ = let
  open pureSimps
  val rwt_th = ASSUME ``!x:'a. x:'a = f x``
  val t = ``x:'a = z``
  fun doit t = QCONV (SIMP_CONV pure_ss [Once rwt_th]) t
  fun check th = aconv (rhs (concl th)) ``f (x:'a):'a = z``
in
  infloop_protect
      "Bounded rwts on variables don't get decremented prematurely"
      check
      doit
      t
end

(* test that a bound on a rewrite applies to all derived rewrite theorems *)
val _ = let
  open boolSimps
  val rwt_th = ASSUME ``(p:bool = x) /\ (q:bool = x)``
  val t = ``p /\ q``
  fun doit t = QCONV (SIMP_CONV bool_ss [Once rwt_th]) t
  fun check th = not (aconv (rhs (concl th)) ``x:bool``)
in
  infloop_protect
      "Bound on rewrites applies to all derived theorems jointly."
      check
      doit
      t
end

(*
(* test improved loop detection *)
val _ = let
  val rwt_th = ASSUME “!x:'a. FN x = if P x then T else FN (g x)”
in
  shouldfail {checkexn = (fn UNCHANGED => true | _ => false),
              printarg = K "Test internal instance loop detection",
              printresult = thm_to_string,
              testfn = SIMP_CONV bool_ss [rwt_th]}
             “FN (n:'a) : bool”
end;
*)

(* test that congruence rule for conditional expressions is working OK *)
val _ = let
  open boolSimps
  val t = ``if a then f a:'a else g a``
  val result = ``if a then f T:'a else g F``
  fun doit t = QCONV (SIMP_CONV bool_ss []) t
  fun check th = aconv (rhs (concl th)) result
in
  infloop_protect "Congruence for conditional expressions" check doit t
end

val _ = let
  open boolSimps
  val t = ``I (f:'b -> 'c) o I (g:'a -> 'b)``
  val result = ``(f:'b -> 'c) o I (g:'a -> 'b)``
  val doit = QCONV (SIMP_CONV (bool_ss ++ combinSimps.COMBIN_ss)
                              [SimpL ``$o``])
  fun check th = aconv (rhs (concl th)) result
in
  infloop_protect "SimpL on operator returning non-boolean" check doit t
end

val _ = shouldfail {testfn = (fn () => remove_ssfrags ["FOOBAR"] bool_ss),
                    printresult = PP.pp_to_string 65 simpLib.pp_simpset,
                    printarg = fn () => "remove_ssfrags throws UNCHANGED",
                    checkexn = fn Conv.UNCHANGED => true | _ => false} ()

val _ = let
  open boolSimps
  val t = ``(!n:'a. P n n) ==> ?m. P c m``
  val result = ``T``
  val doit = QCONV (SIMP_CONV (bool_ss ++ SatisfySimps.SATISFY_ss) [])
  fun check th = aconv (rhs (concl th)) result
in
  infloop_protect "Satisfy" check doit t
end

val _ = let
  val asm = ``Abbrev(f = (\x. x /\ y))``
  val g = ([asm], ``p /\ y``)
  val doit = ASM_SIMP_TAC bool_ss []
  fun geq (asl1, g1) (asl2, g2) =
      aconv g1 g2 andalso
      case (asl1, asl2) of
           ([a1], [a2]) => aconv a1 asm andalso aconv a2 asm
         | _ => false
  fun check (sgs, vfn) = let
    val sgs_ok =
      case sgs of
          [goal] => geq goal ([asm], ``(f:bool -> bool) p``)
        | _ => false
  in
    sgs_ok andalso geq (dest_thm (vfn [mk_thm (hd sgs)])) g
  end
in
  infloop_protect "Abbrev-simplification with abstraction" check doit g
end

(* rewrites on F and T *)
val TF = mk_eq(T,F)
val FT = mk_eq(F,T)

val _ = let
  val t = TF
  val doit = QCONV (SIMP_CONV bool_ss [ASSUME TF, ASSUME FT])
  fun check th = th |> concl |> rhs |> aconv F
in
  infloop_protect "assume T=F and F=T (if hangs, it's failed)" check doit t
end


(* conjunction congruence *)
val _ = let
  val t = list_mk_conj [TF,FT,TF]
  val doit = QCONV (SIMP_CONV (bool_ss ++ CONJ_ss) [])
  fun check th = th |> concl |> rhs |> aconv F
in
  infloop_protect
    "CONJ_ss with T=F and F=T assumptions (if hangs, it's failed)"
    check doit t
end

(* ---------------------------------------------------------------------- *)

val _ = let
  val _ = tprint "Cond_rewr.mk_cond_rewrs on ``hyp ==> (T = e)``"
in
  case Lib.total Cond_rewr.mk_cond_rewrs
                 (ASSUME ``P x ==> (T = Q y)``, BoundedRewrites.UNBOUNDED)
   of
      NONE => die "FAILED!"
    | SOME _ => OK()
end

local
  fun die_r l =
    die ("\n  FAILED!  Incorrectly generated rewrites\n  " ^
         String.concatWith "\n  " (map (thm_to_string o #1) l))
fun testb (s, thm, c) =
  let
    val _ = tprint ("Cond_rewr.mk_cond_rewrs on "^s)
  in
    case Lib.total Cond_rewr.mk_cond_rewrs(thm, BoundedRewrites.UNBOUNDED)
     of
        NONE => die "EXN-FAILED!"
      | SOME l => if length l = c then OK() else die_r l
  end
val lem1 = prove(“a <> b ==> (a = ~b)”,
                 ASM_CASES_TAC “a:bool” THEN ASM_REWRITE_TAC[])
val marker = GSYM markerTheory.Abbrev_def
in
val _ = app testb [
  ("“hyp ==> b”", ASSUME “(!b x y. (P x y = b) ==> b)”, 0),
  ("“hyp ==> ~b”", ASSUME “(!b x y. (p x y = b) ==> ~b)”, 0),
  ("“hyp ==> b=e”", ASSUME “(!b:bool x y. (p x y = b) ==> (b = e))”, 2),
  ("“a <> b ==> (a = ~b)", lem1, 2),
  ("x = Abbrev x", marker, 2)
]

val _ = tprint "Cond_rewr.mk_cond_rewrs on bounded x <=> Abbrev x"
val _ = let
  val b = BoundedRewrites.BOUNDED (ref 1)
in
  case Lib.total Cond_rewr.mk_cond_rewrs (marker, b) of
      NONE => die "EXN-FAILED!"
    | SOME (rs as [(th',b')]) =>
        if concl th' ~~ (marker |> concl |> strip_forall |> #2) then OK()
        else die_r rs
    | SOME rs => die_r rs
end
end (* local fun testb ... *);

val _ = let
  open simpLib boolSimps
  fun del ss s = ss -* ("bool_case_thm" :: s)
  val booleta_ss = bool_ss ++ ETA_ss
  val T_t = “if T then (p:'b) else q”
  val F_t = “if F then (p:'b) else q”
  val beta_t = “(\x:'b. f T x : bool) z”
  val eta_t = “f (\x:'a. g (z:'b) x:'c) : 'd”
  val unwind_t = “?x:'a. p x /\ (x = y) /\ q x y”
  val unwind_beta_t = “?x:'a. p x /\ (\y. y /\ z) q /\ (x = a) /\ r x z”
  val ub_beta_applied_t = “?x:'a. p x /\ (q /\ z) /\ x = a /\ r x z”
  fun mkC ss sl = QCONV (SIMP_CONV (del ss sl) [])
  fun mktag s = "rewrite deletion: " ^ s
  fun mkex_tag s = "deletion via Excl: " ^ s
  fun mkexsf_tag s = "deletion via ExclSF: " ^ s
  fun mktest ss (t,dels) = mkC ss dels t
  fun mkexcltest (dels, t) =
      QCONV (SIMP_CONV bool_ss (map Excl ("bool_case_thm" :: dels))) t
  fun mkexclsftest (dels, t) =
      QCONV (SIMP_CONV booleta_ss (map ExclSF dels)) t
  fun test0 (s,l,ss,t1,t2) =
      (tprint s;
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   (mktest ss) (t1,l))
  fun test (s,l,t1,t2) = test0(s,l,bool_ss,t1,t2)
  fun excltest (s,l,t1,t2) =
      (tprint s;
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   mkexcltest (l, t1))
  fun exclsftest (s,l,t1,t2) =
      (tprint s;
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   mkexclsftest(l,t1))
  fun rmsfs (s, ss, rms, t1, t2) =
      (tprint ("Fragment removal: "^s);
       require_msg (check_result (aconv t2 o rhs o concl))
                   (term_to_string o concl)
                   (QCONV (SIMP_CONV (remove_ssfrags rms ss) [])) t1)
in
  List.app (ignore o test) [
    (mktag "bool_ss -* COND_CLAUSES (1)", ["COND_CLAUSES"], T_t, T_t),
    (mktag "bool_ss -* COND_CLAUSES (2)", ["COND_CLAUSES"], F_t, F_t),
    (mktag "bool_ss -* COND_CLAUSES.1", ["COND_CLAUSES.1"], T_t, T_t),
    (mktag "bool_ss -* COND_CLAUSES.2", ["COND_CLAUSES.2"], T_t, “p:'b”),
    (mktag "bool_ss -* BETA_CONV", ["BETA_CONV"], beta_t, beta_t),
    (mktag "bool_ss -* UNWIND_EXISTS_CONV", ["UNWIND_EXISTS_CONV"],
     unwind_t, unwind_t)
  ];
  List.app (ignore o test0) [
    (mktag "rmfrags [\"UNWIND\"] bool_ss -* BETA_CONV", ["BETA_CONV"],
     remove_ssfrags ["UNWIND"] bool_ss, unwind_beta_t, unwind_beta_t)
  ];
  List.app (ignore o test0) [
    (mktag "rmfrags [\"UNWIND\"] (bool_ss -* BETA_CONV)", [],
     remove_ssfrags ["UNWIND"] (bool_ss -* ["BETA_CONV"]),
     unwind_beta_t, unwind_beta_t)
  ];
  List.app (ignore o excltest) [
    (mkex_tag "bool_ss & \"COND_CLAUSES.1\"", ["COND_CLAUSES.1"],
     T_t, T_t),
    (mkex_tag "bool_ss & \"BETA_CONV\"", ["BETA_CONV"], beta_t, beta_t)
  ];
  List.app (ignore o exclsftest) [
    (mkexsf_tag "booleta_ss & ETA_ss", ["ETA"], eta_t, eta_t),
    (mkexsf_tag "booleta_ss & UNWIND_ss", ["UNWIND"], unwind_beta_t,
     ub_beta_applied_t),
    (mkexsf_tag "booleta_ss & UNWIND_ss", ["UNWIND"], unwind_t, unwind_t),
    (mkexsf_tag "booleta_ss & CONG_ss", ["CONG"], “if p /\ q then p else q”,
     “if p /\ q then p else q”)
  ];
  List.app (ignore o rmsfs) [
    ("UNWIND", bool_ss, ["UNWIND"], unwind_t, unwind_t),
    ("UNWIND on (bool_ss -* [\"BETA_CONV\"]) 1", bool_ss -* ["BETA_CONV"],
     ["UNWIND"], beta_t, beta_t),
    ("UNWIND on (bool_ss -* [\"BETA_CONV\"]) 2", bool_ss -* ["BETA_CONV"],
     ["UNWIND"], unwind_beta_t, unwind_beta_t)
  ]
end;

fun printgoal (asms,w) =
    "([" ^ String.concatWith "," (map term_to_string asms) ^ "], " ^
    term_to_string w ^ ")"
fun printgoals (sgs, _) =
    "[" ^ String.concatWith ",\n" (map printgoal sgs) ^ "]"


(* flavours of Req* *)
val _ = let
  open pureSimps
  val oneone_asm = [“ONE_ONE (f:'a -> 'b)”]
  fun req_test (nm,thl,asms,i,oopt) =
      let
        val _ = tprint nm
        val testresult =
            case oopt of
                NONE => (fn r => case r of Exn.Exn _ => true | _ => false)
              | SOME t => if type_of t = alpha then
                            (fn r => case r of Exn.Res _ => true | _ => false)
                          else
                            (fn r => case r of
                                         Exn.Res (sgs,_) =>
                                           list_eq goal_eq [(asms, t)] sgs
                                       | _ => false)

      in
        require_msg testresult printgoals (VALID (ASM_SIMP_TAC pure_ss thl))
                    (asms,i)
      end
  val oneone = Q.prove(‘ONE_ONE f ==> !x y. (f x = f y) <=> (x = y)’,
                       REWRITE_TAC[ONE_ONE_THM] >> rpt strip_tac >> eq_tac >>
                       strip_tac >-
                         (first_x_assum irule >> ASM_REWRITE_TAC[]) >>
                       ASM_REWRITE_TAC[])
in
List.app (ignore o req_test) [
  ("req0 fires", [Req0 AND_CLAUSES], [], “p /\ T”, SOME “p:bool”),
  ("req0 fires trivially", [Req0 AND_CLAUSES], [], “p /\ q”, SOME “p /\ q”),
  ("reqD fires", [ReqD AND_CLAUSES], [], “p /\ T”, SOME “p:bool”),
  ("reqD fails", [ReqD AND_CLAUSES], [], “p /\ q”, NONE),
  ("req0 succeeds (cond_rwt)", [Req0 oneone], oneone_asm,
   “(f:'a -> 'b) x = f y”, SOME “x:'a = y”),
  ("req0 fails (cond_rwt)", [Req0 oneone], [], “(f:'a -> 'b) x = f y”, NONE),
  ("req0/Once fails", [Req0 (Once AND_CLAUSES)], [], “p /\ T /\ q /\ T”, NONE),
  ("reqD/Once succeeds", [ReqD (Once AND_CLAUSES)], [] ,
   “p /\ T /\ q /\ T”, SOME “x:α”),
  ("req0/Twice succeeds", [Req0 (Ntimes AND_CLAUSES 2)], [],
   “p /\ T /\ q /\ T”, SOME “p /\ q”),
  ("SF ETA_ss succeeds", [SF boolSimps.ETA_ss], [], “P (\x:'a. f x:'b) /\ T”,
   SOME “P (f:'a -> 'b) /\ T”),
  ("SF ETA_ss & DNF_ss succeeds",
   [SF boolSimps.ETA_ss, AND_CLAUSES, SF boolSimps.DNF_ss], [],
   “p /\ (p \/ R (\x:'a . f x:'b))”,
   SOME “p \/ p /\ R (f : 'a -> 'b)”),
  ("SF DISJ_ss & DNF_ss succeeds",
   [SF boolSimps.DISJ_ss, AND_CLAUSES, SF boolSimps.DNF_ss], [],
   “p /\ (p \/ r)”, SOME “p \/ F”)
]
end;


val _ = let
  fun testresult outgs res =
      case res of
          Exn.Res (sgs, _) => list_eq goal_eq outgs sgs
        | _ => false
  fun test (msg, tac, ing, outgs) =
      (tprint msg;
       require_msg (testresult outgs) printgoals tac ing)
  val T_t = “?x:'a. p”
  fun gs c = global_simp_tac c
  val fs = full_simp_tac
  val gsc = {droptrues=true,elimvars=false,strip=true,oldestfirst=true}
  val gsc' = {droptrues=true,elimvars=false,strip=true,oldestfirst=false}
  val bss1 = bool_ss ++ rewrites [ASSUME “x = T”]
  val bss2 = bss1 ++ rewrites [ASSUME “x = F”]
in
  List.app (ignore o test) [
    ("Abbrev var not rewritten",
     rev_full_simp_tac (bool_ss ++ ABBREV_ss) [],
     ([“Abbrev (v <=> q /\ r)”, “v = F”], “P (v:bool):bool”),
     [([“Abbrev (v <=> q /\ r)”, “~v”], “P F:bool”)]),
    ("simp_tac + Excl", simp_tac bool_ss [Excl "EXISTS_SIMP"], ([], T_t),
     [([], T_t)]),
    ("fs + Excl", fs bool_ss [Excl "EXISTS_SIMP"], ([], T_t),
     [([], T_t)]),
    ("gs + Excl", gs gsc bool_ss [Excl "EXISTS_SIMP"], ([], T_t),
     [([], T_t)]),
    ("gs oldestfirst", gs gsc bool_ss [], ([“x:'a = y”, “x:'a = z”], “p:bool”),
     [([“x:'a = z”, “y:'a = z”], “p:bool”)]),
    ("gs oldestfirst", gs gsc' bool_ss [],
     ([“x:'a = y”, “x:'a = z”], “p:bool”),
     [([“z:'a = y”, “x:'a = y”], “p:bool”)]),
    ("fs + Excl (in assumptions)", fs bool_ss [Excl "EXISTS_SIMP"],
     ([“^T_t = X”], “p /\ q”), [([“^T_t = X”], “p /\ q”)]),
    ("gs + Excl (in assumptions)", gs gsc bool_ss [Excl "EXISTS_SIMP"],
     ([“^T_t = X”], “p /\ q”), [([“^T_t = X”], “p /\ q”)]),
    ("NoAsms",
     asm_simp_tac bool_ss [markerLib.NoAsms],
     ([“x = F”], “p /\ x”), [([“x = F”], “p /\ x”)]),
    ("IgnAsm",
     asm_simp_tac bool_ss [markerLib.IgnAsm ‘x = _’],
     ([“x = F”, “y = T”], “p /\ x /\ y”), [([“x = F”, “y = T”], “p /\ x”)]),
    ("IgnAsm (sub-match)",
     asm_simp_tac bool_ss [markerLib.IgnAsm ‘F (* sa *)’],
     ([“x = F”, “y = T”], “p /\ x /\ y”), [([“x = F”, “y = T”], “p /\ x”)]),
    ("Rewrite competition: ASM vs arg",
     asm_simp_tac bool_ss [ASSUME “x = T”],
     ([“x = F”], “P (x:bool):bool”), [([“x = F”], “P F:bool”)]),
    ("Rewrite competition: ARG1 vs arg2",
     asm_simp_tac bool_ss [ASSUME “x = T”, ASSUME “x = F”],
     ([], “P (x:bool):bool”), [([], “P T:bool”)]),
    ("Rewrite competition: ASM1 vs asm2",
     asm_simp_tac bool_ss [],
     ([“x=T”, “x=F”], “P (x:bool):bool”), [([“x=T”,“x=F”], “P T:bool”)]),
    ("Rewrite competition: ss1 vs SS2",
     asm_simp_tac bss2 [],
     ([], “P(x:bool):bool”), [([], “P F:bool”)]),
    ("Rewrite competition: ARG vs ss",
     asm_simp_tac bss1 [ASSUME “x = F”],
     ([], “P(x:bool):bool”), [([], “P F:bool”)]),
    ("Rewrite competition: ASM vs ss",
     asm_simp_tac bss1 [],
    ([“x = F”], “P(x:bool):bool”), [([“x = F”], “P F:bool”)])
  ]
end

(* ---------------------------------------------------------------------- *)
(* Default-equivalence goldens for the traversal solver pipeline.         *)
(* ---------------------------------------------------------------------- *)

local
  val recursive_rwt =
    Q.ASSUME `(p /\ T) ==> ((f : 'a -> 'b) x = y)`
  val failed_rwt =
    Q.ASSUME `(p /\ T) ==> ((f : 'a -> 'b) x = y)`

  val c1 = ``p = q``
  val c2 = ``(f : bool -> bool) = g``
  val c3 = ``(f : (bool -> bool) -> bool) = g``
  val c4 = ``(f : ((bool -> bool) -> bool) -> bool) = g``
  val c5 =
    ``(f : (((bool -> bool) -> bool) -> bool) -> bool) = g``

  fun cond_true condition lhs =
    ASSUME (mk_imp (condition, mk_eq (lhs, T)))

  val root_rwt =
    ASSUME
      (mk_imp (c1,
               mk_eq (``(depth_f : 'a -> 'b) depth_x``, ``depth_y : 'b``)))
  val depth4_rwts =
    [root_rwt, cond_true c2 c1, cond_true c3 c2,
     cond_true c4 c3, ASSUME (mk_eq (c4, T))]
  val depth5_rwts =
    [root_rwt, cond_true c2 c1, cond_true c3 c2,
     cond_true c4 c3, cond_true c5 c4, ASSUME (mk_eq (c5, T))]

  val no_beta_ss = bool_ss -* ["BETA_CONV"]
  val raw_bool_conv =
    Traverse.TRAVERSE (traversedata_for_ss bool_ss) []
in
  val _ = convtest
    ("default pipeline: recursive traversal proves a side condition",
     SIMP_CONV bool_ss [Q.ASSUME `p`, recursive_rwt],
     ``(f : 'a -> 'b) x``, ``y : 'b``)

  val _ = convtest
    ("default pipeline: failed side condition restores traversal limit",
     SIMP_CONV (limit 1 bool_ss) [failed_rwt],
     ``(h : 'b -> bool -> 'c) ((f : 'a -> 'b) x) (q /\ T)``,
     ``(h : 'b -> bool -> 'c) (f x) q``)

  val _ = tprint "default conditional-rewrite stack limit is four"
  val _ =
    if !Cond_rewr.stack_limit = 4 then OK()
    else die ("expected stack limit 4, got " ^
              Int.toString (!Cond_rewr.stack_limit))

  val _ = convtest
    ("default pipeline: four nested side conditions succeed",
     SIMP_CONV pureSimps.pure_ss depth4_rwts,
     ``(depth_f : 'a -> 'b) depth_x``, ``depth_y : 'b``)

  val _ = convtest
    ("default pipeline: fifth nested side condition is rejected",
     QCONV (SIMP_CONV pureSimps.pure_ss depth5_rwts),
     ``(depth_f : 'a -> 'b) depth_x``,
     ``(depth_f : 'a -> 'b) depth_x``)

  val unchanged_tm = ``(unchanged_f : 'a -> 'b) unchanged_x``

  val _ = shouldfail
    {testfn = raw_bool_conv,
     printresult = thm_to_string,
     printarg = K "raw traversal maps congruence UNCHANGED to HOL_ERR",
     checkexn = fn HOL_ERR _ => true | _ => false}
    unchanged_tm

  val _ = shouldfail
    {testfn = SIMP_CONV bool_ss [],
     printresult = thm_to_string,
     printarg = K "public conversion propagates unchanged result",
     checkexn = fn Conv.UNCHANGED => true | _ => false}
    unchanged_tm

  val _ = convtest
    ("default pipeline: QCONV turns unchanged result into reflexivity",
     QCONV (SIMP_CONV bool_ss []), unchanged_tm, unchanged_tm)

  val _ = convtest
    ("default pipeline: unchanged operator preserves changed argument",
     SIMP_CONV bool_ss [],
     ``(unchanged_f : bool -> 'a) (p /\ T)``,
     ``(unchanged_f : bool -> 'a) p``)

  val _ = convtest
    ("default pipeline: changed operator preserves unchanged argument",
     SIMP_CONV bool_ss [],
     ``(unchanged_f : bool -> 'a -> 'b) (p /\ T) unchanged_x``,
     ``(unchanged_f : bool -> 'a -> 'b) p unchanged_x``)

  val _ = convtest
    ("default pipeline: implication context rewrites its consequent",
     SIMP_CONV bool_ss [], ``p ==> p /\ q``, ``p ==> q``)

  val _ = convtest
    ("default pipeline: let context rewrites its body",
     SIMP_CONV no_beta_ss [Cong boolTheory.LET_CONG],
     ``let x : 'a = a in if x = a then y : 'b else z``,
     ``let x : 'a = a in y : 'b``)

  exception EMPTY_CONTEXT
  val prover_error = mk_HOL_ERR "selftest" "toy_solver"
  val excluded_middle =
    SPEC ``toy_p (toy_x : 'a) : bool`` boolTheory.EXCLUDED_MIDDLE
  val solver_rwt =
    ASSUME
      ``(toy_p (toy_x : 'a) \/ ~toy_p toy_x) ==>
        ((toy_f : 'a -> 'b) toy_x = toy_y)``
  fun excluded_middle_solver _ tm =
    if aconv tm (concl excluded_middle) then excluded_middle
    else raise prover_error "Condition not recognized"
  val toy_solver =
    {name="excluded middle", solve=excluded_middle_solver}
  val solver_rewr =
    Cond_rewr.COND_REWR_CONV ("solver_rwt",solver_rwt) false
  val solver_reducer =
    Traverse.REDUCER
      {name=SOME "solver test reducer",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,...} => solver_rewr solver stack}
  val pure_data = traversedata_for_ss pureSimps.pure_ss
  val solver_data =
    {rewriters=[solver_reducer], dprocs=[],
     relation= #relation pure_data, travrules= #travrules pure_data,
     limit=NONE, subgoaler=NONE, solvers=[toy_solver],
     cond_depth=NONE, term_ord=NONE}
  val solver_conv = Traverse.TRAVERSE solver_data []

  val _ = convtest
    ("solver pipeline: unsafe solver proves residual condition",
     solver_conv, ``(toy_f : 'a -> 'b) toy_x``, ``toy_y : 'b``)

  val context_rwt =
    ASSUME ``context_p ==> ((context_f : 'a -> 'b) context_x = context_y)``
  val context_rewr =
    Cond_rewr.COND_REWR_CONV ("context_rwt",context_rwt) false
  val context_reducer =
    Traverse.REDUCER
      {name=SOME "context test reducer",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,...} => context_rewr solver stack}
  val bool_data = traversedata_for_ss bool_ss
  fun context_solver {context_thms,...} tm =
    case List.find (fn th => aconv tm (concl th)) context_thms of
        SOME th => th
      | NONE => raise prover_error "Condition absent from context"
  val context_data =
    {rewriters=[context_reducer], dprocs=[],
     relation= #relation bool_data, travrules= #travrules bool_data,
     limit=NONE, subgoaler=NONE,
     solvers=[{name="context lookup",solve=context_solver}],
     cond_depth=NONE, term_ord=NONE}
  val context_conv = Traverse.TRAVERSE context_data []

  val _ = convtest
    ("solver pipeline: congruence context theorem is visible",
     context_conv,
     ``context_p ==> (context_f : 'a -> 'b) context_x = context_z``,
     ``context_p ==> (context_y : 'b) = context_z``)

  fun failing_solver _ _ =
    raise prover_error "Deliberate solver failure"
  val limited_data =
    {rewriters= #rewriters bool_data, dprocs= #dprocs bool_data,
     relation= #relation bool_data, travrules= #travrules bool_data,
     limit=SOME 1, subgoaler=NONE,
     solvers=[{name="always fails",solve=failing_solver}],
     cond_depth=NONE, term_ord=NONE}
  val solver_failure_conv = Traverse.TRAVERSE limited_data [failed_rwt]

  val _ = convtest
    ("solver pipeline: solver failure restores traversal limit",
     solver_failure_conv,
     ``(h : 'b -> bool -> 'c) ((f : 'a -> 'b) x) (q /\ T)``,
     ``(h : 'b -> bool -> 'c) (f x) q``)

  val passthrough_reducer =
    Traverse.REDUCER
      {name=SOME "solver exception test reducer",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,...} => solver stack}
  fun raising_solver _ _ =
    if !Cond_rewr.stack_limit = 31 andalso
       (!Cond_rewr.term_ord) (boolSyntax.T, boolSyntax.F) = GREATER
    then raise Fail "non-HOL solver exception"
    else raise Fail "dynamic flags not installed before solver exception"
  val exception_data =
    {rewriters=[passthrough_reducer], dprocs=[],
     relation= #relation bool_data, travrules= #travrules bool_data,
     limit=NONE, subgoaler=SOME (fn _ => REFL),
     solvers=[{name="raises Fail",solve=raising_solver}],
     cond_depth=SOME 31, term_ord=SOME (fn _ => GREATER)}
  val exception_conv = Traverse.TRAVERSE exception_data []

  val _ = shouldfail
    {testfn=exception_conv,
     printresult=thm_to_string,
     printarg=K "solver pipeline propagates non-HOL exceptions",
     checkexn=fn Fail "non-HOL solver exception" => true | _ => false}
    ``solver_exception_p``

  val _ = tprint "TRAVERSE restores dynamic flags after an exception"
  val _ =
    if !Cond_rewr.stack_limit = 4 andalso
       (!Cond_rewr.term_ord) (``nested_x:'a``, ``nested_y:'a``) =
       Cond_rewr.ac_term_ord (``nested_x:'a``, ``nested_y:'a``)
    then OK()
    else die "dynamic flags were not restored after an exception"

  fun configure_data (data : Traverse.traverse_data)
                     subgoaler solvers cond_depth term_ord =
    {rewriters= #rewriters data, dprocs= #dprocs data,
     relation= #relation data, travrules= #travrules data,
     limit= #limit data, subgoaler=subgoaler, solvers=solvers,
     cond_depth=cond_depth, term_ord=term_ord}

  fun mk_depth_condition i =
    mk_eq (mk_var ("depth_l" ^ Int.toString i, Type.alpha),
           mk_var ("depth_r" ^ Int.toString i, Type.alpha))
  val depth10_conditions =
    List.tabulate (10, fn i => mk_depth_condition (i + 1))
  fun mk_depth_chain [last] = [ASSUME (mk_eq (last, boolSyntax.T))]
    | mk_depth_chain (current :: (rest as next :: _)) =
        cond_true next current :: mk_depth_chain rest
    | mk_depth_chain [] = raise Fail "empty condition chain"
  val depth10_root =
    ASSUME
      (mk_imp (hd depth10_conditions,
               mk_eq (``(depth10_f : 'a -> 'b) depth10_x``,
                      ``depth10_y : 'b``)))
  val depth10_rwts = depth10_root :: mk_depth_chain depth10_conditions
  val depth_default_data =
    configure_data pure_data NONE [] NONE NONE
  val depth40_data =
    configure_data pure_data NONE [] (SOME 40) NONE
  val depth_default_conv =
    Traverse.TRAVERSE depth_default_data depth10_rwts
  val depth40_conv = Traverse.TRAVERSE depth40_data depth10_rwts
  val depth10_lhs = ``(depth10_f : 'a -> 'b) depth10_x``
  val depth10_rhs = ``depth10_y : 'b``

  fun unchanged_on_hol_err conv tm =
    conv tm handle HOL_ERR _ => REFL tm | Conv.UNCHANGED => REFL tm
  val _ = convtest
    ("cond_depth: depth ten fails at the default four",
     unchanged_on_hol_err depth_default_conv, depth10_lhs, depth10_lhs)

  val _ = convtest
    ("cond_depth: per-traversal depth forty succeeds",
     depth40_conv, depth10_lhs, depth10_rhs)

  val _ =
    Lib.with_flag (Cond_rewr.stack_limit,40)
      (fn () =>
          convtest
            ("cond_depth: NONE honors the global stack limit",
             depth_default_conv, depth10_lhs, depth10_rhs)) ()

  val _ = tprint "cond_depth binding restores the global stack limit"
  val _ =
    if !Cond_rewr.stack_limit = 4 then OK()
    else die "cond_depth did not restore the global stack limit"

  fun reverse_order pair =
    case Cond_rewr.ac_term_ord pair of
        LESS => GREATER
      | EQUAL => EQUAL
      | GREATER => LESS
  val reverse_order_data =
    configure_data pure_data NONE [] NONE (SOME reverse_order)
  val reverse_order_conv =
    Traverse.TRAVERSE reverse_order_data [boolTheory.EQ_SYM_EQ]
  val default_order_conv =
    Traverse.TRAVERSE depth_default_data [boolTheory.EQ_SYM_EQ]

  val _ = convtest
    ("term_ord: default order chooses the ascending equality",
     default_order_conv, ``nested_y:'a = nested_x``,
     ``nested_x:'a = nested_y``)

  val _ = convtest
    ("term_ord: custom order flips the equality normal form",
     reverse_order_conv, ``nested_x:'a = nested_y``,
     ``nested_y:'a = nested_x``)

  val once_order_data =
    configure_data pure_data NONE [] NONE (SOME (fn _ => LESS))
  val once_order_conv =
    Traverse.TRAVERSE once_order_data [Once boolTheory.EQ_SYM_EQ]

  val _ = convtest
    ("term_ord: Once bypasses a custom rejecting order",
     once_order_conv, ``once_x:'a = once_y``, ``once_y:'a = once_x``)

  val _ = convtest
    ("TRAVERSE refreshes Once for each conversion application",
     once_order_conv, ``once_u:'a = once_v``, ``once_v:'a = once_u``)

  val order_probe = (``nested_order_x:'a``, ``nested_order_y:'a``)
  fun has_dynamic_flags depth expected =
    !Cond_rewr.stack_limit = depth andalso
    (!Cond_rewr.term_ord) order_probe = expected
  val nested_inner_condition =
    SPEC ``nested_inner_q:bool`` boolTheory.EXCLUDED_MIDDLE
  val nested_inner_lhs =
    ``(nested_inner_f : 'a -> 'b) nested_inner_x``
  val nested_inner_rhs = ``nested_inner_y:'b``
  val nested_inner_rwt =
    ASSUME
      (mk_imp (concl nested_inner_condition,
               mk_eq (nested_inner_lhs,nested_inner_rhs)))
  fun nested_inner_apply {solver,stack,...} tm =
    if aconv tm nested_inner_lhs then
      MP nested_inner_rwt (solver stack (concl nested_inner_condition))
    else NO_CONV tm
  val nested_inner_reducer =
    Traverse.REDUCER
      {name=SOME "nested inner rewrite", initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt, apply=nested_inner_apply}
  val inner_simp_tm = boolSyntax.T
  fun nested_inner_solver _ tm =
    if not (aconv tm (concl nested_inner_condition)) then
      raise Fail "inner solver received an unexpected condition"
    else if not (has_dynamic_flags 23 LESS) then
      raise Fail "inner TRAVERSE flags not installed"
    else let
      val simp_th = QCONV (SIMP_CONV bool_ss []) inner_simp_tm
      val _ = aconv (rhs (concl simp_th)) boolSyntax.T orelse
              raise Fail "inner solver's SIMP_CONV failed"
      val _ = has_dynamic_flags 23 LESS orelse
              raise Fail "SIMP_CONV disturbed inner TRAVERSE flags"
    in
      nested_inner_condition
    end
  val nested_inner_data =
    {rewriters=[nested_inner_reducer], dprocs=[],
     relation= #relation pure_data, travrules= #travrules pure_data,
     limit=NONE, subgoaler=SOME (fn _ => REFL),
     solvers=[{name="nested inner",solve=nested_inner_solver}],
     cond_depth=SOME 23, term_ord=SOME Cond_rewr.ac_term_ord}
  val nested_inner_conv = Traverse.TRAVERSE nested_inner_data []
  val nested_outer_lhs =
    ``(nested_outer_f : bool -> bool) nested_outer_x``
  val nested_outer_rhs = ``nested_outer_y:bool``
  val nested_outer_rwt =
    ASSUME (mk_eq (nested_outer_lhs,nested_outer_rhs))
  fun nested_outer_apply _ tm =
    if not (aconv tm nested_outer_lhs) then NO_CONV tm
    else let
      val _ = has_dynamic_flags 17 GREATER orelse
              raise Fail "outer TRAVERSE flags not installed"
      val nested_th =
        nested_inner_conv nested_inner_lhs
        handle HOL_ERR _ => raise Fail "inner TRAVERSE raised HOL_ERR"
      val _ = aconv (rhs (concl nested_th)) nested_inner_rhs orelse
              raise Fail "inner TRAVERSE failed"
      val _ = has_dynamic_flags 17 GREATER orelse
              raise Fail "inner TRAVERSE flags were not restored"
    in
      nested_outer_rwt
    end
  val nested_outer_reducer =
    Traverse.REDUCER
      {name=SOME "nested outer rewrite", initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt, apply=nested_outer_apply}
  val nested_outer_data =
    {rewriters=[nested_outer_reducer], dprocs=[],
     relation= #relation pure_data, travrules= #travrules pure_data,
     limit=NONE, subgoaler=NONE, solvers=[],
     cond_depth=SOME 17, term_ord=SOME reverse_order}
  val nested_outer_conv = Traverse.TRAVERSE nested_outer_data []

  val _ = convtest
    ("TRAVERSE reentrancy restores flags around solver SIMP_CONV",
     nested_outer_conv, nested_outer_lhs, nested_outer_rhs)

  val _ = tprint "nested TRAVERSE restores the global dynamic flags"
  val _ =
    if !Cond_rewr.stack_limit = 4 andalso
       (!Cond_rewr.term_ord) (boolSyntax.T, boolSyntax.F) =
       Cond_rewr.ac_term_ord (boolSyntax.T, boolSyntax.F)
    then OK()
    else die "nested TRAVERSE did not restore its dynamic flags"

  val conglib_rwt =
    ASSUME ``(conglib_f : 'a -> 'b) conglib_x = conglib_y``
  val conglib_cs =
    congLib.mk_congset [congLib.csfrag_rewrites [conglib_rwt]]
  val _ = convtest
    ("congLib equality simplification smoke test",
     congLib.CONGRUENCE_EQ_SIMP_CONV conglib_cs pureSimps.pure_ss [],
     ``(conglib_f : 'a -> 'b) conglib_x``, ``conglib_y:'b``)

  val conglib_condition =
    SPEC ``conglib_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val conglib_solver_lhs =
    ``(conglib_solver_f : 'a -> 'b) conglib_solver_x``
  val conglib_solver_rhs = ``conglib_solver_y:'b``
  val conglib_solver_rwt =
    ASSUME
      (mk_imp (concl conglib_condition,
               mk_eq (conglib_solver_lhs,conglib_solver_rhs)))
  val conglib_solver_cs = congLib.mk_congset []
  val conglib_subgoaler_calls = ref 0
  val conglib_solver_calls = ref 0
  fun conglib_subgoaler _ tm =
    (conglib_subgoaler_calls := !conglib_subgoaler_calls + 1; REFL tm)
  fun conglib_solver _ tm =
    let
      val _ = conglib_solver_calls := !conglib_solver_calls + 1
      val flags_ok =
        !Cond_rewr.stack_limit = 29 andalso
        (!Cond_rewr.term_ord) (``conglib_order_x:'a``,
                               ``conglib_order_y:'a``) = GREATER
    in
      if aconv tm (concl conglib_condition) andalso flags_ok then
        conglib_condition
      else raise prover_error "congLib traversal controls missing"
    end
  fun conglib_solver_apply {solver,stack,...} tm =
    if aconv tm conglib_solver_lhs then
      MP conglib_solver_rwt
         (solver stack (concl conglib_condition))
    else NO_CONV tm
  val conglib_solver_reducer =
    Traverse.REDUCER
      {name=SOME "congLib traversal controls",
       initial=EMPTY_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=conglib_solver_apply}
  val conglib_solver_ss =
    pureSimps.pure_ss ++ dproc_ss conglib_solver_reducer
    |> set_subgoaler conglib_subgoaler
    |> add_unsafe_solver
         {name="congLib traversal solver",solve=conglib_solver}
    |> set_cond_depth 29
    |> set_term_ord (fn _ => GREATER)
  val _ = convtest
    ("congLib forwards simpset traversal controls",
     congLib.CONGRUENCE_EQ_SIMP_CONV
       conglib_solver_cs conglib_solver_ss [],
     conglib_solver_lhs,conglib_solver_rhs)
  val _ = tprint "congLib used the configured subgoaler and solver"
  val _ =
    if !conglib_subgoaler_calls = 1 andalso !conglib_solver_calls = 1 then
      OK()
    else die "congLib dropped a configured traversal control"
end

(* ---------------------------------------------------------------------- *)
(* simpLib strategy fields, fragment merges, and history rebuilding.      *)
(* ---------------------------------------------------------------------- *)

fun pp ss = PP.pp_to_string 200 simpLib.pp_simpset ss

  fun occurrences needle haystack =
    let
      val needle_n = String.size needle
      val haystack_n = String.size haystack
      fun loop i n =
        if i + needle_n > haystack_n then n
        else if String.substring(haystack,i,needle_n) = needle then
          loop (i + needle_n) (n + 1)
        else loop (i + 1) n
    in
      if needle_n = 0 then 0 else loop 0 0
    end

  fun position needle haystack =
    let
      val needle_n = String.size needle
      val haystack_n = String.size haystack
      fun loop i =
        if i + needle_n > haystack_n then NONE
        else if String.substring(haystack,i,needle_n) = needle then SOME i
        else loop (i + 1)
    in
      if needle_n = 0 then NONE else loop 0
    end

  fun check msg test =
    (tprint msg; if test () then OK() else die "FAILED!")

  val dummy_looper : simpset -> tactic = fn _ => NO_TAC
  val other_looper : simpset -> tactic = fn _ => ALL_TAC

  val loopers_added =
    empty_ss
    |> add_looper ("surface looper one",dummy_looper)
    |> add_looper ("surface looper two",dummy_looper)
    |> add_looper ("surface looper one",other_looper)
  val loopers_added_pp = pp loopers_added

  val _ = check "looper add updates by name without changing order"
    (fn () =>
       occurrences "surface looper one" loopers_added_pp = 1 andalso
       occurrences "surface looper two" loopers_added_pp = 1 andalso
       (case (position "surface looper one" loopers_added_pp,
              position "surface looper two" loopers_added_pp) of
            (SOME one,SOME two) => one < two
          | _ => false))

  val singleton_looper =
    set_looper ("surface singleton looper",dummy_looper) loopers_added
  val singleton_looper_pp = pp singleton_looper

  val _ = check "set_looper replaces the registered looper list"
    (fn () =>
       occurrences "surface singleton looper" singleton_looper_pp = 1 andalso
       occurrences "surface looper one" singleton_looper_pp = 0 andalso
       occurrences "surface looper two" singleton_looper_pp = 0)

  val no_loopers = del_looper "surface singleton looper" singleton_looper
  val _ = check "del_looper removes a looper by name"
    (fn () =>
       occurrences "surface singleton looper" (pp no_loopers) = 0)

  fun never_solver _ _ =
    raise mk_HOL_ERR "selftest" "never_solver" "not applicable"
  val unsafe_one : Traverse.ssolver =
    {name="surface unsafe one",solve=never_solver}
  val unsafe_duplicate : Traverse.ssolver =
    {name="surface unsafe one",solve=never_solver}
  val safe_one : Traverse.ssolver =
    {name="surface safe one",solve=never_solver}

  val solver_merge_ss =
    empty_ss ++ solver_ss unsafe_one ++ solver_ss unsafe_duplicate
  val solver_merge_data = traversedata_for_ss solver_merge_ss

  val _ = check "solver fragments append and deduplicate by name"
    (fn () =>
       case #solvers solver_merge_data of
           [{name,...}] => name = "surface unsafe one"
         | _ => false)

  val fragment_unsafe : Traverse.ssolver =
    {name="surface fragment unsafe",solve=never_solver}
  val fragment_safe : Traverse.ssolver =
    {name="surface fragment safe",solve=never_solver}
  val strategy_fragment =
    named_merge_ss "surface strategy fragment"
      [looper_ss ("surface fragment looper",dummy_looper),
       solver_ss fragment_unsafe, safe_solver_ss fragment_safe]
  val fragment_set = empty_ss ++ strategy_fragment
  val fragment_removed =
    remove_ssfrags ["surface strategy fragment"] fragment_set
  val fragment_excluded =
    exclude_ssfrags ["surface strategy fragment"] fragment_set
  val replayed_duplicate =
    fragment_set
    |> add_unsafe_solver fragment_unsafe
    |> add_safe_solver fragment_safe
    |> remove_ssfrags ["surface strategy fragment"]
  val replayed_duplicate_data = traversedata_for_ss replayed_duplicate

  val _ = check "history replay retains later duplicate solver additions"
    (fn () =>
       length (#solvers replayed_duplicate_data) = 1 andalso
       occurrences "surface fragment safe" (pp replayed_duplicate) = 1)

  val _ = check "history rebuild removes fragment strategy payloads"
    (fn () =>
       occurrences "surface fragment looper" (pp fragment_removed) = 0 andalso
       occurrences "surface fragment unsafe" (pp fragment_removed) = 0 andalso
       occurrences "surface fragment safe" (pp fragment_removed) = 0 andalso
       occurrences "surface fragment looper" (pp fragment_excluded) = 0 andalso
       occurrences "surface fragment unsafe" (pp fragment_excluded) = 0 andalso
       occurrences "surface fragment safe" (pp fragment_excluded) = 0)

  val both_solvers =
    empty_ss
    |> add_unsafe_solver unsafe_one
    |> add_safe_solver safe_one
  val both_solvers_pp = pp both_solvers

  val _ = check "pp_simpset prints unsafe and safe solver names"
    (fn () =>
       occurrences "surface unsafe one" both_solvers_pp = 1 andalso
       occurrences "surface safe one" both_solvers_pp = 1)

  val removed_solvers = remove_solver "surface unsafe one" both_solvers
  val removed_solvers = remove_solver "surface safe one" removed_solvers

  val _ = check "remove_solver removes names from both solver lists"
    (fn () =>
       occurrences "surface unsafe one" (pp removed_solvers) = 0 andalso
       occurrences "surface safe one" (pp removed_solvers) = 0)

  fun preserving_subgoaler
        ({recurse,...} : Traverse.simp_prover_ctxt) = recurse
  fun reverse_order pair =
    case Cond_rewr.ac_term_ord pair of
        LESS => GREATER
      | EQUAL => EQUAL
      | GREATER => LESS

  val disposable =
    named_rewrites "surface disposable"
      [ASSUME ``surface_disposable_p = T``]
  val configured =
    empty_ss ++ disposable
    |> add_looper ("surface rebuilt looper",dummy_looper)
    |> add_unsafe_solver unsafe_one
    |> add_safe_solver safe_one
    |> set_subgoaler preserving_subgoaler
    |> set_cond_depth 37
    |> set_term_ord reverse_order
  val rebuilt = remove_ssfrags ["surface disposable"] configured
  val rebuilt_data = traversedata_for_ss rebuilt
  val rebuilt_pp = pp rebuilt
  val order_probe = (``surface_order_x:'a``, ``surface_order_y:'a``)
  val subgoal_probe = ``surface_subgoal_x:'a``
  val prover_ctxt =
    {stack=[],context_thms=[],recurse=fn tm => REFL tm}

  val _ = check "remove_ssfrags preserves all strategy fields"
    (fn () =>
       occurrences "surface rebuilt looper" rebuilt_pp = 1 andalso
       occurrences "surface safe one" rebuilt_pp = 1 andalso
       (case #solvers rebuilt_data of
            [{name,...}] => name = "surface unsafe one"
          | _ => false) andalso
       #cond_depth rebuilt_data = SOME 37 andalso
       (case #term_ord rebuilt_data of
            SOME ord => ord order_probe = reverse_order order_probe
          | NONE => false) andalso
       (case #subgoaler rebuilt_data of
            SOME sg =>
              aconv (concl (sg prover_ctxt subgoal_probe))
                    (mk_eq(subgoal_probe,subgoal_probe))
          | NONE => false))

  val cleared = clear_rules configured
  val cleared_data = traversedata_for_ss cleared
  val cleared_pp = pp cleared

  val _ = check "clear_rules drops loopers but keeps strategy and solvers"
    (fn () =>
       occurrences "surface rebuilt looper" cleared_pp = 0 andalso
       occurrences "surface safe one" cleared_pp = 1 andalso
       (case #solvers cleared_data of
            [{name,...}] => name = "surface unsafe one"
          | _ => false) andalso
       #cond_depth cleared_data = SOME 37 andalso
       Option.isSome (#subgoaler cleared_data) andalso
       Option.isSome (#term_ord cleared_data))

  val _ = convtest
    ("clear_rules removes ordinary rewrite rules",
     QCONV (SIMP_CONV (clear_rules bool_ss) []),
     ``surface_clear_p /\ T``, ``surface_clear_p /\ T``)

  val dropping_filter =
    SSFRAG
      {name=SOME "surface dropping filter", convs=[], rewrs=[], ac=[],
       filter=SOME (fn _ => []), dprocs=[], congs=[]}
  val empty_named = name_ss "surface post-clear fragment" empty_ssfrag
  val clear_rebuilt =
    clear_rules (mk_simpset [dropping_filter]) ++ empty_named
    |> remove_ssfrags ["surface post-clear fragment"]
  val clear_rebuilt =
    clear_rebuilt ++
    rewrites [ASSUME ``surface_filtered_x:'a = surface_filtered_y``]

  val _ = convtest
    ("clear_rules preserves mk_rewrs through later history rebuilds",
     QCONV (SIMP_CONV clear_rebuilt []),
     ``surface_filtered_x:'a``, ``surface_filtered_x:'a``)

  val tactic_condition =
    ``surface_solver_x \/ ~surface_solver_x``
  val tactic_rwt =
    ASSUME
      (mk_imp
         (tactic_condition,
          mk_eq(``(surface_solver_f : bool -> 'b) surface_solver_x``,
                ``surface_solver_y:'b``)))
  val tactic_solver =
    mk_tactic_solver
      ("surface tactic solver",
       ACCEPT_TAC
         (SPEC ``surface_solver_x:bool`` boolTheory.EXCLUDED_MIDDLE))
  exception SURFACE_SOLVER_CONTEXT
  val tactic_rewr =
    Cond_rewr.COND_REWR_CONV ("surface tactic rewrite",tactic_rwt) false
  val tactic_reducer =
    Traverse.REDUCER
      {name=SOME "surface tactic reducer", initial=SURFACE_SOLVER_CONTEXT,
       addcontext=fn (ctxt,_) => ctxt,
       apply=fn {solver,stack,...} => tactic_rewr solver stack}
  val tactic_solver_ss =
    pureSimps.pure_ss ++ dproc_ss tactic_reducer
    |> add_unsafe_solver tactic_solver

  val context_fact =
    SPEC ``surface_context_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val context_tactic_solver =
    mk_tactic_solver ("surface context solver",FIRST_ASSUM ACCEPT_TAC)
  val context_result =
    #solve context_tactic_solver
      {stack=[],context_thms=[context_fact],recurse=fn tm => REFL tm}
      (concl context_fact)

  val _ = check "mk_tactic_solver discharges context theorem assumptions"
    (fn () => null (hyp context_result) andalso
              aconv (concl context_result) (concl context_fact))

  val _ = convtest
    ("mk_tactic_solver discharges a SIMP_CONV side condition",
     SIMP_CONV tactic_solver_ss [],
     ``(surface_solver_f : bool -> 'b) surface_solver_x``,
     ``surface_solver_y:'b``)

  val depth_c1 = ``surface_depth_p1 = surface_depth_q1``
  val depth_c2 = ``surface_depth_p2 = surface_depth_q2``
  val depth_c3 = ``surface_depth_p3 = surface_depth_q3``
  val depth_c4 = ``surface_depth_p4 = surface_depth_q4``
  val depth_c5 = ``surface_depth_p5 = surface_depth_q5``
  fun cond_true condition lhs =
    ASSUME (mk_imp(condition,mk_eq(lhs,boolSyntax.T)))
  val depth_lhs = ``(surface_depth_f : 'a -> 'b) surface_depth_x``
  val depth_rhs = ``surface_depth_y:'b``
  val depth_rwts =
    [ASSUME (mk_imp(depth_c1,mk_eq(depth_lhs,depth_rhs))),
     cond_true depth_c2 depth_c1, cond_true depth_c3 depth_c2,
     cond_true depth_c4 depth_c3, cond_true depth_c5 depth_c4,
     ASSUME (mk_eq(depth_c5,boolSyntax.T))]

  val _ = convtest
    ("set_cond_depth configures a simpset invocation",
     SIMP_CONV (set_cond_depth 40 pureSimps.pure_ss) depth_rwts,
     depth_lhs, depth_rhs)

  val _ = convtest
    ("set_term_ord configures permutative rewriting per simpset",
     SIMP_CONV (set_term_ord reverse_order pureSimps.pure_ss)
               [boolTheory.EQ_SYM_EQ],
     ``surface_order_x:'a = surface_order_y``,
     ``surface_order_y:'a = surface_order_x``)

(* ---------------------------------------------------------------------- *)
(* Procedural congruences in simpset fragments.                            *)
(* ---------------------------------------------------------------------- *)

local
  val cond_cong =
    REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO] boolTheory.COND_CONG
  fun equality_refl {arg,...} = REFL arg
  val cond_proc = Opening.CONGPROC equality_refl cond_cong
  val cond_base = pureSimps.pure_ss ++ boolSimps.BOOL_ss
  val cond_tm =
    ``if congproc_p then
        (congproc_f : bool -> 'a) congproc_p
      else congproc_g congproc_p``
  val cond_result =
    ``if congproc_p then
        (congproc_f : bool -> 'a) T
      else congproc_g F``
  val theorem_ss =
    cond_base ++
    SSFRAG
      {name=NONE, convs=[], rewrs=[], ac=[], filter=NONE, dprocs=[],
       congs=[boolTheory.COND_CONG]}
  val proc_frag =
    congproc_ss
      {name="selftest COND procedure", relation=boolSyntax.equality,
       proc=cond_proc}
  val named_proc_frag =
    name_ss "selftest procedural COND fragment" proc_frag
  val procedural_ss = cond_base ++ named_proc_frag
  val disposable =
    name_ss "selftest congproc disposable" empty_ssfrag
  val rebuild_seed = cond_base ++ disposable ++ named_proc_frag
  val removed_rebuild =
    remove_ssfrags ["selftest congproc disposable"] rebuild_seed
  val excluded_rebuild =
    exclude_ssfrags ["selftest congproc disposable"] rebuild_seed
  val wrong_key_calls = ref 0
  fun counted_proc relation args =
    (wrong_key_calls := !wrong_key_calls + 1; cond_proc relation args)
  val wrong_key_ss =
    cond_base ++
    congproc_ss
      {name="selftest wrongly keyed COND procedure",
       relation=boolSyntax.implication, proc=counted_proc}
in
  val _ = convtest
    ("theorem COND congruence reference behavior",
     QCONV (SIMP_CONV theorem_ss []), cond_tm, cond_result)
  val _ = convtest
    ("congproc_ss merges a procedural congruence across ++",
     QCONV (SIMP_CONV procedural_ss []), cond_tm, cond_result)
  val _ = convtest
    ("remove_ssfrags rebuild replays a congproc fragment",
     QCONV (SIMP_CONV removed_rebuild []), cond_tm, cond_result)
  val _ = convtest
    ("exclude_ssfrags rebuild replays a congproc fragment",
     QCONV (SIMP_CONV excluded_rebuild []), cond_tm, cond_result)
  val _ = convtest
    ("congproc_ss keys procedures by relation",
     QCONV (SIMP_CONV wrong_key_ss []), cond_tm, cond_tm)
  val _ =
    (tprint "wrong-relation congproc remains dormant";
     if !wrong_key_calls = 0 then OK()
     else die "wrong-relation congproc was invoked")
end

(* ---------------------------------------------------------------------- *)
(* Tactic-layer solver and looper loop.                                    *)
(* ---------------------------------------------------------------------- *)

local
  fun tactic_result expected result =
    case result of
        Exn.Res (sgs,_) => list_eq goal_eq expected sgs
      | Exn.Exn _ => false
  fun run tac goal = Exn.capture (VALID tac) goal
  fun inc r = r := !r + 1
  fun solver_failure name =
    raise mk_HOL_ERR "selftest" name "not applicable"

  val loop_p = ``loop_p:bool``
  val loop_q = ``loop_q:bool``
  val loop_r = ``loop_r:bool``
  val looper_calls = ref 0
  fun conjunction_looper _ g =
    (inc looper_calls; CONJ_TAC g)
  val solver_calls = ref 0
  fun loop_solver _ tm =
    (inc solver_calls;
     if aconv tm loop_p then ASSUME loop_p
     else solver_failure "loop_solver")
  val loop_ss =
    empty_ss
    |> add_looper ("selftest conjunction",conjunction_looper)
    |> add_unsafe_solver {name="selftest loop solver",solve=loop_solver}
  val loop_result =
    run (GEN_SIMP_TAC {safe=false} loop_ss [markerLib.NoAsms])
        ([loop_p],mk_conj(loop_p,loop_q))

  val _ = tprint "GEN_SIMP_TAC restarts after a looper on every subgoal"
  val _ =
    if tactic_result [([loop_p],loop_q)] loop_result andalso
       !solver_calls = 3 andalso !looper_calls = 2
    then OK()
    else die "looper restart or TRY termination failed"

  val safe_tm =
    ``safe_solver_p \/ ~safe_solver_p``
  val unsafe_tm =
    ``unsafe_solver_p \/ ~unsafe_solver_p``
  val safe_th = SPEC ``safe_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val unsafe_th =
    SPEC ``unsafe_solver_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val safe_calls = ref 0
  val unsafe_calls = ref 0
  fun exact_solver calls th _ tm =
    (inc calls;
     if aconv tm (concl th) then th
     else solver_failure "exact_solver")
  val selection_ss =
    empty_ss
    |> add_safe_solver
         {name="selftest safe",solve=exact_solver safe_calls safe_th}
    |> add_unsafe_solver
         {name="selftest.unsafe.solver",
          solve=exact_solver unsafe_calls unsafe_th}

  val _ = tprint "GEN_SIMP_TAC safe mode selects only safe final solvers"
  val _ =
    if tactic_result []
         (run (GEN_SIMP_TAC {safe=true} selection_ss []) ([],safe_tm))
       andalso !safe_calls = 1 andalso !unsafe_calls = 0
    then OK()
    else die "safe mode selected the wrong final-solver list"

  val _ = tprint "GEN_SIMP_TAC unsafe mode selects only unsafe solvers"
  val _ =
    if tactic_result []
         (run (GEN_SIMP_TAC {safe=false} selection_ss []) ([],unsafe_tm))
       andalso !safe_calls = 1 andalso !unsafe_calls = 1
    then OK()
    else die "unsafe mode selected the wrong final-solver list"

  val _ = tprint "Excl removes a named solver for one invocation"
  val _ =
    if tactic_result [([],unsafe_tm)]
         (run (GEN_SIMP_TAC {safe=false} selection_ss
                            [Excl "selftest.unsafe.solver"])
              ([],unsafe_tm)) andalso
       !unsafe_calls = 1
    then OK()
    else die "Excl did not remove the named solver"

  val context_p = ``final_context_p:bool``
  val context_q = ``final_context_q:bool``
  val context_imp = mk_imp(context_p,context_q)
  val context_calls = ref 0
  fun context_solver {context_thms,...} tm =
    let
      val _ = inc context_calls
      fun find conclusion =
        case List.find (aconv conclusion o concl) context_thms of
            SOME th => th
          | NONE => solver_failure "context_solver"
    in
      if aconv tm context_q then MP (find context_imp) (find context_p)
      else solver_failure "context_solver"
    end
  val context_ss =
    add_unsafe_solver
      {name="selftest final context",solve=context_solver} empty_ss
  val context_result =
    run (GEN_SIMP_TAC {safe=false} context_ss [])
        ([context_p,context_imp],context_q)

  val _ = tprint "final solver sees tactic-layer context theorems"
  val _ =
    if tactic_result [] context_result andalso !context_calls = 1
    then OK()
    else die "final solver could not prove the goal from assumptions"

  val global_p = ``global_context_x = global_context_x``
  val global_pth = REFL ``global_context_x:'a``
  val global_q = ``global_context_q \/ ~global_context_q``
  val global_qth =
    SPEC ``global_context_q:bool`` boolTheory.EXCLUDED_MIDDLE
  val global_impth = DISCH global_p (ADD_ASSUM global_p global_qth)
  val global_context_calls = ref 0
  fun global_context_solver {context_thms,...} tm =
    let
      val _ = inc global_context_calls
      fun find conclusion =
        case List.find (aconv conclusion o concl) context_thms of
            SOME th => th
          | NONE => solver_failure "global_context_solver"
    in
      if aconv tm global_q then MP (find (concl global_impth))
                                  (find global_p)
      else solver_failure "global_context_solver"
    end
  val global_context_ss =
    add_unsafe_solver
      {name="selftest global context",solve=global_context_solver} empty_ss
  val global_cfg =
    {droptrues=true,elimvars=false,strip=true,oldestfirst=true}
  val global_context_result =
    run (global_simp_tac global_cfg global_context_ss
                         [global_pth,global_impth])
        ([],global_q)

  val _ = tprint "global_simp_tac final solver sees supplied theorems"
  val _ =
    if tactic_result [] global_context_result andalso
       !global_context_calls = 1
    then OK()
    else die "global_simp_tac lost the final solver context"

  val entry_looper_ss =
    add_looper ("selftest.entry.conjunction",fn _ => CONJ_TAC) empty_ss
  val entry_goal = ([],mk_conj(loop_p,loop_q))
  val entry_subgoals = [([],loop_p),([],loop_q)]

  val _ = tprint "FULL_SIMP_TAC runs loopers in its final goal step"
  val _ =
    if tactic_result entry_subgoals
         (run (FULL_SIMP_TAC entry_looper_ss []) entry_goal)
    then OK()
    else die "FULL_SIMP_TAC did not use GEN_SIMP_TAC"

  val _ = tprint "global_simp_tac runs loopers in its final goal step"
  val _ =
    if tactic_result entry_subgoals
         (run (global_simp_tac global_cfg entry_looper_ss []) entry_goal)
    then OK()
    else die "global_simp_tac did not use GEN_SIMP_TAC"

  val _ = tprint "Excl removes a named looper for one invocation"
  val _ =
    if tactic_result [entry_goal]
         (run (SIMP_TAC entry_looper_ss
                        [Excl "selftest.entry.conjunction"])
              entry_goal)
    then OK()
    else die "Excl did not remove the named looper"

  val bounded_calls = ref 0
  fun bounded_conjunction_looper _ g =
    (inc bounded_calls; CONJ_TAC g)
  val bounded_ss =
    empty_ss
    |> add_looper ("selftest bounded conjunction",
                   bounded_conjunction_looper)
    |> limit 1
  val bounded_goal = mk_conj(loop_p,mk_conj(loop_q,loop_r))
  val bounded_result =
    run (GEN_SIMP_TAC {safe=false} bounded_ss [markerLib.NoAsms])
        ([],bounded_goal)

  val _ = tprint "simpset limit bounds successful looper rounds"
  val _ =
    if tactic_result [([],loop_p),([],mk_conj(loop_q,loop_r))]
                     bounded_result andalso
       !bounded_calls = 1
    then OK()
    else die "looper ignored the simpset round limit"

  fun legacy_asm_simp_tac ss ths =
    markerLib.process_taclist_then {arg=ths}
      (CONV_TAC o SIMP_CONV ss)
  fun theorem_eq th1 th2 =
    aconv (concl th1) (concl th2) andalso
    list_eq aconv (hyp th1) (hyp th2)
  fun compare_tactics tac1 tac2 goal =
    let
      val (sgs1,vf1) = tac1 goal
      val (sgs2,vf2) = tac2 goal
      val same_goals = list_eq goal_eq sgs1 sgs2
      val th1 = vf1 (map mk_thm sgs1)
      val th2 = vf2 (map mk_thm sgs2)
    in
      same_goals andalso theorem_eq th1 th2
    end
  val zero_goal =
    ([``zero_x = F``],``zero_pred (zero_x:bool):bool``)

  val _ = tprint "empty hooks preserve legacy ASM_SIMP_TAC theorems"
  val _ =
    if compare_tactics
         (legacy_asm_simp_tac bool_ss [])
         (ASM_SIMP_TAC bool_ss []) zero_goal
    then OK()
    else die "ASM_SIMP_TAC changed with empty strategy hooks"

  val _ = tprint "empty hooks preserve legacy SIMP_TAC theorems"
  val _ =
    if compare_tactics
         (legacy_asm_simp_tac bool_ss [markerLib.NoAsms])
         (SIMP_TAC bool_ss []) zero_goal
    then OK()
    else die "SIMP_TAC changed with empty strategy hooks"
in
end

(* ---------------------------------------------------------------------- *)
(* Splitter core: conclusion and assumption splits.                       *)

val mk_asm_split = splitLib.mk_asm_split

fun has_double_neg tm =
  can (find_term (fn subtm =>
    is_neg subtm andalso is_neg (dest_neg subtm))) tm

fun goal_has_double_neg (asms, concl) =
  List.exists has_double_neg (concl :: asms)

val _ = let
  val if_split = TypeBase.case_pred_imp_of ``:bool``
  val if_asm_split =
    mk_asm_split (TypeBase.case_pred_disj_of ``:bool``)
  val split_parameter = ``split_parameter:bool``
  val parameterised_if_asm_split =
    TypeBase.case_pred_disj_of ``:bool``
      |> GEN split_parameter
      |> mk_asm_split
  val expected_parameterised_if_asm_split = GEN split_parameter if_asm_split

  val _ = tprint "splitter: predicate need not be the first quantifier"
  val _ =
    if aconv (concl parameterised_if_asm_split)
             (concl expected_parameterised_if_asm_split)
    then OK()
    else die "mk_asm_split specialised the wrong quantified variable"

  val _ = convtest
    ("splitter: conditional",
     SPLIT_CONV [if_split],
     ``P (if b then x:'a else y) : bool``,
     ``(b ==> P (x:'a)) /\ (~b ==> P y)``)

  val _ = convtest
    ("splitter: conditional under a referenced forall binder",
     SPLIT_CONV [if_split],
     ``!z:'a. P z (if Q z then x:'b else y)``,
     ``!z:'a. (Q z ==> P z (x:'b)) /\ (~Q z ==> P z y)``)

  val _ = convtest
    ("splitter: unreferenced binder remains in the context",
     SPLIT_CONV [if_split],
     ``!z:'a. P (if b then x:'b else y) z``,
     ``(b ==> !z:'a. P (x:'b) z) /\
       (~b ==> !z:'a. P (y:'b) z)``)

  val _ = convtest
    ("splitter: all alpha-equivalent occurrences are replaced",
     SPLIT_CONV [if_split],
     ``P (if b then (\z:'a. z) else f) /\
       Q (if b then (\w:'a. w) else f)``,
     ``(b ==> P (\z:'a. z) /\ Q (\w:'a. w)) /\
       (~b ==> P f /\ Q f)``)

  val _ = convtest
    ("splitter: outermost pack is selected first",
     SPLIT_CONV [if_split],
     ``P (if (if b then c else d) then x:'a else y) : bool``,
     ``((if b then c else d) ==> P (x:'a)) /\
       (~(if b then c else d) ==> P y)``)

  val _ = convtest
    ("splitter: one split per conversion invocation",
     SPLIT_CONV [if_split],
     ``P (if b then x:'a else y) /\ Q (if c then u else v)``,
     ``(b ==> P (x:'a) /\ Q (if c then u else v)) /\
       (~b ==> P y /\ Q (if c then u else v))``)

  val generic_k_split =
    GEN_ALL (REFL ``P (K (x:'a) (y:'b)) : bool``)
  val bool_k_split =
    INST_TYPE [alpha |-> bool, beta |-> bool] generic_k_split
  val _ = convtest
    ("splitter: distinct constant type shapes are not merged",
     SPLIT_CONV [bool_k_split, generic_k_split],
     ``P (K T (f:bool -> bool)) : bool``,
     ``P (K T (f:bool -> bool)) : bool``)

  val _ = shouldfail
    {testfn=fn () => SPLIT_CONV [REFL ``P (if b then x else y)``],
     printresult=K "unexpected conversion",
     printarg=K "splitter rejects a rule with a free context variable",
     checkexn=fn HOL_ERR _ => true | _ => false} ()

  val _ = shouldfail
    {testfn=fn () => SPLIT_CONV [boolTheory.TRUTH],
     printresult=K "unexpected conversion",
     printarg=K "splitter rejects a non-equational rule",
     checkexn=fn HOL_ERR _ => true | _ => false} ()

  val _ = shouldfail
    {testfn=SPLIT_CONV [if_split],
     printresult=thm_to_string,
     printarg=K "splitter rejects a partial case application",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ``P (COND b) : bool``

  val _ = shouldfail
    {testfn=SPLIT_CONV [if_split],
     printresult=thm_to_string,
     printarg=K "splitter enforces the binder-body type test",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ``P (\z:'a. if Q z then x:'b else y) : bool``

  val tactic_goal =
    ([], ``P (if b then x:'a else y) : bool``)
  val tactic_result =
    ``(b ==> P (x:'a)) /\ (~b ==> P y)``
  val _ = tprint "splitter: SPLIT_TAC performs one conclusion split"
  val _ =
    case #1 (VALID (SPLIT_TAC [if_split]) tactic_goal) of
        [([], result)] =>
          if aconv result tactic_result then OK()
          else die "SPLIT_TAC produced the wrong conclusion"
      | _ => die "SPLIT_TAC produced the wrong subgoals"

  fun has asm asms = List.exists (aconv asm) asms
  val asm_goal =
    ([``R (if b then x:'a else y) : bool``], ``G:bool``)
  val _ =
    tprint "splitter: conditional assumption split has clean cases"
  val _ =
    case #1
      (VALID (SPLIT_ASM_TAC [if_split, if_asm_split]) asm_goal) of
        [(left, left_concl), (right, right_concl)] =>
          if aconv left_concl ``G:bool`` andalso
             aconv right_concl ``G:bool`` andalso
             has ``b:bool`` left andalso
             has ``R (x:'a) : bool`` left andalso
             has ``~b`` right andalso
             has ``R (y:'a) : bool`` right andalso
             not (goal_has_double_neg (left, left_concl)) andalso
             not (goal_has_double_neg (right, right_concl))
          then OK()
          else die "SPLIT_ASM_TAC produced incorrect conditional cases"
      | _ => die "SPLIT_ASM_TAC produced the wrong number of cases"

  val double_neg_goal =
    ([``~~R (if b then x:'a else y) : bool``], ``G:bool``)
  val _ =
    tprint "splitter: cleanup preserves a doubly negated assumption lhs"
  val _ =
    case #1 (VALID (SPLIT_ASM_TAC [if_asm_split]) double_neg_goal) of
        [left, right] =>
          if not (goal_has_double_neg left) andalso
             not (goal_has_double_neg right)
          then OK()
          else die "SPLIT_ASM_TAC retained a double negation"
      | _ => die "doubly negated assumption produced the wrong cases"

  val order_goal =
    ([``R (if b then x:'a else y) : bool``],
     ``Q (if c then u:'b else v) : bool``)
  val order_result =
    ``(c ==> Q (u:'b)) /\ (~c ==> Q v)``
  val _ = tprint "splitter: SPLIT_TAC prefers conclusion rules"
  val _ =
    case #1
      (VALID (SPLIT_TAC [if_asm_split, if_split]) order_goal) of
        [(asms, result)] =>
          if aconv result order_result andalso
             has ``R (if b then x:'a else y) : bool`` asms
          then OK()
          else die "SPLIT_TAC did not prefer the conclusion"
      | _ => die "SPLIT_TAC split an assumption before the conclusion"

  val _ = shouldfail
    {testfn= #1 o VALID (SPLIT_ASM_TAC [if_split]),
     printresult=K "unexpected tactic result",
     printarg=K "splitter: rhs shape routes conclusion rules away from asms",
     checkexn=fn HOL_ERR _ => true | _ => false}
    asm_goal

  val _ = shouldfail
    {testfn= #1 o VALID (SPLIT_ASM_TAC [if_asm_split]),
     printresult=K "unexpected tactic result",
     printarg=K "splitter: first syntactic assumption match is selected",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ([``COND b = (f:'a -> 'a -> 'a)``,
      ``R (if b then x:'a else y) : bool``], ``G:bool``)

  val _ = shouldfail
    {testfn= #1 o VALID (SPLIT_TAC [if_split, if_asm_split]),
     printresult=K "unexpected tactic result",
     printarg=K "splitter: SPLIT_TAC fails when nothing splits",
     checkexn=fn HOL_ERR _ => true | _ => false}
    ([], ``R (z:'a) : bool``)
in
end

(* ---------------------------------------------------------------------- *)
(* Splitter integration: registration, caching, fragment, and rule APIs.  *)

val _ = let
  val if_split = type_split_of ``:bool``
  val if_split_again = type_split_of ``:bool``
  val if_asm_split = type_asm_split_of ``:bool``
  val if_asm_split_again = type_asm_split_of ``:bool``
  val named_if_split =
    Feedback.quiet_messages save_thm
      ("simp_split_selftest_rule", if_split)
  val named_if_asm_split =
    Feedback.quiet_messages save_thm
      ("simp_split_selftest_asm_rule",
       mk_asm_split (TypeBase.case_pred_disj_of ``:bool``))

  val _ = tprint "split settype and attribute are registered"
  val _ =
    if List.exists (equal "split") (ThmSetData.all_set_types ()) andalso
       ThmAttribute.is_attribute "split"
    then OK()
    else die "split registration is absent"

  val _ = tprint "datatype split cache returns the same rules twice"
  val _ =
    if aconv (concl if_split) (concl if_split_again) andalso
       aconv (concl if_asm_split) (concl if_asm_split_again)
    then OK()
    else die "cached datatype splits changed"

  val split_goal =
    ([], ``P (if b then x:'a else y) : bool``)
  val split_result =
    ``(b ==> P (x:'a)) /\ (~b ==> P y)``
  val _ = tprint "split_ss splits a conditional in the conclusion"
  val _ =
    case #1 (VALID (SIMP_TAC (bool_ss ++ split_ss) []) split_goal) of
        [([], result)] =>
          if not (aconv result (#2 split_goal)) andalso
             not (can (find_term is_cond) result)
          then OK()
          else die "split_ss did not eliminate the conditional"
      | _ => die "split_ss produced the wrong conditional subgoals"

  val typebase_asm_goal =
    ([``P (if b then x:'a else y) : bool``], ``G:bool``)
  fun clean_asm_goal (asms, goal) =
    not (List.exists (can (find_term is_cond)) (goal :: asms)) andalso
    not (goal_has_double_neg (asms, goal))
  val _ = tprint "split_ss uses TypeBase splits in assumptions"
  val _ =
    case #1
      (VALID (SIMP_TAC (bool_ss ++ split_ss) []) typebase_asm_goal) of
        [goal1, goal2] =>
          if List.all clean_asm_goal [goal1, goal2] then OK()
          else die "TypeBase assumption split retained conditional syntax"
      | _ => die "TypeBase assumption split produced the wrong subgoals"

  val _ = convtest
    ("split_ss cases_simp collapses a trivial split",
     SIMP_CONV (empty_ss ++ split_ss) [],
     ``(b ==> t) /\ (~b ==> t)``,
     ``t:bool``)

  val with_split = add_split named_if_split bool_ss
  val without_split =
    del_split (Theory.current_theory () ^ "$simp_split_selftest_rule")
      with_split
  val _ = tprint "add_split installs a conclusion looper by theorem name"
  val _ =
    case #1 (VALID (SIMP_TAC with_split []) split_goal) of
        [([], result)] =>
          if aconv result split_result then OK()
          else die "add_split installed the wrong looper"
      | _ => die "add_split produced the wrong subgoals"

  val _ = tprint "del_split removes a conclusion looper by theorem name"
  val _ =
    case #1 (VALID (SIMP_TAC without_split []) split_goal) of
        [([], result)] =>
          if aconv result (#2 split_goal) then OK()
          else die "del_split left the conclusion looper active"
      | _ => die "del_split produced the wrong subgoals"

  val _ = tprint "Split installs a split for one invocation"
  val _ =
    case #1 (VALID (SIMP_TAC bool_ss [Split named_if_split]) split_goal) of
        [([], result)] =>
          if not (aconv result (#2 split_goal)) andalso
             not (can (find_term is_cond) result)
          then OK()
          else die "Split did not install its per-invocation rule"
      | _ => die "Split produced the wrong subgoals"

  val split_name =
    "split " ^ Theory.current_theory () ^ "$simp_split_selftest_rule"
  val _ = tprint "Excl suppresses a named split looper"
  val _ =
    case #1
      (VALID (SIMP_TAC with_split [Excl split_name]) split_goal) of
        [([], result)] =>
          if aconv result (#2 split_goal) then OK()
          else die "Excl left the named split looper active"
      | _ => die "named split exclusion produced the wrong subgoals"

  val _ = tprint "Excl split.case suppresses TypeBase splits"
  val _ =
    case #1
      (VALID (SIMP_TAC (bool_ss ++ split_ss)
                       [Excl "split.case bool"]) split_goal) of
        [([], result)] =>
          if aconv result (#2 split_goal) then OK()
          else die "split.case exclusion left the TypeBase split active"
      | _ => die "TypeBase split exclusion produced the wrong subgoals"

  val limited_split_ss = limit 1 (bool_ss ++ split_ss)
  val limited_goal =
    ([], ``P (if b then x:'a else y) /\
           Q (if c then u:'b else v)``)
  val _ = tprint "simpset limit bounds splitter rounds"
  val _ =
    case #1 (VALID (SIMP_TAC limited_split_ss []) limited_goal) of
        [(_,result)] =>
          if not (aconv result (#2 limited_goal)) andalso
             can (find_term is_cond) result
          then OK()
          else die "splitter limit did not stop after one round"
      | _ => die "bounded splitter produced the wrong subgoals"

  val asm_goal =
    ([``P (if b then x:'a else y) : bool``], ``G:bool``)
  val with_asm_split = add_split named_if_asm_split bool_ss
  val _ = tprint "add_split auto-routes an assumption split rule"
  val _ =
    case #1 (VALID (SIMP_TAC with_asm_split []) asm_goal) of
        [_, _] => OK()
      | _ => die "assumption split rule was not routed to the asm looper"
in
  ()
end

(* ---------------------------------------------------------------------- *)
(* Mutual global simplification and extended fixpoint controls.            *)

val _ = let
  val base_cfg =
    {droptrues=true,elimvars=false,strip=false,oldestfirst=true}
  fun mode_xcfg mode concl rebuild =
    GEN_GLOBAL_SIMP_TAC mode
      {base=base_cfg,concl_in_fixpoint=concl,imp_rebuild=rebuild}
  val xcfg = mode_xcfg {safe=false}
  fun result tac goal = #1 (VALID tac goal)
  fun check msg expected tac goal =
    let val _ = tprint msg
    in
      case result tac goal of
          actual =>
            if list_eq goal_eq expected actual then OK()
            else die (msg ^ " produced " ^
                      String.concatWith ", " (map printgoal actual))
    end

  val mutual_goal =
    ([``P (a:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)
  val mutual_expected =
    [([``P (b:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)]
  val _ =
    check "GEN_GLOBAL_SIMP_TAC uses later assumptions mutually"
      mutual_expected
      (xcfg false false bool_ss []) mutual_goal

  val chain_goal =
    ([``(f:'a -> 'b) x = g x``, ``(g:'a -> 'b) x = z``,
      ``R ((f:'a -> 'b) x) : bool``], ``chain_s:bool``)
  val chain_expected =
    [([``(f:'a -> 'b) x = z``, ``(g:'a -> 'b) x = z``,
       ``R (z:'b) : bool``], ``chain_s:bool``)]
  val _ =
    check "GEN_GLOBAL_SIMP_TAC closes a three-assumption mutual chain"
      chain_expected
      (xcfg false false bool_ss []) chain_goal

  val mode_goal =
    ([``global_mode_assumption:bool``],``?b:bool. b``)
  val mode_ss =
    add_unsafe_solver
      (mk_tactic_solver
         ("global unsafe instantiation",
          Q.EXISTS_TAC `T` THEN ACCEPT_TAC TRUTH))
      empty_ss
  val safe_mode_result =
    result (mode_xcfg {safe=true} true false mode_ss []) mode_goal
  val unsafe_mode_result =
    result (xcfg true false mode_ss []) mode_goal
  val _ =
    tprint "safe global simp does not use unsafe final instantiation"
  val _ =
    if list_eq goal_eq [mode_goal] safe_mode_result andalso
       null unsafe_mode_result
    then OK()
    else die "global simp mode selected the wrong final-solver list"

  val side_condition =
    ``global_safe_side_p \/ ~global_safe_side_p``
  val side_condition_th =
    SPEC ``global_safe_side_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val side_lhs =
    ``if global_safe_side_p \/ ~global_safe_side_p
      then global_safe_side_x:'a
      else global_safe_side_y``
  val side_rhs = ``global_safe_side_x:'a``
  val side_rule =
    DISCH side_condition
      (REWRITE_CONV [ASSUME side_condition] side_lhs)
  val side_solver_calls = ref 0
  fun side_solver _ tm =
    (side_solver_calls := !side_solver_calls + 1;
     if aconv tm side_condition then side_condition_th
     else
       raise mk_HOL_ERR "selftest" "side_solver"
                         "not the global safe side condition")
  val side_ss =
    empty_ss ++ rewrites [side_rule]
    |> add_unsafe_solver
         {name="global safe traversal side condition",solve=side_solver}
  val side_goal = ([],mk_comb(``global_safe_side_Q:'a -> bool``,side_lhs))
  val side_expected =
    [([],mk_comb(``global_safe_side_Q:'a -> bool``,side_rhs))]
  val _ =
    check "safe global simp uses unsafe traversal side-condition solvers"
      side_expected
      (mode_xcfg {safe=true} false false side_ss [])
      side_goal
  val _ =
    if !side_solver_calls > 0 then ()
    else die "safe global simp skipped the traversal side-condition solver"

  val schedule_a = ``schedule_a:bool``
  val schedule_b0 = ``schedule_b /\ T``
  val schedule_b1 = ``schedule_b:bool``
  val schedule_c = ``schedule_c:bool``
  val schedule_calls = Array.array (4,0)
  fun increment i =
    Array.update (schedule_calls,i,Array.sub (schedule_calls,i) + 1)
  fun schedule_conv _ _ tm =
    if aconv tm schedule_a then (increment 0; NO_CONV tm)
    else if aconv tm schedule_b0 then
      (increment 1; REWRITE_CONV [boolTheory.AND_CLAUSES] tm)
    else if aconv tm schedule_b1 then (increment 2; NO_CONV tm)
    else if aconv tm schedule_c then (increment 3; NO_CONV tm)
    else NO_CONV tm
  val schedule_ss =
    empty_ss ++
    conv_ss {name="global schedule probe",key=NONE,trace=0,
             conv=schedule_conv}
  val schedule_goal =
    ([schedule_a,schedule_b0,schedule_c], ``schedule_goal:bool``)
  val schedule_expected =
    [([schedule_a,schedule_b1,schedule_c], ``schedule_goal:bool``)]
  val schedule_result =
    result (xcfg false false schedule_ss []) schedule_goal
  val _ = tprint "global change counting skips the provably-fixed tail"
  val _ =
    if list_eq goal_eq schedule_expected schedule_result andalso
       List.tabulate (4,fn i => Array.sub (schedule_calls,i)) = [1,1,1,2]
    then OK()
    else die "global change-count schedule did not skip the fixed tail"

  val conclusion_calls = ref 0
  fun conclusion_probe _ _ tm =
    if aconv tm (#2 schedule_goal) then
      (conclusion_calls := !conclusion_calls + 1; NO_CONV tm)
    else NO_CONV tm
  val per_pass_ss =
    schedule_ss ++
    conv_ss {name="global conclusion pass probe",key=NONE,trace=0,
             conv=conclusion_probe}
  val _ =
    result (xcfg true false per_pass_ss []) schedule_goal
  val _ = tprint "concl_in_fixpoint simplifies the conclusion each pass"
  val _ =
    if !conclusion_calls = 2 then OK()
    else die "conclusion was not simplified on every assumption pass"

  val noop_a = ``global_noop_a:bool``
  val noop_nested = ref false
  fun noop_conv _ _ tm =
    if aconv tm noop_a then
      if !noop_nested then (noop_nested := false; NO_CONV tm)
      else
        let
          val _ = noop_nested := true
          val collapse =
            REWRITE_CONV [boolTheory.AND_CLAUSES]
                         (mk_conj (noop_a,boolSyntax.T))
        in
          SYM collapse
        end
    else NO_CONV tm
  val noop_ss =
    empty_ss ++
    conv_ss {name="global net-noop probe",key=NONE,trace=0,
             conv=noop_conv}
  val noop_cfg =
    {droptrues=true,elimvars=false,strip=true,oldestfirst=true}
  val _ =
    check "global structural net-noop pass terminates"
      [([noop_a],``global_noop_goal:bool``)]
      (GEN_GLOBAL_SIMP_TAC
         {safe=false}
         {base=noop_cfg,concl_in_fixpoint=false,imp_rebuild=false}
         noop_ss [])
      ([noop_a],``global_noop_goal:bool``)

  val fix_asm0 = ``fix_asm_p /\ T``
  val fix_asm1 = ``fix_asm_p:bool``
  val fix_concl0 = ``fix_concl_p /\ T``
  val fix_concl1 = ``fix_concl_p:bool``
  val unlocked = ref false
  fun gate_conv _ _ tm =
    if aconv tm fix_concl0 then
      (unlocked := true; REWRITE_CONV [boolTheory.AND_CLAUSES] tm)
    else if !unlocked andalso aconv tm fix_asm0 then
      REWRITE_CONV [boolTheory.AND_CLAUSES] tm
    else NO_CONV tm
  val gate_ss =
    empty_ss ++
    conv_ss {name="global conclusion gate",key=NONE,trace=0,
             conv=gate_conv}
  val gate_goal = ([fix_asm0],fix_concl0)
  val _ = unlocked := false
  val _ =
    check "default global simplification keeps conclusion outside fixpoint"
      [([fix_asm0],fix_concl1)]
      (xcfg false false gate_ss []) gate_goal
  val _ = unlocked := false
  val _ =
    check "concl_in_fixpoint restarts changed assumptions"
      [([fix_asm1],fix_concl1)]
      (xcfg true false gate_ss []) gate_goal

  val once_p = ``global_once_p:bool``
  val once_rule = CONJUNCT1 (SPEC once_p boolTheory.AND_CLAUSES)
  val once_goal = ([],mk_conj(boolSyntax.T,mk_conj(boolSyntax.T,once_p)))
  val _ =
    check "global supplied Once rewrite is installed exactly once"
      [([],mk_conj(boolSyntax.T,once_p))]
      (xcfg false false empty_ss [Once once_rule])
      once_goal

  val once_asm_p = ``global_once_asm_p:bool``
  val once_concl_p = ``global_once_concl_p:bool``
  val once_across_goal =
    ([mk_conj(boolSyntax.T,once_asm_p)],
     mk_conj(boolSyntax.T,once_concl_p))
  val _ =
    check "global supplied Once lifetime spans assumptions and conclusion"
      [([once_asm_p],mk_conj(boolSyntax.T,once_concl_p))]
      (xcfg false false empty_ss [Once once_rule])
      once_across_goal

  val local_exclsf = concl (ExclSF "BOOL")
  val local_exclsf_target = ``T /\ global_local_exclsf_p``
  (* The target is popped first, leaving ExclSF in the local context. *)
  val local_exclsf_goal =
    ([local_exclsf,local_exclsf_target],``global_local_exclsf_q:bool``)
  val _ =
    check "global remaining ExclSF applies while simplifying assumptions"
      [local_exclsf_goal]
      (xcfg false false bool_ss [])
      local_exclsf_goal

  val once_exclsf_asm = ``T /\ global_once_exclsf_asm_p``
  val once_exclsf_concl = ``T /\ global_once_exclsf_concl_p``
  val once_exclsf_goal =
    ([local_exclsf,once_exclsf_asm],once_exclsf_concl)
  val _ =
    check "global ExclSF rebuild preserves supplied Once lifetime"
      [([local_exclsf,``global_once_exclsf_asm_p:bool``],
         once_exclsf_concl)]
      (xcfg false false bool_ss [Once once_rule])
      once_exclsf_goal

  val supplied_sentinel = REFL ``global_supplied_sentinel:'a``
  fun has_only_untagged_sentinel thms =
    let
      val sentinels =
        List.filter
          (fn th => aconv (concl th) (concl supplied_sentinel))
          thms
    in
      not (null sentinels) andalso
      List.all (not o can BoundedRewrites.DEST_BOUNDED) sentinels
    end
  val supplied_condition =
    SPEC ``global_traversal_p:bool`` boolTheory.EXCLUDED_MIDDLE
  val supplied_solver_calls = ref 0
  fun supplied_solver {context_thms,...} tm =
    let
      val has_sentinel = has_only_untagged_sentinel context_thms
      val _ = supplied_solver_calls := !supplied_solver_calls + 1
    in
      if aconv tm (concl supplied_condition) andalso has_sentinel then
        supplied_condition
      else
        raise mk_HOL_ERR "selftest" "supplied_solver"
                          "supplied theorem absent from traversal context"
    end
  val supplied_tm = concl supplied_condition
  val supplied_rule =
    DISCH supplied_tm (EQT_INTRO (ASSUME supplied_tm))
  val supplied_ss =
    empty_ss ++ rewrites [supplied_rule]
    |> add_unsafe_solver
         {name="global supplied traversal context",solve=supplied_solver}
  val _ = supplied_solver_calls := 0
  val _ =
    check "global traversals see supplied source theorem without bound tag"
      []
      (xcfg false false supplied_ss [Once supplied_sentinel])
      ([supplied_tm],supplied_tm)
  val _ =
    if !supplied_solver_calls >= 2 then ()
    else die "global assumption or conclusion traversal skipped its solver"

  val root_target = ``root_a ==> root_b``
  val root_result = ``root_c ==> root_d``
  val root_condition = ``(root_side_P:bool -> bool) (T /\ T)``
  val root_rule =
    ASSUME (mk_imp (root_condition,mk_eq (root_target,root_result)))
  val root_context = ASSUME ``(root_side_P:bool -> bool) T``
  val root_ss =
    pureSimps.pure_ss ++ rewrites [boolTheory.AND_CLAUSES,root_rule]
  val _ = convtest
    ("root rewriting fully simplifies conditional-rule side conditions",
     Traverse.ROOT_REWRITE (traversedata_for_ss root_ss) [root_context],
     root_target,root_result)

  val imp_goal = ([``imp_p:bool``],``imp_q:bool``)
  val imp_ss =
    empty_ss ++ rewrites [Once (GSYM boolTheory.CONTRAPOS_THM)]
  val _ =
    check "imp_rebuild rewrites a discharged assumption at the root"
      [([``~imp_q``],``~imp_p``)]
      (xcfg false true imp_ss []) imp_goal

  val excluded_imp_name = "global excluded implication rebuild"
  val excluded_imp_marker = concl (ExclSF excluded_imp_name)
  val excluded_imp_target = ``excluded_imp_a ==> excluded_imp_q``
  fun excluded_imp_conv _ _ tm =
    if aconv tm excluded_imp_target then
      REWR_CONV (GSYM boolTheory.CONTRAPOS_THM) tm
    else NO_CONV tm
  val excluded_imp_ss =
    empty_ss ++
    name_ss excluded_imp_name
      (conv_ss
         {name=excluded_imp_name,key=SOME ([],excluded_imp_target),trace=0,
          conv=excluded_imp_conv})
  val excluded_imp_goal =
    ([``excluded_imp_a:bool``,excluded_imp_marker],
     ``excluded_imp_q:bool``)
  val _ =
    check "imp_rebuild applies remaining ExclSF before root rewriting"
      [excluded_imp_goal]
      (xcfg false true excluded_imp_ss [])
      excluded_imp_goal

  val supplied_imp_target =
    ``global_supplied_imp_a ==> global_supplied_imp_b``
  exception SUPPLIED_IMP_CONTEXT of bool
  fun supplied_imp_has_context context =
    (raise context) handle SUPPLIED_IMP_CONTEXT present => present
                         | _ => false
  fun supplied_imp_addcontext (context,thms) =
    let
      val has_source = has_only_untagged_sentinel thms
    in
      SUPPLIED_IMP_CONTEXT
        (supplied_imp_has_context context orelse has_source)
    end
  fun supplied_imp_apply {solver,stack,context,...} tm =
    if aconv tm supplied_imp_target then
      (supplied_imp_has_context context orelse
       raise mk_HOL_ERR "selftest" "supplied_imp_apply"
                         "supplied source theorem absent from dproc context";
       solver stack supplied_tm;
       REWR_CONV (GSYM boolTheory.CONTRAPOS_THM) tm)
    else NO_CONV tm
  val supplied_imp_reducer =
    Traverse.REDUCER
      {name=SOME "global supplied implication rebuild",
       initial=SUPPLIED_IMP_CONTEXT false,
       addcontext=supplied_imp_addcontext,
       apply=supplied_imp_apply}
  val supplied_imp_ss =
    empty_ss ++ dproc_ss supplied_imp_reducer
    |> add_unsafe_solver
         {name="global supplied traversal context",solve=supplied_solver}
  val _ =
    check "imp_rebuild sees supplied theorems in its traversal context"
      [([``~global_supplied_imp_b``],
         ``~global_supplied_imp_a``)]
      (xcfg false true supplied_imp_ss [Once supplied_sentinel])
      ([``global_supplied_imp_a:bool``],
       ``global_supplied_imp_b:bool``)
in
  ()
end

(* These theories are later than simp in the build sequence.  Exercise their
   actual case constants when their already-built objects are available; the
   bool tests above remain the bootstrap regression test for this directory. *)
val _ = let
  fun object_exists path =
    OS.FileSys.access (OS.Path.concat (HOLDIR, path), [])
  val have_datatypes =
    object_exists "sigobj/optionTheory.uo" andalso
    object_exists "sigobj/listTheory.uo"
in
  if not have_datatypes then ()
  else
    let
      val _ = load "optionTheory"
      val option_split = TypeBase.case_pred_imp_of ``:'a option``
      val option_asm_split =
        mk_asm_split (TypeBase.case_pred_disj_of ``:'a option``)
      val _ = convtest
        ("splitter: option case",
         SPLIT_CONV [option_split],
         ``P (option_CASE x (n:'b) (f:'a -> 'b)) : bool``,
         ``(x = NONE ==> P (n:'b)) /\
           !a:'a. x = SOME a ==> P (f a)``)

      val option_asm_goal =
        ([``P (option_CASE x (n:'b) (f:'a -> 'b)) : bool``],
         ``G:bool``)
      val _ = tprint "splitter: option case in an assumption"
      val _ =
        case #1 (VALID (SPLIT_ASM_TAC [option_split, option_asm_split])
                        option_asm_goal) of
            [none_case, some_case] =>
              if not (goal_has_double_neg none_case) andalso
                 not (goal_has_double_neg some_case)
              then OK()
              else die "option assumption split retained double negations"
          | _ => die "option assumption split produced the wrong cases"

      val _ = load "pairTheory"
      val pair_split = TypeBase.case_pred_imp_of ``:'a # 'b``
      val _ = convtest
        ("splitter: Generic.thy Cartesian-product example",
         SPLIT_CONV [pair_split],
         ``P (pair_CASE p (f:'a -> 'b -> 'c)) : bool``,
         ``!a:'a b:'b. p = (a,b) ==> P (f a b)``)

      val _ = load "listTheory"
      val list_split = TypeBase.case_pred_imp_of ``:'a list``
      val _ = convtest
        ("splitter: list case",
         SPLIT_CONV [list_split],
         ``P (list_CASE xs (n:'b)
                        (f:'a -> 'a list -> 'b)) : bool``,
         ``(xs = [] ==> P (n:'b)) /\
           !h:'a t. xs = h::t ==> P (f h t)``)
      val _ = tprint "split_ss splits a list case using TypeBase"
      val list_goal =
        ``P (list_CASE xs (n:'b) (f:'a -> 'a list -> 'b)) : bool``
      val _ =
        case #1
          (VALID (SIMP_TAC (bool_ss ++ split_ss) []) ([], list_goal)) of
            [([], result)] =>
              if not (aconv result list_goal) andalso
                 not (can (find_term TypeBase.is_case) result)
              then OK()
              else die "split_ss did not eliminate the list case"
          | _ => die "split_ss produced the wrong list subgoals"
    in
      ()
    end
end

(* ---------------------------------------------------------------------- *)

val _ = exit_count0 failcount
