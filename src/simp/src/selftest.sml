open HolKernel Parse boolLib simpLib
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
  infloop_protect "CONJ_ss with T=F and F=T assumptions (if hangs, it's failed)" check doit t
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
                       strip_tac >- (first_x_assum irule >> ASM_REWRITE_TAC[])>>
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
    ("gs oldestfirst", gs gsc' bool_ss [], ([“x:'a = y”, “x:'a = z”], “p:bool”),
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
end

(* ---------------------------------------------------------------------- *)

val _ = exit_count0 failcount
