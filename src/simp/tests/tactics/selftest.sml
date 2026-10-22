(* Supplemental TASK18 contracts. No extension module or generic marker edits.
   Every returned validation is called with real, oracle-free kernel proofs. *)
open HolKernel Parse boolLib simpLib Paired
val _ = new_theory "task18_tactics"
fun constant s = (new_constant (s,bool); mk_const(s,bool))
val p = constant "tactic_p"
val q = constant "tactic_q"
val r = constant "tactic_r"
val identity = mk_eq (r,r)
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun sound (asl,w) th = aconv w (concl th) andalso
  HOLset.isSubset (hypset th,HOLset.fromList Term.compare asl) andalso
  List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (tag th)))
fun goalsame ((a,w),(b,v)) = aconv w v andalso
  ListPair.allEq (fn (x,y) => aconv x y) (a,b)
fun solve (asl,w) = let
  fun expand th = th ::
    (if is_conj (concl th) then
       expand (CONJUNCT1 th) @ expand (CONJUNCT2 th)
     else case total markerLib.DEST_LABEL th of
         NONE => [] | SOME t => expand t)
  val available = List.concat (map (expand o ASSUME) asl)
  fun prove t = case List.find (fn th => aconv t (concl th)) available of
      SOME th => th
    | NONE => if aconv t T then TRUTH
      else if is_eq t andalso aconv (lhs t) (rhs t) then REFL (lhs t)
      else if is_conj t then CONJ (prove (lhand t)) (prove (rand t))
      else raise Fail "unprovable residual goal"
  val th = prove w
in if sound (asl,w) th then th else raise Fail "invalid residual proof" end
val validations = ref 0
fun apply name tac original expected expectedProof = let
  val (gs,vf) = testutils.runtac tac original
  val correct = ListPair.allEq goalsame (gs,expected)
  val _ = if correct then () else List.app (fn (asl,w) =>
    print ("RESIDUAL " ^ String.concatWith "," (map term_to_string asl) ^
           " |- " ^ term_to_string w ^ "\n")) gs
  val _ = Paired.check (name ^ " goals") correct
  val proofs = map solve gs
  val result = vf proofs
  val _ = validations := !validations + 1
in Paired.check (name ^ " proof")
     (sound original result andalso same (result,expectedProof)) end
fun twice name tac original expected proof =
  (apply (name ^ " first") tac original expected proof;
   apply (name ^ " reused") tac original expected proof)
fun holerror name f = (f (); false) handle HOL_ERR e =>
  Feedback.top_function_of e = name
val labelled = concl (markerLib.MK_LABEL ("p",ASSUME p))
val _ = twice "ASM" (ASM_SIMP_TAC boolSimps.bool_ss []) ([p],p) [] (ASSUME p)
val _ = twice "asm alias" (asm_simp_tac boolSimps.bool_ss [])
  ([p],p) [] (ASSUME p)
val _ = twice "SIMP" (SIMP_TAC boolSimps.bool_ss [])
  ([p],p) [([p],p)] (ASSUME p)
val _ = twice "simp alias" (simp_tac boolSimps.bool_ss [])
  ([p],p) [([p],p)] (ASSUME p)
val _ = twice "NoAsms" (ASM_SIMP_TAC boolSimps.bool_ss [markerLib.NoAsms])
  ([p],p) [([p],p)] (ASSUME p)
val _ = twice "IgnAsm"
  (ASM_SIMP_TAC boolSimps.bool_ss [markerLib.IgnAsm `tactic_p`])
  ([p,q],p) [([p,q],p)] (ASSUME p)
val _ = twice "label explicit despite NoAsms"
  (SIMP_TAC boolSimps.bool_ss [markerSyntax.L "p"]) ([labelled],p) []
  (markerLib.DEST_LABEL (ASSUME labelled))
val _ = Paired.check "ASM missing label is late error"
  (let val saved = ASM_SIMP_TAC empty_ss [markerSyntax.L "absent"]
   in holerror "process_taclist" (fn () =>
        ignore (testutils.runtac saved ([p],p))) end)

(* Unlike TASK05's global route, these paths have independent strip/drop
   and reverse-fold machinery. Ordered branch assumptions are contractual. *)
val fulls = [("full",FULL_SIMP_TAC),("full alias",full_simp_tac),
  ("reverse",REV_FULL_SIMP_TAC),("reverse alias",rev_full_simp_tac)]
val nostrips = [("no-strip full",NO_STRIP_FULL_SIMP_TAC),
  ("no-strip reverse",NO_STRIP_REV_FULL_SIMP_TAC)]
val _ = List.app (fn (name,tac) =>
  twice (name ^ " disjunction") (tac empty_ss [])
    ([mk_disj(p,q)],identity) [([p],identity),([q],identity)]
    (ADD_ASSUM (mk_disj(p,q)) (REFL r))) fulls
val _ = List.app (fn (name,tac) =>
  twice (name ^ " disjunction") (tac empty_ss [])
    ([mk_disj(p,q)],identity) [([mk_disj(p,q)],identity)]
    (ADD_ASSUM (mk_disj(p,q)) (REFL r))) nostrips
val _ = List.app (fn (name,tac) =>
  twice (name ^ " contradiction") (tac empty_ss []) ([F],p) []
    (CONTR p (ASSUME F))) (fulls @ nostrips)

(* Reverse-full changes the direction of assumption dependency propagation,
   not merely the order of the final simplification of the conclusion. *)
val pq = mk_eq(p,q)
val qr = mk_eq(q,r)
val pr = mk_eq(p,r)
val _ = List.app (fn (name,tac,expected) =>
  twice (name ^ " dependency order") (tac empty_ss []) ([pq,qr],identity)
    [(expected,identity)] (ADD_ASSUM pq (ADD_ASSUM qr (REFL r))))
  [("full",FULL_SIMP_TAC,[pq,qr]),
   ("reverse",REV_FULL_SIMP_TAC,[pr,qr]),
   ("no-strip full",NO_STRIP_FULL_SIMP_TAC,[pq,qr]),
   ("no-strip reverse",NO_STRIP_REV_FULL_SIMP_TAC,[pr,qr])]

fun cfg oldest strip drop elim : simptac_config =
  {oldestfirst=oldest,strip=strip,droptrues=drop,elimvars=elim}
val plain = cfg true false false false
val recent = cfg false false false false
val _ = List.app (fn (name,c,used) =>
  twice ("psr " ^ name) (psr c empty_ss) ([p,q],identity)
    [([q,p],identity)] (ADD_ASSUM used (REFL r)))
  [("oldest",plain,q),("newest",recent,p)]
val _ = List.app (fn (name,c) =>
  twice ("allasms " ^ name) (allasms c empty_ss) ([p,q],identity)
    [([p,q],identity)] (ADD_ASSUM p (ADD_ASSUM q (REFL r))))
  [("oldest",plain),("newest",recent)]
val _ = twice "psr drops true" (psr (cfg false false true false) empty_ss)
  ([T,p],identity) [([p],identity)] (REFL r)
val _ = twice "psr strips conjunction"
  (psr (cfg true true false false) empty_ss)
  ([mk_conj(p,q)],identity) [([q,p],identity)]
  (ADD_ASSUM (mk_conj(p,q)) (REFL r))
val x = mk_var("tactic_x",bool)
val xeq = mk_eq(x,T)
val _ = twice "psr eliminates variable"
  (psr (cfg true false false true) empty_ss)
  ([xeq],mk_eq(x,x)) [([],mk_eq(T,T))] (ADD_ASSUM xeq (REFL x))

(* Conversion/rule policy and exact hypotheses; no VALID/oracle surrogate. *)
val rule = REWRITE_CONV [boolTheory.AND_CLAUSES] (mk_conj(p,T))
val hypRule = ADD_ASSUM r rule
val _ = Paired.check "conversion preserves rule hypothesis"
  (same (SIMP_CONV empty_ss [hypRule] (mk_conj(p,T)),hypRule))
val _ = Paired.check "rule preserves rule hypothesis"
  (same (SIMP_RULE empty_ss [hypRule] (ASSUME (mk_conj(p,T))),
    EQ_MP hypRule (ASSUME (mk_conj(p,T)))))
val _ = Paired.check "SIMP_RULE does not import hypotheses"
  (same (SIMP_RULE empty_ss [] (ASSUME p),ASSUME p))
val _ = Paired.check "ASM_SIMP_RULE imports hypotheses"
  (same (ASM_SIMP_RULE boolSimps.bool_ss [] (ASSUME p),ADD_ASSUM p TRUTH))
val _ = Paired.check "SIMP_PROVE real proof"
  (same (SIMP_PROVE boolSimps.bool_ss [] (mk_eq(p,p)),REFL p))
val ignored = [markerLib.NoAsms,markerLib.IgnAsm `tactic_p`,
               markerSyntax.Abbr `absent`,markerSyntax.L "absent"]
val _ = List.app (fn (name,th) =>
  Paired.check ("conversion ignores " ^ name)
    (same (SIMP_CONV empty_ss [th,rule] (mk_conj(p,T)),rule)))
  (ListPair.zip (["NoAsms","IgnAsm","Abbr","label"],ignored))
val _ = List.app (fn (name,wrap) => let
    val saved = SIMP_CONV empty_ss [wrap rule]
    val _ = Paired.check ("conversion rejects " ^ name)
      (holerror "process_tags" (fn () => ignore (saved (mk_conj(p,T)))))
    val _ = Paired.check ("rule rejects " ^ name)
      (holerror "process_tags" (fn () =>
        ignore (SIMP_RULE empty_ss [wrap rule] (ASSUME p))))
  in Paired.check ("installation rejects " ^ name)
      (holerror "process_tags" (fn () => ignore (empty_ss && [wrap rule])))
  end) [("Req0",Req0),("ReqD",ReqD)]

(* Generic wrapper decoding is recursive only via explicit payload inspection.
   The ordinary tactic strips requirements before passing the bounded payload
   to SIMP_CONV; supplied quotas are fresh on saved-tactic reentry. *)
val nested = Req0 (ReqD (BoundedRewrites.Once hypRule))
val _ = Paired.check "nested generic payload and hypotheses"
  (case markerLib.dest_directive nested of
       SOME (markerLib.DReq0 a) =>
       (case markerLib.dest_directive a of
            SOME (markerLib.DReqD b) =>
            (case markerLib.dest_directive b of
                 SOME (markerLib.DBounded (c,1)) => same (c,hypRule)
               | _ => false)
          | _ => false)
     | _ => false)
val _ = twice "nested ASM payload" (ASM_SIMP_TAC boolSimps.bool_ss [nested])
  ([r,p],mk_conj(p,T)) [] (EQ_MP (SYM hypRule) (ASSUME p))
val _ = twice "nested SIMP payload" (SIMP_TAC empty_ss [nested])
  ([r,p],mk_conj(p,T)) [([r,p],p)] (EQ_MP (SYM hypRule) (ASSUME p))

(* Reenter the SAME ordinary tactic after adding a fresh ignored assumption:
   filter again, do not capture the first goal's fact list. *)
val filtered = ASM_SIMP_TAC boolSimps.bool_ss [markerLib.IgnAsm `tactic_p`]
val _ = apply "reentry filtered initial" filtered ([p],p) [([p],p)]
  (ASSUME p)
val _ = apply "reentry filtered new assumption" filtered ([q,p],q) []
  (ASSUME q)
val noasms = ASM_SIMP_TAC boolSimps.bool_ss [markerLib.NoAsms]
val _ = apply "reentry NoAsms initial" noasms ([p],p) [([p],p)] (ASSUME p)
val _ = apply "reentry NoAsms new assumption" noasms
  ([q,p],q) [([q,p],q)] (ASSUME q)

(* Direct ASM/SIMP construct wrappers at application, unlike global/full.
   Freeze this deliberate distinction rather than moving generic marker work. *)
exception PrinterFailure of unit ref
val token = ref ()
val throwing = ref false
val calls = ref 0
fun printer gs be sys (pp : term_pp_types.ppstream_funs) gravs depth t =
  if aconv t (concl rule) then
    (calls := !calls + 1;
     if !throwing then raise PrinterFailure token else #add_string pp "rule")
  else raise term_pp_types.UserPP_Failed
val _ = Parse.temp_add_user_printer ("task18-printer",concl rule,printer)
fun printerError f = (f (); false)
  handle PrinterFailure t => t = token
fun runProof tac original = let
  val (gs,vf) = testutils.runtac tac original
  val th = vf (map solve gs)
  val _ = validations := !validations + 1
in sound original th end
val direct = [("ASM",ASM_SIMP_TAC),("asm alias",asm_simp_tac),
              ("SIMP",SIMP_TAC),("simp alias",simp_tac)]
val _ = List.app (fn (name,tac,early) =>
  List.app (fn (wrapper,wrap,n) => let
    val label = "stage " ^ name ^ " " ^ wrapper
    val arg = [wrap rule]
    val gl = ([p],mk_conj(p,T))
    val _ = throwing := false
    val _ = calls := 0
    val saved = tac empty_ss arg
    val _ = Paired.check (label ^ " construct")
      (!calls = (if early then n else 0))
    val _ = calls := 0
    val _ = Paired.check (label ^ " first proof") (runProof saved gl)
    val _ = Paired.check (label ^ " first callbacks")
      (!calls = (if early then 0 else n))
    val _ = throwing := true
    val _ = calls := 0
    val _ = Paired.check (label ^ " reuse")
      (if early then runProof saved gl andalso !calls = 0
       else printerError (fn () => ignore (testutils.runtac saved gl))
            andalso !calls = 1)
    val _ = calls := 0
    val _ = Paired.check (label ^ " throwing construction")
      (if early then printerError (fn () => ignore (tac empty_ss arg))
                     andalso !calls = 1
       else (ignore (tac empty_ss arg); !calls = 0))
    val _ = throwing := false
  in () end) [("Req0",Req0,1),("ReqD",ReqD,1),
              ("both",Req0 o ReqD,2)])
  (map (fn (n,t) => (n,t,false)) direct @
   map (fn (n,t) => (n,t,true)) (fulls @ nostrips))

(* Executable validator controls: these never supply fake residual proofs. *)
val _ = Paired.check "validator rejects wrong conclusion"
  (not (sound ([p],p) TRUTH))
val _ = Paired.check "validator rejects foreign hypothesis"
  (not (sound ([],p) (ASSUME p)))
val _ = Paired.check "validator rejects oracle"
  (not (sound ([p],p) (mk_oracle_thm "tactics-control" ([p],p))))
val _ = Paired.check "goal comparator detects reversed branches"
  (not (ListPair.allEq goalsame
    ([([p],identity),([q],identity)],[([q],identity),([p],identity)])))
val _ = Paired.observe "validations" (Int.toString (!validations))
val _ = Paired.observe "complete" "TASK18-tactics-v1"
