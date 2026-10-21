(* Independent staged legacy contracts. Arguments are built before meters.
   No production instrumentation and no oracle subgoal proofs. *)
open HolKernel boolLib simpLib testutils
val _ = new_theory "stagingcontracts"
val cfg = {strip=false, elimvars=false, droptrues=false, oldestfirst=true}
val p = mk_var ("stage_p", bool)
val q = mk_var ("stage_q", bool)
val r = mk_var ("stage_r", bool)
val rule = REWRITE_CONV [boolTheory.AND_CLAUSES] (mk_conj (p,T))
val reqD_rule = ReqD rule
val other = REWRITE_CONV [boolTheory.OR_CLAUSES] (mk_disj (q,F))
val lp = concl (markerLib.MK_LABEL ("p", ASSUME p))
val lq = concl (markerLib.MK_LABEL ("q", ASSUME q))
val basegoal : Abbrev.goal = ([lp,lq,r], mk_conj (p,T))
val unchanged : Abbrev.goal = ([lp,lq,r], mk_eq (p,p))

(* Structural encodings never call a user printer. Hypotheses are sets;
   assumptions/subgoals are ordered lists. No generated pretty names. *)
fun ty t =
  if is_vartype t then "'" ^ dest_vartype t
  else let val {Thy,Tyop,Args} = dest_thy_type t
       in Thy ^ "$" ^ Tyop ^ "[" ^ String.concatWith "," (map ty Args) ^ "]"
       end
fun tm t =
  if is_var t then
    let val (n,t) = dest_var t in "v(" ^ n ^ ":" ^ ty t ^ ")" end
  else if is_const t then
    let val {Thy,Name,Ty} = dest_thy_const t
    in "c(" ^ Thy ^ "$" ^ Name ^ ":" ^ ty Ty ^ ")" end
  else if is_comb t then
    let val (f,x) = dest_comb t in "a(" ^ tm f ^ "," ^ tm x ^ ")" end
  else let val (v,b) = dest_abs t in "l(" ^ tm v ^ "," ^ tm b ^ ")" end
fun terms ts = "[" ^ String.concatWith "," (map tm ts) ^ "]"
fun goal (asl,w) = terms asl ^ "|-" ^ tm w
fun goals gs = String.concatWith ";" (map goal gs)
fun subset xs ys = List.all (fn x => List.exists (aconv x) ys) xs
fun sound (asl,w) th =
  aconv w (concl th) andalso subset (hyp th) asl andalso
  List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (tag th)))

(* Residual goals are genuinely provable from their own assumptions, using
   only kernel rules and label elimination. Failure is a harness failure. *)
fun prove_goal (asl,w) =
  let
    val asms = map ASSUME asl
    val available = asms @ List.mapPartial (total markerLib.DEST_LABEL) asms
    fun prove t =
      case List.find (fn th => aconv t (concl th)) available of
          SOME th => th
        | NONE =>
            if aconv t T then TRUTH
            else if is_conj t then
              let val (a,b) = dest_conj t in CONJ (prove a) (prove b) end
            else if is_eq t andalso aconv (lhs t) (rhs t) then REFL (lhs t)
            else raise Fail ("unprovable residual: " ^ tm t)
    val th = prove w
  in
    if sound (asl,w) th then th else raise Fail "invalid residual proof"
  end

exception PrinterFailure of unit ref
val token = ref ()
val callbacks = ref ([] : string list)
val throwing = ref false
val printer_context : string Context.Data.slot =
  Context.Data.new {name="stagingcontracts.printer", empty="A", pp=I}
fun install_printer grammar =
  let
    fun printer gs be sys (pp : term_pp_types.ppstream_funs) gravs depth t =
      if aconv t (concl rule) orelse aconv t (concl other) then
        let
          val which = if aconv t (concl rule) then "and" else "or"
          val context = Context.Data.get printer_context (Context.snapshot ())
          val text = grammar ^ "/" ^ context ^ ":" ^ which
          val _ = callbacks := text :: !callbacks
        in
          if !throwing then raise PrinterFailure token
          else #add_string pp text
        end
      else raise term_pp_types.UserPP_Failed
  in
    Parse.temp_add_user_printer ("stagingcontracts", concl rule, printer);
    Parse.temp_add_user_printer ("stagingcontracts-other", concl other, printer)
  end
val _ = install_printer "A"
fun exception_text (PrinterFailure t) =
      "PrinterFailure(identity=" ^ Bool.toString (t = token) ^ ")"
  | exception_text (HOL_ERR e) =
      "HOL_ERR(" ^ Feedback.top_structure_of e ^ "." ^
      Feedback.top_function_of e ^ ":" ^
      String.toString (Feedback.message_of e) ^ ")"
  | exception_text Option = "Option(identity=true)"
  | exception_text e = General.exnName e ^ ":" ^
                       String.toString (General.exnMessage e)
datatype 'a outcome = Returned of 'a | Raised of exn
fun observe id field value = Paired.observe (id ^ "." ^ field) value
fun measure id f =
  let
    val _ = callbacks := []
    val meter = Count.mk_meter ()
    val result = Returned (f ()) handle e => Raised e
    val n = #prims (Count.read meter)
    val _ = observe id "prims" (Int.toString n)
    val _ = observe id "callbacks" (String.concatWith "," (rev (!callbacks)))
  in result end

val validations = ref 0
fun validate id original (gs,vf) =
  let
    val supplied = map prove_goal gs
    val result = measure (id ^ ".proof") (fn () =>
      (validations := !validations + 1; vf supplied))
  in
    case result of
        Raised e => raise Fail ("validation raised: " ^ exception_text e)
      | Returned th =>
          (Paired.check (id ^ " proof") (sound original th);
           observe id "theorem" (terms (hyp th) ^ "|-" ^ tm (concl th));
           observe id "oracles" (String.concatWith ","
                                  (#1 (Tag.dest_tag (tag th)))))
  end
fun apply id tac gl =
  case measure id (fn () => runtac tac gl) of
      Raised e => observe id "outcome" (exception_text e)
    | Returned result =>
        (observe id "outcome" "returned";
         observe id "goals" (goals (#1 result));
         validate id gl result)

(* A saved tactic is used twice. Hooks execute OUTSIDE all measured stages.
   A construction exception is recorded, never retried as an application. *)
fun scenario id make before_first first before_second second =
  let
    val result = measure (id ^ ".construct") make
  in
    case result of
        Raised e =>
          (observe (id ^ ".construct") "outcome" (exception_text e);
           observe id "uses" "unavailable")
      | Returned tac =>
          (observe (id ^ ".construct") "outcome" "returned";
           before_first ();
           apply (id ^ ".first") tac first;
           before_second ();
           apply (id ^ ".second") tac second)
  end
fun noop () = ()
fun run id args gl =
  scenario id (fn () => global_simp_tac cfg empty_ss args)
           noop gl noop gl

val _ = run "empty" [] basegoal
val _ = run "unmarked" [rule] basegoal
val _ = run "req0" [Req0 rule] basegoal
val _ = run "reqD" [ReqD rule] basegoal
val _ = run "req0_reqD" [Req0 (ReqD rule)] basegoal
val _ = run "reqD_req0" [ReqD (Req0 rule)] basegoal
val _ = run "req0_failure" [Req0 (BoundedRewrites.Ntimes rule 0)] basegoal
(* An unmatched reflexive goal observes ReqD's zero-to-zero failure.
   With both checks, the inner Req0 raises before the outer ReqD. *)
val _ = run "reqD_failure" [reqD_rule] unchanged
val _ = run "both_failure" [Req0 (ReqD (BoundedRewrites.Ntimes rule 0))]
  basegoal

(* mk_require_tac restarts from its ORIGINAL tac for each list member:
   only the final argument's checks survive, but all printers still run. *)
val _ = run "reqD_then_plain" [ReqD rule,other] unchanged
val _ = run "plain_then_reqD" [other,ReqD rule] unchanged
val _ = run "req0_then_reqD" [Req0 rule,ReqD other] basegoal
val _ = run "reqD_then_req0" [ReqD other,Req0 rule] basegoal
val _ = run "req0_then_plain"
  [Req0 (BoundedRewrites.Ntimes rule 0),other] basegoal

val _ = run "bound0" [BoundedRewrites.Ntimes rule 0] basegoal
val _ = run "bound1" [BoundedRewrites.Once rule] basegoal
val _ = run "bound2" [BoundedRewrites.Ntimes rule 2] basegoal
val two_redex : Abbrev.goal =
  ([lp,lq,r], mk_conj (mk_conj (p,T),mk_conj (q,T)))
val _ = run "bound1_two_redex" [BoundedRewrites.Once rule] two_redex
val _ = run "bound2_two_redex" [BoundedRewrites.Ntimes rule 2] two_redex
val _ = run "req0_bound1_two_redex" [Req0 (BoundedRewrites.Once rule)] two_redex
val installed = empty_ss ++ rewrites [BoundedRewrites.Once rule]
val _ = scenario "installed_bound1"
  (fn () => global_simp_tac cfg installed []) noop basegoal noop basegoal
val _ = run "reqD_bound1" [ReqD (BoundedRewrites.Once rule)] basegoal
val _ = run "bound1_reqD" [BoundedRewrites.Once (ReqD rule)] basegoal
val malformed = ADD_ASSUM
  (mk_comb (boolSyntax.bounded_tm, mk_var ("not-an-int",bool))) rule
val _ = run "malformed_bound" [malformed] basegoal
val _ = run "reqD_malformed_bound" [ReqD malformed] basegoal
val _ = case measure "negative_bound.argument"
                   (fn () => BoundedRewrites.Ntimes rule (~1)) of
    Raised e => observe "negative_bound.argument" "outcome" (exception_text e)
  | Returned _ => raise Fail "negative bound unexpectedly constructed"

(* Prove a two-subgoal composition with nontrivial original hypotheses.
   This catches order changes and validations accepting a wrong conclusion. *)
val _ = scenario "ordered_subgoals"
  (fn () => global_simp_tac cfg empty_ss [rule] THEN CONJ_TAC)
  noop ([lp,lq,r], mk_conj (p,q))
  noop ([lq,lp,r], mk_conj (q,p))
val hyp_rule = ADD_ASSUM r rule
val _ = run "hyp_rule" [ReqD hyp_rule] basegoal
val _ = run "closed" [ReqD rule] ([], mk_conj (T,T))

(* Requirement diagnostics capture grammar/context at construction, whereas
   a replacement printer is used only if construction was wrongly delayed. *)
val grammar0 = Parse.current_grammars ()
val context0 = Context.snapshot ()
fun change_printer () =
  (Context.Data.write printer_context "B"; install_printer "B")
val _ = scenario "grammar_context" (fn () =>
  global_simp_tac cfg empty_ss [reqD_rule])
  change_printer unchanged
  (fn () => (Context.restore context0; Parse.temp_set_grammars grammar0))
  unchanged
val _ = throwing := true
val _ = run "throw_construct" [ReqD rule] basegoal
val _ = throwing := false
val _ = scenario "throw_after" (fn () =>
  global_simp_tac cfg empty_ss [reqD_rule])
  (fn () => throwing := true) basegoal noop basegoal
val _ = throwing := false
val _ = scenario "throw_second" (fn () =>
  global_simp_tac cfg empty_ss [reqD_rule])
  noop basegoal (fn () => throwing := true) basegoal
val _ = throwing := false
(* Even a requirement discarded by the trailing plain theorem prints/throws. *)
val _ = throwing := true
val _ = run "throw_discarded" [ReqD rule,other] unchanged
val _ = throwing := false

(* FRAG (unlike SF) has no eager registration. Look up against each live
   context. First use fails, registration enables the SAME saved tactic. *)
val latefrag = markerLib.FRAG "staging-late"
val _ = scenario "late_fragment"
  (fn () => global_simp_tac cfg empty_ss [latefrag])
  noop basegoal
  (fn () => ignore (register_frag (name_ss "staging-late" (rewrites [rule]))))
  basegoal
val _ = scenario "replaced_fragment"
  (fn () => global_simp_tac cfg empty_ss [latefrag])
  noop basegoal
  (fn () => ignore (register_frag
    (name_ss "staging-late" empty_ssfrag))) basegoal
val _ = scenario "rewound_fragment"
  (fn () => global_simp_tac cfg empty_ss [latefrag])
  noop basegoal (fn () => Context.restore context0) basegoal
val _ = run "missing_fragment" [markerLib.FRAG "staging-missing"] basegoal

(* LLABEL_RES_THEN silently omits missing references. Duplicate labels
   select all matches; distinct references still follow ASSUMPTION order. *)
val label_rule = concl (markerLib.MK_LABEL ("rw", rule))
val label_ref = markerSyntax.L "rw"
val absent_ref = markerSyntax.L "absent"
val _ = scenario "late_label"
  (fn () => global_simp_tac cfg empty_ss [label_ref])
  noop basegoal noop ([label_rule,lp,lq,r], mk_conj (p,T))
val label_alt = concl (markerLib.MK_LABEL
  ("rw", ASSUME (mk_eq (mk_conj (p,T),q))))
val _ = scenario "label_order"
  (fn () => global_simp_tac cfg empty_ss [label_ref,absent_ref])
  noop ([label_rule,label_alt,lp,lq,r], mk_conj (p,T))
  noop ([label_alt,label_rule,lp,lq,r], mk_conj (p,T))
val label_a = concl (markerLib.MK_LABEL ("a", rule))
val label_b = concl (markerLib.MK_LABEL
  ("b", ASSUME (mk_eq (mk_conj (p,T),q))))
val label_refs = [markerSyntax.L "a",markerSyntax.L "b"]
val _ = scenario "label_reference_order"
  (fn () => global_simp_tac cfg empty_ss label_refs)
  noop ([label_b,label_a,lp,lq,r], mk_conj (p,T))
  noop ([label_a,label_b,lp,lq,r], mk_conj (p,T))

(* Abbr's partition/name extraction is early, expansion and missing-abbrev
   failure are late. Save the marker argument BEFORE measuring construction. *)
val abbr = markerSyntax.Abbr [QUOTE "stage_a"]
val a = mk_var ("stage_a", bool)
val abbrev = markerSyntax.mk_abbrev ("stage_a", mk_conj (p,T))
val _ = scenario "late_abbr"
  (fn () => global_simp_tac cfg empty_ss [abbr,rule])
  noop ([abbrev,lp,lq,r],a) noop basegoal
val _ = run "reqD_then_abbr" [ReqD rule,abbr]
  ([abbrev,lp,lq,r],a)
val _ = scenario "reqD_after_abbr"
  (fn () => global_simp_tac cfg empty_ss [abbr,reqD_rule])
  noop ([abbrev,lp,lq,r],a) noop basegoal

(* The validator must reject invalid reconstructions. No fake theorem is
   used as a subgoal proof in the real scenarios. *)
val _ = Paired.check "validator wrong conclusion control"
  (not (sound basegoal TRUTH))
val _ = Paired.check "validator foreign hypothesis control"
  (not (sound ([],p) (ASSUME p)))
val _ = Paired.check "validator oracle control"
  (not (sound basegoal (mk_oracle_thm "staging-control" basegoal)))
val _ = Paired.observe "validations.executed" (Int.toString (!validations))
