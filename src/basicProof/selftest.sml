open Parse BasicProvers simpLib testutils

val _ = Theory.new_theory "scratch"

(* tests for diminish applying to constituents that are "built-in" to srw_ss
   from its point of definition *)
val _ = diminish_srw_ss ["COMBIN"]
val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "diminish_srw_ss before 'realisation'",
                    printresult = thm_to_string,
                    testfn = SIMP_CONV (quietly srw_ss()) []}
                   “K T (x:'a)”

val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "with_simpset_updates removes BETA_CONV",
                    printresult = thm_to_string,
                    testfn = with_simpset_updates
                               (fn ss0 => ss0 -* ["BETA_CONV"])
                               (fn t => SIMP_CONV (srw_ss()) [] t)}
                   “(λx. x /\ p) T”

val _ = convtest ("SIMP_CONV (srw_ss()) [] “p ∧ T”", SIMP_CONV (srw_ss()) [],
                  “p ∧ T”, “p:bool”)

val _ = convtest("above w/simpset_updates removing",
                 BasicProvers.with_simpset_updates
                   (simpLib.remove_simps ["AND_CLAUSES"])
                   (fn x => Conv.QCONV (SIMP_CONV (srw_ss()) []) x),
                   “p ∧ T”, “p ∧ T”)

val _ = convtest("Original again", SIMP_CONV (srw_ss()) [], “p ∧ T”, “p:bool”)

(* ==================================================================
   Regression for issue #2025: Context.restore must not rewind the
   kernelid allocation clock, nor the retire-mutation clock.  Both
   live in process-global Sref counters outside Context.t so that:

     (1) same_const on pre- vs post-restore constants of the same
         name is FALSE (soundness — the exploit constructed ⊢ F by
         collision), and

     (2) symtab_epoch() after a post-restore mutation is strictly
         greater than any value seen before (correctness — the
         ThmSetData / AncestryData / GrammarDeltas memoisation gates
         cannot false-positive after a restore).
   ================================================================== *)

local
  open boolSyntax Drule Term Thm Feedback
in

val _ = tprint "issue #2025 (soundness): Context.restore + redefinition"
val snap = Context.snapshot ()
val c_t = mk_var("issue2025_c", Type.bool)
val c_eq_t = new_definition ("issue2025_A_def", mk_eq (c_t, T))
val () = Context.restore snap
val c_f = mk_var("issue2025_c", Type.bool)
val c_eq_f = new_definition ("issue2025_B_def", mk_eq (c_f, F))
val const_t = lhs (concl c_eq_t)  (* pre-restore Const *)
val const_f = lhs (concl c_eq_f)  (* post-restore Const *)
val () =
    if not (same_const const_t const_f) then OK ()
    else die "same_const holds across Context.restore — exploit re-opened"

val _ = shouldfail {
    checkexn  = fn HOL_ERR _ => true | _ => false,
    printarg  = fn () => "TRANS across a restored constant must fail",
    printresult = thm_to_string,
    testfn    = fn () => TRANS (SYM c_eq_t) c_eq_f} ()

val _ = tprint "issue #2025 (correctness): retire clock is monotonic across restore"
(* Retirement events (Theory.delete_const, delete_type, and the
   internal `remove` triggered by a re-inserting collision) stamp
   retire_epoch from a process-global monotone counter, so
   memoisation gates that key off symtab_epoch cannot false-positive
   after Context.restore. *)
val snap2 = Context.snapshot ()
val _ = new_definition ("issue2025_re_D_def",
                        mk_eq (mk_var("issue2025_re_d", Type.bool), T))
val () = Theory.delete_const "issue2025_re_d"
val e_pre_restore = Term.term_epoch ()
val () = Context.restore snap2
val _ = new_definition ("issue2025_re_D_def",
                        mk_eq (mk_var("issue2025_re_d", Type.bool), T))
val () = Theory.delete_const "issue2025_re_d"
val e_post_restore = Term.term_epoch ()
val () =
    if e_post_restore > e_pre_restore then OK ()
    else die ("retire epoch not strictly monotone across restore: pre="
              ^ Int.toString e_pre_restore
              ^ " post=" ^ Int.toString e_post_restore)

end (* local *)

(* ==================================================================
   `new_theory` must not export the segment it abandons when the
   session is interactive.  `export_theory` is already a no-op there,
   but the implicit export inside `new_theory` was not: changing a
   script's `Theory` name under an editor wrote the old theory to disk,
   added it to the theory graph, and sealed its name in KernelSig --
   which sits outside Context, so no snapshot restore reaches it.
   Changing the name back then failed with `theory: "..." already
   exists.` for the life of the process.
   ================================================================== *)

val _ = tprint "interactive new_theory can return to an abandoned name"
val saved_interactive = !Globals.interactive
val () = Globals.interactive := true
(* The segment this abandons is `scratch`, which the tests above left
   non-empty -- so the first call already takes the branch under test
   rather than the empty-scratch shortcut beside it. *)
val returned =
    (Theory.new_theory "nt_abandon_a";
     Theory.new_theory "nt_abandon_b";
     Theory.new_theory "nt_abandon_a";
     NONE)
    handle e => SOME e
val () = Globals.interactive := saved_interactive
val () =
    case returned of
        SOME e => die ("could not return to the abandoned name: " ^
                       Feedback.exn_to_string e)
      | NONE =>
        if KernelSig.is_sealed_thy "nt_abandon_a" then
          die "the abandoned segment was sealed, so it had been exported"
        else if Theory.current_theory () <> "nt_abandon_a" then
          die ("current theory is " ^ Theory.current_theory () ^
               ", not the name returned to")
        else OK ()

(* RW_TAC and SRW_TAC hand the context they are applied with to the
   reducers they run, not the ambient one. *)
val _ =
  let
    val slot = Context.Data.new {name = "BasicProvers selftest context probe",
                                 empty = 0, pp = Int.toString}
    fun in_slot n f = Context.Data.with_slot_value slot n f ()
    val seen = ref ([] : int list)
    val recording =
      Traverse.REDUCER
        {name = NONE, initial = Fail "probe", addcontext = #1,
         apply = fn {ctxt,...} => fn tm =>
                    (seen := Context.Data.get slot ctxt :: !seen;
                     Conv.NO_CONV tm)}
    val frag = simpLib.dproc_ss recording
    val explicit = in_slot 7 Context.snapshot
    val goal = ([] : Term.term list, “probe_f ∧ T”)
    fun applied what tac =
      (tprint what;
       seen := [];
       in_slot 3 (fn () =>
         ignore (tac goal explicit)
         handle Feedback.HOL_ERR _ => () | Conv.UNCHANGED => ());
       if null (!seen) then die "nothing was applied"
       else if List.all (fn n => n = 7) (!seen) then OK ()
       else die "a reducer saw the wrong context")
  in
    applied "SRW_TAC passes its context" (SRW_TAC [frag] []);
    applied "RW_TAC passes its context"
      (RW_TAC (boolSimps.bool_ss ++ frag) []);
    applied "NORM_TAC passes its context"
      (NORM_TAC (boolSimps.bool_ss ++ frag) [])
  end

(* PROVE_TAC normalises its lemmas with a fixed rewrite set: a lemma that
   an implicit rewrite of the context reduces to T is still passed to
   MESON intact. *)
local
  val plain = Context.snapshot ()
  val g = “(p:'a # 'b = (x,y)) ==> (FST p = x)”
  fun attempt c tac =
    (tac ([], g) c; true) handle Feedback.HOL_ERR _ => false
in
  val _ = tprint "PROVE_TAC [FST] while FST is an ambient implicit rewrite"
  val _ = let
    val _ = Rewrite.add_implicit_rewrites [pairTheory.FST]
    val r = attempt (Context.snapshot ())
                    (BasicProvers.PROVE_TAC [pairTheory.FST])
    val _ = Context.restore plain
  in
    if r then OK () else die "PROVE_TAC lost the lemma"
  end
end
