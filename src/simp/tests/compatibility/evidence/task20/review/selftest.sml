open HolKernel Parse boolLib boolSyntax testutils
val _ = simpExtLib.empty_ss
structure S = simpExtLib
val unsafe = {safe=false}
val p = ``task20_review_p:bool``
val failures = ref 0
fun check label ok =
  (tprint label; if ok then OK () else
     (failures := !failures + 1; print "FAILED!\n"))
val observed = Exn.capture
  (fn () => runtac (S.GEN_SIMP_TAC unsafe S.empty_ss
    [markerSyntax.Abbr [QUOTE "review_missing_abbr"],
     markerLib.FRAG "review_missing_frag"]) ([],p)) ()
val _ = (case observed of Exn.Exn (HOL_ERR e) =>
  (print ("OBS exception=" ^ Feedback.top_structure_of e ^ "." ^
          Feedback.top_function_of e ^ ": " ^ Feedback.message_of e ^ "\n");
   check "Abbr pretactic precedes missing FRAG"
     (String.isSubstring "No assumption of the form"
        (Feedback.message_of e)))
  | _ => check "Abbr pretactic precedes missing FRAG" false)
val rule = ASSUME ``(task20_review_f:bool -> bool) x = y``
val nested = Once (Ntimes rule 2)
val initialBound = #2 (BoundedRewrites.DEST_BOUNDED nested)
val (_,prepared) = S.prepare_rewrite_arguments S.empty_ss [nested]
val after = #2 (BoundedRewrites.DEST_BOUNDED (hd prepared))
val _ = print ("OBS selected bound before=" ^ Int.toString initialBound ^
               " after=" ^ Int.toString after ^ "\n")
val _ = check "preparing nested genuine rewrite preserves selected bound"
  (initialBound = after)
fun remaining (tac : Abbrev.tactic) = #1 (runtac tac ([p],p))
val direct = remaining
  (S.GEN_SIMP_TAC unsafe S.empty_ss [Once markerLib.NoAsms])
val alias = remaining (S.ASM_SIMP_TAC S.empty_ss [Once markerLib.NoAsms])
val _ = print ("OBS explicit NoAsms residuals=" ^
  Int.toString (length direct) ^ " alias residuals=" ^
  Int.toString (length alias) ^ "\n")
val _ = check "extension alias preserves wrapped NoAsms policy"
  (length alias = 1 andalso length direct = 1)
val _ = print ("TASK20_REVIEW_FAILURES=" ^ Int.toString (!failures) ^ "\n")
val _ = OS.Process.exit
  (if !failures = 0 then OS.Process.success else OS.Process.failure)
