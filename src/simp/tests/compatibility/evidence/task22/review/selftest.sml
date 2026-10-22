open HolKernel Parse boolLib boolSyntax testutils
val _ = simpExtLib.empty_ss
structure S = simpExtLib
val failures = ref 0
fun check name ok =
  (tprint name; if ok then OK ()
   else (failures := !failures + 1; print "FAILED\n"))
val injected = mk_HOL_ERR "TASK22_review" "keep" "policy abort"
fun is_injected (HOL_ERR e) = Feedback.top_structure_of e = "TASK22_review"
  | is_injected _ = false
fun rejected f = case Exn.capture f () of
    Exn.Exn e => is_injected e | _ => false
val hold = ``(review_hold:(bool -> bool) -> bool)
               (\u:bool. review_h u)``
(* No opaque reducer: force the pretest to evaluate the policy. *)
val enabled = ref true
val prepared = S.prepare_child_first
  {charge=fn () => (), keep_abstraction=fn _ =>
     if !enabled then raise injected else false} S.empty_ss
val _ = check "pretest propagates original policy error"
  (rejected (fn () => #may_reduce_arguments prepared hold))
val _ = enabled := false
val _ = check "pretest recovers after callback stops throwing"
  (case Exn.capture (#may_reduce_arguments prepared) hold of
       Exn.Res _ => true | Exn.Exn _ => false)
val _ = #normalize prepared [] ``T``
val _ = check "successful normalization leaves reusable pretest"
  (case Exn.capture (#may_reduce_arguments prepared) hold of
       Exn.Res _ => true | Exn.Exn _ => false)
(* Descent creates an ETA candidate after traversal's head-policy pass. *)
val eta_rule = ASSUME
  ``(review_eta_input:bool -> bool) = (\u:bool. review_h u)``
val late = ``review_hold (review_eta_input:bool -> bool):bool``
val eta = S.SSFRAG
  {name=NONE,rewrs=[],ac=[],congs=[],dprocs=[],filter=NONE,
   convs=[{name="ETA_CONV (eta reduction)",trace=0,
           key=SOME ([],hold),conv=K (K (RAND_CONV ETA_CONV))},
          {name="create eta argument",trace=0,
           key=SOME ([],lhs (concl eta_rule)),
           conv=K (K (REWR_CONV eta_rule))}]}
val ss = S.++ (S.empty_ss,eta)
val calls = ref 0
fun keep tm = if aconv tm hold then
    (calls := !calls + 1; raise injected) else false
val policy = {charge=fn () => (),keep_abstraction=keep}
val actual = Exn.capture (S.SIMP_CONV_CHILD_FIRST policy ss []) late
val _ = check "direct child-first visits late ETA policy" (!calls > 0)
val _ = check "direct child-first propagates late ETA HOL_ERR"
  (case actual of Exn.Exn e => is_injected e | _ => false)
val _ = print ("REVIEW_FAILURES=" ^ Int.toString (!failures) ^ "\n")
val _ = OS.Process.exit
  (if !failures = 0 then OS.Process.success else OS.Process.failure)
