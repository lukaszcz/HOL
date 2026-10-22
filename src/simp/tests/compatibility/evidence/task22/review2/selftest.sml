open HolKernel Parse boolLib boolSyntax testutils
val _ = simpExtLib.empty_ss
structure S = simpExtLib
val failures = ref 0
fun check name ok =
  (tprint name; if ok then OK ()
   else (failures := !failures + 1; print "FAILED\n"))
val payload = Feedback.mk_hol_error
  "TASK22_review2" "keep" locn.Loc_Unknown "policy abort"
val injected = HOL_ERR payload
exception Foreign of unit ref
val token = ref ()
val errors = [("HOL_ERR",injected,
                fn HOL_ERR e => Portable.pointer_eq (e,payload) | _ => false),
              ("foreign",Foreign token,
                fn Foreign r => Portable.pointer_eq (r,token) | _ => false),
              ("Interrupt",Portable.Interrupt,
                fn Portable.Interrupt => true | _ => false)]
val hold = ``(review_hold:(bool -> bool) -> bool)
               (\u:bool. review_h u)``
val eta_rule = ASSUME
  ``(review_eta_input:bool -> bool) = (\u:bool. review_h u)``
val late = ``review_hold (review_eta_input:bool -> bool):bool``
val _ = List.app (fn route => List.app (fn (label,error,exact) => let
  val aborted = ref false
  val post_abort_calls = ref 0
  val policy_calls = ref 0
  fun fallback tm =
    (if !aborted then post_abort_calls := !post_abort_calls + 1 else ();
     NO_CONV tm)
  val eta = S.SSFRAG
    {name=NONE,rewrs=[],ac=[],congs=[],dprocs=[],filter=NONE,
     convs=[{name="ETA_CONV (eta reduction)",trace=0,
             key=SOME ([],hold),conv=K (K (RAND_CONV ETA_CONV))},
            {name="fallback callback",trace=0,
             key=SOME ([],hold),conv=K (K fallback)},
            {name="create eta argument",trace=0,
             key=SOME ([],lhs (concl eta_rule)),
             conv=K (K (REWR_CONV eta_rule))}]}
  val ss = S.++ (S.empty_ss,eta)
  fun keep tm = if aconv tm hold then
      (policy_calls := !policy_calls + 1; aborted := true; raise error)
    else false
  val policy = {charge=fn () => (),keep_abstraction=keep}
  val prepared = S.prepare_child_first policy ss
  val observed = S.prepare_child_first_observed (fn _ => ()) policy ss
  val cv = case route of
      "direct" => S.SIMP_CONV_CHILD_FIRST policy ss []
    | "normalize" => #normalize prepared []
    | "observed" => #normalize observed []
    | _ => #arguments prepared []
  val tm = if route = "arguments" then
      mk_comb (``review_outer:bool -> bool``,late) else late
  val result = Exn.capture cv tm
  val name = route ^ "/" ^ label
  val _ = check (name ^ ": original exception propagates")
    (case result of Exn.Exn e => exact e | _ => false)
  val _ = check (name ^ ": one policy abort witnessed") (!policy_calls = 1)
  val _ = print (name ^ ": POST_ABORT_CALLBACKS=" ^
                  Int.toString (!post_abort_calls) ^ "\n")
in check (name ^ ": abort prevents later candidate callbacks")
     (!post_abort_calls = 0) end) errors)
  ["direct","normalize","observed","arguments"]
val _ = print ("REVIEW2_FAILURES=" ^ Int.toString (!failures) ^ "\n")
val _ = OS.Process.exit
  (if !failures = 0 then OS.Process.success else OS.Process.failure)
