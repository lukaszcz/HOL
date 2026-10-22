open TraverseExt HolKernel Parse boolLib boolSyntax testutils
structure E = TraverseExt
val failures = ref 0
fun check name ok =
  (tprint name; if ok then OK ()
   else (failures := !failures + 1; print "FAILED\n"))
val payload = Feedback.mk_hol_error
  "TASK22_review3" "keep" locn.Loc_Unknown "selected child abort"
exception Foreign of unit ref
val token = ref ()
val errors = [("HOL_ERR",HOL_ERR payload,
                fn HOL_ERR e => Portable.pointer_eq (e,payload) | _ => false),
              ("foreign",Foreign token,
                fn Foreign r => Portable.pointer_eq (r,token) | _ => false),
              ("Interrupt",Portable.Interrupt,
                fn Portable.Interrupt => true | _ => false)]
val hold = ``(review3_hold:(bool -> bool) -> bool)
               (\u:bool. review3_h u)``
val outer = ``review3_outer:bool -> bool``
val input = mk_comb (outer,hold)
val expected = AP_TERM outer (RAND_CONV ETA_CONV hold)
val _ = List.app (fn route => List.app (fn (label,error,exact) => let
  val enabled = ref true
  val aborted = ref false
  val policy_calls = ref 0
  val post_abort_calls = ref 0
  fun keep tm = if !enabled andalso aconv tm hold then
      (policy_calls := !policy_calls + 1; aborted := true; raise error)
    else false
  val policy = {charge=fn () => (),keep_abstraction=keep}
  val select : Opening.congproc = fn _ => fn {depther,...} => fn tm =>
    if is_comb tm andalso aconv (rator tm) outer then
      AP_TERM outer (QCONV (depther ([],equality)) (rand tm))
    else NO_CONV tm
  val fallback : Opening.congproc = fn _ => fn _ => fn tm =>
    (if !aborted then post_abort_calls := !post_abort_calls + 1 else ();
     NO_CONV tm)
  val data : E.traverse_data =
    {limit=NONE,rewriters=[],dprocs=[],relation=equality,
     travrules=Travrules.TRAVRULES
       {relations=[Travrules.EQ_preorder],congprocs=[select,fallback],
        weakenprocs=[]}}
  val xd = (data,E.default_config)
  val context = {reducer_context=[],solver_context=[]}
  val saved = case route of
      "generic" => E.TRAVERSE_WITH_CONTEXT (E.ChildFirst policy) xd context
    | "observed" => E.CHILD_FIRST_WITH_OBSERVER (fn _ => ()) policy xd context
    | _ => E.CHILD_FIRST_WITH_ABORT (fn () => ()) NONE policy xd context
  val result = Exn.capture saved input
  val name = route ^ "/" ^ label
  val _ = check (name ^ ": original policy error propagates")
    (case result of Exn.Exn e => exact e | _ => false)
  val _ = check (name ^ ": selected child policy abort witnessed")
    (!policy_calls = 1)
  val _ = print (name ^ ": POST_ABORT_CONGRUENCES=" ^
                  Int.toString (!post_abort_calls) ^ "\n")
  val _ = check (name ^ ": no congruence callback after policy abort")
    (!post_abort_calls = 0)
  val _ = enabled := false
  val _ = aborted := false
in check (name ^ ": saved conversion recovers with correct proof")
     (case Exn.capture saved input of
          Exn.Res th => aconv (concl th) (concl expected) andalso
                        HOLset.equal (hypset th,hypset expected)
        | _ => false) end) errors) ["generic","observed","abort-hook"]
val _ = print ("REVIEW3_FAILURES=" ^ Int.toString (!failures) ^ "\n")
val _ = OS.Process.exit
  (if !failures = 0 then OS.Process.success else OS.Process.failure)
