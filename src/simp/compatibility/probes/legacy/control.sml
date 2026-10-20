(* Legacy-only control: this exact input runs on both implementations. *)
open HolKernel Parse boolLib simpLib testutils
val _ = new_theory "compatcontrol"

fun observe label value = print ("OBS " ^ label ^ "=" ^ value ^ "\n")
fun theorem label th =
  (observe (label ^ ".conclusion") (term_to_string (concl th));
   observe (label ^ ".hypotheses")
     (String.concatWith ";" (List.map term_to_string (hyp th))))
fun check label b = (tprint label; if b then OK () else die "mismatch")

val result = SIMP_CONV boolSimps.bool_ss [] ``T /\ p``
val _ = theorem "simplification" result
val _ = check "ordinary simplification"
  (aconv (concl result) ``(T /\ p) = p`` andalso null (hyp result))

(* Observe callbacks without using any branch-only strategy API. *)
val callbacks = ref ([] : string list)
val ss = empty_ss ++ std_conv_ss
  {name = "compat_control", pats = [],
   conv = fn tm =>
     (callbacks := term_to_string tm :: !callbacks; raise Conv.UNCHANGED)}
val unchanged = QCONV (SIMP_CONV ss []) ``p:bool``
val _ = theorem "callback" unchanged
val _ = observe "callbacks" (String.concatWith ";" (rev (!callbacks)))
val _ = check "unchanged callback result"
  (aconv (concl unchanged) ``(p:bool) = p`` andalso
   null (hyp unchanged) andalso not (null (!callbacks)))

(* Checking subgoals alone would not test a tactic's validation function. *)
val goal : goal = ([], ``T /\ T``)
val (subgoals, validation) = runtac (VALID (SIMP_TAC boolSimps.bool_ss []))
                                  goal
val _ = check "tactic closes control" (null subgoals)
val validated = validation []
val _ = theorem "validation" validated
val _ = check "tactic validation theorem"
  (aconv (concl validated) (#2 goal) andalso null (hyp validated))
val _ = observe "exception" "none"
val _ = OS.Process.exit OS.Process.success
