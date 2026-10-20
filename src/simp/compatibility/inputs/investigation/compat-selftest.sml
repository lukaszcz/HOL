open HolKernel Parse boolLib simpLib testutils
val _ = new_theory "compatprobe"
val failures = ref 0
val _ = diemode := Remember failures
fun check name f =
  (tprint name;
   ((if f () then OK () else die "different behavior")
    handle e => die (General.exnMessage e)))
val _ = check "traversedata_for_ss exposes original REDUCER" (fn () =>
  let val Traverse.REDUCER _ =
        hd (#rewriters (traversedata_for_ss empty_ss))
  in true end)
val prefixes = ["rule:", "solver:", "looper:", "split:", "case:"]
val _ = List.app (fn prefix =>
  check ("unmatched Excl is no-op: " ^ prefix) (fn () =>
    let val _ = empty_ss && [Excl (prefix ^ "compat_missing")]
    in true end)) prefixes
val _ = List.app (fn prefix =>
  check ("Excl removes literal conversion name: " ^ prefix) (fn () =>
    let
      val calls = ref 0
      val name = prefix ^ "compat_probe"
      val ss = boolSimps.bool_ss ++ std_conv_ss
        {name=name, pats=[],
         conv=fn _ => (calls := !calls + 1; raise Conv.UNCHANGED)}
      val removed = ss && [Excl name]
      val _ = QCONV (SIMP_CONV removed []) ``p:bool``
    in !calls = 0 end)) prefixes
val _ = check "ordinary SIMP_CONV still rewrites" (fn () =>
  aconv (rhs (concl
    (SIMP_CONV boolSimps.bool_ss [] ``T /\ p``))) ``p:bool``)
val _ = print ("COMPAT_FAILURES=" ^ Int.toString (!failures) ^ "\n")
val _ = OS.Process.exit
  (if !failures = 0 then OS.Process.success else OS.Process.failure)
