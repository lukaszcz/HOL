(* Compiled by StartupGate.sml after the simplifier is available. A current
   theory is what TAC_PROOF requires. *)
val _ = Theory.new_theory "gate_startup"
val _ = convRef := (fn () =>
  result := SOME (simpLib.SIMP_CONV pureSimps.pure_ss grules gtm))
val _ = tacRef := (fn () =>
  proved := SOME (Tactical.TAC_PROOF
                    (([], gtt),
                     simpLib.SIMP_TAC pureSimps.pure_ss grules)))
