Theory iffRoundTripBase
Ancestors
  clasetSeed
Libs
  BasicProvers clasimpLib

open clasimpLib

fun fail message = raise Fail ("iff round-trip base test: " ^ message)

fun has_rule name =
  List.exists
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

fun has_fragment name ss =
  List.exists
    (fn fragment => fragment = "__clasimp_iff_" ^ name)
    (simpLib.ssfrag_names_of ss)

Definition iff_round_trip_live_def:
  iff_round_trip_live (p : bool) = p
End

Theorem iff_round_trip_live_rule[iff]:
  !p. iff_round_trip_live p <=> p
Proof
  simp[iff_round_trip_live_def]
QED

val live_name = "iffRoundTripBase$iff_round_trip_live_rule"

val _ =
  if not (has_rule (live_name ^ "_intro")) orelse
     not (has_rule (live_name ^ "_dest"))
  then fail "the attribute did not immediately update the claset"
  else if not (has_fragment live_name (BasicProvers.srw_ss ())) orelse
          not (has_fragment live_name (clasimp_ss ()))
  then fail "the attribute did not immediately update the simpsets"
  else ()

Definition iff_round_trip_removed_def:
  iff_round_trip_removed (p : bool) = p
End

Theorem iff_round_trip_removed_rule[iff]:
  !p. iff_round_trip_removed p <=> p
Proof
  simp[iff_round_trip_removed_def]
QED

val removed_name = "iffRoundTripBase$iff_round_trip_removed_rule"
val _ = remove_iff "iffRoundTripBase.iff_round_trip_removed_rule"

val _ =
  if has_rule (removed_name ^ "_intro") orelse
     has_rule (removed_name ^ "_dest")
  then fail "remove_iff did not immediately retract the claset rules"
  else if has_fragment removed_name (BasicProvers.srw_ss ()) orelse
          has_fragment removed_name (clasimp_ss ())
  then fail "remove_iff did not immediately retract the simpset fragment"
  else ()
