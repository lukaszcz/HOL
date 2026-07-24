Theory iffRoundTripChild
Ancestors
  iffRoundTripBase
Libs
  HolKernel BasicProvers clasimpLib

open clasimpLib

fun fail message = raise Fail ("iff round-trip child test: " ^ message)

fun has_rule name =
  List.exists
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

fun has_fragment name ss =
  List.exists
    (fn fragment => fragment = "__clasimp_iff_" ^ name)
    (simpLib.ssfrag_names_of ss)

val live_name = "iffRoundTripBase$iff_round_trip_live_rule"
val removed_name = "iffRoundTripBase$iff_round_trip_removed_rule"

val _ =
  if not (has_rule (live_name ^ "_intro")) orelse
     not (has_rule (live_name ^ "_dest"))
  then fail "the reloaded child claset lost its inherited declaration"
  else if not (has_fragment live_name (BasicProvers.srw_ss ())) orelse
          not (has_fragment live_name (clasimp_ss ()))
  then fail "the reloaded child simpsets lost the inherited declaration"
  else if has_rule (removed_name ^ "_intro") orelse
          has_rule (removed_name ^ "_dest")
  then fail "the removed declaration reappeared in the child claset"
  else if has_fragment removed_name (BasicProvers.srw_ss ()) orelse
          has_fragment removed_name (clasimp_ss ())
  then fail "the removed declaration reappeared in the child simpsets"
  else ()
