Theory iffRoundTripChild
Ancestors
  iffRoundTripBase
Libs
  HolKernel BasicProvers clasimpLib iffTestSupport

open clasimpLib iffTestSupport

fun fail message = failer "iff round-trip child test" message

val live_name = "iffRoundTripBase$iff_round_trip_live_rule"
val removed_name = "iffRoundTripBase$iff_round_trip_removed_rule"
val delsimp_name = "iffRoundTripBase$iff_round_trip_delsimp_rule"
val predelsimp_name = "iffRoundTripBase$iff_round_trip_predelsimp_rule"

val _ =
  let
    val source = ``iffRoundTripBase$iff_round_trip_live T``
    val ordinary =
      Conv.QCONV (simpLib.SIMP_CONV (BasicProvers.srw_ss ()) []) source
    val excluded =
      Conv.QCONV
        (simpLib.SIMP_CONV (BasicProvers.srw_ss ())
          [markerLib.Excl
             "iffRoundTripBase.iff_round_trip_live_rule"])
        source
  in
    if aconv (snd (boolSyntax.dest_eq (concl ordinary))) boolSyntax.T andalso
       aconv (snd (boolSyntax.dest_eq (concl excluded))) source andalso
       has_iff_rules live_name
    then ()
    else fail "Excl did not disable only the named iff rewrite"
  end

val _ =
  if not (has_iff_rules live_name)
  then fail "the reloaded child claset lost its inherited declaration"
  else if not (has_iff_rewrite live_name)
  then fail "the reloaded child simpsets lost the inherited declaration"
  else if has_iff_rules removed_name
  then fail "the removed declaration reappeared in the child claset"
  else if has_iff_rewrite removed_name
  then fail "the removed declaration reappeared in the child simpsets"
  else if has_iff_rewrite delsimp_name
  then fail "the persistent delsimps removal was lost in the child"
  else if not (has_iff_rules delsimp_name)
  then fail "delsimps removed the child claset view"
  else if has_iff_rewrite predelsimp_name
  then fail "the delsimps recorded before the declaration was lost"
  else if not (has_iff_rules predelsimp_name)
  then fail "the early delsimps removed the child claset view"
  else ()
