Theory iffRoundTripBase
Ancestors
  clasetSeed
Libs
  BasicProvers clasimpLib iffTestSupport

open clasimpLib iffTestSupport

fun fail message = failer "iff round-trip base test" message

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
  if not (has_iff_rules live_name)
  then fail "the attribute did not immediately update the claset"
  else if not (has_iff_rewrite live_name)
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
  if has_iff_rules removed_name
  then fail "remove_iff did not immediately retract the claset rules"
  else if has_iff_rewrite removed_name
  then fail "remove_iff did not immediately retract the simpset fragment"
  else ()

Definition iff_round_trip_delsimp_def:
  iff_round_trip_delsimp (p : bool) = p
End

Theorem iff_round_trip_delsimp_rule[iff]:
  !p. iff_round_trip_delsimp p <=> p
Proof
  simp[iff_round_trip_delsimp_def]
QED

val delsimp_name = "iffRoundTripBase$iff_round_trip_delsimp_rule"
val _ = BasicProvers.delsimps ["iff_round_trip_delsimp_rule"]

val _ =
  if has_iff_rewrite delsimp_name
  then fail "delsimps did not retract the iff simpset view"
  else if not (has_iff_rules delsimp_name)
  then fail "delsimps unexpectedly retracted the iff claset view"
  else ()

(* The finaliser weighs a theory's delsimps declarations against its whole
   iff stream, so a delsimps recorded first has to suppress the iff rewrite
   in the session too.  Otherwise the session and a reload disagree. *)
val _ = BasicProvers.delsimps ["iff_round_trip_predelsimp_rule"]

Definition iff_round_trip_predelsimp_def:
  iff_round_trip_predelsimp (p : bool) = p
End

Theorem iff_round_trip_predelsimp_rule[iff]:
  !p. iff_round_trip_predelsimp p <=> p
Proof
  simp[iff_round_trip_predelsimp_def]
QED

val predelsimp_name = "iffRoundTripBase$iff_round_trip_predelsimp_rule"

val _ =
  if has_iff_rewrite predelsimp_name
  then fail "a delsimps recorded before the declaration was ignored"
  else if not (has_iff_rules predelsimp_name)
  then fail "the early delsimps also retracted the iff claset view"
  else ()
