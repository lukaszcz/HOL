Theory HolSmtTrafficController
Ancestors
  integer
Libs
  HolSmtLib

Datatype:
  traffic_direction = NorthSouth | EastWest
End

Datatype:
  traffic_controller =
    <| green : traffic_direction; clock : int |>
End

(* A controller keeps one direction green for thirty ticks, then switches
   direction and resets the clock. *)
Definition traffic_step_def:
  traffic_step controller =
    if controller.clock < 30 then
      controller with clock := controller.clock + 1
    else
      <| green :=
           (case controller.green of
              NorthSouth => EastWest
            | EastWest => NorthSouth);
         clock := 0 |>
End

Definition controller_invariant_def:
  controller_invariant controller <=>
    0 <= controller.clock /\ controller.clock <= 30
End

(* The clock remains inside its permitted interval after every transition.
   PURE_REWRITE_TAC exposes the record literals, update, accessors, and case
   expression to each checked solver. *)
Theorem controller_invariant_z3:
  !controller.
    controller_invariant controller ==>
    controller_invariant (traffic_step controller)
Proof
  PURE_REWRITE_TAC [controller_invariant_def, traffic_step_def] >> Z3_TAC
QED

Theorem controller_invariant_cvc5:
  !controller.
    controller_invariant controller ==>
    controller_invariant (traffic_step controller)
Proof
  PURE_REWRITE_TAC [controller_invariant_def, traffic_step_def] >> CVC_TAC
QED

val _ = export_theory ();
