(* Static actual theorem observation for the SAME equality worker. *)
structure SmtReplayNamedEqualityInput =
struct
  type proof = Thm.thm
  val concl = Thm.concl
end

structure SmtReplayNamedEquality :> SmtReplayNamedEquality =
  SmtReplayNamedEqualityFn(SmtReplayNamedEqualityInput)
