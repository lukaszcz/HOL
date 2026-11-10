(* Static native specialization of the SAME recorded programme. *)
structure SmtReplayNamedClauseInput =
struct
  type input = Thm.thm
  val concl = Thm.concl
  val hyp = Thm.hyp
  val tag = Thm.tag
  fun read proof = proof
end

structure SmtReplayNamedClause :> SmtReplayNamedClause =
  SmtReplayNamedClauseFn(SmtReplayNamedClauseInput)
