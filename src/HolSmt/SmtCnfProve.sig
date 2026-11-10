signature SmtCnfProve =
sig
  (* Refuted has conclusion F and only input clauses as hypotheses.
     Model is a closed native existential witness for the identical Boolean
     abstraction; it does not assert realizability of non-Boolean atoms.
     Unknown keeps the caller's existing solver and exception behavior. *)
  datatype result = Refuted of Thm.thm | Model of Thm.thm | Unknown
  val prove : Term.term Array.array -> result
end
