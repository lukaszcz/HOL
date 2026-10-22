(* Explicit opt-in to intermediate result discovery and rebuilt-RHS beta
   reduction. The continuation/type and exception identities are Opening's. *)
signature OpeningExt =
sig
  type congproc = Opening.congproc
  val THREADED_CONGPROC :
    ({Rinst : Term.term, arg : Term.term} -> Thm.thm) -> Thm.thm -> congproc
end
