(* Operational work admitted by one automation invocation.  A budget is
   passed explicitly to nested consumers; it is not a diagnostic meter. *)
signature searchBudget =
sig
  datatype kind = Candidate | Application | Normalization

  type limits =
    {candidates : int option,
     applications : int option,
     normalization : int option}

  type usage =
    {candidates : int,
     applications : int,
     normalization : int}

  type budget
  exception LimitReached of kind * usage

  val create : limits -> budget
  val unbounded : unit -> budget
  val usage : budget -> usage
  (* Charge before work starts.  A zero limit rejects its first unit. *)
  val charge : budget -> kind -> unit
  (* Add an explicit allocation to a finite limit.  An unbounded
     dimension remains unbounded.  This preserves usage and lets a
     suspended invocation resume with its existing cursors. *)
  val extend : budget -> kind -> int -> unit
end
