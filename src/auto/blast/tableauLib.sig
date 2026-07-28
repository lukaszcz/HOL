signature tableauLib =
sig
  include Abbrev

  type proof = blastSearch.proof
  type branch = blastSearch.branch
  type try_result =
    {fullTrace : branch list list,
     result : proof option}

  val BLAST_TAC : thm list -> tactic
  val BLAST_DEPTH_TAC : int -> thm list -> tactic
  (* Searches with the given claset extended by the safe elimination rules
     the tableau engine needs to decompose a negated implication or a
     negated universal; a caller supplies only its own rules. *)
  val CS_BLAST_DEPTH_TAC : clasetLib.claset -> int -> tactic

  val depth_limit : int ref

  (* Run tableau search only.  The result contains the recorded script and
     the full sequence of branch states; no reconstruction is attempted. *)
  val tryIt : int -> thm list -> goal -> try_result
end
