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
  val CS_BLAST_DEPTH_TAC : clasetLib.claset -> int -> tactic
  val depth_limit : int ref

  (* Run tableau search only.  The result contains the recorded script and
     the full sequence of branch states; no reconstruction is attempted. *)
  val tryIt : int -> thm list -> goal -> try_result
end
