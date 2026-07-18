signature blastReconstruct =
sig
  include Abbrev

  type claset = clasetLib.claset
  type proof = blastSearch.proof

  (* Reconstruction executes the recorded tableau script left-to-right on a
     typed classical-engine node, then grounds and kernel-replays once. *)
  val reconstruct : goal -> proof -> (goal list * validation) option
  val reconstructWith :
    claset -> goal -> proof -> (goal list * validation) option

  (* Search continuations reject failed reconstruction with
     blastSearch.PROOF_FAILED, so the tableau resumes at its choice stack. *)
  val searchGoal :
    claset -> int -> goal -> (proof * (goal list * validation)) option
  val deepenGoal :
    claset -> goal -> (proof * (goal list * validation)) option

  val DEPTH_TAC : claset -> int -> tactic
  val DEEPEN_TAC : claset -> tactic
end
