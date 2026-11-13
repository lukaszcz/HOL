signature hhReconstruct =
sig

  include Abbrev

  (* Settings *)
  val reconstruct_flag : bool ref
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  (* Reconstruction *)
  type settings =
    {minimize : bool, preplay_timeout : real, minimize_timeout : real}
  val hh_reconstruct_with :
    settings -> string list -> goal -> (string * tactic)
  (* Minimizes, with the timeouts in the references above. *)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
