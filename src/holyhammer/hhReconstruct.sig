signature hhReconstruct =
sig

  include Abbrev

  (* Settings *)
  val reconstruct_flag : bool ref
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  (* Reconstruction *)
  val hh_reconstruct_with : bool -> string list -> goal -> (string * tactic)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
