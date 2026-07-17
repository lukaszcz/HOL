signature holyHammer =
sig

  include Abbrev

  val set_timeout : int -> unit
  val holyhammer  : term -> thm
  val hh          : tactic
  val hh_fork     : goal -> Thread.thread
  (* catch the list of lemmas necessary in the last proof *)
  val lemmas_glob : string list option ref
  (* turn off this flag to disable premise selection *)
  val premise_selection_flag : bool ref
  (* Registry names of the provers called by hh. *)
  val all_atps : string list ref
  (* string list is a list of premises of the form "fooTheory.bar" *)
  val hh_pb  : string -> string list -> string list -> goal -> tactic

  (* For developers *)
  (* same as hh_pb but with all atps and premise selection *)
  val main_hh : string -> mlThmData.thmdata -> goal -> tactic
  val main_hh_lemmas : string -> mlThmData.thmdata -> goal -> string list option
  (* evaluation of holyhammer (with premise selection).
     This function is used inside the tactictoe evaluation framework. *)
  (* val hh_eval : mlThmData.thmdata * mlTacticData.tacdata -> goal -> unit *)

end
