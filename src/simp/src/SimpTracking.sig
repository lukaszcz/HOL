(* Internal shared rewrite reporter; not an extension registration. *)
signature SimpTracking =
sig
  val note_rewrite : Thm.thm -> unit
  val with_tracking : ('a -> 'b) -> 'a -> 'b * Thm.thm list
end
