signature hhConfig =
sig
  (* Small filesystem and string helpers, shared with hhProver and hhEval. *)
  val is_dir : string -> bool
  val ensure_dir : string -> unit
  val directory_names : string -> string list
  val trim : string -> string
  val trim_left : string -> string
  val first_some : ('a -> 'b option) -> 'a list -> 'b option

  val state_dir : unit -> string

  val get : string -> string option
  val get_int : string -> int option
  val get_bool : string -> bool option
  val get_path : string -> string option
  val dump : unit -> (string * string) list

  val platform : unit -> string
  val find_exec_with_env : string -> string -> string list -> string option
  val find_exec : string -> string list -> string option
end
