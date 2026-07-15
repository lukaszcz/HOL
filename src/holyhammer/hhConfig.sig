signature hhConfig =
sig
  val state_dir : unit -> string

  val get : string -> string option
  val get_int : string -> int option
  val get_bool : string -> bool option
  val get_path : string -> string option
  val dump : unit -> (string * string) list

  val platform : unit -> string
  val find_exec : string -> string list -> string option
  val find_executable : string -> string list -> string option
end
