signature Unittest =
sig

  val assert : bool * string -> unit
  val die : string -> 'a

  val run_unittests : unit -> unit
  val run_compact_parser_unittests : unit -> unit
  val run_compact_parser_boundary_unittests : unit -> unit

end
