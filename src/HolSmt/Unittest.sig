signature Unittest =
sig

  val assert : bool * string -> unit
  val die : string -> 'a

  val run_unittests : unit -> unit
  val run_binder_resource_unittests : unit -> unit
  val run_cnf_graph_unittests : unit -> unit
  val run_word_graph_unittests : unit -> unit
  val run_fp_graph_unittests : unit -> unit

end
