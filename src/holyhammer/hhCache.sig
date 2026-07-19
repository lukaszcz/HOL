signature hhCache =
sig
  type key_parts =
    {prover : string, version : string option, argv : string list,
     problem : string}

  val key_of : key_parts -> string
  val lookup : hhConfig.hh_options -> key_parts -> hhProver.run_result option
  val store : hhConfig.hh_options -> key_parts -> hhProver.run_result -> unit
  val prune : hhConfig.hh_options -> unit
end
