signature hhSlice =
sig
  val schedule_of_provers : string list -> int -> string list
  val mk_schedule : hhConfig.hh_options ->
    (hhProver.prover_config * hhProver.slice) list
  val slice_budget : int -> hhConfig.hh_options -> hhProver.slice -> real
end
