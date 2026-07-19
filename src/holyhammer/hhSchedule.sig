signature hhSchedule =
sig
  include Abbrev

  datatype event =
      SliceStarted of hhProver.slice
    | SliceDone of hhProver.slice * hhProver.szs * real
    | ProofFound of hhProver.slice * string list
    | Verified of suggestion
    | ScheduleDone of stop_reason
  and stop_reason = MaxProofs | Timeout | Exhausted | Interrupted
  withtype suggestion =
    {stac : string, tac : tactic, lemmas : string list,
     prover : string, slice : hhProver.slice,
     t_prover : real, t_recon : real}

  type result =
    {suggestions : suggestion list,
     slices_run : (hhProver.slice * hhProver.szs * real * bool) list,
     stopped : stop_reason, t_total : real}

  val run :
    {options : hhConfig.hh_options, goal : goal, premises : string list,
     progress : (event -> unit) option} -> result
end
