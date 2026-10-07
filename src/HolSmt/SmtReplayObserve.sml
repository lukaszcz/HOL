(* Opt-in capture of complete local replay obligations.  The observer is
   diagnostic: it receives the result after the checked procedure has run,
   and cannot supply a theorem or change the procedure's selected route. *)
structure SmtReplayObserve =
struct
  type inputs =
    {domain : string, identifier : string,
     premises : (string * Thm.thm) list,
     terms : (string * Term.term) list,
     scope : Term.term list,
     definitions : (string * Term.term * Thm.thm) list,
     metadata : (string * string) list}
  type observation =
    {inputs : inputs, elapsed : Time.time, user : Time.time,
     system : Time.time, gc : Time.time,
     outcome : string, result : Thm.thm option}
  val observer = ref (NONE : (observation -> unit) option)
  fun outcome result = case result of
      Exn.Res _ => "success"
    | Exn.Exn (Feedback.HOL_ERR error) =>
        if SmtResource.is_resource_gate error then "resource" else "HOL_ERR"
    | Exn.Exn Conv.UNCHANGED => "unsupported"
    | Exn.Exn (HolSatLib.SAT_cex _) => "SAT-cex"
    | Exn.Exn (HolSatLib.SAT_satisfiable _) => "SAT"
    | Exn.Exn Interrupt => "interrupt"
    | Exn.Exn (Timeout.TIMEOUT _) => "timeout"
    | Exn.Exn error => General.exnName error
  fun run inputs project action =
    case !observer of
      NONE => action ()
    | SOME observe =>
        let
          val context = inputs ()
          val real_timer = Timer.startRealTimer ()
          val cpu_timer = Timer.startCPUTimer ()
          val result = Exn.capture action ()
          val {nongc, gc} = Timer.checkCPUTimes cpu_timer
          val elapsed = Timer.checkRealTimer real_timer
          val theorem = case result of Exn.Res value => SOME (project value)
            | Exn.Exn _ => NONE
          val observation =
            {inputs = context, elapsed = elapsed, user = #usr nongc,
             system = #sys nongc, gc = Time.+ (#usr gc, #sys gc),
             outcome = outcome result, result = theorem}
          (* A diagnostic write failure must not mask an original resource
             failure, interrupt or other exception from checked replay. *)
          val _ = observe observation handle error =>
            (case result of Exn.Exn original => raise original
             | Exn.Res _ => raise error)
        in Exn.release result end

  (* Retain actual kernel theorem objects and typed terms for a diagnostic
     heap checkpoint.  Serializing them through DiskThms would traverse
     unfolded syntax during atom collection, defeating shared DAG inputs.
     A Poly/ML harness can save one self-contained state containing these
     observations; retention is opt-in and caller-controlled. *)
  val retained = ref ([] : observation list)
  fun retain observation = retained := observation :: !retained
  fun observations () = List.rev (!retained)
  fun clear () = retained := []
  fun write_metadata prefix (observation : observation) =
    let
      val {inputs, elapsed, user, system, gc, outcome, result} = observation
      val {domain, identifier, premises, terms, scope,
        definitions, metadata} = inputs
      val stream = TextIO.openOut (prefix ^ ".txt")
      fun row (key, value) = TextIO.output (stream,
        String.toString key ^ "=" ^ String.toString value ^ "\n")
      val fields =
        [("domain", domain), ("identifier", identifier),
         ("outcome", outcome), ("elapsed", Time.toString elapsed),
         ("user", Time.toString user), ("system", Time.toString system),
         ("gc", Time.toString gc),
         ("premises", Int.toString (List.length premises)),
         ("scope", Int.toString (List.length scope))] @ metadata @
        Lib.mapi (fn index => fn (name, _, _) =>
          ("definition-name/" ^ Int.toString index, name)) definitions
      val written = Exn.capture (List.app row) fields
      val _ = TextIO.closeOut stream
    in Exn.release written end
end
