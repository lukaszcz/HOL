signature aesopData =
sig
  (* The simpset of the context a tactic is run in; aesop_ss is that of
     the ambient context *)
  val aesop_ss_of : Context.t -> simpExtLib.simpset
  val aesop_ss : unit -> simpExtLib.simpset
  (* aesop.trace, the search's trace level *)
  val tracer : traceUtil.tracer
end
