(* Probe: startup and load kinds, the timed ones.  No T33 support code. *)
val t33_probe = "load"
val t33_switches =
  "{\"graph_extra\":false,\"leak\":false,\"hook\":false}"
val _ = QUse.use "T33Kind.ML"
val _ = t33_emit "done" []
