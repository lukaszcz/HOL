(* Probe: a kind's work, then the registries and live words. *)
val t33_probe = "registry"
val t33_switches = T33.switches_json
val _ = T33.install_hook ()
val _ = QUse.use "T33Kind.ML"
val _ = (T33.probe := t33_probe; T33.kind := t33_kind;
         T33.registry (); T33.finish ())
