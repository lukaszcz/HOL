(* Strict legacy parsing only: no ExclX or other branch-only APIs. *)
val _ = LegacyFailures.start "exclusion-parsing";
val _ = ExclusionParsing.run ();
val _ = LegacyFailures.finish ();
