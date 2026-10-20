(* Identical legacy-only history input for both pinned lanes. *)
val _ = LegacyFailures.start "exclusion-history";
val _ = ExclusionHistory.run ();
val _ = LegacyFailures.finish ();
