(* Loaded after the driver records the heap and activates path tracing. *)
val _ = Paired.report := (fn (name, passed) =>
  (testutils.tprint name;
   if passed then testutils.OK () else testutils.die name))
