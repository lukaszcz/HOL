(* Opt-in recipes for realSimps's logged defaults, in append order.
   Loading this module does not update any default simpset or compute set. *)
signature realSimpsExt =
sig
  val REAL_REDUCE_ss : simpExtLib.ssfrag
  val RMULCANON_ss : simpExtLib.ssfrag
  val RMULRELNORM_ss : simpExtLib.ssfrag
end
