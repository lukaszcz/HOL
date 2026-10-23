(* Extension-owned recipes for numSimps's logged numeral defaults only.
   These are opt-in values: loading this module changes no default simpset.
   The ordinary log appends REDUCE, ARITH_RWTS, then MOD, in that order. *)
signature numSimpsExt =
sig
  val REDUCE_ss     : simpExtLib.ssfrag
  val ARITH_RWTS_ss : simpExtLib.ssfrag
  val MOD_ss        : simpExtLib.ssfrag
end
