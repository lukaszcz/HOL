signature def_cnf =
sig

  include Abbrev
  val presimp_conv : conv
  exception to_cnf_unsat of thm
  (* Pass SOME only when the producer already counted the distinct atoms. *)
  val explicit_cnf : int option -> term ->
               (string option * int *
                (term,term)satCommonTools.RBM.dict *
                (term * thm) Array.array)
  val to_cnf : bool -> term ->
               (string option * int *
                (term,term)satCommonTools.RBM.dict *
                (term * thm) Array.array)

end
