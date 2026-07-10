(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB datatype lemmas. *)

structure SmtDatatypeProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtDatatypeProve"

  fun unsupported t =
    raise ERR "datatype_prove"
      ("unsupported th-lemma shape: theory=datatype; checked replay is not " ^
       "implemented for datatype lemmas yet; conclusion=" ^
       Library.term_to_string t)

  fun datatype_prove t = unsupported t

end
