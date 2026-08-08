(* Copyright (c) 2026 The HOL4 contributors. *)

(* Checked replay support for the Z3 Int-array bag encoding. *)

signature SmtBagProve =
sig

  val has_bag_encoding : Term.term -> bool

  val bag_prove_with_arith :
    (Term.term -> Thm.thm) -> Term.term -> Thm.thm
  val bag_prove : Term.term -> Thm.thm

end
