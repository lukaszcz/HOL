(* Copyright (c) 2026 The HOL4 contributors. *)

signature SmtSeqProve =
sig

  val has_seq_type : Term.term -> bool

  val concat_length_prove : Term.term -> Thm.thm
  val unit_empty_prove : Term.term -> Thm.thm
  val access_prove : Term.term -> Thm.thm
  val seq_prove : Term.term -> Thm.thm

end
