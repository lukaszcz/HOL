(* Copyright (c) 2026 The HOL4 contributors. *)

(* These proof-local constructors inspect only bounded schematic operands.
   The ordinary and graph dictionaries retain the same overload order. *)
structure Z3_ProofConstructors =
struct
  type callback = string -> Term.term list -> Term.term list -> Term.term
  val equality : callback = SmtLib_Theories.chainable
    (SmtLib_Theories.same_type_binary SmtRegLanProve.proof_equality)
  val entries : (string * callback) list =
    [("iff", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
     ("implies", SmtLib_Theories.K_zero_two boolSyntax.mk_imp),
     ("~", SmtLib_Theories.K_zero_two boolSyntax.mk_eq),
     ("~", SmtLib_Theories.K_zero_one
       (SmtLib_Theories.typed_unary intSyntax.int_ty intSyntax.mk_negated)),
     ("~", SmtLib_Theories.K_zero_one
       (SmtLib_Theories.typed_unary realSyntax.real_ty realSyntax.mk_negated)),
     ("mkbv", SmtLib_Theories.K_zero_list (fn values =>
       bitstringSyntax.mk_v2w
         (listSyntax.mk_list (List.rev values, Type.bool),
          fcpSyntax.mk_int_numeric_type (List.length values))))]
end
