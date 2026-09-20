signature SmtFpGraph =
sig
  type term = Term.term
  type thm = Thm.thm

  exception Declined of string

  type descriptor =
    {value : term, sign : term, exponent : term, fraction : term,
     representation : thm}

  (* The representation theorem states that value is smtfp_bits of the three
     fields.  Selected constants have concrete fields; NaN uses sign zero and
     all-ones exponent/fraction as one checked representative of the abstract
     NaN value.  Arbitrary variables and uninterpreted FP leaves may retain
     smtfp_rep selectors in their fields.

     convert_atom lowers the selected classifiers and comparisons to Boolean
     and word structure.  Its RHS contains none of the selected smtfloat
     predicates or their smtfp_nan_pattern, smtfp_mag_lt, and smtfp_word_*
     helpers.  Converting the resulting word structure is a separate stage. *)
  val represent : term -> descriptor
  val convert_atom : term -> thm
  val convert_word_projection : Conv.conv
  (* Exact outer-shape domain of [lower_atom], excluding dynamic resource and
     producer failures discovered while constructing the conversion. *)
  val lower_atom_domain : term -> bool
  (* Compose FP conversion with sharing-preserving field and word lowering. *)
  val lower_atom : term -> thm
end
