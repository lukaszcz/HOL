signature SmtWordGraph =
sig
  type metrics =
    (* generated_nodes/edges count newly reachable schema-result nodes after
       instantiation.  They are observations of the staged result graph, not
       a count of allocations performed inside the kernel. *)
    {input_nodes : int,
     visited_nodes : int,
     generated_nodes : int,
     generated_edges : int,
     normalized_nodes : int,
     normalized_dag_nodes : int,
     projection_states : int,
     boolean_nodes : int,
     final_dag_nodes : int,
     type_nodes : int,
     type_tree_work : int,
     operator_calls : int,
     memo_hits : int}

  val normalize : Conv.conv
  val normalize_with_metrics : Term.term -> Thm.thm * metrics
  val normalize_with_node_conversion : Conv.conv -> Conv.conv
  val normalize_with_node_conversion_and_metrics :
    Conv.conv -> Term.term -> Thm.thm * metrics
  val normalize_using_with_metrics :
    {word_conversion : Conv.conv, bit_conversion : Conv.conv,
     node_conversion : Conv.conv} -> Term.term -> Thm.thm * metrics
  (* Total small arithmetic boundary oracle used by admission regressions. *)
  val eager_product_fits_for_test :
    int -> Arbnum.num -> Arbnum.num -> bool

  (* Operation-local numeric admission shared by word-bearing converters.
     Unknown dimensions decline before an eager evaluator is called; excessive
     concrete dimensions retain the existing BitVector resource diagnostics. *)
  type type_admission
  val new_type_admission : unit -> type_admission
  val admit_primitive_type : type_admission -> Type.hol_type -> unit
  val primitive_type_id : type_admission -> Type.hol_type -> int
  val word_width : type_admission -> Type.hol_type -> Arbnum.num
end
