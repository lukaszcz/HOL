signature linarithData =
sig
  include Abbrev

  type linarith_instance = {
    ty : hol_type,
    discrete : bool,
    dest : {
      dest_plus : term -> term * term,
      dest_minus : (term -> term * term) option,
      dest_neg : (term -> term) option,
      dest_mult : term -> term * term,
      dest_div : (term -> term * term) option,
      dest_suc : (term -> term) option,
      dest_lit : term -> Arbrat.rat,
      mk_lit : Arbrat.rat -> term,
      dest_less : term -> term * term,
      dest_leq : term -> term * term
    },
    kit : {
      add_mono : thm list,
      mult_mono : thm list,
      lessD : thm list,
      not_less : thm,
      not_le : thm,
      neqE : thm,
      nonneg : term -> thm option
    },
    norm_conv : conv,
    nnf_rules : thm list,
    pre_split : thm list,
    atom_facts : term -> thm list,
    divmod_facts : (term -> thm list) option
  }

  type linarith_injection = {
    from_ty : hol_type,
    to_ty : hol_type,
    inj : term,
    hom : {le : thm, lt : thm, eq : thm, add : thm, mul : thm}
  }

  val register_instance : linarith_instance -> unit
  val instance_for : hol_type -> linarith_instance option
  val all_instances : unit -> linarith_instance list

  val register_injection : linarith_injection -> unit
  val injections : unit -> linarith_injection list
  val injection_for : hol_type -> hol_type -> linarith_injection option
  val injection_by_const : term -> linarith_injection option

  val arith_facts : unit -> thm list
  val arith_split_thms : unit -> thm list
  val remove_arith : string -> unit
  val remove_arith_split : string -> unit

  type linarith_config = {neq_limit : int, split_limit : int}
  val default_config : linarith_config

  val trace_level : int ref
  val trace : int -> string -> unit
  val trace_thm : int -> string -> thm -> unit
  val trace_terms : int -> string -> term list -> unit
  val trace_items : int -> string -> ('a -> string) -> 'a list -> unit
end
