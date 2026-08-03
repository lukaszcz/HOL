signature linarithData =
sig
  include Abbrev

  (* One carrier's implementation of everything the generic engine
     needs, keyed in the registry by its ty.

     "No value" means two different things here.  A NONE in dest is a
     static fact about the carrier -- it has no such operator at all --
     and never a refusal of a particular term.  The destructors that
     are not optional are partial in the usual xxxSyntax way: they
     raise on a term of the wrong shape, and their callers wrap them in
     Lib.total.  The one per-term option is kit's nonneg, which
     declines the atom it is offered.

     dest_plus, dest_leq and dest_mult are also run over the kit
     theorems to read the carrier's operator constants off them, so
     add_mono must mention addition and non-strict order; a mult_mono
     mentioning no multiplication makes replay scale by repeated
     addition instead.  mk_lit is only ever asked for integer
     values. *)
  type linarith_instance = {
    ty : hol_type,
    (* SOME {lessD} exactly for a discrete order, lessD strengthening a
       strict inequality to the non-strict one about the next element
       (num: |- m < n <=> m + 1 <= n).  These are the discreteness
       theorems only -- everything else replay applies is in kit -- and
       a dense carrier gives NONE and never needs them. *)
    discrete : {lessD : thm list} option,
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
    (* Replay matches these against derived theorems: add_mono adds two
       relations, mult_mono scales one by a positive literal, not_less
       and not_le are the negated-order equivalences (|- ~(x < y) <=>
       y <= x and |- ~(x <= y) <=> y < x), and neqE eliminates a
       disequality, in the shape
       |- x <> y ==> (x < y ==> F) ==> (y < x ==> F) ==> F.
       nonneg atom is SOME (|- 0 <= atom) for an atom of this carrier
       known to be non-negative and NONE to decline it; search adds a
       non-negativity row exactly where it answers SOME, so an answer
       that varies between the two calls makes replay report a declined
       atom. *)
    kit : {
      add_mono : thm list,
      mult_mono : thm list,
      not_less : thm,
      not_le : thm,
      neqE : thm,
      nonneg : term -> thm option
    },
    (* Normalizes a relation or an expression of the carrier, and
       reduces to T the trivially true relations replay builds.  It
       may report "no change" by raising UNCHANGED -- num, int and
       real end theirs in ALL_CONV, which does -- since replay either
       absorbs that exception or drops it with Lib.total.  The one
       thing it must decide is reflexivity: replay hands left <= left
       straight to EQT_ELIM, so an instance that leaves that term
       alone raises UNCHANGED out of the whole tactic rather than
       failing. *)
    norm_conv : conv,
    (* Carrier rewrites (num: SUB_EQ_0) applied to the assumptions
       after the propositional negation-normal-form pass, not as part
       of it. *)
    nnf_rules : thm list,
    (* P-form operator-splitting rules arriving with the instance:
       session-global, independent of theory ancestry, and not
       removable -- remove_arith_split reaches only the user
       [arith_split] table. *)
    pre_split : thm list,
    (* Extra facts about one atom.  Every registered instance's
       atom_facts is called on every atom, whatever the atom's carrier,
       so it must return [] for the terms it does not recognize; firing
       outside its own carrier is allowed and deliberate (the int
       instance returns INT_OF_NUM facts for Num i : num). *)
    atom_facts : term -> thm list
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

  (* check_asm_split function what th: raise ERR function
     ("Malformed " ^ what) unless th is a split rule in P-form. *)
  val check_asm_split : string -> string -> thm -> unit

  type linarith_config = {neq_limit : int, split_limit : int}
  val default_config : linarith_config

  val trace : int -> string -> unit
  val trace_thm : int -> string -> thm -> unit
  val trace_terms : int -> string -> term list -> unit
  val trace_items : int -> string -> ('a -> string) -> 'a list -> unit
end
