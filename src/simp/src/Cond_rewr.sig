(* ----------------------------------------------------------------------
    COND_REWR_CONV : thm -> bool -> (term -> thm) -> conv

    Build a conversion based on a conditional rewrite theorem.  The
    theorem must be of the form

          A |- P1 ==> ... Pm ==> (Q[x1,...,xn] = R[x1,...,xn])

    The conversion matches the input term against Q, using limited
    higher order matching.  This instantiates x1 ... xn, which the
    conversion then solves with the solver provided.  If any of the
    conditions are not solved COND_REWR_CONV fails.

    The theorem can be a permutative rewrite, such as
         |- (x = y) = (y = x)
         |- (x + y) = (y + x)

    In these cases the rewrite will be applied if

      * the ordering of the variables in the term is not in strictly
        ascending order, according to a term_lt function which places
        a total ordering on terms (Nb. The term ordering needs to be
        "AC" compatible - see Termord); or
      * if the boolean argument is true, which happens if the theorem
        being used is a bounded rewrite, and so cannot cause a loop
        when it is used.

    FAILURE CONDITIONS

    Fails if any of the assumptions cannot be solved by the solver,
    or if the term does not match the rewrite in the first place.
   ---------------------------------------------------------------------- *)

signature Cond_rewr =
sig

  include Abbrev
  type controlled_thm = BoundedRewrites.controlled_thm
  val ac_term_ord    : term * term -> order
  val mk_cond_rewrs  : controlled_thm -> controlled_thm list
  val IMP_EQ_CANON   : controlled_thm -> controlled_thm list
  val COND_REWR_CONV : string * thm -> bool ->
                       (term list -> term -> thm) -> term list -> conv
  val QUANTIFY_CONDITIONS : controlled_thm -> controlled_thm list
  val stack_limit : int ref

  (* run something, and report which rewrites fired while it ran *)
  val with_tracking : ('a -> 'b) -> 'a -> 'b * thm list

  (* Read-only access to the exact captured stock false templates.
     No new genvar/theorem is produced by selecting or reading a handle. *)
  datatype false_template_kind=FalseConclusion | TruthEqualsFalse
    | FalseEqualsTruth
  type false_template
  val false_template : false_template_kind -> false_template
  val false_template_data : false_template ->
    {proof:thm,condition:term,result:term}

  (* Read-only singleton of the SAME existing EQ_SYM_EQ namespace object. *)
  type eq_sym_template
  val eq_sym_template : unit -> eq_sym_template
  val eq_sym_template_data : eq_sym_template -> {proof:thm,statement:term}

  (* Exact existing Cond operator/law capture. Selector/getter create no
     theorem, variable or Source admission; P does not depend on Cond. *)
  val CONJ_DISCH : term list -> thm -> thm
  type conj_discharge_template
  val conj_discharge_template : unit -> conj_discharge_template
  val conj_discharge_template_data : conj_discharge_template ->
    {proof:thm,first:term,second:term,third:term}

  (* Immutable native-constructor DATA beside the SAME existing cache.
     No current declaration validity, fee, Scope or proof admission. *)
  val conj_discharge_constructor_data : conj_discharge_template ->
    {statement:term,tag:Tag.tag,bare:bool,closed:bool}

  (* SAME existing law and actual separate forall/exists binder DATA only.
     Selecting/reading this handle grants no Source, Scope or Work credit. *)
  type left_forall_imp_template
  val left_forall_imp_template : unit -> left_forall_imp_template
  val left_forall_imp_template_data : left_forall_imp_template ->
    {proof:thm,statement:term,outer_predicate:term,
     outer_consequent:term,forall_binder:term,exists_binder:term}

  (* A unit-only fixed-law match to genuine default-decoder origin.
     This supplies no current declaration validity, scoped permission,
     proof getter, FV fact, invoice or executable Ready authority. *)
  type left_forall_imp_decode_origin
  val left_forall_imp_decode_origin : unit ->
    left_forall_imp_decode_origin option


end
