(* Optional actual public instantiation-site DATA, never Work authority. *)
signature SmtReplayInstanceObservation =
sig
  type statistics =
    {inst_calls:IntInf.int,inst_type_calls:IntInf.int,
     schema_raw_nodes:IntInf.int,schema_inc_nodes:IntInf.int,
     schema_annotation_nodes:IntInf.int}
  val with_statistics : (unit -> 'a) -> 'a * statistics
  (* Exact repeated input concl+Hyp DATA; memo visits each physical term. *)
  val input_profile : Thm.thm ->
    {raw:IntInf.int,inc:IntInf.int,annotations:IntInf.int}
  val inst : (Term.term,Term.term) Lib.subst -> Thm.thm -> Thm.thm
  val inst_type : (Type.hol_type,Type.hol_type) Lib.subst -> Thm.thm -> Thm.thm
  (* Exact Drule.INST_TY_TERM order: actual INST_TYPE followed by INST. *)
  val inst_ty_term : (Term.term,Term.term) Lib.subst *
    (Type.hol_type,Type.hol_type) Lib.subst -> Thm.thm -> Thm.thm
end
