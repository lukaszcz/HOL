(* Exact genuine emitter provenance; semantic data, not Work admission. *)
signature SmtLib_TranslationEmissions =
sig
  type receipt
  type options =
    {policy : SmtLib.logic_selection_policy,dialect : SmtLib.ho_dialect,
     apply_operator : SmtLib.standard27_apply_operator,get_proof : bool,
     target : {solver:string,version:string option} option}
  val emit : options -> Abbrev.goal ->
    {receipt:receipt,translation:SmtLib.translation,strings:string list}
  (* Compare expected translation and exact input goal before the held
     receipt's epoch checks. Records derive from one genuine emitter call. *)
  val describe_for : SmtLib.translation -> Abbrev.goal -> receipt ->
    {records:SmtLib.translation_record list,
     definitions:SmtLib.emitted_definition list}
end
