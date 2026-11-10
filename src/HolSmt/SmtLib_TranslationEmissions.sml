structure SmtLib_TranslationEmissions :> SmtLib_TranslationEmissions =
struct
  type options =
    {policy:SmtLib.logic_selection_policy,dialect:SmtLib.ho_dialect,
     apply_operator:SmtLib.standard27_apply_operator,get_proof:bool,
     target:{solver:string,version:string option} option}
  datatype receipt = Receipt of
    {translation:SmtLib.translation,goal:Abbrev.goal,
     records:SmtLib.translation_record list,
     definitions:SmtLib.emitted_definition list,epoch:int,symbols:int}
  val _ = SmtLib.goal_to_SmtLib_translation_for_solver
  val ERR = Feedback.mk_HOL_ERR "SmtLib_TranslationEmissions"
  fun exact ((lefts,left),(rights,right)) =
    Portable.pointer_eq (left,right) andalso
    length lefts = length rights andalso
    ListPair.allEq Portable.pointer_eq (lefts,rights)
  fun emit (options:options) goal =
    let val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
        (* Caller cannot supply a translation, record or theorem. The fixed
           existing emitter constructs every declaration before selection. *)
        val (raw,strings) =
          SmtLib.goal_to_SmtLib_translation_for_solver options goal
        val records = SmtLib.translation_records raw
        val definitions = SmtLib.emitted_definitions_for_records records
        (* The old emitter rebuilds metadata on every records call. This
           additive result retains its ONE actual record collection so the
           exact EncodedSymbol identity survives parser and worker use. *)
        val translation : SmtLib.translation =
          {logic = #logic raw,regime = #regime raw,tydict = #tydict raw,
           tmdict = #tmdict raw,records = fn () => records}
        val _ = if Type.type_epoch () = epoch andalso
            Term.term_epoch () = symbols then () else
          raise ERR "emit" "translation callback changed declaration epoch"
        val receipt = Receipt {translation = translation,goal = goal,
          records = records,definitions = definitions,
          epoch = epoch,symbols = symbols}
    in {receipt = receipt,translation = translation,strings = strings} end
  fun describe_for expected goal
      (Receipt {translation,goal = original,records,definitions,
                epoch,symbols}) =
    (if Portable.pointer_eq (expected,translation) andalso exact (goal,original)
       then () else raise ERR "describe_for" "different actual translation";
     if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
       then () else raise ERR "describe_for" "declaration lifetime changed";
     {records = records,definitions = definitions})
end
