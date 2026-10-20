open HolKernel Parse boolLib boolSimps simpLib splitLib testutils

val _ = Theory.new_theory "split_registration"
fun check label ok = (tprint label; if ok then OK () else die label)
fun free () = not (ThmAttribute.is_attribute "split") andalso
  not (List.exists (equal "split") (ThmSetData.all_set_types ()))
fun empty () = null (split_thms ()) andalso null (named_split_thms ())
fun same th1 th2 = aconv (concl th1) (concl th2) andalso
  ListPair.allEq (fn (a,b) => aconv a b) (hyp th1,hyp th2)
fun silent f =
  let
    val old = !Feedback.WARNING_outstream
    val warnings = ref ([] : string list)
    fun run () =
      (Feedback.WARNING_outstream := (fn s => (warnings := s :: !warnings;
                                               old s));
       f ())
    val result = Portable.finally
      (fn () => Feedback.WARNING_outstream := old) run ()
    val _ = check "operation emits no warnings" (null (!warnings))
  in result end
fun conflict () =
  let
    val ctxt = Context.snapshot ()
    val result =
      (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
    val _ = check "conflict leaves the entire Context unchanged"
      (Portable.pointer_eq (ctxt,Context.snapshot ()))
  in
    check "explicit conflict has library error identity"
      (case result of
           SOME e =>
             Feedback.top_structure_of e = "splitLib" andalso
             Feedback.top_function_of e = "enable_split_attribute" andalso
             Feedback.message_of e =
               "settype or attribute split already exists"
         | NONE => false)
  end

val uninitialized = Context.snapshot ()
val _ = check "ordinary static loading leaves split unclaimed" (free ())
val _ = check "uninitialized queries return no rules" (empty () andalso free ())
val rule = type_split_of ``:bool``
val goal : goal = ([],``P (if b then x:'a else y):bool``)
fun changed tac =
  case VALID tac goal (Context.snapshot ()) of
      ([(asms,result)],_) =>
        null asms andalso not (aconv result (#2 goal))
    | _ => false
val _ = check "pure conversion works before initialization"
  (not (aconv (rhs (concl (SPLIT_CONV [rule] (#2 goal)))) (#2 goal)))
val _ = check "local Split works before initialization"
  (changed (SIMP_TAC bool_ss [Split rule]))
val _ = check "TypeBase split_ss works before initialization"
  (changed (SIMP_TAC (bool_ss ++ split_ss) []))
val _ = check "local and TypeBase use claim no namespace" (free () andalso empty ())

val thy = Theory.current_theory ()
val name = {Thy=thy,Name="rule"}
val stored = save_thm ("rule",rule)
val attrarg = {name="rule",attrname="split",args=[],thm=stored}
val _ = silent enable_split_attribute
val _ = check "explicit initialization claims both registries"
  (ThmAttribute.is_attribute "split" andalso
   List.exists (equal "split") (ThmSetData.all_set_types ()) andalso empty ())
val attribute = valOf (ThmAttribute.attribute_fns "split")
val exporter = valOf (ThmSetData.data_exportfns {settype="split"})
val _ = ThmAttribute.store_at_attribute attrarg
fun has_rule () =
  case named_split_thms () of
      [(key,th)] => key = thy ^ "$rule" andalso same th stored
    | _ => false
val _ = check "stored attribute adds named rule and persistent ADD"
  (has_rule () andalso
   (case ThmSetData.current_data {settype="split"} of
        [ThmSetData.ADD (n,th)] => n = name andalso same th stored
      | _ => false))
val owned = Context.snapshot ()
val _ = silent enable_split_attribute
val _ = check "idempotent opt-in leaves the entire Context unchanged"
  (Portable.pointer_eq (owned,Context.snapshot ()))
val _ = check "idempotence preserves handlers and data"
  (has_rule () andalso
   Portable.pointer_eq
     (attribute,valOf (ThmAttribute.attribute_fns "split")) andalso
   Portable.pointer_eq
     (exporter,valOf (ThmSetData.data_exportfns {settype="split"})) andalso
   length (ThmSetData.current_data {settype="split"}) = 1)
val _ = #remove exporter {thy=thy,remove=thy ^ "$rule"}
val _ = check "owned exporter REMOVE updates queries" (empty ())
val _ = Context.restore owned
val _ = silent (fn () => ignore (save_thm ("touch_first",TRUTH)))
val _ = check "restore after opt-in recovers handle and data" (has_rule ())
val _ = Context.restore uninitialized
val _ = check "restore before opt-in discards handle and registries"
  (free () andalso empty ())
val _ = silent (fn () => ignore (save_thm ("touch_uninitialized",TRUTH)))
val _ = silent enable_split_attribute
val _ = check "can initialize again after rewind" (empty ())
val _ = save_thm ("rule",rule)
val _ = ThmAttribute.store_at_attribute attrarg
val _ = silent (fn () => ignore (save_thm ("touch_second",TRUTH)))
val _ = check "reinitialized theory-data hook uses its own witness"
  (has_rule () andalso
   length (ThmSetData.current_data {settype="split"}) = 1)
val _ = #remove (valOf (ThmSetData.data_exportfns {settype="split"}))
  {thy=thy,remove=thy ^ "$rule"}
val _ = ThmAttribute.local_attribute
  {name="local",attrname="split",args=[],thm=rule}
val _ = check "local attribute works without recording an ADD"
  (length (split_thms ()) = 1 andalso
   length (ThmSetData.current_data {settype="split"}) = 1)
val _ = Context.restore owned
val _ = silent (fn () => ignore (save_thm ("touch_restored",TRUTH)))
val _ = check "restore selects original handle and theory-data witness"
  (has_rule () andalso
   length (ThmSetData.current_data {settype="split"}) = 1)

(* Foreign attribute alone, with no theorem-set mutation on failure. *)
val _ = Context.restore uninitialized
val calls = ref 0
fun foreign_attr _ = calls := !calls + 1
val foreign_handlers = {localf=foreign_attr,storedf=foreign_attr}
val _ = ThmAttribute.register_attribute ("split",foreign_handlers)
val foreign_attribute = Context.snapshot ()
val _ = silent conflict
val _ = check "attribute conflict does not partially create a set"
  (empty () andalso
   not (List.exists (equal "split") (ThmSetData.all_set_types ())) andalso
   Portable.pointer_eq
     (foreign_handlers,valOf (ThmAttribute.attribute_fns "split")))
val _ = ThmAttribute.local_attribute attrarg
val _ = check "foreign attribute behavior survives" (!calls = 1)
val _ = Context.restore owned
val _ = check "owned state still usable" (has_rule ())
val _ = Context.restore foreign_attribute
val _ = check "restore to foreign attribute never uses stale handle" (empty ())
val _ = silent conflict

(* Public exporters claim both names. Check exact foreign data/handlers. *)
val _ = Context.restore uninitialized
val _ = save_thm ("foreign",TRUTH)
val additions = ref 0
val removals = ref 0
val foreign_efns =
  {add=fn _ => additions := !additions + 1,
   remove=fn _ => removals := !removals + 1}
val foreign_set = ThmSetData.new_exporter
  {settype="split",efns=foreign_efns}
val _ = #export foreign_set "foreign"
val foreign_both = Context.snapshot ()
fun foreign_intact () =
  Portable.pointer_eq
    (foreign_efns,valOf (ThmSetData.data_exportfns {settype="split"})) andalso
  (case ThmSetData.current_data {settype="split"} of
       [ThmSetData.ADD ({Thy,Name},th)] =>
         Thy = thy andalso Name = "foreign" andalso same th TRUTH
     | _ => false)
val _ = silent conflict
val _ = check "foreign set data is neither adopted nor mutated"
  (foreign_intact () andalso empty ())
val _ = Context.restore owned
val _ = Context.restore foreign_both
val _ = check "restore to foreign set returns no library rules"
  (foreign_intact () andalso empty ())
val _ = silent conflict

(* Replacements with an existing library handle must invalidate queries.
   For set-only ownership mismatch reinstall the original library attribute,
   so the theorem-set identity check is independently exercised. Warnings
   from these deliberate public replacements are expected and forwarded. *)
val _ = Context.restore owned
val _ = ThmAttribute.register_attribute ("split",foreign_handlers)
val _ = check "attribute replacement invalidates existing handle" (empty ())
val _ = silent conflict
val _ = Context.restore owned
val _ = save_thm ("foreign",TRUTH)
val _ = ThmSetData.new_exporter {settype="split",efns=foreign_efns}
val _ = ThmAttribute.register_attribute ("split",attribute)
val _ = check "set replacement alone invalidates existing handle" (empty ())
val _ = silent conflict
val _ = check "set-only conflict leaves original attribute untouched"
  (Portable.pointer_eq
     (attribute,valOf (ThmAttribute.attribute_fns "split")))
val _ = #add (valOf (ThmSetData.data_exportfns {settype="split"}))
  {thy=thy,named_thm=(name,rule)}
val _ = #remove (valOf (ThmSetData.data_exportfns {settype="split"}))
  {thy=thy,remove="foreign"}
val _ = check "foreign exporter callbacks survive conflicts"
  (!additions = 2 andalso !removals = 1)
(* A foreign ancestry exporter uses the same serialized data names, not
   the older exporter's bare split tag. Its UniversalType witnesses must
   not leak into a restored library registration. *)
val _ = Context.restore uninitialized
val foreign_ancestry = ThmSetData.export_simple_dictionary
  {settype="split",initial=[("foreign",TRUTH)]}
val _ = ThmAttribute.local_attribute
  {name="foreign_local",attrname="split",args=[],thm=TRUTH}
val foreign_ancestry_context = Context.snapshot ()
val _ = check "foreign ancestry data is not adopted"
  (empty () andalso length (#get_thms foreign_ancestry ()) = 2)
val _ = silent conflict
val _ = Context.restore owned
val _ = #remove exporter {thy=thy,remove=thy ^ "$rule"}
fun replay () =
  check "TheoryLoaded dispatch has no stale-witness exceptions"
    (null (Listener.call_listener Theory.delta_hook
             (TheoryDelta.TheoryLoaded thy)))
val _ = silent replay
val _ = check "restored library hook replays its own ADD" (has_rule ())
val _ = Context.restore foreign_ancestry_context
val _ = silent (fn () => ignore (save_thm ("touch_foreign",TRUTH)))
val _ = silent replay
val _ = check "restored foreign ancestry hook keeps foreign data"
  (empty () andalso length (#get_thms foreign_ancestry ()) = 2)
val _ = silent conflict

(* Listener-name conflicts are also preflighted before ancestry slots or
   loadable-data operations are allocated; retry after removal must work. *)
val _ = Context.restore uninitialized
val hookname = "ThmSetData.onload.split.deltas"
val dispatcher = valOf (Listener.remove_listener Theory.delta_hook hookname)
val _ = Theory.register_hook (hookname,K ())
val no_listener_context = Context.snapshot ()
val listener_error =
  (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
val _ = check "foreign listener rejected without partial Context mutation"
  (Portable.pointer_eq (no_listener_context,Context.snapshot ()) andalso
   free () andalso empty () andalso
   (case listener_error of
        SOME e => Feedback.top_structure_of e = "ThyDataSexp" andalso
                  Feedback.top_function_of e = "check_registration"
      | NONE => false))
val _ = Listener.remove_listener Theory.delta_hook hookname
val _ = Theory.register_hook (hookname,dispatcher)
val _ = silent enable_split_attribute
val _ = check "opt-in succeeds after foreign listener removal" (empty ())
val _ = Context.restore owned
val _ = check "final restoration recovers library rules" (has_rule ())
val _ = silent enable_split_attribute
val _ = Context.restore uninitialized
val _ = ThmAttribute.reserve_word "split"
val _ = silent conflict
val _ = check "reserved word conflict creates neither registry"
  (free () andalso empty ())
val _ = Context.restore uninitialized
val _ = ThmAttribute.define_abbreviation {abbrev="split",expansion=[]}
val _ = silent conflict
val _ = check "abbreviation conflict creates neither registry"
  (free () andalso empty ())
val _ = Context.restore uninitialized
val _ = ThmAttribute.define_abbreviation
  {abbrev="split",expansion=[("split",[])]}
val _ = silent conflict
val _ = check "cyclic abbreviation rejected without expansion"
  (free () andalso empty ())
val _ = Context.restore uninitialized
val _ = Context.with_context owned (fn () =>
  (check "pinned queries select owned snapshot" (has_rule ());
   silent enable_split_attribute)) ()
val _ = check "idempotent pinned opt-in does not mutate live context"
  (free () andalso empty ())
val _ = Context.restore owned
val _ = Context.with_context uninitialized (fn () =>
  let
    val _ = check "pinned pre-opt-in queries ignore live owned handle"
      (empty ())
    val result =
      (enable_split_attribute (); NONE) handle HOL_ERR e => SOME e
  in
    check "new initialization rejects pinned context"
      (case result of SOME e =>
         Feedback.top_function_of e = "enable_split_attribute" andalso
         Feedback.message_of e = "cannot initialize in a pinned context"
       | NONE => false)
  end) ()
val _ = check "rejected pinned initialization leaves live ownership intact"
  (has_rule ())
val _ = OS.Process.exit OS.Process.success
