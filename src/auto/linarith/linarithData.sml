structure linarithData :> linarithData =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "linarithData"

fun same_type left right = Type.compare (left, right) = EQUAL

type linarith_instance = {
  ty : hol_type,
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
  kit : {
    add_mono : thm list,
    mult_mono : thm list,
    not_less : thm,
    not_le : thm,
    neqE : thm,
    nonneg : term -> thm option
  },
  norm_conv : conv,
  nnf_rules : thm list,
  pre_split : thm list,
  atom_facts : term -> thm list
}

(* The dest record is matched whole, without a ... wildcard, so that a
   new destructor is a compile error here instead of a silently wrong
   complement at the sites that reason about it. *)
fun compound_ops
      ({dest = {dest_plus = _, dest_minus, dest_neg, dest_mult = _,
                dest_div, dest_suc, dest_lit = _, mk_lit = _,
                dest_less = _, dest_leq = _}, ...} : linarith_instance) =
  let
    fun recognises f tm = Option.isSome (Lib.total f tm)
  in
    List.mapPartial Lib.I
      [Option.map recognises dest_minus,
       Option.map recognises dest_neg,
       Option.map recognises dest_div,
       Option.map recognises dest_suc]
  end

type linarith_injection = {
  from_ty : hol_type,
  to_ty : hol_type,
  inj : term,
  hom : {le : thm, lt : thm, eq : thm, add : thm, mul : thm}
}

val instance_registry = Sref.new ([] : linarith_instance list)

fun register_instance instance =
  let
    val ty = #ty instance
    fun same_carrier entry = same_type ty (#ty entry)
    val replaced =
      Sref.gen_update instance_registry
        (fn entries =>
          (instance :: List.filter (not o same_carrier) entries,
           List.exists same_carrier entries))
  in
    if replaced then
      HOL_WARNING "linarithData" "register_instance"
        ("replacing the linarith instance for type " ^
         Parse.type_to_string ty)
    else
      ()
  end

fun instance_for ty =
  List.find (fn instance => same_type ty (#ty instance))
    (Sref.value instance_registry)

fun all_instances () = Sref.value instance_registry

val injection_registry = Sref.new ([] : linarith_injection list)

fun same_injection left right =
  (same_type (#from_ty left) (#from_ty right) andalso
   same_type (#to_ty left) (#to_ty right)) orelse
  Term.aconv (#inj left) (#inj right)

fun register_injection injection =
  Sref.update injection_registry
    (fn entries =>
      injection :: List.filter (not o same_injection injection) entries)

fun injections () = Sref.value injection_registry

fun injection_for from_ty to_ty =
  List.find
    (fn injection =>
      same_type from_ty (#from_ty injection) andalso
      same_type to_ty (#to_ty injection))
    (injections ())

fun injection_by_const constant =
  List.find (fn injection => Term.aconv constant (#inj injection))
    (injections ())

val persistent_name = KernelSig.name_toString

fun remove_name name table =
  let
    val key =
      if String.isSubstring "$" name then name
      else persistent_name (ThmSetData.toKName name)
  in
    Symtab.delete_safe key table
  end

fun apply_arith_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        Symtab.update (persistent_name name, theorem) table
    | ThmSetData.REMOVE name => remove_name name table

(* The P-form test is the whole of split validation; the two channels
   differ only in how they name what they rejected. *)
fun check_asm_split function what theorem =
  (ignore (splitLib.is_asm_split theorem)
   handle HOL_ERR _ => raise ERR function ("Malformed " ^ what))

fun apply_arith_split_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        let
          val _ =
            check_asm_split "apply_arith_split_delta"
              ("[arith_split] theorem " ^ persistent_name name) theorem
        in
          Symtab.update (persistent_name name, theorem) table
        end
    | ThmSetData.REMOVE name => remove_name name table

fun guard_registration settype =
  if List.exists (equal settype) (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute settype
  then
    raise ERR "registration"
      ("settype or attribute " ^ settype ^ " already exists")
  else
    ()

val _ = guard_registration "arith"
val _ = guard_registration "arith_split"

val arith_data =
  ThmSetData.export_with_ancestry
    {settype = "arith",
     delta_ops =
       {apply_to_global = apply_arith_delta,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_arith_delta}}

val arith_split_data =
  ThmSetData.export_with_ancestry
    {settype = "arith_split",
     delta_ops =
       {apply_to_global = apply_arith_split_delta,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_arith_split_delta}}

fun table_thms data = map #2 (Symtab.dest (#get_global_value data ()))

fun arith_facts () = table_thms arith_data
fun arith_split_thms () = table_thms arith_split_data

fun remove data apply_delta name =
  let
    val delta = ThmSetData.REMOVE name
    val _ = #update_global_value data (apply_delta delta)
  in
    #record_delta data delta
  end

fun remove_arith name = remove arith_data apply_arith_delta name
fun remove_arith_split name =
  remove arith_split_data apply_arith_split_delta name

type linarith_config = {neq_limit : int, split_limit : int}

val default_config : linarith_config = {neq_limit = 9, split_limit = 9}

val trace_level = ref 0
val _ = Feedback.register_trace ("linarith", trace_level, 3)

fun tracing level = !trace_level >= level

(* Rendering a theorem or a term list costs more than the test that
   decides whether anyone will read it, so every helper asks first.  A
   caller that has to build its message itself asks with tracing. *)
fun trace level message =
  if tracing level then print ("linarith: " ^ message ^ "\n") else ()

fun trace_thm level label theorem =
  if tracing level then
    trace level (label ^ "\n" ^ Parse.thm_to_string theorem)
  else ()

fun trace_items level label render items =
  if tracing level then
    trace level
      (label ^
       (if null items then " <none>"
        else "\n" ^ String.concatWith "\n" (map render items)))
  else ()

fun trace_terms level label terms =
  trace_items level label Parse.term_to_string terms

end
