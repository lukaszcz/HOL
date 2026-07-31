structure linarithData :> linarithData =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "linarithData"

fun same_type left right = Type.compare (left, right) = EQUAL

fun find _ [] = NONE
  | find predicate (item :: rest) =
      if predicate item then SOME item else find predicate rest

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

val instance_registry =
  Sref.new ([] : (hol_type * linarith_instance) list)

fun register_instance instance =
  let
    val ty = #ty instance
    val replaced =
      Sref.gen_update instance_registry
        (fn entries =>
          let
            val replaced =
              List.exists (fn (old_ty, _) => same_type ty old_ty) entries
            val others =
              List.filter (fn (old_ty, _) => not (same_type ty old_ty))
                entries
          in
            ((ty, instance) :: others, replaced)
          end)
  in
    if replaced then
      HOL_WARNING "linarithData" "register_instance"
        ("replacing the linarith instance for type " ^
         Parse.type_to_string ty)
    else
      ()
  end

fun instance_for ty =
  Option.map #2
    (find (fn (registered_ty, _) => same_type ty registered_ty)
      (Sref.value instance_registry))

fun all_instances () = map #2 (Sref.value instance_registry)

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
  find
    (fn injection =>
      same_type from_ty (#from_ty injection) andalso
      same_type to_ty (#to_ty injection))
    (injections ())

fun injection_by_const constant =
  find (fn injection => Term.aconv constant (#inj injection))
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

fun validate_split name theorem =
  (ignore (splitLib.is_asm_split theorem)
   handle HOL_ERR _ =>
     raise ERR "apply_arith_split_delta"
       ("Malformed [arith_split] theorem " ^ persistent_name name))

fun apply_arith_split_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        let
          val _ = validate_split name theorem
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

fun trace level message =
  if !trace_level >= level then print ("linarith: " ^ message ^ "\n")
  else ()

fun trace_thm level label theorem =
  trace level (label ^ "\n" ^ Parse.thm_to_string theorem)

fun trace_items level label render items =
  trace level
    (label ^
     (if null items then " <none>"
      else "\n" ^ String.concatWith "\n" (map render items)))

fun trace_terms level label terms =
  trace_items level label Parse.term_to_string terms

end
