structure seedCollections :> seedCollections =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "seedCollections"
val persistent_name = KernelSig.name_toString

fun apply_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        Symtab.update (persistent_name name, theorem) table
    | ThmSetData.REMOVE name => Symtab.delete_safe name table

fun guard_registration settype =
  if List.exists (equal settype) (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute settype
  then
    raise ERR "registration"
      ("settype or attribute " ^ settype ^ " already exists")
  else
    ()

fun register settype =
  let
    val _ = guard_registration settype
  in
    ThmSetData.export_with_ancestry
      {settype = settype,
       delta_ops =
         {apply_to_global = apply_delta,
          thy_finaliser = NONE,
          uptodate_delta = K true,
          initial_value = Symtab.empty,
          apply_delta = apply_delta}}
  end

val algebra_data = register "algebra_simps"
val field_data = register "field_simps"

fun table_entries data = Symtab.dest (#get_global_value data ())
fun table_thms data = map #2 (table_entries data)
fun persistent_to_name name =
  case String.fields (equal #"$") name of
      [thy, theorem] => {Thy = thy, Name = theorem}
    | _ => raise ERR "persistent_to_name" ("Malformed name: " ^ name)
fun named_entries data =
  map (fn (name, theorem) => (persistent_to_name name, theorem))
    (table_entries data)

fun algebra_rewrites () = table_thms algebra_data
fun field_rewrites () = table_thms field_data

fun algebra_ss () = simpLib.rewrites_with_names (named_entries algebra_data)
fun field_ss () = simpLib.rewrites_with_names (named_entries field_data)

fun removal_key function name =
  let
    val key = clasetLib.normalise_rule_name name
  in
    if String.isSubstring "$" key then key
    else raise ERR function ("Malformed name: " ^ name)
  end

fun remove data function name =
  let
    val delta = ThmSetData.REMOVE (removal_key function name)
    val _ = #update_global_value data (apply_delta delta)
  in
    #record_delta data delta
  end

fun remove_algebra_simps name =
  remove algebra_data "remove_algebra_simps" name

fun remove_field_simps name =
  remove field_data "remove_field_simps" name

end
