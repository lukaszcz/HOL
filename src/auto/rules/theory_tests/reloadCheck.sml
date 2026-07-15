open HolKernel clasetLib
open reloadBaseTheory

fun fail message = raise Fail ("claset reload test: " ^ message)

val prefix = "__claset_tyinfo_reloadBase_reload_datatype_"

fun begins_with prefix name =
  size name >= size prefix andalso
  String.substring (name, 0, size prefix) = prefix

val reload_rules =
  List.filter
    (fn (_, (name, _)) => begins_with prefix name)
    (rules_of (the_claset ()))

fun same_statement (_, (_, th1)) (_, (_, th2)) =
  Term.aconv (concl (clasetRules.canonical_rule th1))
    (concl (clasetRules.canonical_rule th2))

fun has_duplicate [] = false
  | has_duplicate (rule :: rest) =
      List.exists (same_statement rule) rest orelse has_duplicate rest

val _ =
  if List.null reload_rules then
    fail "the TypeBase hook did not add reload_datatype rules"
  else if has_duplicate reload_rules then
    fail "reloading duplicated a TypeBase-derived rule"
  else ()
