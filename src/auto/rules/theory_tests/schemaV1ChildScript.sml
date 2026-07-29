Theory schemaV1Child
Ancestors
  schemaV1Base
Libs
  clasetLib

open clasetLib

fun fail message =
  raise Fail ("claset schema-v1 compatibility test: " ^ message)

fun find_rule name =
  List.find (fn (_, (name', _)) => name = name') (rules_of (the_claset ()))

fun has_spec name kind prio =
  case find_rule name of
      SOME ({kind = kind', safe = false, prio = prio'}, _) =>
        kind = kind' andalso prio = prio'
    | _ => false

val _ =
  if not
    (has_spec "schemaV1Base$schema_v1_intro"
       clasetRules.Intro (SOME 64))
  then fail "the intro clasetADD1 delta did not reload"
  else if not
    (has_spec "schemaV1Base$schema_v1_elim"
       clasetRules.Elim (SOME 37))
  then fail "the elim clasetADD1 delta did not reload"
  else if not
    (has_spec "schemaV1Base$schema_v1_dest"
       clasetRules.Dest (SOME 82))
  then fail "the dest clasetADD1 delta did not reload"
  else ()
