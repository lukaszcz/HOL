Theory schemaV2Child
Ancestors
  schemaV2Base
Libs
  clasetLib

open clasetLib

fun fail message =
  raise Fail ("claset schema-v2 reload test: " ^ message)

fun find_rule name =
  List.find (fn (_, (name', _)) => name = name') (rules_of (the_claset ()))

fun has_spec name kind safe prio =
  case find_rule name of
      SOME ({kind = kind', safe = safe', prio = prio'}, _) =>
        kind = kind' andalso safe = safe' andalso prio = prio'
    | NONE => false

val _ =
  if not
    (has_spec "schemaV2Base$schema_v2_forward"
       clasetRules.Forward false (SOME 73))
  then fail "the unsafe Forward clasetADD2 delta did not reload"
  else if not
    (has_spec "schemaV2Base$schema_v2_sforward"
       clasetRules.Forward true NONE)
  then fail "the safe Forward clasetADD2 delta did not reload"
  else if not
    (has_spec "schemaV2Base$schema_v2_norm_default"
       clasetRules.Norm false NONE)
  then fail "the default Norm clasetADD2 delta did not reload"
  else if not
    (has_spec "schemaV2Base$schema_v2_norm_negative"
       clasetRules.Norm false (SOME ~7))
  then fail "the negative Norm clasetADD2 delta did not reload"
  else ()
