Theory declB
Ancestors
  declA
Libs
  HolKernel clasetLib

open clasetLib

fun fail message = raise Fail ("declB claset test: " ^ message)

fun find_rule name =
  List.find (fn (_, (name', _)) => name = name') (rules_of (the_claset ()))

fun has_spec name kind safe =
  case find_rule name of
      SOME ({kind = kind', safe = safe', ...}, _) =>
        kind = kind' andalso safe = safe'
    | NONE => false

val expected_order = ["declA$declA_attr", "declA$declA_export"]
val actual_order =
  map (fn (_, (name, _)) => name)
    (List.filter
       (fn (_, (name, _)) =>
          List.exists (fn expected => expected = name) expected_order)
       (rules_of (the_claset ())))

val _ =
  if not (has_spec "declA$declA_attr" clasetRules.Intro true) then
    fail "the attribute rule is absent or has the wrong specification"
  else if not (has_spec "declA$declA_export" clasetRules.Intro false) then
    fail "the exported rule is absent or has the wrong specification"
  else if Option.isSome (find_rule "declA$declA_removed") then
    fail "the removed rule is still present"
  else if actual_order <> expected_order then
    fail "canonical declaration order is wrong"
  else ()
