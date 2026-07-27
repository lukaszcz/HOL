Theory iffWithinRemoveChild
Ancestors
  iffWithinRemove
Libs
  BasicProvers clasimpLib iffTestSupport

open iffTestSupport

val removed_name = "iffWithinRemove$iff_within_remove_rule"

val _ =
  if has_iff_rewrite removed_name orelse has_iff_rules removed_name
  then fail "same-theory final iff state was not removal in the child"
  else ()
