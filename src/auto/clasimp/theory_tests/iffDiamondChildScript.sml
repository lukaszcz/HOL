Theory iffDiamondChild
Ancestors
  iffDiamondAdd iffDiamondRemove
Libs
  HolKernel BasicProvers clasimpLib

open clasimpLib

fun fail message = raise Fail ("iff diamond test: " ^ message)

fun has_rule name =
  List.exists
    (fn (_, (name', _)) => name = name')
    (clasetLib.rules_of (clasetLib.the_claset ()))

fun has_fragment name ss =
  List.exists
    (fn fragment => fragment = "__clasimp_iff_" ^ name)
    (simpLib.ssfrag_names_of ss)

val root_name = "iffDiamondRoot$iff_diamond_root_rule"
val add_name = "iffDiamondAdd$iff_diamond_add_rule"

val _ =
  if not (has_rule (add_name ^ "_intro")) orelse
     not (has_rule (add_name ^ "_dest"))
  then fail "the sibling addition was not ancestry-merged into the claset"
  else if not (has_fragment add_name (BasicProvers.srw_ss ())) orelse
          not (has_fragment add_name (clasimp_ss ()))
  then fail "the sibling addition was not ancestry-merged into the simpsets"
  else if has_rule (root_name ^ "_intro") orelse
          has_rule (root_name ^ "_dest")
  then fail "the sibling removal did not beat the root claset addition"
  else if has_fragment root_name (BasicProvers.srw_ss ()) orelse
          has_fragment root_name (clasimp_ss ())
  then fail "the sibling removal did not beat the root simpset addition"
  else ()
