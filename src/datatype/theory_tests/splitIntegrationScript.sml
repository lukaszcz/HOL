Theory splitIntegration[bare]
Libs
  HolKernel Parse boolLib Tactic Datatype simpLib splitLib boolSimps

open HolKernel simpLib splitLib boolSimps

val _ = Datatype`split_local = SplitLocalA | SplitLocalB num`;

Theorem tagged_if_split[split]:
  !P. P (if b then x else y) <=> (b ==> P x) /\ (~b ==> P y)
Proof
  MATCH_ACCEPT_TAC (type_split_of ``:bool``)
QED

fun fail message = raise Fail ("split integration test: " ^ message)

val _ =
  if List.exists
       (fn th => aconv (concl th) (concl tagged_if_split))
       (split_thms ())
  then ()
  else fail "[split] theorem is absent from split_thms"

fun check_typebase_split label goal =
  case #1 (VALID (SIMP_TAC (bool_ss ++ split_ss) []) ([], goal)) of
      [([], result)] =>
        if not (aconv result goal) andalso
           not (can (find_term TypeBase.is_case) result)
        then ()
        else fail (label ^ " case expression was not split")
    | _ => fail (label ^ " split produced the wrong subgoals")

val local_goal =
  ``P (split_local_CASE x (n:'b) (f:num -> 'b)) : bool``

val _ = check_typebase_split "locally defined datatype" local_goal
val _ = check_typebase_split "cached locally defined datatype" local_goal

val local_split_1 = type_split_of ``:split_local``
val local_split_2 = type_split_of ``:split_local``
val local_asm_split_1 = type_asm_split_of ``:split_local``
val local_asm_split_2 = type_asm_split_of ``:split_local``

val _ =
  if aconv (concl local_split_1) (concl local_split_2) andalso
     aconv (concl local_asm_split_1) (concl local_asm_split_2)
  then ()
  else fail "cached local datatype rules changed"

val _ = export_theory()
