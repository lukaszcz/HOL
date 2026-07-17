Theory clasetMarker[bare]
Libs
  HolKernel Parse boolLib

(* Per-invocation claset rule modifiers. *)

val SIntro_def = new_definition("SIntro_def", ``SIntro (x:bool) = x``);
val Intro_def = new_definition("Intro_def", ``Intro (x:bool) = x``);
val SElim_def = new_definition("SElim_def", ``SElim (x:bool) = x``);
val Elim_def = new_definition("Elim_def", ``Elim (x:bool) = x``);
val SDest_def = new_definition("SDest_def", ``SDest (x:bool) = x``);
val Dest_def = new_definition("Dest_def", ``Dest (x:bool) = x``);
val Del_def = new_definition("Del_def", ``Del (x:'a) = T``);

val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SIntro"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Intro"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SElim"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Elim"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "SDest"},
   name = (["Unwanted"], "id")}
val _ = OpenTheoryMap.OpenTheory_const_name
  {const = {Thy = "clasetMarker", Name = "Dest"},
   name = (["Unwanted"], "id")}
