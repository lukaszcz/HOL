(* Foreign overloads exist before markerTheory arrives through simpLib.
   Removing only the qualified marker mappings must not remove these. *)
val _ = List.app (fn name =>
  (testutils.tprint ("ordinary load preserves foreign syntax: " ^ name);
   if Term.aconv (Parse.Term [QUOTE name]) boolSyntax.T
   then testutils.OK () else testutils.die "foreign overload changed"))
  ["Split","ExcludeX"];
val _ = List.app (fn name =>
  (testutils.tprint ("qualified marker constant remains available: " ^ name);
   if Term.same_const
        (Parse.Term [QUOTE ("marker$" ^ name)])
        (Term.prim_mk_const {Thy="marker",Name=name})
   then testutils.OK () else testutils.die "qualified marker unavailable"))
  ["Split","ExcludeX"];
