(* Copyright (c) 2026 The HOL4 contributors. *)
structure Z3_HypothesisPresenceTests =
struct
open HolKernel testutils;
fun run () =
let
val _=tprint "guarded open-hypothesis metadata"
val old=Z3_ProofReplay.hypothesis_has_free_variables_legacy_for_test;
val alternative=Z3_ProofReplay.hypothesis_has_free_variables_for_test;
fun check term=assert (fn answer=>answer=old term) (alternative term);
val p=Term.mk_var ("presence_p",Type.bool);
val q=Term.mk_var ("presence_q",Type.bool);
fun shared 0 term=term
 | shared n term=let val child=shared (n-1) term
   in boolSyntax.mk_conj (child,child) end;
fun type_tree 0=Type.bool
 | type_tree n=let val child=type_tree (n-1) in child --> child end;
val ty64=listSyntax.mk_list_type (type_tree 5);
val ty65=listSyntax.mk_list_type ty64;
val _=List.app (fn t=>ignore (check t))
 [p,boolSyntax.T,boolSyntax.F,boolSyntax.mk_conj (p,q),
  shared 80 p,Term.mk_abs (p,p),Term.mk_abs (p,q),
  boolSyntax.mk_conj (q,Term.mk_comb (Term.mk_abs (p,p),q)),
  Term.mk_var ("presence_t64",ty64),Term.mk_var ("presence_t65",ty65)];
val name="presence_stale_const";
val _=Theory.new_constant (name,Type.bool);
val held=Term.prim_mk_const {Name=name,Thy=Theory.current_theory ()};
val _=Theory.delete_const name;
val source=boolSyntax.mk_conj (p,held);

fun outcome worker =
 ((SOME (worker source),NONE)
  handle Interrupt=>raise Interrupt | error=>(NONE,SOME error));
val old_outcome=outcome old;
val new_outcome=outcome alternative;
val _=case (old_outcome,new_outcome) of
 ((SOME a,NONE),(SOME b,NONE))=>assert (fn x=>x=a) b
 | ((NONE,SOME (Feedback.HOL_ERR a)),
    (NONE,SOME (Feedback.HOL_ERR b)))=>
    assert (fn x=>x)
     (Feedback.top_structure_of a=Feedback.top_structure_of b andalso
      Feedback.top_function_of a=Feedback.top_function_of b andalso
      Feedback.message_of a=Feedback.message_of b)
 | _=>raise Fail "presence changed stale-source outcome";

val _=Count.counting_thms true
val prior=Count.thm_count ()
val _=Portable.finally (fn () => Count.counting_thms false)
 (fn () =>
   (assert (fn b=>b) (alternative (shared 80 p));
    assert (fn n=>n=prior) (Count.thm_count ());())) ()
in OK () end
end
