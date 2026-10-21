(* Baseline-only client. Replication must preserve the original type identity;
   the REDUCER-only function is deliberately exhaustive on develop. Do not
   add a wildcard or extension imports to silence the candidate warning. *)
open HolKernel boolLib
structure PublicReplica =
struct
  datatype reducer = datatype Traverse.reducer
end
fun public_reducer_fields
      (PublicReplica.REDUCER {name, initial, addcontext, apply}) =
  (name, initial, addcontext, apply)

exception PublicContext of thm list
val p = mk_var ("public_atom", bool)
val probe = ref true
val touched = ref false
fun collect (PublicContext old, extra) = PublicContext (old @ extra)
  | collect _ = raise Fail "wrong context identity"
fun apply {solver : term list -> term -> thm,
           conv : term list -> term -> thm,
           context : Traverse.context, stack : term list,
           relation = (rel : term, refl : term -> thm)} tm =
  if not (!probe) then NO_CONV tm
  else
    let
      val _ = case context of PublicContext [_] => ()
                            | _ => raise Fail "wrong collected context"
      val solved = solver stack T
      val converted = conv stack tm
      val _ = touched :=
        (aconv (concl solved) T andalso
         aconv (concl converted) (mk_eq (tm, tm)) andalso
         aconv rel (rator (rator (mk_eq (tm, tm)))) andalso
         length stack = 1)
    in refl tm end
val reducer : Traverse.reducer = PublicReplica.REDUCER
  {name = SOME "public-reducer", initial = PublicContext [],
   addcontext = collect, apply = apply}
val _ : PublicReplica.reducer = reducer
val extended : PublicReplica.reducer = Traverse.addctxt [TRUTH] reducer
val (name, initial, addcontext, apply) = public_reducer_fields extended
val _ : Traverse.context = initial
val data = Traverse.dest_reducer extended
val (eq, _) = strip_comb (mk_eq (p, p))
val result = (#apply data)
  {solver = fn _ => fn _ => TRUTH, conv = fn _ => REFL,
   context = #initial data, stack = [p], relation = (eq, REFL)} p
val _ = Paired.check "replication and every reducer field"
  (!touched andalso name = SOME "public-reducer" andalso
   aconv (concl result) (mk_eq (p, p)) andalso null (hyp result))
val _ = probe := false
val td : Traverse.traverse_data =
  {rewriters = [reducer], dprocs = [], limit = SOME 5,
   travrules = Travrules.EQ_tr, relation = eq}
val {rewriters, dprocs, limit, travrules, relation} = td
val _ = Paired.check "every traverse_data field"
  (length rewriters = 1 andalso null dprocs andalso limit = SOME 5 andalso
   aconv relation eq)
val _ : simpLib.weakener_data = ([Travrules.EQ_preorder], [], reducer)
val ss = simpLib.++ (simpLib.empty_ss, simpLib.dproc_ss reducer)
val projected : Traverse.traverse_data = simpLib.traversedata_for_ss ss
val frag = congLib.CSFRAG
  {relations = [Travrules.EQ_preorder], rewrs = [], congs = [],
   dprocs = [reducer]}
val cs = congLib.mk_congset [frag]
val th = congLib.CONGRUENCE_EQ_SIMP_CONV cs ss [] p
val _ = Paired.check "ordinary reducer/simpset/congset interoperability"
  (aconv (concl th) (mk_eq (p, p)) andalso null (hyp th))
