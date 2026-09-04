structure orderLib :> orderLib =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "orderLib"

(* The goal's own assumptions are the context: an order arrives as a
   premise, so a tactic that ignored them would decide nothing.  The
   prefix is stripped first, which is what puts the axioms of a goal
   stated as [!R. transitive R ==> ...] into the assumptions. *)
fun solve theorems (asl, w) =
  ([], fn _ => orderSolve.prove_with (List.map ASSUME asl @ theorems) w)

fun ORDER_TAC theorems =
  REPEAT GEN_TAC THEN
  REPEAT (DISCH_THEN STRIP_ASSUME_TAC) THEN
  solve theorems

fun ORDER_PROVE tm = TAC_PROOF (([], tm), ORDER_TAC [])

fun ORDER_CONV tm = EQT_INTRO (ORDER_PROVE tm)

(* The contexts are derived once per addition to the simplifier's
   context rather than once per atom: deriving them rewrites each
   context theorem with the order definitions, and a decision procedure
   is asked about far more terms than it is given theorems. *)
val ORDER_REDUCER =
  let
    exception CTXT of thm list * orderData.context list
    fun get_context e = (raise e) handle CTXT value => value
    fun addcontext (context, newtheorems) =
      let
        val (theorems, contexts) = get_context context
        val added = List.concat (List.map CONJUNCTS newtheorems)
        val theorems = added @ theorems
      in
        (* A context is derived from order axioms alone, so the
           derivation is repeated only when one arrives.  The
           simplifier adds to its context at every assumption it
           passes, and rewriting each of those with the order
           definitions to find nothing is the cost this avoids. *)
        if orderData.has_order_axiom added then
          CTXT (theorems, orderData.contexts theorems)
        else CTXT (theorems, contexts)
      end
    fun apply args tm =
      let
        val (theorems, contexts) = get_context (#context args)
      in
        if List.exists (fn c => orderData.is_literal c tm) contexts then
          EQT_INTRO (orderSolve.prove_using contexts theorems tm)
        else raise ERR "ORDER_DP" "not a literal of an order in the context"
      end
  in
    Traverse.REDUCER
      {name = SOME "ORDER_DP",
       addcontext = addcontext,
       apply = apply,
       initial = CTXT ([], [])}
  end

val ORDER_ss =
  simpLib.named_merge_ss "ORDER"
    [simpLib.SSFRAG
       {name = SOME "ORDER_DP",
        convs = [], rewrs = [], congs = [], filter = NONE,
        ac = [], dprocs = [ORDER_REDUCER]}]

end
