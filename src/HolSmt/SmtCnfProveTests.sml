(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtCnfProveTests =
struct
open HolKernel testutils;
val atoms=List.tabulate (3,fn i=>Term.mk_var
 ("model_p" ^ Int.toString i,Type.bool));
fun block n=boolSyntax.list_mk_disj (List.tabulate (3,fn i=>
 if (n div (IntInf.toInt (IntInf.pow (2,i)))) mod 2=0 then
   List.nth (atoms,i) else boolSyntax.mk_neg (List.nth (atoms,i))));
val clauses=List.tabulate (8,block);
fun classify expected inputs =
 let val inventory=Array.fromList (List.map (fn c=>(c,Thm.ASSUME c)) inputs)
     val result=SmtCnfProve.prove (Array.tabulate (Array.length inventory,
       fn i=> #1 (Array.sub (inventory,i))))
 in case result of SmtCnfProve.Refuted proof=>
     (assert (fn x=>not x) expected;
      assert (Term.aconv boolSyntax.F) (Thm.concl proof);
      assert (fn h=>List.all (fn c=>List.exists (Term.aconv c) inputs) h)
        (Thm.hyp proof);
      Library.check_oracle_tags "SmtCnfProveTests" "unsat" proof)
   | SmtCnfProve.Model witness=>
     (assert (fn x=>x) expected;assert null (Thm.hyp witness);
      Library.check_oracle_tags "SmtCnfProveTests" "sat" witness)
   | SmtCnfProve.Unknown=>raise Fail "small native CNF declined"
 end;
fun run () =
let
 val _=tprint "bounded native CNF and model witnesses"
val _=List.app (fn mask=>classify (mask<>255)
 (List.mapPartial (fn i=>if
   (mask div (IntInf.toInt (IntInf.pow (2,i)))) mod 2=1
   then SOME (List.nth (clauses,i)) else NONE)
   (List.tabulate (8,fn i=>i)))) (List.tabulate (256,fn i=>i));
val p=hd atoms;
val _=classify true [boolSyntax.T];
val _=classify false [boolSyntax.F];
val _=classify false [boolSyntax.mk_neg boolSyntax.T];
val _=classify true [boolSyntax.mk_neg boolSyntax.F];
val _=classify false [p,boolSyntax.mk_neg p];
val _=classify true [boolSyntax.mk_disj (p,boolSyntax.mk_neg p)];

fun large_type 0=Type.bool
  | large_type depth=let val child=large_type (depth-1)
    in child --> child end
val ty=large_type 21
val large_atom=boolSyntax.mk_eq
  (Term.mk_var ("cnf_hidden_type",ty),boolSyntax.mk_arb ty)
fun unknown source=case SmtCnfProve.prove (Array.fromList [source]) of
  SmtCnfProve.Unknown=>()
 | _=>raise Fail "native CNF optional guard did not delegate"
val _=unknown large_atom
val binder=boolSyntax.mk_forall
  (Term.mk_var ("cnf_binder",Type.bool),boolSyntax.T)
val _=unknown binder
val _=case SmtCnfProve.prove (Array.array (2049,p)) of
  SmtCnfProve.Unknown=>()
 | _=>raise Fail "native CNF optional inventory did not delegate"
val word=Term.mk_var ("cnf_word",wordsSyntax.mk_int_word_type 3)
val bit=wordsSyntax.mk_index (word,numSyntax.zero_tm)
val _=classify false [bit,boolSyntax.mk_neg bit]
val _=classify true [boolSyntax.mk_disj (bit,boolSyntax.mk_neg bit)]
val _=classify true [Term.mk_var ("native_sat_model_1",Type.bool)]
(* A negative compound atom remains opaque to the existing DIMACS route.
   Encoding a whole subterm substitution would wrongly collapse the positive
   disjunction structure into that atom. *)
val q=List.nth (atoms,1)
val r=List.nth (atoms,2)
val compound=boolSyntax.mk_disj (p,q)
val overlapping=[boolSyntax.mk_disj (compound,r),
  boolSyntax.mk_neg compound,boolSyntax.mk_neg r]
val _=classify true overlapping
val _=classify false (overlapping @
  [boolSyntax.mk_neg p,boolSyntax.mk_neg q])
val refutation=boolSyntax.list_mk_conj overlapping
val _=case
 ((ignore (HolSatLib.GEN_SAT_PROVE_ONLY
    (satConfig.set_flag_is_cnf true
      (satConfig.set_term refutation satConfig.base_config)));false)
  handle HolSatLib.SAT_satisfiable _=>true) of
 true=>() | false=>raise Fail "CNF model changed the legacy abstraction"

fun check_circuit cnf output =
  let val proof = SmtCircuitSat.prove_cnf (cnf,output) in
    assert (Term.aconv (boolSyntax.mk_imp (cnf,output))) (Thm.concl proof);
    assert null (Thm.hyp proof);
    Library.check_oracle_tags "SmtCnfProveTests" "circuit" proof
  end
val unrelated = SmtCircuitSat.balanced_conjunction_term
  (List.tabulate (128,fn _ => boolSyntax.mk_disj (q,r)))
val contradiction = boolSyntax.mk_conj (p,boolSyntax.mk_neg p)
val sparse = boolSyntax.mk_conj (unrelated,contradiction)
val (_,sparse_stats) = SmtReplayRuleObservation.with_statistics
  (fn () => check_circuit sparse q)
(* The three projections follow the right branch to the two used leaves.
   The other one-premise returns are the final CCONTR and DISCH. *)
val _ = assert (fn n => n = 5) (#one_premise_returns sparse_stats)
val not_true = boolSyntax.mk_neg boolSyntax.T
val _ = check_circuit (boolSyntax.mk_conj
  (boolSyntax.mk_conj (boolSyntax.T,not_true),not_true)) boolSyntax.T
val duplicates = SmtCircuitSat.balanced_conjunction_term
  (List.tabulate (128,fn _ => not_true))
val (_,duplicate_stats) = SmtReplayRuleObservation.with_statistics
  (fn () => check_circuit duplicates boolSyntax.T)
(* Only the first duplicate is projected, along the leftmost seven edges.
   The denied output is another duplicate and introduces no assumption. *)
val _ = assert (fn n => n = 9) (#one_premise_returns duplicate_stats)
val _ = assert (fn n => n = 1) (#zero_premise_returns duplicate_stats)
(* Include the three trailing facts in the limit. The last fact is
   necessary for refutation, so the accepted cases must keep it. *)
val trailing = [boolSyntax.T,boolSyntax.mk_neg boolSyntax.F,boolSyntax.mk_neg p]
fun check_limit (clause_count,accepted) =
  let val cnf = SmtCircuitSat.balanced_conjunction_term
        (List.tabulate (clause_count - List.length trailing,fn _ => p))
  in
    case SmtCnfProve.prove_conjunction (cnf,trailing) of
        SmtCnfProve.Refuted proof =>
          assert (fn yes => yes andalso
            HOLset.member (Thm.hypset proof,List.last trailing)) accepted
      | SmtCnfProve.Unknown => assert not accepted
      | SmtCnfProve.Model _ => raise Fail "bounded CNF lost its trailing facts"
  end
val _ = List.app (ignore o check_limit) [(2047,true),(2048,true),(2049,false)]
val fallback_cnf = boolSyntax.mk_conj
  (boolSyntax.mk_conj (binder,p),boolSyntax.mk_conj (boolSyntax.mk_neg p,q))
val (_,solver_stats) = satTools.with_solver_statistics
  (fn () => check_circuit fallback_cnf r)
val _ = assert (fn n => n > 0)
  (#external_calls solver_stats + #internal_calls solver_stats)

in OK () end
end
