(* Independent tracked recipes with the ordinary catalog's immutable inputs. *)
signature boolSimpsExt =
sig
     include Abbrev

     val bool_ss : simpExtLib.simpset
     val BOOL_ss : simpExtLib.ssfrag       (* boolean rewrites and
                                           beta conversion *)
     val CONG_ss : simpExtLib.ssfrag       (* congruence rules for ==> and
                                           if-then-else *)
     val ABBREV_ss : simpExtLib.ssfrag     (* congruence rule for Abbrev,
                                           preventing rewrites in var pos'n,
                                           and Abbrev tidying conversion *)
     val CONJ_ss : simpExtLib.ssfrag       (* congruence rules for /\; not
                                           included in bool_ss, but
                                           occasionally useful *)
     val DISJ_ss : simpExtLib.ssfrag    (* analogous congruence rules for \/ *)
     val NOT_ss : simpExtLib.ssfrag        (* rewrites that move negations
                                           inwards, included in bool_ss *)
     val COND_elim_ss : simpExtLib.ssfrag  (* eliminates if-then-else's;
                                           not in bool_ss *)
     val LIFT_COND_ss : simpExtLib.ssfrag  (* lifts conds high in a term, but
                                           doesn't eliminate them; can merge
                                           those of the same guard or
                                           opposing guards *)
     val UNWIND_ss : simpExtLib.ssfrag     (* "pointwise" elimination for
                                            ? and !, included in bool_ss *)
     val ETA_ss : simpExtLib.ssfrag        (* eta conversion;
                                           not included in bool_ss *)

     val LET_ss : simpExtLib.ssfrag        (* writes out let terms, using a
                                           congruence to evaluate the
                                           second argument first *)

     val literal_case_ss : simpExtLib.ssfrag (* writes out literal case terms,
                                           using a congruence to evaluate
                                           the second argument first *)

     val DNF_ss : simpExtLib.ssfrag
        (* converts a term to DNF at the level of propositional logic, and
           also moves quantifiers around to give them maximum useful scope
           over their bodies:
               (?x. P x) /\ Q   -->  ?x. P x /\ Q
               P /\ (?x. Q x)   -->  ?x. P /\ Q x
               (?x. P x) ==> Q  -->  !x. P x ==> Q
               P ==> !x. Q x    -->  !x. P ==> Q x
               !x. P x /\ Q x   -->  (!x. P x) /\ (!x. Q x)
               ?x. P x \/ Q x   -->  (?x. P x) \/ (?x. Q x)
           Think of this simpset fragment as attempting to achieve as
           much as possible of STRIP_TAC within a single goal.

           Note that it leaves ==> alone, but includes the following
           extra rewrites:
               P \/ Q ==> R     -->  (P ==> R) /\ (Q ==> R)
               P ==> Q /\ R     -->  (P ==> Q) /\ (P ==> R)

           This simpset fragment will give UNWIND_ss maximum opportunity to
           eliminate equalities. *)

     val EQUIV_EXTRACT_ss : simpExtLib.ssfrag
        (* Extracts common terms from both sides of an equivalence. Example:

           ``A /\ B /\ C <=> C /\ B /\ D`` is transformed to

           |- (A /\ B /\ C <=> C /\ B /\ D) <=> C /\ B ==> (A <=> D)
         *)

     val NORMEQ_ss : simpExtLib.ssfrag
       (* flips equalities that have a ground term on the left and a
          non-ground term on the right *)

     val LABEL_CONG_ss : simpExtLib.ssfrag
       (* stops the simplifier from changing labelled terms *)

     val HIDE_ss : simpExtLib.ssfrag
       (* stops simplifier from changing hidden terms *)

     val SimpLHS : thm
     val SimpRHS : thm
     val SimpL   : term -> thm
     val SimpR   : term -> thm


end
