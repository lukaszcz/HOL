open Parse BasicProvers simpLib testutils

(* tests for diminish applying to constituents that are "built-in" to srw_ss
   from its point of definition *)
val _ = diminish_srw_ss ["COMBIN"]
val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "diminish_srw_ss before 'realisation'",
                    printresult = thm_to_string,
                    testfn = SIMP_CONV (quietly srw_ss()) []}
                   “K T (x:'a)”

val _ = shouldfail {checkexn = (fn Conv.UNCHANGED => true | _ => false),
                    printarg = fn _ => "with_simpset_updates removes BETA_CONV",
                    printresult = thm_to_string,
                    testfn = with_simpset_updates
                               (fn ss0 => ss0 -* ["BETA_CONV"])
                               (fn t => SIMP_CONV (srw_ss()) [] t)}
                   “(λx. x /\ p) T”

val _ = convtest ("SIMP_CONV (srw_ss()) [] “p ∧ T”", SIMP_CONV (srw_ss()) [],
                  “p ∧ T”, “p:bool”)

val _ = convtest("above w/simpset_updates removing",
                 BasicProvers.with_simpset_updates
                   (simpLib.remove_simps ["AND_CLAUSES"])
                   (fn x => Conv.QCONV (SIMP_CONV (srw_ss()) []) x),
                   “p ∧ T”, “p ∧ T”)

val _ = convtest("Original again", SIMP_CONV (srw_ss()) [], “p ∧ T”, “p:bool”)

(* RW_TAC's final IF_CASES_TAC phase solves these goals.  The opt-in
   splitter must provide at least the same conditional-splitting strength. *)
local
  fun solves tac goal = null (#1 (Tactical.VALID tac ([],goal)))
  fun parity (name,goal) =
    let
      val _ = tprint ("RW_TAC/split_ss parity: " ^ name)
      val rw_solves = solves (RW_TAC (srw_ss ()) []) goal
      val split_solves =
        solves (SIMP_TAC (boolSimps.bool_ss ++ split_ss) []) goal
    in
      if rw_solves andalso split_solves then OK ()
      else die (name ^ " failed RW_TAC/split_ss parity (RW_TAC=" ^
                Bool.toString rw_solves ^ ", split_ss=" ^
                Bool.toString split_solves ^ ")")
    end
in
  val _ = List.app parity
    [("conditional chooses one branch",
      “(if b then x:'a else y) = x ∨ (if b then x else y) = y”),
     ("boolean conditional implication",
      “(if b then p else q) ⇒ p ∨ q”),
     ("conditional occurs in opposite equality sides",
      “(if b then x:'a else y) = x ∨
       y = (if b then x else y)”),
     ("nested conditional condition",
      “(if (if b then c else d) then x:'a else y) = x ∨
       (if (if b then c else d) then x else y) = y”),
     ("conditional under an application",
      “f (if b then x:'a else y) = f x ∨
       f (if b then x else y) = f y”)]
end
