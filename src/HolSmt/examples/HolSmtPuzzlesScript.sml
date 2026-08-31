Theory HolSmtPuzzles
Ancestors
  integer
Libs
  HolSmtLib

(* Classic constraint puzzles are the traditional first demonstration of SMT
   solving.  Stated as HOL theorems, they become *uniqueness* results: the
   constraints pin down exactly one solution, and the solver proves it by
   refuting the existence of any other.  Each proof is replayed in HOL by
   the checked tactic, so nothing rests on trusting the solver. *)

(* A knights-and-knaves dialogue (Smullyan).  Knights always tell the truth,
   knaves always lie.  A says: "we are both knaves".  It follows that A is a
   knave and B is a knight.  `ka` means "A is a knight". *)
Theorem knights_and_knaves:
  !ka kb. (ka <=> ~ka /\ ~kb) ==> ~ka /\ kb
Proof
  Z3_TAC
QED

(* Buy exactly 100 animals for exactly 100 dollars: dogs cost $15, cats $1,
   mice 25 cents, and you must buy at least one of each.  Prices are in
   cents to stay within linear integer arithmetic.  The solution is unique,
   so it is a theorem that any solution equals it. *)
Theorem dog_cat_mouse:
  !d c m : int.
    1 <= d /\ 1 <= c /\ 1 <= m /\
    d + c + m = 100 /\
    1500 * d + 100 * c + 25 * m = 10000 ==>
    d = 3 /\ c = 41 /\ m = 56
Proof
  Z3_TAC
QED

(* SEND + MORE = MONEY (Dudeney, 1924): assign distinct decimal digits to
   the letters, with no leading zeros, so that the addition is correct.
   The famous unique solution is 9567 + 1085 = 10652.  The letter O is
   named B below, because HOL already uses both o and O for composition
   operators. *)
Theorem send_more_money:
  !S E N D M B R Y : int.
    0 <= S /\ S <= 9 /\ 0 <= E /\ E <= 9 /\ 0 <= N /\ N <= 9 /\
    0 <= D /\ D <= 9 /\ 0 <= M /\ M <= 9 /\ 0 <= B /\ B <= 9 /\
    0 <= R /\ R <= 9 /\ 0 <= Y /\ Y <= 9 /\
    1 <= S /\ 1 <= M /\
    S <> E /\ S <> N /\ S <> D /\ S <> M /\ S <> B /\ S <> R /\ S <> Y /\
    E <> N /\ E <> D /\ E <> M /\ E <> B /\ E <> R /\ E <> Y /\
    N <> D /\ N <> M /\ N <> B /\ N <> R /\ N <> Y /\
    D <> M /\ D <> B /\ D <> R /\ D <> Y /\
    M <> B /\ M <> R /\ M <> Y /\
    B <> R /\ B <> Y /\
    R <> Y /\
    (1000 * S + 100 * E + 10 * N + D) +
    (1000 * M + 100 * B + 10 * R + E) =
    10000 * M + 1000 * B + 100 * N + 10 * E + Y ==>
    S = 9 /\ E = 5 /\ N = 6 /\ D = 7 /\ M = 1 /\ B = 0 /\ R = 8 /\ Y = 2
Proof
  Z3_TAC
QED
