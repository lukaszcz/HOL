structure benchPresburger =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method representative goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/ex/PresburgerEx.thy", line = line,
      commit = commit},
   representative = representative}

fun presburger line representative goal =
  entry ("presburger_L" ^ Int.toString line) line "by presburger"
    representative goal

(* HOL4's own integer regression goals, run alongside the translated
   ones.  They have no Isabelle proof, so there is no parity claim for
   a named procedure to inflate; [benchDerive.native] is what says so,
   and it is the only route by which a tactic is written down rather
   than derived. *)
fun integer_case id line procedure goal =
  benchDerive.native procedure
    {id = "integer_" ^ id, goal = goal,
     source_method = "test_cases.perform_tests",
     provenance =
       {file = "src/integer/testing/test_cases.sml", line = line,
        commit = "HOL4-worktree"},
     representative = false}

val raw_goals =
  [presburger 11 true
     ``~((m : num) <= j) ==> ~((n : num) <= i) ==>
       (e : num) <> 0 ==> SUC j <= ja ==>
       ?m. !ja ia. m <= ja ==>
         (if j = ja /\ i = ia then e else 0) = 0``,
   presburger 12 false
     ``0 < emBits MOD 8 ==>
       8 + emBits DIV 8 * 8 - emBits = 8 - emBits MOD 8``,
   presburger 17 true
     ``(!y : int. 3 int_divides y) ==>
       !x : int. b < x ==> a <= x``,
  presburger 20 false
     ``3 int_divides (z : int) ==> 2 int_divides (y : int) ==>
       (?x : int. 2 * x = y) /\ (?k : int. 3 * k = z)``,
  presburger 24 false
     ``SUC (n : num) < 6 ==> 3 int_divides (z : int) ==>
       2 int_divides (y : int) ==>
       (?x : int. 2 * x = y) /\ (?k : int. 3 * k = z)``,
   presburger 28 true
     ``!x : num. ?y : num. (0 : num) <= 5 ==> y = 5 + x``,
   presburger 32 false
     ``!x : num. ?y : num. y = 5 + x \/ x DIV 6 + 1 = 2``,
   presburger 35 true ``?x : int. 0 < x``,
   presburger 38 true
     ``!x y : int. x < y ==> 2 * x + 1 < 2 * y``,
   presburger 41 true
     ``!x y : int. 2 * x + 1 <> 2 * y``,
   presburger 44 false
     ``?x y : int. 0 < x /\ 0 <= y /\ 3 * x - 5 * y = 1``,
   presburger 47 true
     ``~(?x : int. ?y : int. ?z : int.
       4 * x + (-6 : int) * y = (1 : int))``,
   presburger 54 true ``~(?x : int. F)``,
   presburger 61 false
     ``!x : int. 2 int_divides x ==> ?y : int. x = 2 * y``,
   presburger 67 false
     ``!x : int.
       (2 int_divides x <=> ?y : int. x = 2 * y)``,
   presburger 70 false
     ``!x : int.
       (2 int_divides x <=> !y : int. x <> 2 * y + 1)``,
   presburger 73 false
     ``~(!x : int.
       ((2 int_divides x <=> !y : int. x <> 2 * y + 1) \/
        (?q u i : int. 3 * i + 2 * q - u < 17)) ==>
       0 < x \/ (~(3 int_divides x) /\ x + 8 = 0))``,
   presburger 79 false
     ``~(!i : int. 4 <= i ==>
       ?x y : int. 0 <= x /\ 0 <= y /\ 3 * x + 5 * y = i)``,
   presburger 82 false
     ``!i : int. 8 <= i ==>
       ?x y : int. 0 <= x /\ 0 <= y /\ 3 * x + 5 * y = i``,
   presburger 85 false
     ``?j : int. !i : int. j <= i ==>
       ?x y : int. 0 <= x /\ 0 <= y /\ 3 * x + 5 * y = i``,
   presburger 88 false
     ``~(!j i : int. j <= i ==>
       ?x y : int. 0 <= x /\ 0 <= y /\ 3 * x + 5 * y = i)``,
   presburger 91 false
     ``(?m : num. n = 2 * m) ==> (n + 1) DIV 2 = n DIV 2``,
   entry "presburger_L102" 102 "by arith" false
     ``x3 = ABS x2 - x1 ==> x4 = ABS x3 - x2 ==>
       x5 = ABS x4 - x3 ==> x6 = ABS x5 - x4 ==>
       x7 = ABS x6 - x5 ==> x8 = ABS x7 - x6 ==>
       x9 = ABS x8 - x7 ==> x10 = ABS x9 - x8 ==>
       x11 = ABS x10 - x9 ==> x1 = x10 /\ x2 = (x11 : int)``]

val integer_goals =
  [integer_case "pt1" 220 benchLib.IntArith
     ``!x y z : int. x < y /\ y < z ==> x < z``,
   integer_case "pt2" 221 benchLib.Cooper
     ``?x y : int. 4 * x + 3 * y = 10``,
   integer_case "pt3" 222 benchLib.IntArith
     ``!x : int. 3 * x < 4 * x ==> x > 0``,
   integer_case "pt4" 223 benchLib.IntArith
     ``?y : int. !x : int. x + y = x``,
   integer_case "pt5" 224 benchLib.Cooper
     ``?y : int. (!x : int. x + y = x) /\
       !y' : int. (!x : int. x + y' = x) ==> y = y'``,
   integer_case "pt6" 226 benchLib.Cooper
     ``!x : int.
       3 int_divides x /\ 2 int_divides x ==> 6 int_divides x``,
   integer_case "pt7" 227 benchLib.Cooper
     ``?!y : int. !x : int. x + y = x``,
   integer_case "pt8" 228 benchLib.Cooper
     ``!x : int. ?!y : int. x + y = 0``,
   integer_case "pt9" 229 benchLib.IntArith
     ``?x y : int. x + y = 6 /\ 2 * x + 3 * y = 11``,
   integer_case "pt10" 230 benchLib.IntArith
     ``!x z : int. ?!y : int. x - y = z``,
   integer_case "pt11" 231 benchLib.Cooper
     ``!x y z : int. 2 * x < y /\ y < 2 * z ==>
       ?w : int. (y = 2 * w \/ y = 2 * w + 1) /\
         x <= w /\ w < z``]

val goals =
  benchDerive.prepare "presburger" raw_goals @ integer_goals

(* Lines 14 and 64 repeat lines 12 and 61 exactly. *)
val shortfalls : benchLib.shortfall list = []

fun run level =
  benchLib.run_corpus_family
    {family = "presburger", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
