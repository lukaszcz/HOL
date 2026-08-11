structure benchAlgebra =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method mapped representative goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   mapped = mapped, excl = [],
   provenance =
     {file = "src/HOL/Examples/Groebner_Examples.thy", line = line,
      commit = commit},
   representative = representative}

val goals =
  [entry "groebner_L39" 39 "by algebra" benchLib.IntRing true
     ``!x y z : int.
       (x + y) ** 3 - 1 = (x - z) ** 2 - 10 ==>
       x = z + 3 ==> x = -y``,
   entry "groebner_L42" 42 "by algebra" benchLib.NumRing true
     ``(4 : num) + 4 = 3 + 5``,
   entry "groebner_L49" 49 "using assms by algebra"
     benchLib.IntRing false
     ``!a b c d e f x : int.
       a * x ** 2 + b * x + c = 0 /\
       d * x ** 2 + e * x + f = 0 ==>
       d ** 2 * c ** 2 - 2 * d * c * a * f +
       a ** 2 * f ** 2 - e * d * b * c - e * b * a * f +
       a * e ** 2 * c + f * d * b ** 2 = 0``,
   entry "groebner_L55" 55 "by algebra" benchLib.IntRing false
     ``!x : int.
       (x ** 3 - x ** 2 - 5 * x - 3 = 0 <=>
        x = 3 \/ x = -1)``,
   entry "groebner_L58" 58 "by algebra" benchLib.IntRing false
     ``!x : int.
       (x * (x ** 2 - x - 5) - 3 = 0 <=>
        x = 3 \/ x = -1)``,
   entry "groebner_L106" 106
     "using assms by (algebra add: collinear_def split_def fst_conv snd_conv)"
     benchLib.IntRing false
     ``!Ax Ay Bx By Cx Cy c s : int.
       (Ax - Bx) * (By - Cy) = (Ay - By) * (Bx - Cx) /\
       c ** 2 + s ** 2 = 1 ==>
       ((Ax * c - Ay * s) - (Bx * c - By * s)) *
         ((By * c + Bx * s) - (Cy * c + Cx * s)) =
       ((Ay * c + Ax * s) - (By * c + Bx * s)) *
         ((Bx * c - By * s) - (Cx * c - Cy * s))``,
   entry "groebner_L113" 113 "by algebra" benchLib.IntRing true
     ``(?d : int. a * y - a * x = n * d) ==>
       (?u v : int. a * u + n * v = 1) ==>
       ?e : int. y - x = n * e``]

val shortfalls : benchLib.shortfall list =
  [{id = "groebner_L61", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle idom has no type-for-type HOL4 carrier"},
   {id = "groebner_L72", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle idom has no type-for-type HOL4 carrier"},
   {id = "groebner_L82", cause = benchLib.TranslationGap,
    date = "2026-08-10",
    note = "Isabelle idom has no type-for-type HOL4 carrier"},
   {id = "groebner_L113", cause = benchLib.AcceptedGap,
    date = "2026-08-10",
    note = "D58 ideal-membership witness construction is out of scope"}]

fun run level =
  benchLib.run_family
    {family = "algebra", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
