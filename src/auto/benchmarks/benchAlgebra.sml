structure benchAlgebra =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method representative goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/Examples/Groebner_Examples.thy", line = line,
      commit = commit},
   representative = representative}

fun translated id line method goal : benchLib.source_goal =
  {id = id, goal = goal, source_method = method,
   provenance =
     {file = "src/HOL/Examples/Groebner_Examples.thy", line = line,
      commit = commit},
   representative = false}

val translated_goals =
  [translated "groebner_L61" 61 "by algebra"
     (Thm.concl
       parityAlgebraTranslationTheory.source_idom_simultaneous_squares),
   translated "groebner_L72" 72 "by (algebra add: sq_def)"
     (Thm.concl parityAlgebraTranslationTheory.source_idom_four_square),
   translated "groebner_L82" 82 "by (algebra add: sq_def)"
     (Thm.concl parityAlgebraTranslationTheory.source_idom_eight_square)]

val raw_goals =
  translated_goals @
  [entry "groebner_L39" 39 "by algebra" true
     ``!x y z : int.
       (x + y) ** 3 - 1 = (x - z) ** 2 - 10 ==>
       x = z + 3 ==> x = -y``,
   entry "groebner_L42" 42 "by algebra" true
     ``(4 : num) + 4 = 3 + 5``,
   entry "groebner_L49" 49 "using assms by algebra" false
     ``!a b c d e f x : int.
       a * x ** 2 + b * x + c = 0 /\
       d * x ** 2 + e * x + f = 0 ==>
       d ** 2 * c ** 2 - 2 * d * c * a * f +
       a ** 2 * f ** 2 - e * d * b * c - e * b * a * f +
       a * e ** 2 * c + f * d * b ** 2 = 0``,
   entry "groebner_L55" 55 "by algebra" false
     ``!x : int.
       (x ** 3 - x ** 2 - 5 * x - 3 = 0 <=>
        x = 3 \/ x = -1)``,
   entry "groebner_L58" 58 "by algebra" false
     ``!x : int.
       (x * (x ** 2 - x - 5) - 3 = 0 <=>
        x = 3 \/ x = -1)``,
   entry "groebner_L106" 106
     "using assms by (algebra add: collinear_def split_def fst_conv snd_conv)" false
     ``!Ax Ay Bx By Cx Cy c s : int.
       (Ax - Bx) * (By - Cy) = (Ay - By) * (Bx - Cx) /\
       c ** 2 + s ** 2 = 1 ==>
       ((Ax * c - Ay * s) - (Bx * c - By * s)) *
         ((By * c + Bx * s) - (Cy * c + Cx * s)) =
       ((Ay * c + Ax * s) - (By * c + Bx * s)) *
         ((Bx * c - By * s) - (Cx * c - Cy * s))``,
   entry "groebner_L113" 113 "by algebra" true
     ``(?d : int. a * y - a * x = n * d) ==>
       (?u v : int. a * u + n * v = 1) ==>
       ?e : int. y - x = n * e``]

val goals = benchDerive.prepare "algebra" raw_goals

(* The two abstract integral-domain goals the derived recipe does not
   close.  Both diagnoses are measured, not inferred: the four-square
   identity of the same family closes in 0.8 s, and the eight-square
   one closes in 0.3 s once its two abbreviations are unfolded. *)
val shortfalls : benchLib.shortfall list =
  [{id = "groebner_L61", cause = benchLib.EngineLimitation,
    date = "2026-08-28",
    note =
      "ringLib.RING_TAC proves ring equations, and this goal is an "
      ^ "equivalence between a conjunction of equations and a "
      ^ "disjunction of them.  Deciding it needs the integral "
      ^ "domain's zero-divisor-freeness and a case split on the "
      ^ "factors, which Isabelle's algebra has for an idom and the "
      ^ "HOL4 ring normalizer does not; it declines in a "
      ^ "millisecond without attempting the goal"},
   {id = "groebner_L82", cause = benchLib.EngineLimitation,
    date = "2026-08-28",
    note =
      "the translation states the eight-square identity through two "
      ^ "abbreviations, source_ring_sum8 and source_ring_neg, that "
      ^ "Isabelle's statement does not have -- it writes the sum and "
      ^ "the negation out.  The Isabelle method names only sq_def, so "
      ^ "the derived recipe unfolds only sq_def and the ring "
      ^ "normalizer meets two opaque constants.  Unfolding all three "
      ^ "closes the goal in 0.3 s, so what is measured here is the "
      ^ "translation's notation, not the automation"}]

fun run level =
  benchLib.run_corpus_family
    {family = "algebra", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
