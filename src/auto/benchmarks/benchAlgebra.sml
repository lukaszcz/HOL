structure benchAlgebra =
struct

open HolKernel autoSeedTheory

val commit = "f7e02b7e"

fun entry id line method mapped representative goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method,
   recipe = benchLib.Invoke (mapped, []), excl = [],
   provenance =
     {file = "src/HOL/Examples/Groebner_Examples.thy", line = line,
      commit = commit},
   representative = representative}

fun named name theorem : benchLib.named_thm =
  {name = name, theorem = theorem}

fun translated id line method recipe goal : benchLib.corpus_goal =
  {id = id, goal = goal, source_method = method, recipe = recipe,
   excl = [], provenance =
     {file = "src/HOL/Examples/Groebner_Examples.thy", line = line,
      commit = commit},
   representative = false}

val explicit_ring_definitions =
  [benchLib.DefinitionAdd
     (named "parityAlgebraTranslation$source_ring_sq_def"
       parityAlgebraTranslationTheory.source_ring_sq_def),
   benchLib.DefinitionAdd
     (named "parityAlgebraTranslation$source_ring_sum8_def"
       parityAlgebraTranslationTheory.source_ring_sum8_def),
   benchLib.DefinitionAdd
     (named "parityAlgebraTranslation$source_ring_neg_def"
       parityAlgebraTranslationTheory.source_ring_neg_def)]

val translated_goals =
  [translated "groebner_L61" 61 "by algebra"
     (benchLib.AllGoals
       (benchLib.Invoke
         (benchLib.Auto,
          [benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityAlgebraTranslation$source_idom_squares_x_nonzero_x"
              parityAlgebraTranslationTheory.source_idom_squares_x_nonzero_x),
         benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityAlgebraTranslation$source_idom_squares_x_nonzero_y"
              parityAlgebraTranslationTheory.source_idom_squares_x_nonzero_y),
         benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityAlgebraTranslation$source_idom_squares_y_nonzero_x"
              parityAlgebraTranslationTheory.source_idom_squares_y_nonzero_x),
         benchLib.IntroAdd
           (benchLib.SafeRule,
            named "parityAlgebraTranslation$source_idom_squares_y_nonzero_y"
              parityAlgebraTranslationTheory.source_idom_squares_y_nonzero_y),
           benchLib.RewriteAdd
             (named "ring$integral_domain_one_ne_zero"
               ringTheory.integral_domain_one_ne_zero)]),
        benchLib.Invoke (benchLib.ExplicitRing, [])))
     (Thm.concl
       parityAlgebraTranslationTheory.source_idom_simultaneous_squares),
   translated "groebner_L72" 72 "by (algebra add: sq_def)"
     (benchLib.Invoke
       (benchLib.ExplicitRing, explicit_ring_definitions))
     (Thm.concl parityAlgebraTranslationTheory.source_idom_four_square),
   translated "groebner_L82" 82 "by (algebra add: sq_def)"
     (benchLib.Invoke
       (benchLib.ExplicitRing, explicit_ring_definitions))
     (Thm.concl parityAlgebraTranslationTheory.source_idom_eight_square)]

val raw_goals =
  translated_goals @
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
   entry "groebner_L113" 113 "by algebra" benchLib.IntIdeal true
     ``(?d : int. a * y - a * x = n * d) ==>
       (?u v : int. a * u + n * v = 1) ==>
       ?e : int. y - x = n * e``]

val goals = map benchLib.prepare_goal raw_goals

val shortfalls : benchLib.shortfall list = []

fun run level =
  benchLib.run_family
    {family = "algebra", goals = goals, shortfalls = shortfalls,
     budget = benchLib.default_budget,
     battery = [benchLib.Auto, benchLib.Aesop], level = level}

end
