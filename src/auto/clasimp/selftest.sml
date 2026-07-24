open HolKernel testutils

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun residual tactic goal =
  #1 (Tactical.VALID tactic goal)

fun solves tactic goal =
  null (residual tactic goal)

val solver_ss = simpLib.clear_rules (clasimpLib.clasimp_ss ())
val safe_simp = clasimpLib.safe_asm_full_simp solver_ss []

val _ =
  test
    ("safe solver accepts an alpha-matching assumption",
     fn () =>
       solves safe_simp
         ([``(\x:'a. P x) a : bool``], ``(\y:'a. P y) a : bool``))

val _ =
  test
    ("safe solver proves an alpha-reflexive equality",
     fn () =>
       solves safe_simp
         ([], ``(\x:'a. f x) = (\y:'a. f y)``))

val _ =
  test
    ("safe solver proves truth",
     fn () => solves safe_simp ([], boolSyntax.T))

val _ =
  test
    ("safe solver closes from a false assumption",
     fn () =>
       solves safe_simp
         ([boolSyntax.F], ``clasimp_false_goal:bool``))

val _ =
  test
    ("safe solver does not instantiate an existential witness",
     fn () =>
       case residual safe_simp
         ([``P (clasimp_witness:'a) : bool``], ``?x:'a. P x``) of
           [goal] =>
             boolSyntax.goal_eq
               goal
                 ([``P (clasimp_witness:'a) : bool``], ``?x:'a. P x``)
         | _ => false)

val _ =
  test
    ("clasimpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traversedata_for_ss (clasimpLib.clasimp_ss ())) =
       SOME 40)

val _ =
  test
    ("clasimpset carries the splitter",
     fn () =>
       let
         val original =
           ``P (if clasimp_split_b then clasimp_split_x:'a
               else clasimp_split_y) : bool``
       in
         case residual
           (simpLib.SIMP_TAC (clasimpLib.clasimp_ss ()) [])
           ([], original) of
             [([], result)] =>
               not (aconv result original) andalso
               not (can (find_term boolSyntax.is_cond) result)
           | _ => false
       end)

val derived_lhs = ``clasimp_derived_lhs:'a``
val derived_rhs = ``clasimp_derived_rhs:'a``
val derived_rule = ASSUME (boolSyntax.mk_eq (derived_lhs, derived_rhs))
val derived_before =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

val _ =
  BasicProvers.augment_srw_ss
    [simpLib.named_rewrites "clasimp-selftest-derived" [derived_rule]]

val derived_after =
  Conv.QCONV
    (simpLib.SIMP_CONV (clasimpLib.clasimp_ss ()) []) derived_lhs

val _ =
  test
    ("clasimpset cache recomputes after augment_srw_ss",
     fn () =>
       aconv (snd (boolSyntax.dest_eq (concl derived_before)))
         derived_lhs andalso
       aconv (snd (boolSyntax.dest_eq (concl derived_after)))
         derived_rhs)

val mutual_goal =
  ([``P (a:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)
val mutual_expected =
  [([``P (b:'a) : bool``, ``a:'a = b``], ``mutual_q:bool``)]

val _ =
  test
    ("asm_full_simp uses later assumptions mutually",
     fn () =>
       ListPair.allEq
         (fn (goal1, goal2) => boolSyntax.goal_eq goal1 goal2)
         (residual
            (clasimpLib.asm_full_simp BasicProvers.bool_ss [])
            mutual_goal,
          mutual_expected))

val chain_goal =
  ([``(f:'a -> 'b) x = g x``, ``(g:'a -> 'b) x = z``,
    ``R ((f:'a -> 'b) x) : bool``], ``chain_s:bool``)
val chain_expected =
  [([``(f:'a -> 'b) x = z``, ``(g:'a -> 'b) x = z``,
     ``R (z:'b) : bool``], ``chain_s:bool``)]

val _ =
  test
    ("asm_full_simp closes a three-assumption mutual chain",
     fn () =>
       ListPair.allEq
         (fn (goal1, goal2) => boolSyntax.goal_eq goal1 goal2)
         (residual
            (clasimpLib.asm_full_simp BasicProvers.bool_ss [])
            chain_goal,
          chain_expected))
