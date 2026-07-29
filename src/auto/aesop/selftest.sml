open HolKernel testutils

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun residual tactic goal =
  #1 (Tactical.VALID tactic goal)

fun rewrite_rhs ss tm =
  snd
    (boolSyntax.dest_eq
      (concl (Conv.QCONV (simpLib.SIMP_CONV ss []) tm)))

val _ =
  test
    ("aesop_simp settype and attribute are registered without collision",
     fn () =>
       List.exists (equal "aesop_simp") (ThmSetData.all_set_types ()) andalso
       ThmAttribute.is_attribute "aesop_simp")

val _ =
  test
    ("aesop trace is registered at levels one through three",
     fn () =>
       List.exists
         (fn Feedback.TraceElt {name, max, ...} =>
           name = "aesop" andalso max = 3)
         (Feedback.traces ()))

val _ =
  test
    ("aesop simpset fixes conditional-rewrite depth at forty",
     fn () =>
       #cond_depth
         (simpLib.traversedata_for_ss (aesopData.aesop_ss ())) =
       SOME 40)

val _ =
  test
    ("aesop simpset uses the clasimp safe solver stack",
     fn () =>
       null
         (residual
           (simpLib.GEN_GLOBAL_SIMP_TAC {safe = true}
             {base =
                {strip = false, elimvars = false, droptrues = false,
                 oldestfirst = false},
              concl_in_fixpoint = false, imp_rebuild = false}
             (simpLib.clear_rules (aesopData.aesop_ss ())) [])
           ([boolSyntax.F], ``aesop_safe_solver_goal:bool``)))

val derived_lhs = ``aesop_derived_lhs:'a``
val derived_rhs = ``aesop_derived_rhs:'a``
val derived_rule =
  ASSUME (boolSyntax.mk_eq (derived_lhs, derived_rhs))
val derived_before =
  rewrite_rhs (aesopData.aesop_ss ()) derived_lhs
val derived_after =
  BasicProvers.with_simpset_updates
    (fn ss =>
      simpLib.++
        (ss,
         simpLib.named_rewrites "aesop-selftest-derived" [derived_rule]))
    (fn () => rewrite_rhs (aesopData.aesop_ss ()) derived_lhs)
    ()
val derived_restored =
  rewrite_rhs (aesopData.aesop_ss ()) derived_lhs

val _ =
  test
    ("aesop simpset cache derives from srw_ss updates",
     fn () =>
       aconv derived_before derived_lhs andalso
       aconv derived_after derived_rhs andalso
       aconv derived_restored derived_lhs)

val attribute_lhs = ``aesop_attribute_lhs:'a``
val attribute_rhs = ``aesop_attribute_rhs:'a``
val attribute_rule =
  ASSUME (boolSyntax.mk_eq (attribute_lhs, attribute_rhs))
val attribute_before =
  rewrite_rhs (aesopData.aesop_ss ()) attribute_lhs
val _ =
  ThmAttribute.local_attribute
    {attrname = "aesop_simp", name = "aesop_selftest_attribute",
     args = [], thm = attribute_rule}
val attribute_after =
  rewrite_rhs (aesopData.aesop_ss ()) attribute_lhs

val _ =
  test
    ("aesop_simp additions mark the derived simpset cache stale",
     fn () =>
       aconv attribute_before attribute_lhs andalso
       aconv attribute_after attribute_rhs)

val _ =
  test
    ("aesop simpset leaves conditional splitting to safe rules",
     fn () =>
       let
         val original =
           ``P (if aesop_split_b then aesop_split_x:'a
               else aesop_split_y) : bool``
         val goal = ([], original)
         val unsplit =
           residual
             (simpLib.SIMP_TAC (aesopData.aesop_ss ()) []) goal
         val split =
           residual
             (simpLib.SIMP_TAC
               (simpLib.++ (aesopData.aesop_ss (), simpLib.split_ss)) [])
             goal
       in
         case (unsplit, split) of
             ([([], unsplit_goal)], [([], split_goal)]) =>
               can (find_term boolSyntax.is_cond) unsplit_goal andalso
               not (can (find_term boolSyntax.is_cond) split_goal)
           | _ => false
       end)
