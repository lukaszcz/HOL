open testutils blastTerm

infix 9 $

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun unassigned v =
  case !v of
      NONE => true
    | SOME _ => false

val _ =
  test
    ("reserved and real constant heads cannot collide",
     fn () =>
       goal_name = "*Goal*" andalso false_name = "*False*" andalso
       const_name {Thy = "bool", Name = "~"} = "bool$~" andalso
       isGoal (mkGoal (Free "p")) andalso
       not (isGoal (Const (const_name {Thy = "x", Name = "Goal"}, []))))

val _ =
  test
    ("occurs check rejects direct and indirect cycles",
     fn () =>
       let
         val state = newState ()
         val x = ref NONE
         val y = ref NONE
         val direct = not (unify state ([], Var x, Free "f" $ Var x))
         val linked = unify state ([], Var x, Var y)
         val indirect = not (unify state ([], Var y, Free "g" $ Var x))
       in
         direct andalso linked andalso indirect andalso
         trailSize state = 1 andalso unassigned y
       end)

val _ =
  test
    ("occurs check rejects dangling de Bruijn variables",
     fn () =>
       let
         val state = newState ()
         val v = ref NONE
       in
         not (unify state ([], Var v, Bound 0)) andalso
         not (unify state ([], Abs ("x", Var v),
                            Abs ("y", Bound 0))) andalso
         unassigned v andalso trailSize state = 0
       end)

val _ =
  test
    ("Skolem dependencies enforce the eigenvariable condition",
     fn () =>
       let
         val denied_state = newState ()
         val denied = ref NONE
         val allowed_state = newState ()
         val allowed = ref NONE
         val other = ref NONE
       in
         not (unify denied_state
                ([], Var denied, Skolem ("s", [denied]))) andalso
         unassigned denied andalso
         unify allowed_state
           ([], Var allowed, Skolem ("t", [other])) andalso
         trailSize allowed_state = 1
       end)

val _ =
  test
    ("unification decomposes abstractions, applications and type args",
     fn () =>
       let
         val state = newState ()
         val type_var = ref NONE
         val left =
           Abs ("x", Const ("c", [Var type_var]) $ Bound 0)
         val right =
           Abs ("y", Const ("c", [Free "ty"]) $ Bound 0)
       in
         unify state ([], left, right) andalso
         not (unify state
           ([], Const ("c", [Free "a"]), Const ("c", []))) andalso
         not (unify state
           ([], Const ("c", []), Const ("d", [])))
       end)

val _ =
  test
    ("failed unification rolls all branch assignments back",
     fn () =>
       let
         val state = newState ()
         val v = ref NONE
         val left = (Const ("f", []) $ Var v) $ Const ("a", [])
         val right = (Const ("f", []) $ Free "x") $ Const ("b", [])
       in
         not (unify state ([], left, right)) andalso
         unassigned v andalso trailSize state = 0
       end)

val _ =
  test
    ("clearTo restores exactly the requested trail suffix",
     fn () =>
       let
         val state = newState ()
         val x = ref NONE
         val y = ref NONE
         val first = unify state ([], Var x, Free "a")
         val mark = trailSize state
         val second = unify state ([], Var y, Free "b")
         val _ = clearTo state mark
         val x_ok =
           case !x of
               SOME (Free "a") => true
             | _ => false
       in
         first andalso second andalso x_ok andalso unassigned y andalso
         trailSize state = mark
       end)

val _ =
  test
    ("norm chases assignments and beta-normalizes applications",
     fn () =>
       let
         val state = newState ()
         val v = ref NONE
         val _ = unify state ([], Var v, Free "z")
         val beta = Abs ("x", Bound 0) $ Var v
         val typed = Const ("c", [Abs ("x", Bound 0) $ Free "a"])
         val under_abs = Abs ("x", Abs ("y", Bound 0) $ Free "a")
       in
         aconv (norm beta, Free "z") andalso
         aconv (norm typed, Const ("c", [Free "a"])) andalso
         aconv (norm under_abs, under_abs)
       end)

val _ =
  test
    ("norm prunes assigned Skolem dependency references",
     fn () =>
       let
         val state = newState ()
         val assigned = ref NONE
         val live = ref NONE
         val _ = unify state ([], Var assigned, Var live)
       in
         case norm (Skolem ("s", [assigned])) of
             Skolem ("s", [v]) => v = live
           | _ => false
       end)

val _ =
  test
    ("wkNorm performs head beta and eta contraction",
     fn () =>
       let
         val beta = (Abs ("x", Bound 0) $ Free "a") $ Free "b"
         val eta = Abs ("x", Free "f" $ Bound 0)
         val no_eta = Abs ("x", Bound 0 $ Bound 0)
       in
         aconv (wkNorm beta, Free "a" $ Free "b") andalso
         aconv (wkNorm eta, Free "f") andalso
         aconv (wkNorm no_eta, no_eta)
       end)

val _ =
  test
    ("de Bruijn substitution shifts arguments without capture",
     fn () =>
       let
         val body = Abs ("y", Bound 1)
       in
         aconv (subst_bound (Free "a", body), Abs ("y", Free "a"))
         andalso
         aconv (subst_bound (Bound 0, body), Abs ("y", Bound 1))
         andalso loose_bnos (Abs ("x", Bound 1)) = [0]
       end)

val _ =
  test
    ("rule-local variables are assigned off-trail in preference",
     fn () =>
       let
         val state = newState ()
         val branch = ref NONE
         val rule_var = ref NONE
         val ok = unify state ([rule_var], Var branch, Var rule_var)
         val local_ok =
           case !rule_var of
               SOME (Var v) => v = branch
             | _ => false
       in
         ok andalso local_ok andalso unassigned branch andalso
         trailSize state = 0
       end)

val _ =
  test
    ("failed unification restores only trailed branch variables",
     fn () =>
       let
         val state = newState ()
         val rule_var = ref NONE
         val branch = ref NONE
         val left =
           Const ("f", [Var rule_var, Var branch, Const ("a", [])])
         val right =
           Const ("f", [Free "l", Free "b", Const ("c", [])])
         val failed = not (unify state ([rule_var], left, right))
         val local_ok =
           case !rule_var of
               SOME (Free "l") => true
             | _ => false
       in
         failed andalso local_ok andalso unassigned branch andalso
         trailSize state = 0
       end)
