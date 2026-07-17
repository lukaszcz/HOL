open HolKernel testutils searchHeap

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun the_store (SOME store) = store
  | the_store NONE = raise Fail "unexpected metavariable binding failure"

fun the_singleton [value] = value
  | the_singleton _ = raise Fail "expected one value"

fun int_compare (x : int, y : int) =
  if x < y then LESS else if x > y then GREATER else EQUAL

fun from_list compare values =
  List.foldl (fn (x, heap) => add x heap) (empty compare) values

fun drain heap =
  if is_empty heap then [] else min heap :: drain (delete_min heap)

val _ =
  test
    ("heap returns values in ascending order",
     fn () =>
       let
         val heap = from_list int_compare [5, 1, 4, 2, 3]
       in
         size heap = 5 andalso drain heap = [1, 2, 3, 4, 5]
       end)

fun key_compare ((key1, _) : int * string, (key2, _)) =
  int_compare (key1, key2)

val duplicate_heap =
  from_list key_compare [(2, "c"), (1, "a"), (3, "d"), (1, "b")]

val _ =
  test
    ("heap preserves entries with duplicate keys",
     fn () =>
       size duplicate_heap = 4 andalso
       map #1 (drain duplicate_heap) = [1, 1, 2, 3])

val _ =
  test
    ("delete_all_min pops every entry with the minimal key",
     fn () =>
       let
         val (entries, rest) = delete_all_min duplicate_heap
         val payloads = map #2 entries
       in
         length entries = 2 andalso
         List.all (fn (key, _) => key = 1) entries andalso
         List.exists (fn value => value = "a") payloads andalso
         List.exists (fn value => value = "b") payloads andalso
         size rest = 2 andalso min rest = (2, "c")
       end)

fun raises_empty f =
  (f (); false) handle Empty => true | _ => false

val _ =
  test
    ("empty heap operations fail",
     fn () =>
       let
         val heap : int heap = empty int_compare
       in
         raises_empty (fn () => ignore (min heap)) andalso
         raises_empty (fn () => ignore (delete_min heap)) andalso
         raises_empty (fn () => ignore (delete_all_min heap))
       end)

val bool_ty = Type.bool
val fixed = Term.mk_var ("fixed", bool_ty)

val _ =
  test
    ("metavariable create bind and walk round-trip",
     fn () =>
       let
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
       in
         clasetMeta.is_meta m andalso
         length (clasetMeta.metas_of store0 (boolSyntax.mk_eq (m, m))) = 1
         andalso
         case clasetMeta.bind (m, fixed) store0 of
           NONE => false
         | SOME store1 =>
             Term.aconv (clasetMeta.walk store1 m) fixed andalso
             Term.aconv (clasetMeta.norm store1 m) fixed
       end)

val _ =
  test
    ("normalization follows bindings and contracts beta and eta",
     fn () =>
       let
         val fun_ty = bool_ty --> bool_ty
         val x = Term.mk_var ("x", bool_ty)
         val f = Term.mk_var ("f", fun_ty)
         val identity = Term.mk_abs (x, x)
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = fun_ty}
             clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (m, identity) store0)
         val beta_term = Term.mk_comb (m, boolSyntax.T)
         val eta_term = Term.mk_abs (x, Term.mk_comb (f, x))
       in
         Term.aconv (clasetMeta.norm store1 beta_term) boolSyntax.T
         andalso Term.aconv (clasetMeta.norm store1 eta_term) f
       end)

val _ =
  test
    ("bind rejects occurs-check and allow-set violations",
     fn () =>
       let
         val eigen = Term.mk_var ("eigen", bool_ty)
         val generated_eigen = Term.genvar bool_ty
         val (blocked, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (permitted, store1) =
           clasetMeta.new_meta {allow = [eigen], ty = bool_ty} store0
         val (indirect, store2) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store1
         val store3 =
           the_store (clasetMeta.bind (indirect, permitted) store2)
         val registered =
           the_store
             (clasetMeta.register_eigen generated_eigen store0)
       in
         not (Option.isSome (clasetMeta.bind (blocked, blocked) store0))
         andalso
         Option.isSome
           (clasetMeta.bind (blocked, generated_eigen) store0)
         andalso
         not (Option.isSome
           (clasetMeta.bind (blocked, generated_eigen) registered))
         andalso
         not (Option.isSome (clasetMeta.bind (blocked, eigen) store1))
         andalso
         Option.isSome (clasetMeta.bind (blocked, fixed) store0)
         andalso
         Option.isSome (clasetMeta.bind (permitted, eigen) store1)
         andalso
         not (Option.isSome (clasetMeta.bind (permitted, eigen) store3))
       end)

val _ =
  test
    ("stores are persistent",
     fn () =>
       let
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (m, fixed) store0)
       in
         Term.aconv (clasetMeta.walk store0 m) m andalso
         Term.aconv (clasetMeta.walk store1 m) fixed
       end)

val _ =
  test
    ("stores reject forged and foreign metavariables",
     fn () =>
       let
         val (m, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign, _) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (name, _) = Term.dest_var m
         val forged = Term.mk_var (name, Type.ind)
         val (tymeta, store1) = clasetMeta.new_tymeta store0
         val (foreign_ty, _) = clasetMeta.new_tymeta clasetMeta.empty
       in
         not (Option.isSome
           (clasetMeta.bind (forged, Term.genvar Type.ind) store0))
         andalso
         not (Option.isSome (clasetMeta.bind (m, foreign) store0))
         andalso
         not (Option.isSome
           (clasetMeta.bind_ty (tymeta, tymeta) store1))
         andalso
         not (Option.isSome
           (clasetMeta.bind_ty (tymeta, foreign_ty) store1))
       end)

fun type_subst_eq [] [] = true
  | type_subst_eq
      ({redex = left_r, residue = left_s} :: left)
      ({redex = right_r, residue = right_s} :: right) =
      left_r = right_r andalso left_s = right_s andalso
      type_subst_eq left right
  | type_subst_eq _ _ = false

fun term_subst_eq [] [] = true
  | term_subst_eq
      ({redex = left_r, residue = left_s} :: left)
      ({redex = right_r, residue = right_s} :: right) =
      Term.aconv left_r right_r andalso Term.aconv left_s right_s andalso
      term_subst_eq left right
  | term_subst_eq _ _ = false

val _ =
  test
    ("ground is deterministic and grounds types before terms",
     fn () =>
       let
         val (tymeta, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (m, store1) =
           clasetMeta.new_meta {allow = [], ty = tymeta} store0
         val grounded1 = clasetMeta.ground store1
         val grounded2 = clasetMeta.ground store1
         val (tys1, tms1) = clasetMeta.collapse grounded1
         val (tys2, tms2) = clasetMeta.collapse grounded2
       in
         type_subst_eq tys1 tys2 andalso term_subst_eq tms1 tms2
         andalso length tys1 = 1 andalso length tms1 = 1
         andalso #residue (hd tys1) = bool_ty
         andalso Term.aconv (#redex (hd tms1))
           (Term.inst tys1 m)
         andalso Term.aconv (#residue (hd tms1))
           (boolSyntax.mk_arb bool_ty)
       end)

val _ =
  test
    ("collapse substitutions instantiate kernel theorems",
     fn () =>
       let
         val (tymeta1, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (tymeta2, store1) = clasetMeta.new_tymeta store0
         val (m1, store2) =
           clasetMeta.new_meta {allow = [], ty = tymeta1} store1
         val (m2, store3) =
           clasetMeta.new_meta {allow = [], ty = tymeta1} store2
         val theorem = ASSUME (boolSyntax.mk_eq (m1, m2))
         val store4 =
           the_store (clasetMeta.bind_ty (tymeta1, tymeta2) store3)
         val store5 =
           the_store (clasetMeta.bind_ty (tymeta2, bool_ty) store4)
         val store6 = the_store (clasetMeta.bind (m1, m2) store5)
         val store7 =
           the_store (clasetMeta.bind (m2, boolSyntax.T) store6)
         val (type_subst, term_subst) = clasetMeta.collapse store7
         val instantiated =
           Drule.INST_TY_TERM (term_subst, type_subst) theorem
       in
         length type_subst = 2 andalso length term_subst = 2
         andalso
         Term.aconv (concl instantiated)
           (boolSyntax.mk_eq (boolSyntax.T, boolSyntax.T))
       end)

fun unify_with store mode rule_metas pair =
  clasetUnify.unify store {mode = mode, rule_metas = rule_metas} pair

val no_rule_metas = {terms = [], types = []}

fun bool_meta allow store =
  clasetMeta.new_meta {allow = allow, ty = bool_ty} store

fun bool_fun_meta allow store =
  clasetMeta.new_meta {allow = allow, ty = bool_ty --> bool_ty} store

val _ =
  test
    ("unifier handles typed first-order cases and occurs checks",
     fn () =>
       let
         val (m, store0) = bool_meta [] clasetMeta.empty
         val nested_left = boolSyntax.mk_conj (m, boolSyntax.T)
         val nested_right = boolSyntax.mk_conj (boolSyntax.F, boolSyntax.T)
         val bound = Term.mk_var ("bound", bool_ty)
         val lambda_left = Term.mk_abs (bound, m)
         val lambda_right = Term.mk_abs (bound, bound)
       in
         case unify_with store0 clasetUnify.Unify no_rule_metas
           (nested_left, nested_right)
         of
           NONE => false
         | SOME store1 =>
             Term.aconv (clasetMeta.norm store1 m) boolSyntax.F
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (m, boolSyntax.mk_neg m)))
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (fixed, boolSyntax.T)))
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (lambda_left, lambda_right)))
       end)

val _ =
  test
    ("types-only unification is integrated and checks occurs",
     fn () =>
       let
         val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
         val (m, store1) =
           clasetMeta.new_meta {allow = [], ty = a} store0
       in
         case unify_with store1 clasetUnify.Unify no_rule_metas
           (m, boolSyntax.T)
         of
           NONE => false
         | SOME store2 =>
             Term.aconv (clasetMeta.norm store2 m) boolSyntax.T
             andalso
             Option.isSome
               (clasetUnify.unify_types store0
                 {mode = clasetUnify.Unify,
                  rule_metas = no_rule_metas}
                 (a, bool_ty))
             andalso
             not (Option.isSome
               (clasetUnify.unify_types store0
                 {mode = clasetUnify.Unify,
                  rule_metas = no_rule_metas}
                 (a, a --> bool_ty)))
       end)

val _ =
  test
    ("pattern unification abstracts distinct eigenvariables",
     fn () =>
       let
         val x = Term.genvar bool_ty
         val y = Term.genvar bool_ty
         val (m, store0) = bool_fun_meta [x, y] clasetMeta.empty
         val lhs = Term.mk_comb (m, x)
         val rhs = boolSyntax.mk_conj (x, y)
         val (n, store1) = bool_fun_meta [x] store0
         val symmetric = Term.mk_comb (n, x)
       in
         case unify_with store1 clasetUnify.Unify no_rule_metas
           (lhs, rhs)
         of
           NONE => false
         | SOME store2 =>
             Term.aconv (clasetMeta.norm store2 lhs) rhs
             andalso
             case unify_with store1 clasetUnify.Unify no_rule_metas
               (boolSyntax.mk_neg x, symmetric)
             of
               NONE => false
             | SOME store3 =>
                 Term.aconv
                   (clasetMeta.norm store3 symmetric)
                   (boolSyntax.mk_neg x)
       end)

val _ =
  test
    ("pattern bindings enforce allow sets and distinct spines",
     fn () =>
       let
         val x = Term.genvar bool_ty
         val y = Term.genvar bool_ty
         val (_, store0) = bool_meta [y] clasetMeta.empty
         val (blocked, store1) = bool_fun_meta [x] store0
         val repeated_ty = bool_ty --> bool_ty --> bool_ty
         val (repeated, store2) =
           clasetMeta.new_meta {allow = [x], ty = repeated_ty} store1
         val repeated_app =
           Term.list_mk_comb (repeated, [x, x])
       in
         not (Option.isSome
           (unify_with store1 clasetUnify.Unify no_rule_metas
             (Term.mk_comb (blocked, x), y)))
         andalso
         not (Option.isSome
           (unify_with store2 clasetUnify.Unify no_rule_metas
             (repeated_app, x)))
       end)

val _ =
  test
    ("patterns handle explicit scope, multiple arguments and fallback",
     fn () =>
       let
         val x = Term.mk_var ("scope_x", bool_ty)
         val y = Term.mk_var ("scope_y", bool_ty)
         val (constant, store0) = bool_fun_meta [] clasetMeta.empty
         val store1 =
           the_store (clasetMeta.register_eigen x store0)
         val constant_app = Term.mk_comb (constant, x)
         val binary_ty = bool_ty --> bool_ty --> bool_ty
         val (binary, store2) =
           clasetMeta.new_meta
             {allow = [x, y], ty = binary_ty} store1
         val binary_app = Term.list_mk_comb (binary, [x, y])
         val binary_rhs = boolSyntax.mk_conj (y, x)
         val (argument, store3) = bool_meta [x] store2
         val fallback_rhs = Term.mk_comb (constant, argument)
       in
         case unify_with store3 clasetUnify.Unify no_rule_metas
           (constant_app, boolSyntax.mk_neg x)
         of
           NONE => false
         | SOME constant_store =>
             Term.aconv
               (clasetMeta.norm constant_store constant_app)
               (boolSyntax.mk_neg x)
             andalso
             case unify_with store3 clasetUnify.Unify no_rule_metas
               (binary_app, binary_rhs)
             of
               NONE => false
             | SOME binary_store =>
                 Term.aconv
                   (clasetMeta.norm binary_store binary_app)
                   binary_rhs
                 andalso
                 case unify_with store3 clasetUnify.Unify no_rule_metas
                   (constant_app, fallback_rhs)
                 of
                   NONE => false
                 | SOME fallback_store =>
                     Term.aconv
                       (clasetMeta.norm fallback_store argument) x
       end)

val _ =
  test
    ("first-order approximation decomposes only equal arities",
     fn () =>
       let
         val x = Term.mk_var ("approx_x", bool_ty)
         val y = Term.mk_var ("approx_y", bool_ty)
         val not_head = #1 (strip_comb (boolSyntax.mk_neg x))
         val and_head =
           #1 (strip_comb (boolSyntax.mk_conj (x, y)))
         val (m, store0) = bool_fun_meta [] clasetMeta.empty
         val equal_left = Term.mk_comb (m, x)
         val equal_right = Term.mk_comb (not_head, x)
         val unequal_right =
           Term.list_mk_comb (and_head, [x, y])
       in
         case unify_with store0 clasetUnify.Unify no_rule_metas
           (equal_left, equal_right)
         of
           NONE => false
         | SOME store1 =>
             Term.aconv (clasetMeta.norm store1 m) not_head
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (equal_left, unequal_right)))
             andalso
             not (Option.isSome
               (unify_with store0 clasetUnify.Unify no_rule_metas
                 (equal_left, Term.mk_comb (not_head, y))))
       end)

val _ =
  test
    ("unification compares modulo beta eta normalization",
     fn () =>
       let
         val x = Term.mk_var ("eta_x", bool_ty)
         val f = Term.mk_var ("eta_f", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val identity = Term.mk_abs (x, x)
         val beta = Term.mk_comb (identity, boolSyntax.T)
         val (m, store0) = bool_fun_meta [] clasetMeta.empty
         val non_eta = Term.mk_abs (x, Term.mk_comb (f, boolSyntax.T))
       in
         Option.isSome
           (unify_with clasetMeta.empty clasetUnify.Unify
             no_rule_metas (eta, f))
         andalso
         Option.isSome
           (unify_with clasetMeta.empty clasetUnify.Unify
             no_rule_metas (beta, boolSyntax.T))
         andalso
         not (Option.isSome
           (unify_with clasetMeta.empty clasetUnify.Unify
             no_rule_metas (non_eta, f)))
         andalso
         case unify_with store0 clasetUnify.Unify no_rule_metas
           (m, eta)
         of
           NONE => false
         | SOME store1 => Term.aconv (clasetMeta.norm store1 m) f
       end)

val _ =
  test
    ("match mode protects old term and type metavariables",
     fn () =>
       let
         val (old, store0) = bool_meta [] clasetMeta.empty
         val (rule, store1) = bool_meta [] store0
         val (old_head, store2) = bool_fun_meta [] store1
         val (rule_arg, store3) = bool_meta [] store2
         val (old_ty, store4) = clasetMeta.new_tymeta store3
         val (rule_ty, store5) = clasetMeta.new_tymeta store4
         val match_metas =
           {terms = [rule, rule_arg], types = [rule_ty]}
       in
         not (Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (old, boolSyntax.T)))
         andalso
         Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (rule, old))
         andalso
         Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (Term.mk_comb (old_head, rule_arg),
              Term.mk_comb (old_head, boolSyntax.T)))
         andalso
         not (Option.isSome
           (unify_with store5 clasetUnify.Match match_metas
             (Term.mk_comb (old_head, boolSyntax.T),
              boolSyntax.mk_neg boolSyntax.T)))
         andalso
         not (Option.isSome
           (clasetUnify.unify_types store5
             {mode = clasetUnify.Match, rule_metas = match_metas}
             (old_ty, bool_ty)))
         andalso
         Option.isSome
           (clasetUnify.unify_types store5
             {mode = clasetUnify.Match, rule_metas = match_metas}
             (rule_ty, bool_ty))
       end)

fun apply_substitution (tys, tms) tm =
  Term.subst tms (Term.inst tys tm)

fun oracle_agrees store rigid_types rigid_terms pair =
  let
    open optmonad
    infix >>
    val ours =
      unify_with store clasetUnify.Unify no_rule_metas pair
    val oracle =
      FullUnify.Env.fromEmpty
        (FullUnify.unify rigid_types rigid_terms pair >>
         FullUnify.collapse)
  in
    case (ours, oracle) of
      (NONE, NONE) => true
    | (SOME ours_store, SOME full_subst) =>
        Term.aconv
          (clasetMeta.norm ours_store (#1 pair))
          (apply_substitution full_subst (#1 pair))
        andalso
        Term.aconv
          (clasetMeta.norm ours_store (#2 pair))
          (apply_substitution full_subst (#2 pair))
    | _ => false
  end

val _ =
  test
    ("first-order results agree with FullUnify oracle",
     fn () =>
       let
         val x = Term.mk_var ("oracle_x", bool_ty)
         val y = Term.mk_var ("oracle_y", bool_ty)
         val (m, store0) = bool_meta [] clasetMeta.empty
         val (f, store1) = bool_fun_meta [] store0
         val (a, store2) = clasetMeta.new_tymeta store1
         val (typed, store3) =
           clasetMeta.new_meta {allow = [], ty = a} store2
         val (typed_fun, store4) =
           clasetMeta.new_meta {allow = [], ty = a --> a} store3
         val (n, store5) = bool_meta [] store4
         val bound = Term.mk_var ("oracle_bound", bool_ty)
         val identity = Term.mk_abs (bound, bound)
         val rigid_ty = Type.mk_vartype "'oracle_rigid"
         val rigid_typed = Term.mk_var ("rigid_typed", rigid_ty)
         val ind_typed = Term.mk_var ("ind_typed", Type.ind)
         val cases =
           [(store5, [], [], (m, boolSyntax.T)),
            (store5, [], [x], (m, x)),
            (store5, [], [x],
             (Term.mk_comb (f, x), boolSyntax.mk_neg x)),
            (store5, [], [], (m, boolSyntax.mk_neg m)),
            (store5, [], [x, y], (x, y)),
            (store5, [], [], (typed, boolSyntax.T)),
            (store5, [], [], (typed_fun, identity)),
            (store5, [], [], (m, n)),
            (store5, [rigid_ty], [rigid_typed],
             (rigid_typed, boolSyntax.T)),
            (store5, [], [ind_typed, fixed], (ind_typed, fixed)),
            (store5, [], [], (identity, identity))]
       in
         List.all
           (fn (store, rigid_types, rigid_terms, pair) =>
             oracle_agrees store rigid_types rigid_terms pair)
           cases
       end)

val _ =
  test
    ("unifier returns one reproducible deterministic solution",
     fn () =>
       let
         val x = Term.mk_var ("det_x", bool_ty)
         val (m, store0) = bool_fun_meta [] clasetMeta.empty
         val pair = (Term.mk_comb (m, x), boolSyntax.mk_neg x)
       in
         case
           (unify_with store0 clasetUnify.Unify no_rule_metas pair,
            unify_with store0 clasetUnify.Unify no_rule_metas pair)
         of
           (SOME left, SOME right) =>
             let
               val (left_tys, left_tms) = clasetMeta.collapse left
               val (right_tys, right_tms) = clasetMeta.collapse right
             in
               type_subst_eq left_tys right_tys andalso
               term_subst_eq left_tms right_tms
             end
         | _ => false
       end)

val goal_p = Term.mk_var ("goal_p", bool_ty)
val goal_q = Term.mk_var ("goal_q", bool_ty)
val goal_r = Term.mk_var ("goal_r", bool_ty)

fun aconv_list left right =
  ListPair.allEq (fn (tm1, tm2) => Term.aconv tm1 tm2) (left, right)

val _ =
  test
    ("engine intake preserves ordered assumptions",
     fn () =>
       let
         val node = clasetGoal.from_goal ([goal_p, goal_q], goal_r)
         val {params, asl, w} =
           the_singleton (clasetGoal.goals node)
       in
         List.null params andalso aconv_list asl [goal_p, goal_q]
         andalso Term.aconv w goal_r
         andalso clasetGoal.replay_length node = 0
         andalso clasetGoal.level node = 0
       end)

val _ =
  test
    ("new assumptions are consed at the front",
     fn () =>
       let
         val parent = {params = [], asl = [goal_r], w = goal_r}
         val {asl, ...} =
           clasetGoal.cons_assumptions [goal_p, goal_q] parent
       in
         aconv_list asl [goal_q, goal_p, goal_r]
       end)

val _ =
  test
    ("premise children strip only the outer prefix",
     fn () =>
       let
         val x = Term.mk_var ("x", bool_ty)
         val pred_p = Term.mk_var ("pred_p", bool_ty --> bool_ty)
         val pred_q = Term.mk_var ("pred_q", bool_ty --> bool_ty)
         val pred_r = Term.mk_var ("pred_r", bool_ty --> bool_ty)
         fun app f arg = Term.mk_comb (f, arg)
         val quantified =
           boolSyntax.mk_forall
             (x, boolSyntax.mk_imp
               (app pred_p x,
                boolSyntax.mk_imp (app pred_q x, app pred_r x)))
         val nested =
           boolSyntax.mk_imp
             (goal_p,
              boolSyntax.mk_forall
                (x, boolSyntax.mk_imp (goal_q, goal_r)))
         val parent = {params = [x], asl = [goal_r], w = goal_r}
         val sibling_fixed = Term.variant [x] x
         val sibling =
           {params = [], asl = [], w = sibling_fixed}
         val store0 = the_store
           (clasetMeta.register_eigen x clasetMeta.empty)
         val node0 = clasetGoal.create
           {goals = [parent, sibling], store = store0, level = 0}
         val (children, store1) =
           clasetGoal.children node0
             {pos = 1, premises = [quantified, nested],
              consumed = NONE}
         val first = List.nth (children, 0)
         val second = List.nth (children, 1)
         val fresh = List.nth (#params first, 1)
         val (fresh_name, _) = Term.dest_var fresh
         val node1 = clasetGoal.set_store store1 node0
         val (again_children, store2) =
           clasetGoal.children node1
             {pos = 1, premises = [quantified], consumed = NONE}
         val again = the_singleton again_children
         val fresh_again = List.nth (#params again, 1)
         val (m, store3) =
           clasetMeta.new_meta {allow = #params first, ty = bool_ty} store2
       in
         length (#params first) = 2
         andalso String.isPrefix "x" fresh_name
         andalso not (Term.aconv fresh x)
         andalso not (Term.aconv fresh sibling_fixed)
         andalso not (clasetMeta.is_eigen store1 sibling_fixed)
         andalso
         aconv_list (#asl first)
           [app pred_q fresh, app pred_p fresh, goal_r]
         andalso Term.aconv (#w first) (app pred_r fresh)
         andalso aconv_list (#params second) [x]
         andalso aconv_list (#asl second) [goal_p, goal_r]
         andalso boolSyntax.is_forall (#w second)
         andalso not (Term.aconv fresh fresh_again)
         andalso
         Option.isSome (clasetMeta.bind (m, fresh) store3)
       end)

val _ =
  test
    ("elim alternatives delete one positional assumption from every child",
     fn () =>
       let
         val parent =
           {params = [], asl = [goal_p, goal_q, goal_p], w = goal_r}
         val node = clasetGoal.create
           {goals = [parent], store = clasetMeta.empty, level = 0}
         val alternatives =
           clasetGoal.elim_children node
             {pos = 1, premises = [goal_q, goal_r]}
         fun child_asls alternative = map #asl (#children alternative)
       in
         map #assumption alternatives = [1, 2, 3]
         andalso aconv_list (map #major alternatives)
           [goal_p, goal_q, goal_p]
         andalso
         List.all
           (fn asl => aconv_list asl [goal_q, goal_p])
           (child_asls (List.nth (alternatives, 0)))
         andalso
         List.all
           (fn asl => aconv_list asl [goal_p, goal_p])
           (child_asls (List.nth (alternatives, 1)))
         andalso
         List.all
           (fn asl => aconv_list asl [goal_p, goal_q])
           (child_asls (List.nth (alternatives, 2)))
       end)

val _ =
  test
    ("node constructors register every declared parameter",
     fn () =>
       let
         val eigen = Term.mk_var ("declared_param", bool_ty)
         val node = clasetGoal.create
           {goals =
              [{params = [eigen], asl = [], w = boolSyntax.T}],
            store = clasetMeta.empty, level = 0}
         val (m, store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             (clasetGoal.store node)
       in
         clasetMeta.is_eigen store eigen
         andalso not (Option.isSome (clasetMeta.bind (m, eigen) store))
       end)

val _ =
  test
    ("engine size counts atoms and abstractions after substitution",
     fn () =>
       let
         val x = Term.mk_var ("size_x", bool_ty)
         val f = Term.mk_var ("size_f", bool_ty --> bool_ty)
         val lambda = Term.mk_abs (x, Term.mk_comb (f, x))
         val (m, store0) =
           clasetMeta.new_meta
             {allow = [], ty = bool_ty --> bool_ty} clasetMeta.empty
         val identity = Term.mk_abs (x, x)
         val store1 = the_store (clasetMeta.bind (m, identity) store0)
         val applied = Term.mk_comb (m, boolSyntax.T)
         val node = clasetGoal.create
           {goals = [{params = [], asl = [], w = applied}],
            store = store1, level = 0}
       in
         clasetGoal.term_size goal_p = 1
         andalso clasetGoal.term_size (Term.mk_comb (f, x)) = 2
         andalso clasetGoal.term_size lambda = 3
         andalso clasetGoal.size node = 1
       end)

val _ =
  test
    ("node equality and ordering use canonical alpha rendering",
     fn () =>
       let
         val x = Term.mk_var ("alpha_x", bool_ty)
         val y = Term.mk_var ("alpha_y", bool_ty)
         val pfun = Term.mk_var ("alpha_p", bool_ty --> bool_ty)
         val qfun = Term.mk_var ("alpha_q", bool_ty --> bool_ty)
         fun singleton param body =
           clasetGoal.create
             {goals =
                [{params = [param], asl = [],
                  w = Term.mk_comb (body, param)}],
              store = clasetMeta.empty, level = 0}
         val left = singleton x pfun
         val alpha = singleton y pfun
         val other = singleton x qfun
         val assumed = clasetGoal.from_goal ([goal_p], goal_q)
         val implication = clasetGoal.from_goal
           ([], boolSyntax.mk_imp (goal_p, goal_q))
         val small = clasetGoal.from_goal ([], boolSyntax.T)
         val large = clasetGoal.from_goal
           ([], boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T))
         val forward = clasetGoal.compare (left, other)
         val backward = clasetGoal.compare (other, left)
       in
         clasetGoal.equal (left, alpha)
         andalso clasetGoal.compare (left, alpha) = EQUAL
         andalso not (clasetGoal.equal (left, other))
         andalso forward <> EQUAL andalso backward <> EQUAL
         andalso forward <> backward
         andalso not (clasetGoal.equal (assumed, implication))
         andalso not (clasetGoal.equal (small, large))
         andalso clasetGoal.compare (small, large) = LESS
       end)

val _ =
  test
    ("unrender records eigenvariables introduced by a tactic",
     fn () =>
       let
         val x = Term.mk_var ("render_x", bool_ty)
         val predicate =
           Term.mk_var ("render_predicate", bool_ty --> bool_ty)
         val quantified = boolSyntax.mk_forall
           (x, Term.mk_comb (predicate, x))
         val node = clasetGoal.from_goal ([], quantified)
         val result = Tactic.GEN_TAC (clasetGoal.render node 1)
       in
         case clasetGoal.unrender node 1 result of
           NONE => false
         | SOME node' =>
             let
               val child = the_singleton (clasetGoal.goals node')
               val param = the_singleton (#params child)
             in
               clasetMeta.is_eigen (clasetGoal.store node') param
               andalso Term.aconv (#w child)
                 (Term.mk_comb (predicate, param))
             end
       end)

fun first_step step cs goal =
  case seq.cases (step cs (clasetGoal.from_goal goal, 1)) of
      NONE => NONE
    | SOME (result, _) => SOME result

fun rendered_goals node =
  let
    fun recurse pos [] = []
      | recurse pos (_ :: rest) =
          clasetGoal.render node pos :: recurse (pos + 1) rest
  in
    recurse 1 (clasetGoal.goals node)
  end

fun valid_step goal (record, node) =
  let
    val materialized =
      clasetGoal.render (clasetGoal.from_goal goal) 1
    val tactic =
      fn _ => (rendered_goals node, clasetStep.validation_of record)
    val _ = Tactical.VALID tactic materialized
  in
    true
  end
  handle HOL_ERR _ => false

val _ =
  test
    ("metavariable-free nodes render and lift tactic children",
     fn () =>
       let
         val node = clasetGoal.from_goal
           ([], boolSyntax.mk_imp (goal_p, goal_q))
         val rendered = clasetGoal.render node 1
         val result = Tactic.DISCH_TAC rendered
       in
         List.null (#1 rendered)
         andalso Term.aconv (#2 rendered)
           (boolSyntax.mk_imp (goal_p, goal_q))
         andalso
         case clasetGoal.unrender node 1 result of
           NONE => false
         | SOME node' =>
             let
               val {params, asl, w} =
                 the_singleton (clasetGoal.goals node')
             in
               List.null params andalso aconv_list asl [goal_p]
               andalso Term.aconv w goal_q
               andalso clasetGoal.replay_length node' = 0
             end
       end)

val _ =
  test
    ("safe-step cascade reaches each ordered slot with valid evidence",
     fn () =>
       let
         open clasetStep
         val implication = boolSyntax.mk_imp (goal_p, goal_q)
         val mp_goal = ([goal_p, implication], goal_r)
         val safe0_cs =
           clasetLib.add_sintros [("truth", boolTheory.TRUTH)]
             clasetLib.empty_cs
         val safep_cs =
           clasetLib.add_sintros
             [("and", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         val subst_x = Term.mk_var ("subst_x", bool_ty)
         val subst_goal =
           ([boolSyntax.mk_eq (subst_x, goal_p)], subst_x)
         val cases =
           [(first_step safe_step clasetLib.empty_cs
               ([goal_p], goal_p),
             fn Assumption _ => true | _ => false),
            (first_step safe_step clasetLib.empty_cs mp_goal,
             fn ModusPonens _ => true | _ => false),
            (first_step safe_step safe0_cs ([], boolSyntax.T),
             fn RuleApplication _ => true | _ => false),
            (first_step safe_step clasetLib.empty_cs ([], implication),
             fn Disch => true | _ => false),
            (first_step safe_step clasetLib.empty_cs subst_goal,
             fn HypSubst => true | _ => false),
            (first_step safe_step safep_cs
               ([], boolSyntax.mk_conj (goal_p, goal_q)),
             fn RuleApplication _ => true | _ => false)]
         fun good (NONE, _) = false
           | good (SOME (record, node), expected) =
               expected (kind_of record) andalso
               valid_step
                 (case kind_of record of
                      Assumption _ => ([goal_p], goal_p)
                    | ModusPonens _ => mp_goal
                    | Disch => ([], implication)
                    | HypSubst => subst_goal
                    | RuleApplication _ =>
                        if List.null (clasetGoal.goals node) then
                          ([], boolSyntax.T)
                        else
                          ([], boolSyntax.mk_conj (goal_p, goal_q))
                    | _ => ([], goal_r))
                 (record, node)
       in
         List.all good cases
       end)

val _ =
  test
    ("assumption closing uses shared beta-eta equality",
     fn () =>
       let
         val x = Term.mk_var ("close_x", bool_ty)
         val f = Term.mk_var ("close_f", bool_ty --> bool_ty)
         val h = Term.mk_var ("close_h", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val abstraction =
           Term.mk_abs (h, boolSyntax.mk_eq (h, f))
         val assumption = Term.mk_comb (abstraction, eta)
         val input = ([assumption], boolSyntax.mk_eq (f, f))
       in
         case first_step clasetStep.safe_step clasetLib.empty_cs input of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Assumption 1 =>
                      valid_step input (record, node)
                  | _ => false)
       end)

val _ =
  test
    ("clarify bimatch2 accepts one closing child and rejects branching",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("and", boolTheory.AND_INTRO_THM)] clasetLib.empty_cs
         val closing_child = boolSyntax.mk_conj (goal_p, goal_q)
         val target = boolSyntax.mk_conj (closing_child, goal_r)
         val accepted = ([closing_child], target)
         val rejected = ([], target)
       in
         case first_step clasetStep.clarify_step cs accepted of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.RuleApplication _ =>
                      length (clasetGoal.goals node) = 1 andalso
                      valid_step accepted (record, node) andalso
                      not (Option.isSome
                        (first_step clasetStep.clarify_step cs rejected))
                  | _ => false)
       end)

val _ =
  test
    ("match mode skips unfixed safe-rule premise variables",
     fn () =>
       let
         val x = Term.mk_var ("unfixed_x", bool_ty)
         val predicate =
           Term.mk_var ("unfixed_predicate", bool_ty --> bool_ty)
         val premise = Term.mk_comb (predicate, x)
         val rule = GEN x (DISCH premise boolTheory.TRUTH)
         val cs =
           clasetLib.add_sintros [("unfixed", rule)] clasetLib.empty_cs
         val old_trace = Feedback.current_trace "classical"
         val notices = ref ([] : string list)
         fun record_notice message =
           notices := message :: !notices
         val _ = Feedback.set_trace "classical" 1
         val result =
           Lib.with_flag
             (Feedback.MESG_outstream, record_notice)
             (fn () =>
               first_step clasetStep.safe_step cs ([], boolSyntax.T)) ()
         val _ = Feedback.set_trace "classical" old_trace
       in
         not (Option.isSome result) andalso
         List.exists
           (String.isSubstring "unfixed premise variables") (!notices)
       end)

val _ =
  test
    ("safe wrappers surround the complete cascade",
     fn () =>
       let
         fun truth_before tac =
           NTactical.NORELSE
             (NTactical.LIFT (Tactic.ACCEPT_TAC boolTheory.TRUTH), tac)
         val cs =
           clasetLib.add_safe_wrapper ("truth", truth_before)
             clasetLib.empty_cs
         val goal = ([], boolSyntax.T)
       in
         case first_step clasetStep.safe_step cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Wrapper => valid_step goal (record, node)
                  | _ => false)
       end)

val _ =
  test
    ("safe eq-mp slot closes a matching contradiction",
     fn () =>
       let
         val proposition = boolSyntax.mk_conj (goal_p, goal_q)
         val goal =
           ([boolSyntax.mk_neg proposition, proposition], goal_r)
       in
         case first_step clasetStep.safe_step clasetLib.empty_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Contradiction (1, 2) =>
                      clasetStep.consumed_of record = SOME 1 andalso
                      valid_step goal (record, node)
                  | _ => false)
       end)

val _ =
  test
    ("rule premise stripping keeps explicit negation opaque",
     fn () =>
       let
         val negative = boolSyntax.mk_neg goal_p
         val rule = DISCH negative (ASSUME negative)
         val cs =
           clasetLib.add_sintros [("negative", rule)]
             clasetLib.empty_cs
         val goal = ([], negative)
       in
         case first_step clasetStep.safe_step cs goal of
             NONE => false
           | SOME (record, node) =>
               let
                 val child = the_singleton (clasetGoal.goals node)
               in
                 List.null (#asl child) andalso
                 Term.aconv (#w child) negative andalso
                 valid_step goal (record, node)
               end
       end)

val _ =
  test
    ("elim lookup dedups tags but keeps positional alternatives",
     fn () =>
       let
         val disjunction = boolSyntax.mk_disj (goal_p, goal_q)
         val goal = ([disjunction, disjunction], goal_r)
         val cs =
           clasetLib.add_selims [("or", boolTheory.OR_ELIM_THM)]
             clasetLib.empty_cs
         val sequence =
           clasetStep.safe_step cs (clasetGoal.from_goal goal, 1)
         fun drain results remaining =
           case seq.cases remaining of
               NONE => List.rev results
             | SOME (result, rest) => drain (result :: results) rest
         val results = drain [] sequence
         val consumed = map (clasetStep.consumed_of o #1) results
       in
         consumed = [SOME 1, SOME 2] andalso
         List.all (valid_step goal) results
       end)

val _ =
  test
    ("rule validations normalize local theorem hypotheses",
     fn () =>
       let
         val x = Term.mk_var ("hyp_close_x", bool_ty)
         val f = Term.mk_var ("hyp_close_f", bool_ty --> bool_ty)
         val h = Term.mk_var ("hyp_close_h", bool_ty --> bool_ty)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val abstraction =
           Term.mk_abs (h, boolSyntax.mk_eq (h, f))
         val assumption = Term.mk_comb (abstraction, eta)
         val rule = Drule.ADD_ASSUM assumption boolTheory.TRUTH
         val cs =
           clasetLib.add_sintros [("local", rule)] clasetLib.empty_cs
         val goal = ([assumption], boolSyntax.T)
       in
         case first_step clasetStep.safe_step cs goal of
             NONE => false
           | SOME result => valid_step goal result
       end)

val _ =
  test
    ("GEN step records its eigenvariable and valid evidence",
     fn () =>
       let
         val x = Term.mk_var ("step_gen_x", bool_ty)
         val predicate =
           Term.mk_var ("step_gen_predicate", bool_ty --> bool_ty)
         val goal =
           ([], boolSyntax.mk_forall
             (x, Term.mk_comb (predicate, x)))
       in
         case first_step clasetStep.safe_step clasetLib.empty_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Gen =>
                      length (clasetStep.eigenvariables_of record) = 1
                      andalso valid_step goal (record, node)
                  | _ => false)
       end)

fun same_goal ((asl1, w1), (asl2, w2)) =
  boolSyntax.goal_eq (asl1, w1) (asl2, w2)

fun same_goals left right = ListPair.allEq same_goal (left, right)

fun tactic_fails tactic goal =
  (ignore (tactic goal); false)
  handle HOL_ERR _ => true

val _ =
  test
    ("SAFE_TAC saturates implication and conjunction in premise order",
     fn () =>
       let
         val goal =
           ([], boolSyntax.mk_imp
             (goal_p, boolSyntax.mk_conj (goal_q, goal_r)))
         val (residues, _) =
           Tactical.VALID
             (classicalLib.SAFE_TAC
               [clasetLib.SIntro boolTheory.AND_INTRO_THM]) goal
         val expected = [([], goal_q), ([], goal_r)]
       in
         same_goals residues expected
       end)

val _ =
  test
    ("CLARIFY_TAC leaves a genuinely branching conjunction intact",
     fn () =>
       let
         val conjunction = boolSyntax.mk_conj (goal_q, goal_r)
         val goal = ([], boolSyntax.mk_imp (goal_p, conjunction))
         val (residues, _) =
           Tactical.VALID
             (classicalLib.CLARIFY_TAC
               [clasetLib.SIntro boolTheory.AND_INTRO_THM]) goal
       in
         same_goals residues [([], conjunction)]
       end)

val _ =
  test
    ("public step tactics perform one valid step",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (goal_p, goal_q)
         val goal = ([], implication)
         val expected = [([goal_p], goal_q)]
         val (safe_goals, _) =
           Tactical.VALID (classicalLib.SAFE_STEP_TAC []) goal
         val (clarify_goals, _) =
           Tactical.VALID (classicalLib.CLARIFY_STEP_TAC []) goal
       in
         same_goals safe_goals expected andalso
         same_goals clarify_goals expected
       end)

val _ =
  test
    ("safe and clarify tactics fail exactly when nothing changes",
     fn () =>
       let val goal = ([], goal_p)
       in
         tactic_fails (classicalLib.SAFE_TAC []) goal andalso
         tactic_fails (classicalLib.CLARIFY_TAC []) goal andalso
         tactic_fails (classicalLib.SAFE_STEP_TAC []) goal andalso
         tactic_fails (classicalLib.CLARIFY_STEP_TAC []) goal
       end)

val _ =
  test
    ("an unmarked extra theorem is unsafe, not a SAFE_TAC rule",
     fn () =>
       let
         val theorem = DISCH goal_q (ASSUME goal_q)
         val goal = ([], goal_q)
       in
         tactic_fails (classicalLib.SAFE_TAC [theorem]) goal
       end)

val _ =
  test
    ("per-invocation claset changes never leak",
     fn () =>
       let
         fun global_rule_names () =
           map (fn (_, (name, _)) => name)
             (clasetLib.rules_of (clasetLib.the_claset ()))
         val initial_names = global_rule_names ()
         val a = Term.mk_var ("leak_a", Type.ind)
         val p = Term.mk_var ("leak_p", Type.ind --> Type.bool)
         val q = Term.mk_var ("leak_q", Type.ind --> Type.bool)
         val pa = mk_comb (p, a)
         val qa = mk_comb (q, a)
         val disjunction = boolSyntax.mk_disj (pa, qa)
         val local_rule = DISCH pa (DISJ1 (ASSUME pa) qa)
         val marker = clasetLib.SIntro local_rule
         val success_goal = ([pa], disjunction)
         val _ =
           Tactical.VALID (classicalLib.SAFE_TAC [marker]) success_goal
         val _ =
           tactic_fails (classicalLib.SAFE_TAC [marker]) ([], goal_p)
       in
         initial_names = global_rule_names ()
       end)

(* TASK_07 group 1: golden safe-cascade ordering. *)

fun step_gives cs goal expected_kind expected_goals =
  case first_step clasetStep.safe_step cs goal of
      NONE => false
    | SOME (record, node) =>
        expected_kind (clasetStep.kind_of record) andalso
        same_goals (rendered_goals node) expected_goals andalso
        valid_step goal (record, node)

val phase1_a = Term.mk_var ("phase1_a", Type.ind)
val phase1_p = Term.mk_var ("phase1_p", Type.ind --> Type.bool)
val phase1_q = Term.mk_var ("phase1_q", Type.ind --> Type.bool)
val phase1_r = Term.mk_var ("phase1_r", Type.ind --> Type.bool)
val phase1_pa = mk_comb (phase1_p, phase1_a)
val phase1_qa = mk_comb (phase1_q, phase1_a)
val phase1_ra = mk_comb (phase1_r, phase1_a)
val phase1_x = Term.mk_var ("phase1_x", Type.ind)
val phase1_c = boolSyntax.mk_arb Type.ind
val phase1_eq = boolSyntax.mk_eq (phase1_x, phase1_c)

val cascade_cs =
  clasetLib.add_sintros
    [("cascade-truth", boolTheory.TRUTH),
     ("cascade-and", boolTheory.AND_INTRO_THM)]
    clasetLib.empty_cs

val _ =
  test
    ("safe cascade slot 1 closes by assumption with exact residue",
     fn () =>
       step_gives cascade_cs ([phase1_pa], phase1_pa)
         (fn clasetStep.Assumption 1 => true | _ => false) [])

val _ =
  test
    ("safe cascade slot 2 performs modus ponens before later slots",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_pa, phase1_qa)
         val goal = ([phase1_pa, implication], phase1_ra)
         val expected = [([phase1_qa, phase1_pa], phase1_ra)]
       in
         step_gives cascade_cs goal
           (fn clasetStep.ModusPonens
                 {implication = 2, antecedent = 1} => true
             | _ => false)
           expected
       end)

val _ =
  test
    ("safe cascade slot 3 applies a safe zero-premise rule",
     fn () =>
       step_gives cascade_cs ([], boolSyntax.T)
         (fn clasetStep.RuleApplication {elim = false, ...} => true
           | _ => false)
         [])

val _ =
  test
    ("DISCH occupies the built-in position before hyp substitution",
     fn () =>
       let
         val goal =
           ([phase1_eq], boolSyntax.mk_imp (phase1_pa, phase1_qa))
         val expected = [([phase1_pa, phase1_eq], phase1_qa)]
       in
         step_gives cascade_cs goal
           (fn clasetStep.Disch => true | _ => false) expected
       end)

val _ =
  test
    ("GEN occupies the built-in position before hyp substitution",
     fn () =>
       let
         val quantified =
           boolSyntax.mk_forall
             (phase1_x, Term.mk_comb (phase1_p, phase1_x))
         val goal = ([phase1_eq], quantified)
       in
         case first_step clasetStep.safe_step cascade_cs goal of
             NONE => false
           | SOME (record, node) =>
               (case (clasetStep.kind_of record, rendered_goals node) of
                    (clasetStep.Gen, [(asms, body)]) =>
                      let val fresh = rand body
                      in
                        same_goals [(asms, body)]
                          [([phase1_eq], mk_comb (phase1_p, fresh))]
                        andalso
                        not (Term.aconv fresh phase1_x)
                        andalso valid_step goal (record, node)
                      end
                  | _ => false)
       end)

val _ =
  test
    ("safe cascade slot 4 saturates hypothesis substitution",
     fn () =>
       let val goal = ([phase1_eq], mk_comb (phase1_p, phase1_x))
       in
         step_gives cascade_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], mk_comb (phase1_p, phase1_c))]
       end)

val _ =
  test
    ("safe cascade slot 5 applies a positive-premise safe rule",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val expected = [([], phase1_pa), ([], phase1_qa)]
       in
         step_gives cascade_cs goal
           (fn clasetStep.RuleApplication {elim = false, ...} => true
             | _ => false)
           expected
       end)

(* TASK_07 group 2: CLARIFY_TAC restrictions and bimatch2. *)

fun three_premise_intro () =
  let
    val p = Term.mk_var ("three_p", Type.bool)
    val q = Term.mk_var ("three_q", Type.bool)
    val r = Term.mk_var ("three_r", Type.bool)
    val body = CONJ (ASSUME p) (CONJ (ASSUME q) (ASSUME r))
  in
    GENL [p, q, r] (DISCH p (DISCH q (DISCH r body)))
  end

val _ =
  test
    ("CLARIFY accepts weight 1 and asserts its exact residue",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_qa, phase1_pa)
         val cs =
           clasetLib.add_sintros [("clarify-one", ASSUME implication)]
             clasetLib.empty_cs
         val goal = ([implication], phase1_pa)
       in
         case first_step clasetStep.clarify_step cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node)
                 [([implication], phase1_qa)] andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY rejects rules of weight 3",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("clarify-three", three_premise_intro ())]
             clasetLib.empty_cs
         val target =
           boolSyntax.mk_conj
             (phase1_pa, boolSyntax.mk_conj (phase1_qa, phase1_ra))
       in
         not (Option.isSome
           (first_step clasetStep.clarify_step cs ([], target)))
       end)

val _ =
  test
    ("CLARIFY bimatch2 closes the left branch exactly",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("clarify-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val goal =
           ([phase1_pa], boolSyntax.mk_conj (phase1_pa, phase1_qa))
       in
         case first_step clasetStep.clarify_step cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node)
                 [([phase1_pa], phase1_qa)] andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY bimatch2 closes the right branch exactly",
     fn () =>
       let
         val cs =
           clasetLib.add_sintros
             [("clarify-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val goal =
           ([phase1_qa], boolSyntax.mk_conj (phase1_pa, phase1_qa))
       in
         case first_step clasetStep.clarify_step cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node)
                 [([phase1_qa], phase1_pa)] andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY bimatch2 accepts a matching-contradiction branch",
     fn () =>
       let
         val negated = boolSyntax.mk_neg phase1_pa
         val disjunction = boolSyntax.mk_disj (phase1_pa, phase1_qa)
         val cs =
           clasetLib.add_selims
             [("clarify-or", boolTheory.OR_ELIM_THM)]
             clasetLib.empty_cs
         val goal = ([negated, disjunction], phase1_ra)
         val expected = [([phase1_qa, negated], phase1_ra)]
       in
         case first_step clasetStep.clarify_step cs goal of
             NONE => false
           | SOME (record, node) =>
               same_goals (rendered_goals node) expected andalso
               valid_step goal (record, node)
       end)

val _ =
  test
    ("CLARIFY leaves an unclosable conjunction conclusion untouched",
     fn () =>
       let
         val target = boolSyntax.mk_conj (phase1_pa, phase1_qa)
         val goal = ([], target)
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY
               (classicalLib.CLARIFY_TAC
                 [clasetLib.SIntro boolTheory.AND_INTRO_THM]))
             goal
       in
         same_goals residues [goal]
       end)

(* TASK_07 group 3: SAFE_TAC against the seed claset. *)

val _ =
  test
    ("seed SAFE_TAC splits conjunctions with exact residues",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues [([], phase1_pa), ([], phase1_qa)]
       end)

val _ =
  test
    ("seed SAFE_TAC eliminates a conjunctive assumption exactly",
     fn () =>
       let
         val conjunction = boolSyntax.mk_conj (phase1_pa, phase1_qa)
         val goal = ([], boolSyntax.mk_imp (conjunction, phase1_ra))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues [([phase1_qa, phase1_pa], phase1_ra)]
       end)

val _ =
  test
    ("seed SAFE_TAC handles universal introduction and implication",
     fn () =>
       let
         val body =
           boolSyntax.mk_imp
             (mk_comb (phase1_p, phase1_x),
              mk_comb (phase1_p, phase1_x))
         val goal = ([], boolSyntax.mk_forall (phase1_x, body))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         List.null residues
       end)

val _ =
  test
    ("seed SAFE_TAC applies safe disjunction introduction exactly",
     fn () =>
       let
         val target = boolSyntax.mk_disj (phase1_pa, phase1_qa)
         val goal = ([], target)
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues
           [([boolSyntax.mk_neg phase1_qa], phase1_pa)]
       end)

val _ =
  test
    ("seed SAFE_TAC never applies unsafe universal elimination",
     fn () =>
       let
         val universal =
           boolSyntax.mk_forall
             (phase1_x, mk_comb (phase1_p, phase1_x))
         val goal = ([universal], phase1_pa)
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.SAFE_TAC [])) goal
       in
         same_goals residues [goal]
       end)

val _ =
  test
    ("seed SAFE_TAC never instantiates EXISTS_INTRO_THM",
     fn () =>
       let
         val existential =
           boolSyntax.mk_exists
             (phase1_x, mk_comb (phase1_p, phase1_x))
         val goal = ([phase1_pa], existential)
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.SAFE_TAC [])) goal
       in
         same_goals residues [goal]
       end)

(* TASK_07 group 4: failure, markers, wrappers, and state isolation. *)

val _ =
  test
    ("D27 exposes raw no-change behavior through TRY",
     fn () =>
       let
         val goal = ([], phase1_pa)
         val (safe_goals, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.SAFE_TAC [])) goal
         val (clarify_goals, _) =
           Tactical.VALID
             (Tactical.TRY (classicalLib.CLARIFY_TAC [])) goal
       in
         tactic_fails (classicalLib.SAFE_TAC []) goal andalso
         tactic_fails (classicalLib.CLARIFY_TAC []) goal andalso
         same_goals safe_goals [goal] andalso
         same_goals clarify_goals [goal]
       end)

fun marker_consumed marker =
  let val (_, leftovers) =
    clasetLib.process_claset_tags [marker] clasetLib.empty_cs
  in List.null leftovers end

val _ =
  test
    ("classical marker vocabulary is consumed and generic tags pass",
     fn () =>
       let
         val consumed =
           [clasetLib.SIntro boolTheory.AND_INTRO_THM,
            clasetLib.Intro boolTheory.EQ_EXT,
            clasetLib.SElim boolTheory.OR_ELIM_THM,
            clasetLib.Elim clasetSeedTheory.FORALL_ELIM_THM,
            clasetLib.SDest boolTheory.OR_ELIM_THM,
            clasetLib.Dest clasetSeedTheory.FORALL_ELIM_THM,
            clasetLib.Del "not-present"]
         val passthrough =
           [markerLib.Cong boolTheory.TRUTH,
            markerLib.Excl "simp-rule"]
         val (_, leftovers) =
           clasetLib.process_claset_tags passthrough clasetLib.empty_cs
       in
         List.all marker_consumed consumed andalso
         ListPair.allEq
           (fn (left, right) => Term.aconv (concl left) (concl right))
           (leftovers, passthrough)
       end)

val _ =
  test
    ("generic Excl passes through without deleting a seed rule",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val (residues, _) =
           Tactical.VALID
             (classicalLib.SAFE_TAC
               [markerLib.Excl "bool$AND_INTRO_THM"])
             goal
       in
         same_goals residues [([], phase1_pa), ([], phase1_qa)]
       end)

val _ =
  test
    ("Del is consumed and removes a seed rule for one invocation",
     fn () =>
       let
         val goal = ([], boolSyntax.mk_conj (phase1_pa, phase1_qa))
         val (residues, _) =
           Tactical.VALID
             (Tactical.TRY
               (classicalLib.SAFE_TAC
                 [clasetLib.Del "bool$AND_INTRO_THM"]))
             goal
         val (after, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) goal
       in
         same_goals residues [goal] andalso
         same_goals after [([], phase1_pa), ([], phase1_qa)]
       end)

fun safe_before tactic base =
  NTactical.NORELSE (NTactical.LIFT tactic, base)

val _ =
  test
    ("safe wrappers compose newest innermost with ORELSE commitment",
     fn () =>
       let
         val left = boolSyntax.mk_imp (phase1_pa, phase1_pa)
         val right = boolSyntax.mk_imp (phase1_qa, phase1_qa)
         val target = boolSyntax.mk_conj (left, right)
         val left_thm = DISCH phase1_pa (ASSUME phase1_pa)
         val right_thm = DISCH phase1_qa (ASSUME phase1_qa)
         val target_thm = CONJ left_thm right_thm
         val cs =
           clasetLib.add_safe_wrapper
             ("new", safe_before (Tactic.ACCEPT_TAC target_thm))
             (clasetLib.add_safe_wrapper
               ("old", safe_before Tactic.CONJ_TAC)
               clasetLib.empty_cs)
         val goal = ([], target)
       in
         case first_step clasetStep.safe_step cs goal of
             NONE => false
           | SOME (record, node) =>
               (case clasetStep.kind_of record of
                    clasetStep.Wrapper =>
                      same_goals (rendered_goals node)
                        [([], left), ([], right)] andalso
                      valid_step goal (record, node)
                  | _ => false)
       end)

(* TASK_07 group 5: the materialized hypothesis-substitution slot. *)

val phase1_y = Term.mk_var ("phase1_y", Type.ind)
val phase1_f = Term.mk_var ("phase1_f", Type.ind --> Type.ind)

val _ =
  test
    ("hyp-subst saturates a chain in one safe step",
     fn () =>
       let
         val first = boolSyntax.mk_eq (phase1_x, phase1_c)
         val second = boolSyntax.mk_eq (phase1_y, phase1_x)
         val goal =
           ([first, second], mk_comb (phase1_p, phase1_y))
       in
         step_gives clasetLib.empty_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], mk_comb (phase1_p, phase1_c))]
       end)

val _ =
  test
    ("hyp-subst refuses both orientations of an occurs-check cycle",
     fn () =>
       let
         val fx = mk_comb (phase1_f, phase1_x)
         val left = boolSyntax.mk_eq (phase1_x, fx)
         val right = boolSyntax.mk_eq (fx, phase1_x)
         fun refuses equality =
           not (Option.isSome
             (first_step clasetStep.safe_step clasetLib.empty_cs
               ([equality], phase1_pa)))
       in
         refuses left andalso refuses right
       end)

val _ =
  test
    ("hyp-subst deletes reflexive equalities",
     fn () =>
       let
         val reflexive = boolSyntax.mk_eq (phase1_x, phase1_x)
         val goal = ([reflexive], mk_comb (phase1_p, phase1_x))
       in
         step_gives clasetLib.empty_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], mk_comb (phase1_p, phase1_x))]
       end)

val _ =
  test
    ("hyp-subst keeps HOL4 positive and negative bool-atom extras",
     fn () =>
       let
         val atom_p = Term.mk_var ("hyp_atom_p", Type.bool)
         val atom_q = Term.mk_var ("hyp_atom_q", Type.bool)
         val goal =
           ([atom_p, boolSyntax.mk_neg atom_q], phase1_ra)
       in
         step_gives clasetLib.empty_cs goal
           (fn clasetStep.HypSubst => true | _ => false)
           [([], phase1_ra)]
       end)

(* TASK_10: unify-mode cascades and bounded depth selection. *)

fun drain_steps sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (result, rest) => result :: drain_steps rest

val _ =
  test
    ("unify rule application leaves and records a witness metavariable",
     fn () =>
       let
         val witness = Term.mk_var ("unify_witness", Type.ind)
         val predicate =
           Term.mk_var ("unify_predicate", Type.ind --> Type.bool)
         val target =
           boolSyntax.mk_exists (witness, mk_comb (predicate, witness))
         val cs =
           clasetLib.add_intros
             [("unify-exists", clasetSeedTheory.EXISTS_INTRO_THM)]
             clasetLib.empty_cs
         val input = ([], target)
       in
         case first_step clasetStep.unsafe_step cs input of
             NONE => false
           | SOME (record, node) =>
               let
                 val {terms, types} = clasetStep.created_of record
                 val (_, child_w) = the_singleton (rendered_goals node)
                 val unresolved =
                   clasetMeta.metas_of (clasetGoal.store node) child_w
               in
                 (case clasetStep.kind_of record of
                      clasetStep.RuleApplication {elim = false, ...} => true
                    | _ => false) andalso
                 not (List.null terms) andalso
                 not (List.null types) andalso
                 not (List.null unresolved)
               end
       end)

val _ =
  test
    ("inst0 assumption unifies the goal with an assumption",
     fn () =>
       let
         val proposition = Term.mk_var ("unify_assumption", Type.bool)
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [proposition], w = meta}],
              store = store, level = 0}
       in
         case seq.cases
           (clasetStep.inst0_step clasetLib.empty_cs (node, 1))
         of
             NONE => false
           | SOME ((record, next), _) =>
               (case clasetStep.kind_of record of
                    clasetStep.Assumption 1 => true
                  | _ => false) andalso
               List.null (clasetGoal.goals next) andalso
               Term.aconv
                 (clasetMeta.norm (clasetGoal.store next) meta)
                 proposition
       end)

val _ =
  test
    ("inst0 APPEND keeps assumption then contradiction alternatives",
     fn () =>
       let
         val proposition = Term.mk_var ("append_proposition", Type.bool)
         val negative = boolSyntax.mk_neg proposition
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [proposition, negative], w = meta}],
              store = store, level = 0}
         val results =
           drain_steps
             (clasetStep.inst0_step clasetLib.empty_cs (node, 1))
         val kinds = map (clasetStep.kind_of o #1) results
       in
         case kinds of
             [clasetStep.Assumption 1,
              clasetStep.Assumption 2,
              clasetStep.Contradiction (2, 1)] => true
           | _ => false
       end)

val _ =
  test
    ("slow_step APPEND keeps unsafe alternatives after inst_step",
     fn () =>
       let
         val witness = Term.mk_var ("slow_append_x", Type.ind)
         val predicate =
           Term.mk_var ("slow_append_p", Type.ind --> Type.bool)
         val proposition = Term.mk_var ("slow_append_q", Type.bool)
         val premise = mk_comb (predicate, witness)
         val safe_rule =
           GENL [predicate, witness]
             (DISCH premise boolTheory.TRUTH)
         val unsafe_rule =
           GEN proposition (DISCH proposition boolTheory.TRUTH)
         val cs =
           clasetLib.add_intros [("slow-unsafe", unsafe_rule)]
             (clasetLib.add_sintros [("slow-inst", safe_rule)]
               clasetLib.empty_cs)
         val node = clasetGoal.from_goal ([], boolSyntax.T)
         val fast =
           drain_steps (clasetStep.step cs (node, 1))
         val slow =
           drain_steps (clasetStep.slow_step cs (node, 1))
         fun child_target (_, result_node) =
           #2 (the_singleton (rendered_goals result_node))
       in
         length fast = 1 andalso length slow = 2 andalso
         is_comb (child_target (hd fast)) andalso
         is_comb (child_target (hd slow)) andalso
         clasetMeta.is_meta (child_target (List.nth (slow, 1)))
       end)

val _ =
  test
    ("metavariable hyp-subst eliminates only the rigid variable side",
     fn () =>
       let
         val variable = Term.mk_var ("internal_subst_x", Type.ind)
         val predicate =
           Term.mk_var ("internal_subst_p", Type.ind --> Type.bool)
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.ind}
             clasetMeta.empty
         val equality = boolSyntax.mk_eq (variable, meta)
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [equality],
                  w = mk_comb (predicate, variable)}],
              store = store, level = 0}
       in
         case seq.cases
           (clasetStep.safe_step clasetLib.empty_cs (node, 1))
         of
             NONE => false
           | SOME ((record, next), _) =>
               let
                 val expected = mk_comb (predicate, meta)
                 val child = the_singleton (rendered_goals next)
                 val tactic =
                   fn _ =>
                     ([child], clasetStep.validation_of record)
                 val _ =
                   Tactical.VALID tactic (clasetGoal.render node 1)
               in
                 (case clasetStep.kind_of record of
                      clasetStep.HypSubst => true
                    | _ => false) andalso
                 same_goal (child, ([], expected)) andalso
                 Term.aconv
                   (clasetMeta.walk (clasetGoal.store next) meta) meta
               end
       end)

val _ =
  test
    ("step saturates every safe goal before its selected unsafe rung",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_pa, phase1_pa)
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [], w = implication},
                 {params = [], asl = [phase1_qa], w = phase1_qa}],
              store = clasetMeta.empty, level = 0}
       in
         case seq.cases (clasetStep.step clasetLib.empty_cs (node, 2)) of
             NONE => false
           | SOME ((_, next), _) => List.null (clasetGoal.goals next)
       end)

val _ =
  test
    ("depth_step selects duplicate versus consuming unsafe rules",
     fn () =>
       let
         val bound = Term.mk_var ("depth_bound", Type.ind)
         val predicate =
           Term.mk_var ("depth_predicate", Type.ind --> Type.bool)
         val target = Term.mk_var ("depth_target", Type.bool)
         val universal =
           boolSyntax.mk_forall (bound, mk_comb (predicate, bound))
         val observations =
           ref ([] : (term list * term) list list)

         fun observe tactic goal =
           seq.map
             (fn result as (goals, _) =>
               (observations := goals :: !observations; result))
             (tactic goal)

         val cs =
           clasetLib.add_unsafe_wrapper ("observe-depth", observe)
             (clasetLib.add_elims
               [("depth-forall", clasetSeedTheory.FORALL_ELIM_THM)]
               clasetLib.empty_cs)
         val node = clasetGoal.from_goal ([universal], target)

         val forall_head = #1 (strip_comb universal)
         fun is_forall_head tm =
           same_const forall_head (#1 (strip_comb tm))
           handle HOL_ERR _ => false
         fun retained runs =
           List.exists
             (List.exists
               (fn (asl, _) => List.exists is_forall_head asl))
             runs

         val _ =
           seq.length
             (clasetStep.depth_step cs (clasetLib.unsafe_part cs) 1
               (node, 1))
         val unsafe_runs = !observations
         val _ = observations := []
         val _ =
           seq.length
             (clasetStep.depth_step cs (clasetLib.dup_part cs) 1
               (node, 1))
         val dup_runs = !observations
       in
         not (List.null unsafe_runs) andalso
         not (retained unsafe_runs) andalso retained dup_runs
       end)

(* TASK_11: grounded, zero-search replay and shared vocabulary. *)

fun first_node_step step cs node pos =
  case seq.cases (step cs (node, pos)) of
      NONE => raise Fail "expected a classical engine step"
    | SOME ((record, next), _) => (record, next)

fun valid_grounded_replay original final_node =
  let
    val grounded =
      clasetReplay.ground (clasetGoal.store final_node)
        (clasetGoal.replay final_node)
    val (residues, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) original
  in
    List.null residues
  end

val _ =
  test
    ("match-mode derivation grounds and replays without search",
     fn () =>
       let
         val conjunction = boolSyntax.mk_conj (phase1_pa, phase1_qa)
         val original = ([phase1_pa, phase1_qa], conjunction)
         val cs =
           clasetLib.add_sintros
             [("replay-and", boolTheory.AND_INTRO_THM)]
             clasetLib.empty_cs
         val (rule_record, after_rule) =
           first_node_step clasetStep.safe_step cs
             (clasetGoal.from_goal original) 1
         val (_, after_left) =
           first_node_step clasetStep.safe_step cs after_rule 1
         val (_, solved) =
           first_node_step clasetStep.safe_step cs after_left 1
       in
         (case clasetStep.kind_of rule_record of
              clasetStep.RuleApplication
                {original = theorem, variant = clasetStep.Plain,
                 elim = false, ...} =>
                Term.aconv (concl theorem)
                  (concl boolTheory.AND_INTRO_THM)
            | _ => false) andalso
         clasetGoal.replay_length solved = 3 andalso
         valid_grounded_replay original solved
       end)

val _ =
  test
    ("unify-mode witness is grounded before zero-search replay",
     fn () =>
       let
         val witness = Term.mk_var ("replay_witness", Type.ind)
         val constant = boolSyntax.mk_arb Type.ind
         val predicate =
           Term.mk_var ("replay_predicate", Type.ind --> Type.bool)
         val fact = mk_comb (predicate, constant)
         val target =
           boolSyntax.mk_exists (witness, mk_comb (predicate, witness))
         val original = ([fact], target)
         val cs =
           clasetLib.add_intros
             [("replay-exists", clasetSeedTheory.EXISTS_INTRO_THM)]
             clasetLib.empty_cs
         val (_, after_rule) =
           first_node_step clasetStep.unsafe_step cs
             (clasetGoal.from_goal original) 1
         val (_, solved) =
           first_node_step clasetStep.inst0_step cs after_rule 1
       in
         clasetGoal.replay_length solved = 2 andalso
         valid_grounded_replay original solved
       end)

val _ =
  test
    ("grounded scripts and substitutions are deterministic",
     fn () =>
       let
         val (tymeta, store0) =
           clasetMeta.new_tymeta clasetMeta.empty
         val (meta, store1) =
           clasetMeta.new_meta {allow = [], ty = tymeta} store0
         val validation = fn [] => boolTheory.TRUTH
           | _ => raise Fail "bad deterministic validation"
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Assumption 1, target = 1,
              consumed = SOME 1,
              created = {terms = [meta], types = [tymeta]},
              eigenvariables = [], validation = validation,
              action = clasetReplay.assumption_action 1,
              children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val first = clasetReplay.ground store1 script
         val second = clasetReplay.ground store1 script
         val first_subst =
           clasetMeta.collapse (clasetReplay.grounded_store first)
         val second_subst =
           clasetMeta.collapse (clasetReplay.grounded_store second)
       in
         clasetReplay.grounded_to_string first =
           clasetReplay.grounded_to_string second andalso
         type_subst_eq (#1 first_subst) (#1 second_subst) andalso
         term_subst_eq (#2 first_subst) (#2 second_subst)
       end)

val _ =
  test
    ("move-assumption-to-back validates and round-trips",
     fn () =>
       let
         val original = ([phase1_pa, phase1_qa, phase1_ra], goal_r)
         val move = clasetReplay.MOVE_ASSUMPTION_TO_BACK_TAC 1
         val tactic =
           Tactical.THEN (move, Tactical.THEN (move, move))
         val (goals, _) = Tactical.VALID tactic original
       in
         same_goals goals [original]
       end)

val _ =
  test
    ("corrupt replay is a catchable outcome",
     fn () =>
       let
         val validation = fn [] => boolTheory.TRUTH
           | _ => raise Fail "bad corrupt validation"
         val record =
           clasetReplay.make_record
             {kind = clasetReplay.Assumption 99, target = 1,
              consumed = SOME 99, created = {terms = [], types = []},
              eigenvariables = [], validation = validation,
              action = clasetReplay.assumption_action 99,
              children = []}
         val script =
           clasetReplay.append (clasetReplay.empty 1) record
         val grounded =
           clasetReplay.ground clasetMeta.empty script
       in
         case clasetReplay.replay grounded ([phase1_pa], phase1_pa) of
             clasetReplay.ReplayFailed _ => true
           | clasetReplay.Replayed _ => false
       end)

(* TASK_12: D24 rigid wrapper materialization and opaque replay. *)

val _ =
  test
    ("metavariable wrapper round-trips and replays its validation",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val target = boolSyntax.mk_conj (meta, meta)
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [meta], w = target}],
              store = store, level = 0}
         val cs =
           clasetLib.add_safe_wrapper
             ("meta-conjunction", safe_before Tactic.CONJ_TAC)
             clasetLib.empty_cs
       in
         case seq.cases (clasetStep.safe_step cs (node, 1)) of
             NONE => false
           | SOME ((record, lifted), _) =>
               let
                 val children = rendered_goals lifted
                 val grounded =
                   clasetReplay.ground (clasetGoal.store lifted)
                     (clasetGoal.replay lifted)
                 val (replayed, validation) =
                   Tactical.VALID (clasetReplay.REPLAY_TAC grounded)
                     (clasetGoal.render node 1)
                 val theorem = validation [ASSUME meta, ASSUME meta]
               in
                 (case clasetStep.kind_of record of
                      clasetStep.Wrapper => true
                    | _ => false) andalso
                 clasetGoal.replay_length lifted = 1 andalso
                 same_goals children
                   [([meta], meta), ([meta], meta)] andalso
                 same_goals replayed children andalso
                 Term.aconv (concl theorem) target
               end
       end)

val _ =
  test
    ("wrapper cannot introduce a marked free it did not receive",
     fn () =>
       let
         val (received, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val (foreign, _) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = received}],
              store = store, level = 0}
         fun forged _ =
           seq.result
             ([([], foreign)],
              fn _ => raise Fail "a rejected validation was called")
         val cs =
           clasetLib.add_safe_wrapper
             ("foreign-marker", fn _ => forged)
             clasetLib.empty_cs
       in
         case seq.cases (clasetStep.safe_step cs (node, 1)) of
             NONE => true
           | SOME _ => false
       end)

val _ =
  test
    ("unrender rejects an unreceived marked type variable",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val (foreign_type, _) =
           clasetMeta.new_tymeta clasetMeta.empty
         val foreign =
           Term.mk_var ("wrapper_foreign_type", foreign_type)
         val forged = boolSyntax.mk_eq (foreign, foreign)
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = meta}],
              store = store, level = 0}
         val result =
           ([([], forged)],
            fn _ => raise Fail "a rejected validation was called")
       in
         not (Option.isSome (clasetGoal.unrender node 1 result))
       end)

(* TASK_13: search drivers, dynamic pruning, bounding, and tracing. *)

fun search_node goals store =
  clasetGoal.create {goals = goals, store = store, level = 0}

fun search_singleton tm =
  search_node [{params = [], asl = [], w = tm}] clasetMeta.empty

fun search_solved store = search_node [] store

fun search_results sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: search_results rest

fun search_target node = #w (hd (clasetGoal.goals node))

val dfs_root_tm = Term.mk_var ("dfs_root", bool_ty)
val dfs_left_tm = Term.mk_var ("dfs_left", bool_ty)
val dfs_right_tm = Term.mk_var ("dfs_right", bool_ty)
val dfs_solution1_tm = Term.mk_var ("dfs_solution1", bool_ty)
val dfs_solution2_tm = Term.mk_var ("dfs_solution2", bool_ty)
val dfs_solution3_tm = Term.mk_var ("dfs_solution3", bool_ty)

val _ =
  test
    ("DEPTH_FIRST is lazy, depth-first, and suppresses duplicate solutions",
     fn () =>
       let
         val forced_right = ref false
         fun satisfied node =
           let val target = search_target node
           in
             Term.aconv target dfs_solution1_tm orelse
             Term.aconv target dfs_solution2_tm orelse
             Term.aconv target dfs_solution3_tm
           end
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target dfs_root_tm then
               seq.fromList
                 [search_singleton dfs_left_tm,
                  search_singleton dfs_right_tm]
             else if Term.aconv target dfs_left_tm then
               seq.fromList
                 [search_singleton dfs_solution1_tm,
                  search_singleton dfs_solution1_tm]
             else if Term.aconv target dfs_right_tm then
               (forced_right := true;
                seq.result (search_singleton dfs_solution2_tm))
             else if Term.aconv target dfs_solution1_tm then
               seq.result (search_singleton dfs_solution3_tm)
             else seq.empty
           end
         val results =
           clasetSearch.DEPTH_FIRST satisfied expand
             (search_singleton dfs_root_tm)
         val first = seq.hd results
       in
         Term.aconv (search_target first) dfs_solution1_tm andalso
         not (!forced_right) andalso
         aconv_list (map search_target (search_results results))
           [dfs_solution1_tm, dfs_solution3_tm, dfs_solution2_tm]
       end)

fun bool_function_chain 0 tm = tm
  | bool_function_chain count tm =
      let
        val function =
          Term.mk_var
            ("search_pad_" ^ Int.toString count, bool_ty --> bool_ty)
      in
        bool_function_chain (count - 1) (Term.mk_comb (function, tm))
      end

val best_root_tm = Term.mk_var ("best_root", bool_ty)
val best_small_tm = Term.mk_var ("best_small", bool_ty)
val best_large_tm = bool_function_chain 4
  (Term.mk_var ("best_large", bool_ty))
val best_small_solution_tm = Term.mk_var ("best_small_solution", bool_ty)
val best_large_solution_tm = Term.mk_var ("best_large_solution", bool_ty)

val _ =
  test
    ("BEST_FIRST orders by size and eagerly drains child sequences",
     fn () =>
       let
         val generated = ref 0
         fun satisfied node =
           let val target = search_target node
           in
             Term.aconv target best_small_solution_tm orelse
             Term.aconv target best_large_solution_tm
           end
         fun eager_children values =
           case values of
               [] => seq.empty
             | value :: rest =>
                 seq.delay
                   (fn () =>
                     (generated := !generated + 1;
                      seq.cons value (eager_children rest)))
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target best_root_tm then
               eager_children
                 [search_singleton best_large_tm,
                  search_singleton best_small_tm]
             else if Term.aconv target best_small_tm then
               seq.result (search_singleton best_small_solution_tm)
             else if Term.aconv target best_large_tm then
               seq.result (search_singleton best_large_solution_tm)
             else seq.empty
           end
         val result =
           seq.hd
             (clasetSearch.BEST_FIRST satisfied expand
               (search_singleton best_root_tm))
       in
         !generated = 2 andalso
         Term.aconv (search_target result) best_small_solution_tm
       end)

val _ =
  test
    ("BEST_FIRST delete_all_min expands an equal node only once",
     fn () =>
       let
         val small_expansions = ref 0
         fun satisfied node =
           Term.aconv (search_target node) best_small_solution_tm
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target best_root_tm then
               seq.fromList
                 [search_singleton best_small_tm,
                  search_singleton best_small_tm]
             else if Term.aconv target best_small_tm then
               (small_expansions := !small_expansions + 1;
                seq.result (search_singleton best_small_solution_tm))
             else seq.empty
           end
         val results =
           search_results
             (clasetSearch.BEST_FIRST satisfied expand
               (search_singleton best_root_tm))
       in
         length results = 1 andalso !small_expansions = 1
       end)

val astar_root_tm = Term.mk_var ("astar_root", bool_ty)
val astar_parent_tm = Term.mk_var ("astar_parent", bool_ty)
val astar_new_tm = Term.mk_var ("astar_new", bool_ty)
val astar_old_tm = bool_function_chain 5
  (Term.mk_var ("astar_old", bool_ty))
val astar_new_solution_tm =
  Term.mk_var ("astar_new_solution", bool_ty)
val astar_old_solution_tm =
  Term.mk_var ("astar_old_solution", bool_ty)

val _ =
  test
    ("ASTAR uses size plus five times level and LIFO equal costs",
     fn () =>
       let
         fun satisfied node =
           let val target = search_target node
           in
             Term.aconv target astar_new_solution_tm orelse
             Term.aconv target astar_old_solution_tm
           end
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target astar_root_tm then
               seq.fromList
                 [search_singleton astar_parent_tm,
                  search_singleton astar_old_tm]
             else if Term.aconv target astar_parent_tm then
               seq.result (search_singleton astar_new_tm)
             else if Term.aconv target astar_new_tm then
               seq.result (search_singleton astar_new_solution_tm)
             else if Term.aconv target astar_old_tm then
               seq.result (search_singleton astar_old_solution_tm)
             else seq.empty
           end
         val result =
           seq.hd
             (clasetSearch.ASTAR satisfied expand
               (search_singleton astar_root_tm))
       in
         clasetGoal.term_size astar_old_tm = 6 andalso
         Term.aconv (search_target result) astar_new_solution_tm
       end)

val _ =
  test
    ("ASTAR suppresses the first equal-cost duplicate",
     fn () =>
       let
         val parent_expansions = ref 0
         fun satisfied node =
           Term.aconv (search_target node) astar_new_solution_tm
         fun expand node =
           let val target = search_target node
           in
             if Term.aconv target astar_root_tm then
               seq.fromList
                 [search_singleton astar_parent_tm,
                  search_singleton astar_parent_tm]
             else if Term.aconv target astar_parent_tm then
               (parent_expansions := !parent_expansions + 1;
                seq.result (search_singleton astar_new_solution_tm))
             else seq.empty
           end
         val _ =
           search_results
             (clasetSearch.ASTAR satisfied expand
               (search_singleton astar_root_tm))
       in
         !parent_expansions = 1
       end)

val _ =
  test
    ("DEEPEN restarts and commits to its first successful bound",
     fn () =>
       let
         val attempted = ref ([] : int list)
         val later_forced = ref false
         val solved_invoked = ref false
         fun bounded bound node =
           (attempted := !attempted @ [bound];
            if bound < 3 then seq.empty
            else if bound = 3 then
              seq.fromList [node, search_singleton dfs_solution1_tm]
            else
              (later_forced := true; seq.result node))
         val results =
           search_results
             (clasetSearch.DEEPEN (2, 7) bounded 1
               (search_singleton dfs_root_tm))
         val solved_results =
           search_results
             (clasetSearch.DEEPEN (2, 7)
               (fn _ => fn node =>
                 (solved_invoked := true; seq.result node))
               1 (search_solved clasetMeta.empty))
       in
         !attempted = [1, 3] andalso length results = 2 andalso
         not (!later_forced) andalso List.null solved_results andalso
         not (!solved_invoked)
       end)

val _ =
  test
    ("BEST_FIRST node counter stops a runaway frontier cleanly",
     fn () =>
       let
         val saved_limit = !clasetSearch.node_limit
         fun expand node =
           let
             val next = clasetGoal.level node + 1
             val target =
               Term.mk_var
                 ("bounded_node_" ^ Int.toString next, bool_ty)
           in
             seq.result (search_singleton target)
           end
         val _ = clasetSearch.node_limit := 2
         val results =
           search_results
             (clasetSearch.BEST_FIRST (fn _ => false) expand
               (search_singleton best_root_tm))
         val count = clasetSearch.node_count ()
         val _ = clasetSearch.node_limit := saved_limit
       in
         List.null results andalso count = 2
       end)

val _ =
  test
    ("D25 prunes alternatives whose bindings cannot reach a sibling",
     fn () =>
       let
         val rigid = Term.mk_var ("prune_rigid", bool_ty)
         val (meta, store0) = bool_meta [] clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (meta, boolSyntax.T) store0)
         val root =
           search_node
             [{params = [], asl = [], w = meta},
              {params = [], asl = [], w = rigid}]
             store0
         fun child () =
           search_node [{params = [], asl = [], w = rigid}] store1
         val expansions = ref 0
         fun expand node =
           (expansions := !expansions + 1;
            case clasetGoal.goals node of
                [_, _] => seq.fromList [child (), child ()]
              | [_] => seq.result (search_solved (clasetGoal.store node))
              | _ => seq.empty)
         val results =
           search_results (clasetSearch.DEPTH_SOLVE expand root)
       in
         length results = 1 andalso !expansions = 2 andalso
         clasetSearch.pruning_count () > 0
       end)

val _ =
  test
    ("D25 retains alternatives that bind a sibling metavariable",
     fn () =>
       let
         val (tymeta, type_store) =
           clasetMeta.new_tymeta clasetMeta.empty
         val (outer, fresh_store) =
           clasetMeta.new_meta {allow = [], ty = tymeta} type_store
         val (shared, unbound_store) =
           clasetMeta.new_meta {allow = [], ty = tymeta} fresh_store
         val chained_store =
           the_store (clasetMeta.bind (outer, shared) unbound_store)
         val store0 =
           the_store (clasetMeta.bind_ty (tymeta, bool_ty) chained_store)
         val true_store =
           the_store (clasetMeta.bind (shared, boolSyntax.T) store0)
         val false_store =
           the_store (clasetMeta.bind (shared, boolSyntax.F) store0)
         val root =
           search_node
             [{params = [], asl = [], w = shared},
              {params = [], asl = [], w = outer}]
             store0
         fun child store =
           search_node [{params = [], asl = [], w = outer}] store
         val expansions = ref 0
         fun expand node =
           (expansions := !expansions + 1;
            case clasetGoal.goals node of
                [_, _] =>
                  seq.fromList [child true_store, child false_store]
              | [_] =>
                  if Term.aconv (#2 (clasetGoal.render node 1)) boolSyntax.F
                  then seq.result (search_solved (clasetGoal.store node))
                  else seq.empty
              | _ => seq.empty)
         val results =
           search_results (clasetSearch.DEPTH_SOLVE expand root)
       in
         length results = 1 andalso !expansions = 3
       end)

val _ =
  test
    ("D25 does not mistake a solved later sibling for the active goal",
     fn () =>
       let
         val active = Term.mk_var ("prune_active", bool_ty)
         val later = Term.mk_var ("prune_later", bool_ty)
         val dead = Term.mk_var ("prune_dead", bool_ty)
         val live = Term.mk_var ("prune_live", bool_ty)
         val root =
           search_node
             [{params = [], asl = [], w = active},
              {params = [], asl = [], w = later}]
             clasetMeta.empty
         fun expand node =
           case clasetGoal.goals node of
               [_, _] =>
                 seq.fromList
                   [search_singleton dead, search_singleton live]
             | [_] =>
                 if Term.aconv (search_target node) live then
                   seq.result (search_solved (clasetGoal.store node))
                 else seq.empty
             | _ => seq.empty
       in
         length
           (search_results (clasetSearch.DEPTH_SOLVE expand root)) = 1
       end)

val _ =
  test
    ("classical trace levels report summaries and full candidates",
     fn () =>
       let
         val old_trace = Feedback.current_trace "classical"
         val notices = ref ([] : string list)
         fun remember message = notices := message :: !notices
         val _ = Feedback.set_trace "classical" 3
         val _ =
           Lib.with_flag
             (Feedback.MESG_outstream, remember)
             (fn () =>
               ignore
                 (search_results
                   (clasetSearch.BEST_FIRST (fn _ => false)
                     (fn _ => seq.empty)
                     (search_singleton best_root_tm)))) ()
         val _ = Feedback.set_trace "classical" old_trace
       in
         List.exists (String.isSubstring "best-first expansion") (!notices)
         andalso
         List.exists (String.isSubstring "candidate:") (!notices)
         andalso
         List.exists (String.isSubstring "search exhausted") (!notices)
       end)

(* TASK_14: public and claset-explicit driver surfaces. *)

fun tactic_solves tactic goal =
  let val (residues, _) = Tactical.VALID tactic goal
  in List.null residues end

val driver_witness = Term.mk_var ("driver_witness", Type.ind)
val driver_constant = Term.mk_var ("driver_constant", Type.ind)
val driver_exists_goal : Abbrev.goal =
  ([], boolSyntax.mk_exists
    (driver_witness,
     boolSyntax.mk_eq (driver_witness, driver_constant)))

val _ =
  test
    ("FAST_TAC instantiates a witness and replays the solution",
     fn () => tactic_solves (classicalLib.FAST_TAC []) driver_exists_goal)

val _ =
  test
    ("single engine step drivers replay their resulting nodes",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (goal_p, goal_q)
         val goal = ([], implication)
         val expected = [([], goal_q)]
         val (step_goals, _) =
           Tactical.VALID (classicalLib.STEP_TAC []) goal
         val (slow_goals, _) =
           Tactical.VALID (classicalLib.SLOW_STEP_TAC []) goal
         val (inst_goals, _) =
           Tactical.VALID
             (classicalLib.INST_STEP_TAC [])
             ([goal_p], goal_p)
       in
         same_goals step_goals expected andalso
         same_goals slow_goals expected andalso
         List.null inst_goals
       end)

fun nested_exists 0 body = body
  | nested_exists count body =
      let
        val witness =
          Term.mk_var
            ("deep_witness_" ^ Int.toString count, Type.ind)
      in
        boolSyntax.mk_exists
          (witness, nested_exists (count - 1) body)
      end

val _ =
  test
    ("DEEPEN supports a raised programmatic start beyond four",
     fn () =>
       let
         val goal = ([], nested_exists 5 boolSyntax.T)
         val tactic =
           NTactical.DETERM
             (classicalLib.deepen_tac (clasetLib.the_claset ())
               {start = 6})
       in
         tactic_solves tactic goal andalso
         tactic_solves (classicalLib.DEEPEN_TAC []) goal
       end)

val _ =
  test
    ("all solve-completely drivers fail cleanly on a non-theorem",
     fn () =>
       let
         val goal = ([], Term.mk_var ("driver_non_theorem", bool_ty))
         val drivers =
           [classicalLib.FAST_TAC [], classicalLib.SLOW_TAC [],
            classicalLib.BEST_TAC [], classicalLib.SLOW_BEST_TAC [],
            classicalLib.FIRST_BEST_TAC [], classicalLib.ASTAR_TAC [],
            classicalLib.SLOW_ASTAR_TAC [], classicalLib.DEEPEN_TAC []]
       in
         List.all (fn tactic => tactic_fails tactic goal) drivers
       end)

val _ =
  test
    ("frontier drivers replay Tactical.VALID-checked solutions",
     fn () =>
       let
         val drivers =
           [classicalLib.BEST_TAC [],
            classicalLib.SLOW_BEST_TAC [],
            classicalLib.FIRST_BEST_TAC [],
            classicalLib.ASTAR_TAC [],
            classicalLib.SLOW_ASTAR_TAC []]
       in
         List.all
           (fn tactic => tactic_solves tactic driver_exists_goal)
           drivers
       end)

(* TASK_15 group 1: eigenvariable discipline through every driver. *)

val complete_drivers =
  [("FAST_TAC", classicalLib.FAST_TAC []),
   ("SLOW_TAC", classicalLib.SLOW_TAC []),
   ("BEST_TAC", classicalLib.BEST_TAC []),
   ("SLOW_BEST_TAC", classicalLib.SLOW_BEST_TAC []),
   ("FIRST_BEST_TAC", classicalLib.FIRST_BEST_TAC []),
   ("ASTAR_TAC", classicalLib.ASTAR_TAC []),
   ("SLOW_ASTAR_TAC", classicalLib.SLOW_ASTAR_TAC []),
   ("DEEPEN_TAC", classicalLib.DEEPEN_TAC [])]

val eigen_x = Term.mk_var ("eigen_x", Type.ind)
val eigen_y = Term.mk_var ("eigen_y", Type.ind)
val eigen_z = Term.mk_var ("eigen_z", Type.ind)
val eigen_predicate =
  Term.mk_var
    ("eigen_predicate", Type.ind --> Type.ind --> Type.bool)

fun eigen_app left right =
  Term.list_mk_comb (eigen_predicate, [left, right])

val early_meta_non_theorem : Abbrev.goal =
  ([], boolSyntax.mk_exists
    (eigen_x,
     boolSyntax.mk_forall
       (eigen_y, boolSyntax.mk_eq (eigen_x, eigen_y))))

val dual_eigen_non_theorem : Abbrev.goal =
  ([], boolSyntax.mk_imp
    (boolSyntax.mk_forall
      (eigen_x,
       boolSyntax.mk_exists
         (eigen_y, eigen_app eigen_x eigen_y)),
     boolSyntax.mk_exists
       (eigen_y,
        boolSyntax.mk_forall
          (eigen_x, eigen_app eigen_x eigen_y))))

val sibling_eigen_non_theorem : Abbrev.goal =
  ([], boolSyntax.mk_exists
    (eigen_z,
     boolSyntax.mk_conj
       (boolSyntax.mk_forall
         (eigen_x, boolSyntax.mk_eq (eigen_z, eigen_x)),
        boolSyntax.mk_eq (eigen_z, eigen_z))))

fun every_driver_fails goal =
  List.all (fn (_, tactic) => tactic_fails tactic goal) complete_drivers

val _ =
  test
    ("all drivers reject capture by a later eigenvariable",
     fn () => every_driver_fails early_meta_non_theorem)

val _ =
  test
    ("all drivers reject the dual quantifier interchange",
     fn () => every_driver_fails dual_eigen_non_theorem)

val _ =
  test
    ("all drivers reject capture from a sibling-local parameter",
     fn () => every_driver_fails sibling_eigen_non_theorem)

(* TASK_15 group 2: replay and grounding at the driver boundary. *)

fun theorem_equal left right =
  Term.aconv (concl left) (concl right) andalso
  ListPair.allEq
    (fn (left_hyp, right_hyp) => Term.aconv left_hyp right_hyp)
    (hyp left, hyp right)

fun solved_theorem tactic goal =
  let
    val (residues, validation) = Tactical.VALID tactic goal
  in
    if List.null residues then validation []
    else raise Fail "a complete driver left residual goals"
  end

val _ =
  test
    ("every complete driver success passes Tactical.VALID replay",
     fn () =>
       List.all
         (fn (_, tactic) =>
           tactic_solves tactic driver_exists_goal)
         complete_drivers)

val _ =
  test
    ("grounded driver theorems are deterministic across identical runs",
     fn () =>
       List.all
         (fn (_, tactic) =>
           theorem_equal
             (solved_theorem tactic driver_exists_goal)
             (solved_theorem tactic driver_exists_goal))
         complete_drivers)

val _ =
  test
    ("D24 metavariable wrapper round-trips through a complete driver",
     fn () =>
       let
         val witness = Term.mk_var ("wrapper_driver_witness", Type.bool)
         val target =
           boolSyntax.mk_exists
             (witness, boolSyntax.mk_conj (witness, witness))
         val saw_marked_goal = ref false

         fun observed_conjunction (goal as (_, conclusion)) =
           (if List.exists clasetMeta.is_meta (free_vars conclusion) then
              saw_marked_goal := true
            else ();
            Tactic.CONJ_TAC goal)

         val cs =
           clasetLib.add_safe_wrapper
             ("driver-meta-conjunction",
              safe_before observed_conjunction)
             (clasetLib.the_claset ())
         val tactic = NTactical.DETERM (classicalLib.fast_tac cs)
       in
         tactic_solves tactic ([], target) andalso !saw_marked_goal
       end)

(* TASK_15 group 3: driver selection, bounds, and D25 pruning. *)

val _ =
  test
    ("SLOW backtracks past the instantiation rung that commits FAST",
     fn () =>
       let
         val schematic = Term.mk_var ("driver_slow_m", Type.ind)
         val constant = Term.mk_var ("driver_slow_c", Type.ind)
         val predicate =
           Term.mk_var ("driver_slow_p", Type.ind --> Type.bool)
         val available = mk_comb (predicate, constant)
         val unsafe_p = Term.mk_var ("driver_slow_u", Type.bool)
         val reflexive = boolSyntax.mk_eq (schematic, schematic)
         val blocked = boolSyntax.mk_imp (reflexive, boolSyntax.F)
         val inst_rule =
           GEN schematic (DISCH blocked boolTheory.TRUTH)
         val unsafe_rule =
           GEN unsafe_p (DISCH unsafe_p boolTheory.TRUTH)
         val cs =
           clasetLib.add_intros [("driver-unsafe", unsafe_rule)]
             (clasetLib.add_sintros [("driver-inst", inst_rule)]
               clasetLib.empty_cs)
         val goal = ([available], boolSyntax.T)
         val fast = NTactical.DETERM (classicalLib.fast_tac cs)
         val slow = NTactical.DETERM (classicalLib.slow_tac cs)
       in
         tactic_fails fast goal andalso tactic_solves slow goal
       end)

val _ =
  test
    ("BEST driver expands the smaller child before an earlier large one",
     fn () =>
       let
         val constant = Term.mk_var ("best_driver_c", Type.ind)
         val predicate =
           Term.mk_var ("best_driver_p", Type.ind --> Type.bool)
         val small = mk_comb (predicate, constant)
         val large = bool_function_chain 5 small
         val large_rule = DISCH large boolTheory.TRUTH
         val small_rule = DISCH small boolTheory.TRUTH
         val visited = ref ([] : term list)

         fun observe base (goal as (_, target)) =
           (visited := target :: !visited; base goal)

         val plain_cs =
           clasetLib.add_intros
             [("best-driver-small", small_rule),
              ("best-driver-large", large_rule)]
             clasetLib.empty_cs
         val cs =
           clasetLib.add_safe_wrapper ("best-driver-observe", observe)
             plain_cs
         val goal = ([large, small], boolSyntax.T)
         val first_target =
           case first_step clasetStep.unsafe_step plain_cs goal of
               NONE => raise Fail "expected a large first alternative"
             | SOME (_, node) => #2 (the_singleton (rendered_goals node))
         val tactic = NTactical.DETERM (classicalLib.best_tac cs)
         val solved = tactic_solves tactic goal
         val order = List.rev (!visited)
       in
         Term.aconv first_target large andalso solved
         andalso length order >= 2
         andalso Term.aconv (List.nth (order, 1)) small
       end)

fun depth_solves cs bound node =
  List.exists
    (List.null o clasetGoal.goals o #2)
    (drain_steps
      (clasetStep.depth_step cs (clasetLib.dup_part cs) bound
        (node, 1)))

val _ =
  test
    ("DEEPEN accounting leaves safe steps and inst0 free",
     fn () =>
       let
         val implication = boolSyntax.mk_imp (phase1_pa, phase1_pa)
         val safe_node = clasetGoal.from_goal ([], implication)
         val (meta, store) = bool_meta [] clasetMeta.empty
         val inst0_node =
           clasetGoal.create
             {goals = [{params = [], asl = [phase1_pa], w = meta}],
              store = store, level = 0}
         val cs = clasetLib.the_claset ()
       in
         depth_solves cs 0 safe_node andalso
         depth_solves cs 0 inst0_node
       end)

val _ =
  test
    ("DEEPEN charges exactly one for an unsafe witness step",
     fn () =>
       let
         val witness = Term.mk_var ("bound_witness", Type.ind)
         val constant = Term.mk_var ("bound_constant", Type.ind)
         val predicate =
           Term.mk_var ("bound_predicate", Type.ind --> Type.bool)
         val fact = mk_comb (predicate, constant)
         val target =
           boolSyntax.mk_exists
             (witness, mk_comb (predicate, witness))
         val node = clasetGoal.from_goal ([fact], target)
         val cs = clasetLib.the_claset ()
       in
         not (depth_solves cs 0 node) andalso depth_solves cs 1 node
       end)

val _ =
  test
    ("DEEPEN charges exactly one for a duplicating elimination",
     fn () =>
       let
         val bound = Term.mk_var ("dup_bound", Type.ind)
         val constant = Term.mk_var ("dup_constant", Type.ind)
         val predicate =
           Term.mk_var ("dup_predicate", Type.ind --> Type.bool)
         val universal =
           boolSyntax.mk_forall (bound, mk_comb (predicate, bound))
         val target = mk_comb (predicate, constant)
         val node = clasetGoal.from_goal ([universal], target)
         val cs = clasetLib.the_claset ()
       in
         not (depth_solves cs 0 node) andalso depth_solves cs 1 node
       end)

val _ =
  test
    ("D25 negative case retains shared alternatives in the driver",
     fn () =>
       let
         val (shared, store0) = bool_meta [] clasetMeta.empty
         val true_store =
           the_store (clasetMeta.bind (shared, boolSyntax.T) store0)
         val false_store =
           the_store (clasetMeta.bind (shared, boolSyntax.F) store0)
         val root =
           search_node
             [{params = [], asl = [], w = shared},
              {params = [], asl = [], w = shared}]
             store0
         fun child store =
           search_node [{params = [], asl = [], w = shared}] store
         val steps = ref 0
         fun expand node =
           (steps := !steps + 1;
            case clasetGoal.goals node of
                [_, _] =>
                  seq.fromList [child true_store, child false_store]
              | [_] =>
                  if Term.aconv (#2 (clasetGoal.render node 1))
                       boolSyntax.F
                  then seq.result
                    (search_solved (clasetGoal.store node))
                  else seq.empty
              | _ => seq.empty)
         val results =
           search_results (clasetSearch.DEPTH_SOLVE expand root)
       in
         length results = 1 andalso !steps = 3
       end)
