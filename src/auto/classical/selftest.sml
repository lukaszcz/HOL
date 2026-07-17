open HolKernel testutils searchHeap

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun the_store (SOME store) = store
  | the_store NONE = raise Fail "unexpected metavariable binding failure"

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
