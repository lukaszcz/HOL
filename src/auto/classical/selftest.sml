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

fun key_compare ((key1, _) : int * string, (key2, _)) =
  int_compare (key1, key2)

val duplicate_heap =
  from_list key_compare [(2, "c"), (1, "a"), (3, "d"), (1, "b")]

val _ =
  test
    ("delete_all_min pops every entry with the minimal key",
     fn () =>
       let
         val (entries, rest) = delete_all_min duplicate_heap
         val payloads = map #2 entries
         val (second, final) = delete_all_min rest
      in
         length entries = 2 andalso
         List.all (fn (key, _) => key = 1) entries andalso
         List.exists (fn value => value = "a") payloads andalso
         List.exists (fn value => value = "b") payloads andalso
         map #1 second = [2] andalso
         not (is_empty final)
       end)

fun raises_empty f =
  (f (); false) handle Empty => true | _ => false

val _ =
  test
    ("delete_all_min fails on an empty heap",
     fn () =>
       let
         val heap : int heap = empty int_compare
       in
         raises_empty (fn () => ignore (delete_all_min heap))
       end)

val bool_ty = Type.bool
val fixed = Term.mk_var ("fixed", bool_ty)

fun beta_eta_term tm =
  #2
    (boolSyntax.dest_eq
      (concl
        (Conv.QCONV
          (Conv.REDEPTH_CONV
            (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV))) tm)))

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
    ("term walks ignore unrelated historical type bindings",
     fn () =>
       let
         fun add_types 0 store = store
           | add_types remaining store =
               let
                 val (tymeta, store1) = clasetMeta.new_tymeta store
                 val store2 =
                   the_store (clasetMeta.bind_ty (tymeta, bool_ty) store1)
               in
                 add_types (remaining - 1) store2
               end
         val store = add_types 5000 clasetMeta.empty
         fun walk 0 = true
           | walk remaining =
               Term.aconv
                 (clasetMeta.walk store boolSyntax.T) boolSyntax.T andalso
               walk (remaining - 1)
       in
         Timeout.apply (Time.fromSeconds 3) walk 20000
         handle Timeout.TIMEOUT _ => false
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
    ("absorb merges all store tables and preserves eigen allow-sets",
     fn () =>
       let
         val left_eigen =
           Term.mk_var ("absorb_left_eigen", bool_ty)
         val right_eigen =
           Term.mk_var ("absorb_right_eigen", bool_ty)
         val (base_meta, base0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (base_tymeta, base) = clasetMeta.new_tymeta base0

         val (left_probe, left0) =
           clasetMeta.new_meta {allow = [left_eigen], ty = bool_ty}
             base
         val (left_bound, left1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} left0
         val left2 =
           the_store (clasetMeta.bind (left_bound, boolSyntax.T) left1)
         val (left_tymeta, left3) = clasetMeta.new_tymeta left2
         val left =
           the_store (clasetMeta.bind_ty (left_tymeta, bool_ty) left3)

         val (right_probe, right0) =
           clasetMeta.new_meta {allow = [right_eigen], ty = bool_ty}
             base
         val (right_bound, right1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} right0
         val right2 =
           the_store
             (clasetMeta.bind (right_bound, boolSyntax.F) right1)
         val (right_tymeta, right3) = clasetMeta.new_tymeta right2
         val right =
           the_store
             (clasetMeta.bind_ty (right_tymeta, Type.ind) right3)

         val merged =
           clasetMeta.absorb {base = base, extensions = [left, right]}
       in
         length (clasetMeta.metas_of merged base_meta) = 1 andalso
         Option.isSome
           (clasetMeta.bind_ty (base_tymeta, bool_ty) merged) andalso
         clasetMeta.is_eigen merged left_eigen andalso
         clasetMeta.is_eigen merged right_eigen andalso
         Option.isSome (clasetMeta.bind (left_probe, left_eigen) merged)
         andalso
         not (Option.isSome
           (clasetMeta.bind (left_probe, right_eigen) merged)) andalso
         Option.isSome
           (clasetMeta.bind (right_probe, right_eigen) merged) andalso
         not (Option.isSome
           (clasetMeta.bind (right_probe, left_eigen) merged)) andalso
         Term.aconv (clasetMeta.walk merged left_bound) boolSyntax.T
         andalso
         Term.aconv (clasetMeta.walk merged right_bound) boolSyntax.F
         andalso clasetMeta.norm_type merged left_tymeta = bool_ty
         andalso clasetMeta.norm_type merged right_tymeta = Type.ind
       end)

val _ =
  test
    ("absorb reports conflicting store entries",
     fn () =>
       let
         val (m, base) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val left = the_store (clasetMeta.bind (m, boolSyntax.T) base)
         val right = the_store (clasetMeta.bind (m, boolSyntax.F) base)
       in
         (ignore
            (clasetMeta.absorb
              {base = base, extensions = [left, right]});
          false)
         handle HOL_ERR error =>
           String.isSubstring "conflicting term binding entry"
             (Feedback.message_of error)
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

val _ =
  test
    ("collapse normalizes a redex exposed by a late lambda binding",
     fn () =>
       let
         val x = Term.mk_var ("late_lambda_x", bool_ty)
         val identity = Term.mk_abs (x, x)
         val function_ty = bool_ty --> bool_ty
         val (dependency, store0) =
           clasetMeta.new_meta {allow = [], ty = function_ty}
             clasetMeta.empty
         val (outer, store1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store0
         val raw_outer = Term.mk_comb (dependency, boolSyntax.T)
         val store2 =
           the_store (clasetMeta.bind (outer, raw_outer) store1)
         val store3 =
           the_store (clasetMeta.bind (dependency, identity) store2)
         val (type_substitution, term_substitution) =
           clasetMeta.collapse store3
         val kernel_result =
           Drule.INST_TY_TERM
             (term_substitution, type_substitution) (ASSUME outer)
         fun residue redex =
           Option.map #residue
             (List.find
               (fn substitution =>
                 Term.aconv (#redex substitution) redex)
               term_substitution)
       in
         null type_substitution andalso
         length term_substitution = 2 andalso
         Option.map (fn tm => Term.aconv tm identity)
           (residue dependency) = SOME true andalso
         Option.map (fn tm => Term.aconv tm boolSyntax.T)
           (residue outer) = SOME true andalso
         Term.aconv (concl kernel_result) boolSyntax.T andalso
         Term.aconv (clasetMeta.norm store3 outer) boolSyntax.T andalso
         Term.aconv
           (clasetMeta.instantiate store3 outer)
           (Term.mk_comb (identity, boolSyntax.T))
       end)

val _ =
  test
    ("bindings persist semantically normalized beta-dead residues",
     fn () =>
       let
         fun dead argument =
           let
             val ignored =
               Term.mk_var ("beta_dead_ignored", type_of argument)
           in
             Term.mk_comb
               (Term.mk_abs (ignored, boolSyntax.T), argument)
           end
         fun collapsed store target =
           let
             val (type_substitution, term_substitution) =
               clasetMeta.collapse store
           in
             concl
               (Drule.INST_TY_TERM
                 (term_substitution, type_substitution) (ASSUME target))
           end
         fun persistent_residue store target =
           case #terms (clasetMeta.bindings store) of
               [(redex, residue)] =>
                 Term.aconv redex target andalso
                 Term.aconv residue boolSyntax.T
             | _ => false
         fun accepts base target raw =
           case clasetMeta.bind (target, raw) base of
               SOME ordinary =>
                 persistent_residue ordinary target andalso
                 Term.aconv
                   (clasetMeta.norm ordinary target) boolSyntax.T andalso
                 Term.aconv (collapsed ordinary target) boolSyntax.T
             | _ => false

         val (self, self_store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign_target, foreign_store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign, _) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val eigen = Term.mk_var ("beta_dead_eigen", bool_ty)
         val (eigen_target, eigen_store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val eigen_store =
           the_store (clasetMeta.register_eigen eigen eigen_store0)
         val (type_target, type_store) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (foreign_tymeta, _) =
           clasetMeta.new_tymeta clasetMeta.empty
         val typed_argument =
           Term.mk_var ("beta_dead_typed", foreign_tymeta)
         val cases =
           [(self_store, self, dead self),
            (foreign_store, foreign_target, dead foreign),
            (eigen_store, eigen_target, dead eigen),
            (type_store, type_target, dead typed_argument)]
       in
         List.all
           (fn (store, target, raw) =>
             not (Term.aconv raw boolSyntax.T) andalso
             accepts store target raw)
           cases
       end)

val _ =
  test
    ("three-meta term bindings expand in both orders without capture",
     fn () =>
       let
         val parameter = Term.mk_var ("capture_x", Type.ind)
         val bound = Term.mk_var ("capture_x", Type.ind)
         val relation =
           Term.mk_var
             ("capture_R", Type.ind --> Type.ind --> bool_ty)
         fun schema dependency =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val (leaf, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val (middle, store1) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind} store0
         val (outer, store2) =
           clasetMeta.new_meta
             {allow = [parameter], ty = bool_ty} store1
         val unresolved = schema middle
         val expected =
           Term.subst
             [{redex = middle, residue = parameter}] unresolved
         val normalized_expected = beta_eta_term expected
         val dependency_first =
           the_store (clasetMeta.bind (leaf, parameter) store2)
         val dependency_first =
           the_store
             (clasetMeta.bind (middle, leaf) dependency_first)
         val dependency_first =
           the_store
             (clasetMeta.bind (outer, unresolved) dependency_first)
         val outer_first =
           the_store (clasetMeta.bind (outer, unresolved) store2)
         val outer_first =
           the_store
             (clasetMeta.bind (middle, leaf) outer_first)
         val outer_first =
           the_store (clasetMeta.bind (leaf, parameter) outer_first)
         val (_, dependency_first_subst) =
           clasetMeta.collapse dependency_first
         val (_, outer_first_subst) = clasetMeta.collapse outer_first
         val dependency_first_theorem =
           Drule.INST_TY_TERM
             (dependency_first_subst, []) (ASSUME outer)
         val outer_first_theorem =
           Drule.INST_TY_TERM
             (outer_first_subst, []) (ASSUME outer)
         val direct =
           clasetMeta.norm outer_first unresolved
         val captured =
           boolSyntax.mk_forall
              (bound,
               Term.list_mk_comb (relation, [bound, bound]))
         fun exact_substitution substitution =
           let
             fun residue redex =
               Option.map #residue
                 (List.find
                   (fn entry => Term.aconv (#redex entry) redex)
                   substitution)
           in
             length substitution = 3 andalso
             Option.map (fn tm => Term.aconv tm parameter)
               (residue leaf) = SOME true andalso
             Option.map (fn tm => Term.aconv tm parameter)
               (residue middle) = SOME true andalso
             Option.map (fn tm => Term.aconv tm normalized_expected)
               (residue outer) = SOME true
           end
       in
         Term.aconv (clasetMeta.norm store2 outer) outer andalso
         Term.aconv
           (clasetMeta.norm dependency_first outer)
           normalized_expected andalso
         Term.aconv
           (clasetMeta.norm outer_first outer) normalized_expected andalso
         exact_substitution dependency_first_subst andalso
         exact_substitution outer_first_subst andalso
         Term.aconv
           (concl dependency_first_theorem) normalized_expected andalso
         Term.aconv
           (concl outer_first_theorem) normalized_expected andalso
         Term.aconv direct normalized_expected andalso
         not (Term.aconv captured expected)
       end)

val _ =
  test
    ("term expansion preserves unrelated and unbound dependencies",
     fn () =>
       let
         val parameter = Term.mk_var ("preserve_x", Type.ind)
         val bound = Term.mk_var ("preserve_x", Type.ind)
         val relation =
           Term.mk_var
             ("preserve_R", Type.ind --> Type.ind --> bool_ty)
         val (dependency, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val (outer, store1) =
           clasetMeta.new_meta
             {allow = [parameter], ty = bool_ty} store0
         val (unrelated, store2) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store1
         val unresolved =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val store3 =
           the_store (clasetMeta.bind (outer, unresolved) store2)
         val store4 =
           the_store
             (clasetMeta.bind (unrelated, boolSyntax.T) store3)
         val (_, substitution) = clasetMeta.collapse store4
         val instantiated =
           Drule.INST_TY_TERM (substitution, []) (ASSUME outer)
       in
         Term.aconv
           (clasetMeta.norm store4 outer) (beta_eta_term unresolved)
         andalso
         Term.aconv (concl instantiated) (beta_eta_term unresolved)
         andalso
         Term.aconv
           (clasetMeta.norm store4 boolSyntax.F) boolSyntax.F
       end)

val _ =
  test
    ("shared and duplicated dependencies expand to exact substitutions",
     fn () =>
       let
         val (leaf, store0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (left, store1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store0
         val (right, store2) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store1
         val (outer, store3) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} store2
         val raw =
           boolSyntax.mk_conj
             (left, boolSyntax.mk_conj (left, right))
         val expected =
           boolSyntax.mk_conj
             (boolSyntax.T,
              boolSyntax.mk_conj (boolSyntax.T, boolSyntax.T))
         val store4 = the_store (clasetMeta.bind (outer, raw) store3)
         val store5 = the_store (clasetMeta.bind (left, leaf) store4)
         val store6 = the_store (clasetMeta.bind (right, leaf) store5)
         val store7 =
           the_store (clasetMeta.bind (leaf, boolSyntax.T) store6)
         val (type_substitution, term_substitution) =
           clasetMeta.collapse store7
         val theorem =
           Drule.INST_TY_TERM
             (term_substitution, type_substitution) (ASSUME outer)
         fun residue redex =
           Option.map #residue
             (List.find
               (fn entry => Term.aconv (#redex entry) redex)
               term_substitution)
         fun is_truth redex =
           Option.map (fn tm => Term.aconv tm boolSyntax.T)
             (residue redex) = SOME true
       in
         null type_substitution andalso
         length term_substitution = 4 andalso
         is_truth leaf andalso is_truth left andalso is_truth right andalso
         Option.map (fn tm => Term.aconv tm expected)
           (residue outer) = SOME true andalso
         Term.aconv (clasetMeta.norm store7 outer) expected andalso
         Term.aconv (concl theorem) expected
       end)

val _ =
  test
    ("indirect store cycles are rejected persistently by both bind paths",
     fn () =>
       let
         fun invariant store first second =
           let
             val bindings = clasetMeta.bindings store
             val (_, substitution) = clasetMeta.collapse store
           in
             null (#types bindings) andalso
             (case #terms bindings of
                  [(redex, residue)] =>
                    Term.aconv redex first andalso
                    Term.aconv residue second
                | _ => false) andalso
             (case substitution of
                  [{redex, residue}] =>
                    Term.aconv redex first andalso
                    Term.aconv residue second
                | _ => false) andalso
             Term.aconv (clasetMeta.norm store first) second andalso
             Term.aconv (clasetMeta.norm store second) second
           end
         val (ordinary_a, ordinary0) =
           clasetMeta.new_meta {allow = [], ty = bool_ty}
             clasetMeta.empty
         val (ordinary_b, ordinary1) =
           clasetMeta.new_meta {allow = [], ty = bool_ty} ordinary0
         val ordinary2 =
           the_store
             (clasetMeta.bind (ordinary_a, ordinary_b) ordinary1)
         val ordinary_rejected =
           clasetMeta.bind (ordinary_b, ordinary_a) ordinary2
       in
         not (Option.isSome ordinary_rejected) andalso
         invariant ordinary2 ordinary_a ordinary_b
       end)

val _ =
  test
    ("term expansion instantiates dependency types capture-safely",
     fn () =>
       let
         val (tymeta, store0) =
           clasetMeta.new_tymeta clasetMeta.empty
         val parameter = Term.mk_var ("typed_capture_x", Type.ind)
         val bound = Term.mk_var ("typed_capture_x", tymeta)
         val relation =
           Term.mk_var
             ("typed_capture_R", tymeta --> tymeta --> bool_ty)
         val (dependency, store1) =
           clasetMeta.new_meta
             {allow = [parameter], ty = tymeta} store0
         val (outer, store2) =
           clasetMeta.new_meta
             {allow = [parameter], ty = bool_ty} store1
         val unresolved =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val store3 =
           the_store (clasetMeta.bind (outer, unresolved) store2)
         val store4 =
           the_store
             (clasetMeta.bind_ty (tymeta, Type.ind) store3)
         val store5 =
           the_store
             (clasetMeta.bind (dependency, parameter) store4)
         val typed_unresolved =
           Term.inst [{redex = tymeta, residue = Type.ind}] unresolved
         val typed_dependency =
           Term.inst [{redex = tymeta, residue = Type.ind}] dependency
         val expected =
           Term.subst
             [{redex = typed_dependency, residue = parameter}]
             typed_unresolved
       in
         Term.aconv
           (clasetMeta.norm store5 outer) (beta_eta_term expected)
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

(* Keep every production branch represented by a table-driven fixture. *)
val _ =
  test
    ("ordinary and timed unifiers have table-driven branch parity",
     fn () =>
       let
         val unify_config =
           {mode = clasetUnify.Unify, rule_metas = no_rule_metas}

         fun type_meta_terms () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val (m, store1) =
               clasetMeta.new_meta {allow = [], ty = a --> bool_ty}
                 store0
             val (n, store2) =
               clasetMeta.new_meta
                 {allow = [], ty = Type.ind --> bool_ty} store1
           in
             (store2, unify_config, (m, n))
           end

         fun type_meta_right () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val (m, store1) =
               clasetMeta.new_meta {allow = [], ty = a} store0
             val rigid = Term.mk_var ("parity_type_right", bool_ty)
           in
             (store1, unify_config, (rigid, m))
           end

         fun type_occurs () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val left = Term.mk_var ("parity_type_occurs_left", a)
             val right =
               Term.mk_var ("parity_type_occurs_right", a --> bool_ty)
           in
             (store0, unify_config, (left, right))
           end

         fun rigid_type_constructor_mismatch () =
           (clasetMeta.empty, unify_config,
            (boolSyntax.T,
             Term.mk_var ("parity_rigid_type_ind", Type.ind)))

         fun match_term rule_on_left () =
           let
             val (old, store0) = bool_meta [] clasetMeta.empty
             val (rule, store1) = bool_meta [] store0
             val metas = {terms = [rule], types = []}
             val pair =
               if rule_on_left then (rule, old) else (old, boolSyntax.T)
           in
             (store1,
              {mode = clasetUnify.Match, rule_metas = metas}, pair)
           end

         fun match_type include_type () =
           let
             val (a, store0) = clasetMeta.new_tymeta clasetMeta.empty
             val (m, store1) =
               clasetMeta.new_meta {allow = [], ty = a} store0
             val metas =
               {terms = [m], types = if include_type then [a] else []}
           in
             (store1, {mode = clasetUnify.Match, rule_metas = metas},
              (m, boolSyntax.T))
           end

         fun pattern reverse () =
           let
             val x = Term.genvar bool_ty
             val (m, store0) = bool_fun_meta [x] clasetMeta.empty
             val application = Term.mk_comb (m, x)
             val target = boolSyntax.mk_neg x
           in
             (store0, unify_config,
              if reverse then (target, application)
              else (application, target))
           end

         fun pattern_fallback reverse () =
           let
             val x = Term.mk_var ("parity_fallback_x", bool_ty)
             val (head, store0) = bool_fun_meta [] clasetMeta.empty
             val store1 = the_store (clasetMeta.register_eigen x store0)
             val (argument, store2) = bool_meta [x] store1
             val pattern = Term.mk_comb (head, x)
             val blocked = Term.mk_comb (head, argument)
           in
             (store2, unify_config,
              if reverse then (blocked, pattern) else (pattern, blocked))
           end

         fun lambda equal () =
           let
             val x = Term.mk_var ("parity_lambda_x", bool_ty)
             val y = Term.mk_var ("parity_lambda_y", bool_ty)
             val (m, store) = bool_meta [] clasetMeta.empty
             val left = Term.mk_abs (x, if equal then m else boolSyntax.T)
             val right = Term.mk_abs (y, if equal then boolSyntax.T
                                                   else boolSyntax.F)
           in
             (store, unify_config, (left, right))
           end

         fun approximation same_arity () =
           let
             val x = Term.mk_var ("parity_approx_x", bool_ty)
             val y = Term.mk_var ("parity_approx_y", bool_ty)
             val (m, store0) = bool_fun_meta [] clasetMeta.empty
             val left = Term.mk_comb (m, x)
             val right =
               if same_arity then boolSyntax.mk_neg x
               else boolSyntax.mk_conj (x, y)
           in
             (store0, unify_config, (left, right))
           end

         fun match_approximation () =
           let
             val x = Term.mk_var ("parity_match_approx_x", bool_ty)
             val (head, store0) = bool_fun_meta [] clasetMeta.empty
             val (argument, store1) = bool_meta [] store0
             val metas = {terms = [argument], types = []}
           in
             (store1,
              {mode = clasetUnify.Match, rule_metas = metas},
              (Term.mk_comb (head, argument),
               Term.mk_comb (head, boolSyntax.T)))
           end

         fun match_unequal_head_approximation () =
           let
             val x = Term.mk_var ("parity_match_unequal_x", bool_ty)
             val (head, store0) = bool_fun_meta [] clasetMeta.empty
             val (argument, store1) = bool_meta [] store0
             val metas = {terms = [argument], types = []}
           in
             (store1,
              {mode = clasetUnify.Match, rule_metas = metas},
              (Term.mk_comb (head, argument), boolSyntax.mk_neg x))
           end

         fun occurs () =
           let
             val (m, store0) = bool_meta [] clasetMeta.empty
           in
             (store0, unify_config, (m, boolSyntax.mk_neg m))
           end

         fun allow_failure () =
           let
             val x = Term.mk_var ("parity_allow_x", bool_ty)
             val (m, store0) = bool_meta [] clasetMeta.empty
             val store1 = the_store (clasetMeta.register_eigen x store0)
           in
             (store1, unify_config, (m, x))
           end

         fun normalized_store () =
           let
             val x = Term.mk_var ("parity_normalized_x", bool_ty)
             val identity = Term.mk_abs (x, x)
             val (m, store0) = bool_fun_meta [] clasetMeta.empty
             val store1 = the_store (clasetMeta.bind (m, identity) store0)
           in
             (store1, unify_config,
              (Term.mk_comb (m, boolSyntax.T), boolSyntax.T))
           end

         fun beta_eta () =
           let
             val x = Term.mk_var ("parity_eta_x", bool_ty)
             val f = Term.mk_var ("parity_eta_f", bool_ty --> bool_ty)
           in
             (clasetMeta.empty, unify_config,
              (Term.mk_abs (x, Term.mk_comb (f, x)), f))
           end

         fun rigid_constants () =
           (clasetMeta.empty, unify_config,
            (boolSyntax.T, boolSyntax.F))

         fun rigid_variables () =
           (clasetMeta.empty, unify_config,
            (Term.mk_var ("parity_rigid_left", bool_ty),
             Term.mk_var ("parity_rigid_right", bool_ty)))

         fun rigid_right_variable () =
           (clasetMeta.empty, unify_config,
            (boolSyntax.T,
             Term.mk_var ("parity_structural_right", bool_ty)))

         fun structural_wildcard_mismatch () =
           let
             val x = Term.mk_var ("parity_wildcard_x", bool_ty)
             val not_head = #1 (strip_comb (boolSyntax.mk_neg x))
           in
             (clasetMeta.empty, unify_config,
              (Term.mk_abs (x, boolSyntax.T), not_head))
           end

         fun combination_decomposition () =
           let
             val (m, store0) = bool_meta [] clasetMeta.empty
           in
             (store0, unify_config,
              (boolSyntax.mk_conj (m, boolSyntax.T),
               boolSyntax.mk_conj (boolSyntax.F, boolSyntax.T)))
           end

         fun succeeds (_, _, (left, right), SOME result) =
               Term.aconv (clasetMeta.norm result left)
                 (clasetMeta.norm result right)
           | succeeds _ = false

         fun fails (_, _, _, NONE) = true
           | fails _ = false

         (* A failed pattern binding falls through to equal-head
            approximation.  Its distinguishing store leaves [head]
            unbound and binds [argument] to the eigenvariable [x]. *)
         fun fallback_succeeds reverse
               (_, _, (left, right), SOME result) =
               let
                 val (head, left_args) = strip_comb left
                 val (_, right_args) = strip_comb right
                 val x = hd (if reverse then right_args else left_args)
                 val argument =
                   hd (if reverse then left_args else right_args)
               in
                 Term.aconv (clasetMeta.norm result head) head andalso
                 Term.aconv (clasetMeta.norm result argument) x andalso
                 Term.aconv (clasetMeta.norm result left)
                   (clasetMeta.norm result right)
               end
           | fallback_succeeds _ _ = false

         datatype parity_branch =
             NoNamedBranch
           | RigidTypeMismatch
           | ProtectedUnequalHead
           | RightPatternFallback
           | LambdaDescent
           | StructuralWildcard

         (* The explicit term shapes in the failure rows select the named
            branch before returning NONE; successful rows additionally pin
            the complete unifying substitution through [succeeds]. *)
         val fixtures =
           [("type-constructor recursion and left type binding",
             type_meta_terms, succeeds, [84, 24, 5, 109, 2, 35],
             NoNamedBranch),
            ("right type-meta binding", type_meta_right, succeeds,
             [29, 13, 2, 39, 2, 34], NoNamedBranch),
            ("type occurs-check failure", type_occurs, fails,
             [4, 6, 1, 13, 0, 2], NoNamedBranch),
            ("rigid type-constructor mismatch",
             rigid_type_constructor_mismatch, fails, [2, 0, 2, 3, 0, 0],
             RigidTypeMismatch),
            ("Match rule-term binding", match_term true, succeeds,
             [40, 17, 2, 55, 1, 33], NoNamedBranch),
            ("Match protected left variable", match_term false, fails,
             [12, 2, 2, 14, 0, 10], NoNamedBranch),
            ("Match rule-type and term binding", match_type true, succeeds,
             [29, 12, 2, 33, 2, 34], NoNamedBranch),
            ("Match protected type-variable failure",
             match_type false, fails, [1, 1, 1, 3, 0, 0], NoNamedBranch),
            ("left-pattern binding", pattern false, succeeds,
             [48, 7, 1, 38, 1, 46], NoNamedBranch),
            ("right-pattern binding", pattern true, succeeds,
             [48, 7, 1, 39, 1, 46], NoNamedBranch),
            ("left-pattern binding-failure fallback",
             pattern_fallback false, fallback_succeeds false,
             [139, 31, 6, 156, 1, 98], NoNamedBranch),
            ("right-pattern binding-failure fallback",
             pattern_fallback true, fallback_succeeds true,
             [139, 31, 6, 156, 1, 98], RightPatternFallback),
            ("structural lambda descent and binding", lambda true, succeeds,
             [48, 10, 4, 44, 2, 44], LambdaDescent),
            ("structural lambda descent failure", lambda false, fails,
             [28, 2, 4, 22, 1, 22], LambdaDescent),
            ("flexible-head approximation", approximation true, succeeds,
             [72, 9, 6, 69, 1, 58], NoNamedBranch),
            ("approximation arity mismatch", approximation false, fails,
             [19, 3, 2, 21, 0, 19], NoNamedBranch),
            ("protected applied-meta equal-head fallback",
             match_approximation, succeeds, [54, 12, 5, 57, 1, 48],
             NoNamedBranch),
            ("protected applied-meta unequal-head fallback",
             match_unequal_head_approximation, fails,
             [20, 4, 2, 24, 0, 16], ProtectedUnequalHead),
            ("term occurs-check failure", occurs, fails,
             [35, 11, 2, 43, 0, 34], NoNamedBranch),
            ("term allow-set failure", allow_failure, fails,
             [31, 7, 2, 32, 1, 38], NoNamedBranch),
            ("stored normalization and beta equality",
             normalized_store, succeeds, [25, 4, 1, 15, 0, 21],
             NoNamedBranch),
            ("eta-normalized equality", beta_eta, succeeds,
             [17, 0, 1, 11, 0, 14], NoNamedBranch),
            ("structural rigid-constant mismatch", rigid_constants, fails,
             [10, 0, 2, 8, 0, 10], NoNamedBranch),
            ("structural left rigid-variable failure",
             rigid_variables, fails, [10, 0, 2, 11, 0, 10],
             NoNamedBranch),
            ("structural right rigid-variable failure",
             rigid_right_variable, fails, [10, 0, 2, 10, 0, 10],
             NoNamedBranch),
            ("structural combination decomposition",
             combination_decomposition, succeeds, [90, 10, 8, 73, 1, 90],
             NoNamedBranch),
            ("structural wildcard mismatch",
             structural_wildcard_mismatch, fails, [16, 0, 2, 12, 0, 11],
             StructuralWildcard)]

         fun agrees (_, make, expected, _, _) =
           let
             val (store, config, pair) = make ()
             val result = clasetUnify.unify store config pair
           in
             expected (store, config, pair, result)
           end
       in
         List.foldl
           (fn (fixture, all) => agrees fixture andalso all) true fixtures
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
    ("exact prefixes stay static while ordinary children stay eager",
     fn () =>
       let
         val x = Term.mk_var ("static_prefix_x", Type.ind)
         val c =
           Term.mk_var
             ("static_prefix_C", Type.ind --> bool_ty)
         val g =
           Term.mk_var
             ("static_prefix_G", Type.ind --> bool_ty)
         val exposed =
           boolSyntax.mk_forall
             (x,
              boolSyntax.mk_imp
                (Term.mk_comb (c, x), Term.mk_comb (g, x)))
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [], ty = bool_ty} clasetMeta.empty
         val store1 = the_store (clasetMeta.bind (meta, exposed) store0)
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [], w = goal_p}],
              store = store1, level = 0}
         val descriptor = clasetReplay.exact_prefix_descriptor meta
         val (exact, _, rebuilds) =
           clasetGoal.exact_blast_children node
             {pos = 1, premises = [meta], prefixes = [descriptor],
              consumed = NONE}
         val (ordinary, _) =
           clasetGoal.children node
             {pos = 1, premises = [meta], consumed = NONE}
         val exact_child = the_singleton exact
         val ordinary_child = the_singleton ordinary
         val nested = boolSyntax.mk_imp (goal_q, exposed)
         val nested_descriptor : clasetReplay.exact_prefix_descriptor =
           clasetReplay.exact_prefix_descriptor nested
         val nested_split =
           clasetReplay.split_exact_prefix
             {descriptor = nested_descriptor, premise = nested,
              fresh = []}
         val malformed =
           total
             (fn () =>
               clasetReplay.split_exact_prefix
                 {descriptor = {foralls = 1, implications = 0},
                  premise = goal_p,
                  fresh = [Term.mk_var ("bad_prefix", bool_ty)]}) ()
       in
         length rebuilds = 1 andalso
         List.null (#params exact_child) andalso
         List.null (#asl exact_child) andalso
         Term.aconv (#w exact_child) exposed andalso
         length (#params ordinary_child) = 1 andalso
         length (#asl ordinary_child) = 1 andalso
         #foralls nested_descriptor = 0 andalso
         #implications nested_descriptor = 1 andalso
         aconv_list (#assumptions nested_split) [goal_q] andalso
         Term.aconv (#residual nested_split) exposed andalso
         not (Option.isSome malformed) andalso
         let
           val fresh = the_singleton (#params ordinary_child)
         in
           Term.aconv (#w ordinary_child) (Term.mk_comb (g, fresh))
         end
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

(* [rule_origin] recovers the declaration an applied theorem came from by
   comparing the theorem against the canonicalisation the claset stored for
   that declaration.  Probing with forms rebuilt by clasetRules.ext_info
   pins both halves at once: the stored forms have to be exactly what
   ext_info derives, or no probe would match and every case would take the
   fallback; and the reported variant has to follow the scan's priority --
   plain and swapped only for a non-duplicating application, then the two
   duplicated forms whatever the application was, then plain regardless --
   with an undeclared theorem its own origin. *)
val _ =
  test
    ("rule_origin classifies every stored rule form and falls back",
     fn () =>
       let
         open clasetStep
         val origin_p = Term.mk_var ("origin_p", bool_ty)
         val origin_q = Term.mk_var ("origin_q", bool_ty)
         val conjunction = boolSyntax.mk_conj (origin_p, origin_q)
         val intro_thm =
           DISCH origin_p (DISJ1 (ASSUME origin_p) origin_q)
         val dest_thm =
           DISCH conjunction (CONJUNCT1 (ASSUME conjunction))
         val unsafe_intro =
           {kind = clasetRules.Intro, safe = false, prio = NONE}
         val safe_intro =
           {kind = clasetRules.Intro, safe = true, prio = NONE}
         val safe_dest =
           {kind = clasetRules.Dest, safe = true, prio = NONE}
         fun declared spec named_th =
           let
             val cs = clasetLib.add_rule spec named_th clasetLib.empty_cs
             val (_, (_, original)) = the_singleton (clasetLib.rules_of cs)
           in
             (cs, original, clasetRules.ext_info spec original)
           end
         fun reports cs duplicated theorem (origin, expected) =
           let
             val (reported, variant) = rule_origin cs duplicated theorem
           in
             Term.aconv (concl reported) (concl origin) andalso
             variant = expected
           end
         val (unsafe_cs, unsafe_orig,
              {rl = (plain, swapped), dup_rl = (dup, dup_swapped)}) =
           declared unsafe_intro ("origin_unsafe", intro_thm)
         val (safe_cs, safe_orig, {rl = (safe_plain, _), dup_rl = _}) =
           declared safe_intro ("origin_safe", intro_thm)
         val (dest_cs, dest_orig, {rl = (dest_plain, _), dup_rl = _}) =
           declared safe_dest ("origin_dest", dest_thm)
         (* A claset the scan has to look past its first declaration in. *)
         val both_cs =
           clasetLib.add_rule safe_dest ("origin_dest", dest_thm)
             (clasetLib.add_rule unsafe_intro
                ("origin_unsafe", intro_thm) clasetLib.empty_cs)
       in
         reports unsafe_cs false plain (unsafe_orig, Plain) andalso
         reports unsafe_cs false (valOf swapped)
           (unsafe_orig, Swapped) andalso
         reports unsafe_cs false dup (unsafe_orig, Duplicate) andalso
         reports unsafe_cs true dup (unsafe_orig, Duplicate) andalso
         reports unsafe_cs true (valOf dup_swapped)
           (unsafe_orig, Duplicate) andalso
         (* The last resort: a duplicating application of the plain form of
            a rule whose duplicated form differs from it. *)
         reports unsafe_cs true plain (unsafe_orig, Plain) andalso
         (* A safe rule duplicates to itself, so a duplicating application
            of it reaches the duplicate test rather than the plain one. *)
         reports safe_cs false safe_plain (safe_orig, Plain) andalso
         reports safe_cs true safe_plain (safe_orig, Duplicate) andalso
         (* A destruction rule is applied in its made-elimination form,
            which is not the declared theorem. *)
         reports dest_cs false dest_plain (dest_orig, MakeElim) andalso
         reports both_cs false plain (unsafe_orig, Plain) andalso
         reports both_cs false dest_plain (dest_orig, MakeElim) andalso
         (* No declaration derived this theorem, so it is its own origin. *)
         reports unsafe_cs false boolTheory.TRUTH
           (boolTheory.TRUTH, Plain) andalso
         reports unsafe_cs true boolTheory.TRUTH
           (boolTheory.TRUTH, Duplicate)
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

fun tactic_error_message tactic goal =
  (ignore (tactic goal); NONE)
  handle HOL_ERR error => SOME (Feedback.message_of error)

val classical_marker_entry_points =
  [classicalLib.SAFE_TAC, classicalLib.CLARIFY_TAC,
   classicalLib.SAFE_STEP_TAC, classicalLib.CLARIFY_STEP_TAC,
   classicalLib.STEP_TAC, classicalLib.SLOW_STEP_TAC,
   classicalLib.INST_STEP_TAC, classicalLib.FAST_TAC,
   classicalLib.SLOW_TAC, classicalLib.BEST_TAC,
   classicalLib.SLOW_BEST_TAC, classicalLib.FIRST_BEST_TAC,
   classicalLib.ASTAR_TAC, classicalLib.SLOW_ASTAR_TAC,
   classicalLib.DEEPEN_TAC]

val _ =
  test
    ("classical tactics clearly reject Simp and Iff markers",
     fn () =>
       let
         val goal = ([], boolSyntax.T)
         fun rejected (marker, expected) =
           List.all
             (fn entry_point =>
                tactic_error_message (entry_point [marker]) goal =
                  SOME expected)
             classical_marker_entry_points
       in
         rejected
           (clasetLib.Simp boolTheory.TRUTH,
            "Simp marker requires a tactic with a simpset") andalso
         rejected
           (clasetLib.Iff boolTheory.TRUTH,
            "Iff marker requires a tactic with a simpset")
       end)

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
    ("SAFE_TAC validates an eta-reduced EXISTS major in match mode",
     fn () =>
       let
         val bound = Term.mk_var ("safe_eta_bound", Type.ind)
         val predicate =
           Term.mk_var ("safe_eta_predicate", Type.ind --> bool_ty)
         val target = Term.mk_var ("safe_eta_target", bool_ty)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC []) ([major], target)
       in
         case residues of
             [([assumption], conclusion)] =>
               let val (head, arguments) = strip_comb assumption
               in
                 Term.aconv head predicate andalso
                 length arguments = 1 andalso
                 Term.aconv conclusion boolSyntax.F
               end
           | _ => false
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

(* Inserting a fact changes the goal, so the invocation has made progress
   even when the engine then finds no step; discarding the fact would fail
   an invocation that did change something. *)
val _ =
  test
    ("safe and clarify tactics keep an inserted fact when nothing steps",
     fn () =>
       let
         val theorem = boolTheory.TRUTH
         val goal = ([], goal_p)
         val expected = [([concl theorem], goal_p)]
         fun residues tactic =
           #1 (Tactical.VALID (tactic [theorem]) goal)
       in
         same_goals (residues classicalLib.SAFE_TAC) expected andalso
         same_goals (residues classicalLib.CLARIFY_TAC) expected
       end)

val _ =
  test
    ("an unmarked theorem is visible in non-closing tactic residues",
     fn () =>
       let
         val residue_fact = concl boolTheory.TRUTH
         val theorem = boolTheory.TRUTH
         val goal = ([], boolSyntax.mk_conj (goal_p, goal_q))
         val (residues, _) =
           Tactical.VALID (classicalLib.SAFE_TAC [theorem]) goal
       in
         same_goals residues
           [([residue_fact], goal_p), ([residue_fact], goal_q)]
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
    ("FAST_TAC unwraps and inserts a Once-wrapped theorem",
     fn () =>
       let
         val theorem = combinTheory.I_THM
         val goal = ([], concl theorem)
       in
         tactic_fails (classicalLib.FAST_TAC []) goal andalso
         not
           (tactic_fails
             (classicalLib.FAST_TAC [BoundedRewrites.Once theorem])
             goal)
       end)

val _ =
  test
    ("FAST_TAC honors Abbr controls before classical search",
     fn () =>
       let
         val abbreviation = "classical_abbreviated_p"
         val abbreviated =
           Term.mk_var (abbreviation, Type.bool)
         val goal =
           ([markerSyntax.mk_abbrev (abbreviation, phase1_pa), phase1_pa],
            abbreviated)
       in
         tactic_fails (classicalLib.FAST_TAC []) goal andalso
         not
           (tactic_fails
             (classicalLib.FAST_TAC
               [markerLib.Abbr [QUOTE abbreviation]]) goal)
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

fun drain_exact sequence =
  case seq.cases sequence of
      NONE => []
    | SOME (value, rest) => value :: drain_exact rest

fun exact_rule_api_variants cs plain selected input =
  [drain_exact
     (clasetStep.blast_rule_step cs plain (input ())),
   drain_exact
     (clasetStep.blast_rule_step_at cs selected (input ()))]


fun exact_source_term store tm =
  let
    val (type_substitution, term_substitution) =
      clasetMeta.collapse store
  in
    concl
      (Drule.INST_TY_TERM
        (term_substitution, type_substitution) (ASSUME tm))
  end

fun normalize_exact_term tm =
  #2
    (boolSyntax.dest_eq
      (concl
        (Conv.QCONV
          (Conv.REDEPTH_CONV
            (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV))) tm)))

fun exact_transition_variants cs specification goal =
  [drain_exact
     (clasetStep.blast_rule_step cs specification
       (clasetGoal.from_goal goal, 1))]

fun valid_open_replay goal (record, node) =
  let
    val expected = rendered_goals node
    val grounded =
      clasetReplay.ground (clasetGoal.store node)
        (clasetGoal.replay node)
    val (actual, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
  in
    valid_step goal (record, node) andalso
    same_goals actual expected
  end

fun same_rule_alternatives goal left right =
  length left = length right andalso
  ListPair.allEq
    (fn ((left_record, left_node), (right_record, right_node)) =>
      clasetStep.consumed_of left_record =
        clasetStep.consumed_of right_record andalso
      same_goals (rendered_goals left_node) (rendered_goals right_node)
      andalso valid_open_replay goal (left_record, left_node)
      andalso valid_open_replay goal (right_record, right_node))
    (left, right)

val _ =
  test
    ("rule_step uses standard children while blast keeps prefixes intact",
     fn () =>
       let
         val schema = Term.mk_var ("bounded_intro_schema", bool_ty)
         val atom = Term.mk_var ("bounded_intro_atom", bool_ty)
         val target = boolSyntax.mk_imp (atom, atom)
         val theorem = GEN schema (DISCH schema (ASSUME schema))
         val goal = ([], target)
         val cs = clasetLib.empty_cs
         val specification = {theorem = theorem, elim = false}
         val selected =
           {theorem = theorem, elim = false, major = NONE}
         fun input () = (clasetGoal.from_goal goal, 1)
         val variants =
           exact_rule_api_variants cs specification selected input
         val standard =
           drain_exact
             (clasetStep.rule_step
               {theorem = theorem, elim = false,
                mode = clasetUnify.Match} (input ()))
         val (ordinary_children, ordinary_validation) =
           clasetReplay.RULE_TAC
             {theorem = SPEC target theorem, elim = false,
              consumed = NONE, parameters = [],
              eigenvariables = [[]]} goal

         fun exact result =
           case result of
               [(record, node)] =>
                 same_goals (rendered_goals node) [([], target)]
                 andalso clasetGoal.replay_length node = 1
                 andalso valid_open_replay goal (record, node)
             | _ => false
       in
         List.all exact variants andalso
         (case standard of
              [(record, node)] =>
                same_goals (rendered_goals node) [([atom], atom)]
                andalso valid_open_replay goal (record, node)
            | _ => false) andalso
         same_goals ordinary_children [([atom], atom)] andalso
         let val result = ordinary_validation [ASSUME atom]
         in Term.aconv (concl result) target end
       end)

val _ =
  test
    ("rule_step agrees with blast on plain intro and elim rules",
     fn () =>
       let
         val p = Term.mk_var ("rule_step_diff_p", bool_ty)
         val q = Term.mk_var ("rule_step_diff_q", bool_ty)
         val conjunction = boolSyntax.mk_conj (p, q)
         val intro_goal = ([p, q], conjunction)
         val elim_goal = ([p, p], boolSyntax.T)
         val elim_theorem = DISCH p boolTheory.TRUTH

         fun standard theorem elim goal =
           drain_exact
             (clasetStep.rule_step
               {theorem = theorem, elim = elim,
                mode = clasetUnify.Unify}
               (clasetGoal.from_goal goal, 1))
         fun blast theorem elim goal =
           drain_exact
             (clasetStep.blast_rule_step clasetLib.empty_cs
               {theorem = theorem, elim = elim}
               (clasetGoal.from_goal goal, 1))

         val standard_intro =
           standard boolTheory.AND_INTRO_THM false intro_goal
         val blast_intro =
           blast boolTheory.AND_INTRO_THM false intro_goal
         val standard_elim = standard elim_theorem true elim_goal
         val blast_elim = blast elim_theorem true elim_goal
       in
         same_rule_alternatives intro_goal standard_intro blast_intro
         andalso
         same_rule_alternatives elim_goal standard_elim blast_elim
         andalso
         map (clasetStep.consumed_of o #1) standard_elim =
           [SOME 1, SOME 2]
       end)

val _ =
  test
    ("exact elim keeps a newly exposed implication intact",
     fn () =>
       let
         val bound = Term.mk_var ("bounded_elim_bound", Type.ind)
         val predicate =
           Term.mk_var
             ("bounded_elim_predicate", Type.ind --> bool_ty)
         val marker =
           Term.mk_var ("bounded_elim_marker", bool_ty)
         val atom = Term.mk_var ("bounded_elim_atom", bool_ty)
         val target = boolSyntax.mk_imp (atom, atom)
         val major =
           boolSyntax.mk_exists
             (bound,
              boolSyntax.mk_conj
                (Term.mk_comb (predicate, bound), marker))
         val goal = ([major], target)
         val variants =
           exact_transition_variants clasetLib.empty_cs
             {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
              elim = true} goal
         val selected =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 1}
               (clasetGoal.from_goal goal, 1))

         fun exact result =
           case result of
               [(record, node)] =>
                 (case rendered_goals node of
                      [(assumptions, conclusion)] =>
                        let
                          fun predicate_assumption assumption =
                            case total boolSyntax.dest_conj assumption of
                                SOME (left, right) =>
                                  let
                                    val (head, arguments) = strip_comb left
                                  in
                                    Term.aconv head predicate andalso
                                    length arguments = 1 andalso
                                    Term.aconv right marker
                                  end
                              | NONE => false
                          val shape =
                            length assumptions = 1 andalso
                            List.exists predicate_assumption assumptions
                            andalso Term.aconv conclusion target
                        in
                          shape andalso
                          clasetStep.consumed_of record = SOME 1 andalso
                          valid_open_replay goal (record, node)
                        end
                    | _ => false)
             | _ => false
       in
         List.all exact (selected :: variants)
       end)

val _ =
  test
    ("exact descriptors follow the canonicalized rule premises",
     fn () =>
       let
         val p = Term.mk_var ("canonical_prefix_p", bool_ty)
         val q = Term.mk_var ("canonical_prefix_q", bool_ty)
         val conjunction = boolSyntax.mk_conj (p, q)
         val raw = DISCH conjunction (ASSUME conjunction)
         val goal = ([p, q], conjunction)
         val variants =
           exact_transition_variants clasetLib.empty_cs
             {theorem = raw, elim = false} goal

         fun exact result =
           case result of
               [(record, node)] =>
                 same_goals (rendered_goals node)
                   [([p, q], p), ([p, q], q)] andalso
                 clasetGoal.replay_length node = 1 andalso
                 valid_open_replay goal (record, node)
             | _ => false
       in
         List.all exact variants
       end)

(* A forward rule discharges every immediate premise from an assumption, so
   with more than one premise the assumptions selected for the earlier
   premises decide the conclusion just as much as the major one does. *)
val forward_object = Type.ind
val forward_a = Term.mk_var ("forward_a", forward_object)
val forward_b = Term.mk_var ("forward_b", forward_object)
val forward_c = Term.mk_var ("forward_c", forward_object)
val forward_d = Term.mk_var ("forward_d", forward_object)
val forward_x = Term.mk_var ("forward_x", forward_object)
val forward_y = Term.mk_var ("forward_y", forward_object)
val forward_z = Term.mk_var ("forward_z", forward_object)
val forward_edge =
  Term.mk_var
    ("forward_edge", forward_object --> forward_object --> bool_ty)
val forward_node =
  Term.mk_var ("forward_node", forward_object --> bool_ty)
val forward_goal_target = Term.mk_var ("forward_goal_target", bool_ty)

fun forward_edge_of source destination =
  Term.list_mk_comb (forward_edge, [source, destination])

fun forward_node_of value = Term.mk_comb (forward_node, value)

fun forward_reach_of value =
  boolSyntax.mk_exists
    (forward_z,
     boolSyntax.mk_conj
       (forward_edge_of value forward_z, forward_node_of forward_z))

(* |- !x y. Edge x y ==> Node y ==> ?z. Edge x z /\ Node z *)
val forward_reach_rule =
  GENL [forward_x, forward_y]
    (DISCH (forward_edge_of forward_x forward_y)
      (DISCH (forward_node_of forward_y)
        (EXISTS (forward_reach_of forward_x, forward_y)
          (CONJ
            (ASSUME (forward_edge_of forward_x forward_y))
            (ASSUME (forward_node_of forward_y))))))

(* The conclusion each alternative adds, once it has been checked to keep
   the assumptions it matched and to replay against the original goal. *)
fun forward_alternatives assumptions =
  let
    val goal = (assumptions, forward_goal_target)
    val results =
      drain_exact
        (clasetStep.forward_rule_step
          {theorem = forward_reach_rule, immediate = NONE,
           mode = clasetUnify.Match}
          (clasetGoal.from_goal goal, 1))
    fun added (record, node) =
      case rendered_goals node of
          [(conclusion :: retained, target)] =>
            if clasetStep.consumed_of record = NONE andalso
               same_goals [(retained, target)] [goal] andalso
               valid_open_replay goal (record, node)
            then SOME conclusion
            else NONE
        | _ => NONE
  in
    map added results
  end

val _ =
  test
    ("forward_rule_step derives every conclusion of a two-premise rule",
     fn () =>
       let
         val alternatives =
           forward_alternatives
             [forward_edge_of forward_a forward_c,
              forward_edge_of forward_b forward_c,
              forward_node_of forward_c]
       in
         length alternatives = 2 andalso
         ListPair.allEq
           (fn (actual, expected) =>
             case actual of
                 SOME conclusion => Term.aconv conclusion expected
               | NONE => false)
           (alternatives,
            [forward_reach_of forward_a, forward_reach_of forward_b])
       end)

val _ =
  test
    ("forward_rule_step drops conclusions the goal already states",
     fn () =>
       let
         val shared =
           forward_alternatives
             [forward_edge_of forward_a forward_c,
              forward_edge_of forward_a forward_d,
              forward_node_of forward_c,
              forward_node_of forward_d]
         val stated =
           forward_alternatives
             [forward_reach_of forward_a,
              forward_edge_of forward_a forward_c,
              forward_node_of forward_c]
       in
         (case shared of
              [SOME conclusion] =>
                Term.aconv conclusion (forward_reach_of forward_a)
            | _ => false) andalso
         List.null stated
       end)

val _ =
  test
    ("exact EXISTS elim preserves an eta-reduced major assumption",
     fn () =>
       let
         val bound = Term.mk_var ("eta_major_bound", Type.ind)
         val predicate =
           Term.mk_var
             ("eta_major_predicate", Type.ind --> bool_ty)
         val target = Term.mk_var ("eta_major_target", bool_ty)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val goal = ([major], target)
         val variants =
           exact_transition_variants clasetLib.empty_cs
             {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
              elim = true} goal
         val selected =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 1}
               (clasetGoal.from_goal goal, 1))

         fun exact result =
           case result of
               [(record, node)] =>
                 (case rendered_goals node of
                      [([assumption], conclusion)] =>
                        let
                          val (head, arguments) = strip_comb assumption
                        in
                          Term.aconv head predicate andalso
                          length arguments = 1 andalso
                          Term.aconv conclusion target andalso
                          clasetStep.consumed_of record = SOME 1 andalso
                          valid_open_replay goal (record, node)
                        end
                    | _ => false)
             | _ => false
       in
         List.all exact (selected :: variants)
       end)

val _ =
  test
    ("exact EXISTS elim instantiates an engine-meta major soundly",
     fn () =>
       let
         val target = Term.mk_var ("meta_major_target", bool_ty)
         val (major, store) =
           clasetMeta.new_meta
             {allow = [], ty = bool_ty} clasetMeta.empty
         val node =
           clasetGoal.create
             {goals = [{params = [], asl = [major], w = target}],
              store = store, level = 0}
         val specification =
           {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
            elim = true}
         val ordinary =
           drain_exact
             (clasetStep.blast_rule_step clasetLib.empty_cs
               specification (node, 1))
         val selected =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 1} (node, 1))

         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val final_store = clasetGoal.store next
                   val materialized_major =
                     clasetMeta.norm final_store major
                   val materialized_goal =
                     ([materialized_major], target)
                   val expected = rendered_goals next
                   val (direct, _) =
                     Tactical.VALID
                       (fn _ =>
                         (expected, clasetStep.validation_of record))
                       materialized_goal
                   val ground_store = clasetMeta.ground final_store
                   val grounded_goal =
                     ([clasetMeta.norm ground_store major], target)
                   val grounded_node =
                     clasetGoal.set_store ground_store next
                   val grounded =
                     clasetReplay.ground final_store
                       (clasetGoal.replay next)
                   val (replayed, _) =
                     Tactical.VALID
                       (clasetReplay.REPLAY_TAC grounded) grounded_goal
                 in
                   not (Term.aconv materialized_major major) andalso
                   length expected = 1 andalso
                   same_goals direct expected andalso
                   same_goals replayed (rendered_goals grounded_node)
                 end
             | _ => false
       in
         List.all exact [ordinary, selected]
       end)

val _ =
  test
    ("exact quantified major uses the final engine store before ASSUME",
     fn () =>
       let
         val parameter =
           Term.mk_var ("quantified_major_x", Type.ind)
         val bound =
           Term.mk_var ("quantified_major_x", Type.ind)
         val predicate =
           Term.mk_var
             ("quantified_major_R",
              Type.ind --> Type.ind --> bool_ty)
         val marker =
           Term.mk_var
             ("quantified_major_S", Type.ind --> bool_ty)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (predicate, [meta, bound]))
         val target = Term.mk_comb (marker, parameter)
         val major = boolSyntax.mk_conj (quantified, target)
         val normalized_major = clasetMeta.norm store major
         val source_major =
           Term.subst [{redex = meta, residue = parameter}] major
         val specification =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true, major = SOME 2}
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [major, major],
                   w = target}],
               store = store, level = 0},
            1)
         val plain =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true}
         val all_variants =
           [drain_exact
              (clasetStep.blast_rule_step clasetLib.empty_cs
                plain (input ()))]
         val selected_variants =
           [drain_exact
              (clasetStep.blast_rule_step_at clasetLib.empty_cs
                specification (input ()))]
         val invalid =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.CONJ_ELIM_THM,
                elim = true, major = SOME 3} (input ()))

         fun exact position result =
           case result of
               [(record, next)] =>
                 let
                   val proof =
                     clasetStep.validation_of record [ASSUME target]
                 in
                   clasetStep.consumed_of record = SOME position andalso
                   Term.aconv (concl proof) target andalso
                   aconv_list (hyp proof) [source_major]
                 end
             | _ => false
         fun all_exact results =
           ListPair.allEq
             (fn (result, position) => exact position [result])
             (results, [1, 2])
       in
         Term.aconv
           (clasetMeta.norm (clasetGoal.store (#1 (input ()))) major)
           normalized_major andalso
         Term.aconv (List.nth ([major, major], 1)) major andalso
         List.all all_exact all_variants andalso
         List.all (exact 2) selected_variants andalso null invalid
       end)

val _ =
  test
    ("exact elim replay avoids capture in its selected major",
     fn () =>
       let
         val parameter =
           Term.mk_var ("replay_collision_x", Type.ind)
         val bound =
           Term.mk_var ("replay_collision_x", Type.ind)
         val predicate =
           Term.mk_var
             ("replay_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val marker =
           Term.mk_var
             ("replay_collision_S", Type.ind --> bool_ty)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (predicate, [meta, bound]))
         val target = Term.mk_comb (marker, parameter)
         val engine_major = boolSyntax.mk_conj (quantified, target)
         fun input () =
           clasetGoal.create
             {goals =
                [{params = [parameter], asl = [engine_major],
                  w = target}],
              store = store, level = 0}
         val specification =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true, major = SOME 1}
         val plain =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true}
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain
             specification (fn () => (input (), 1))
         val source_major =
           Term.subst
             [{redex = meta, residue = parameter}] engine_major
         val (source_quantified, source_target) =
           boolSyntax.dest_conj source_major
         val expected_quantified = beta_eta_term source_quantified
         val captured_quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (predicate, [bound, bound]))
         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val script =
                     clasetReplay.append (clasetReplay.empty 1) record
                   val grounded =
                     clasetReplay.ground (clasetGoal.store next) script
                 in
                   case clasetReplay.replay grounded
                          ([source_major], target) of
                       clasetReplay.Replayed
                         (children as
                            [([actual_target, actual_quantified],
                              child_target)],
                          validation) =>
                         let
                           val theorem = validation [ASSUME child_target]
                         in
                           same_goals children
                             [([source_target, expected_quantified],
                               source_target)] andalso
                           Term.aconv actual_target source_target andalso
                           Term.aconv actual_quantified
                             expected_quantified andalso
                           Term.aconv child_target source_target andalso
                           Term.term_eq (concl theorem) source_target andalso
                           HOLset.equal
                             (Thm.hypset theorem,
                              HOLset.fromList Term.compare [source_major])
                         end
                     | _ => false
                 end
             | _ => false
       in
         not (Term.aconv captured_quantified source_quantified) andalso
         List.all exact variants
       end)

val _ =
  test
    ("exact intro replay avoids capture in its conclusion",
     fn () =>
       let
         val parameter =
           Term.mk_var ("intro_collision_x", Type.ind)
         val bound =
           Term.mk_var ("intro_collision_x", Type.ind)
         val relation =
           Term.mk_var
             ("intro_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val marker =
           Term.mk_var
             ("intro_collision_S", Type.ind --> bool_ty)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val quantified =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [meta, bound]))
         val raw_target =
           boolSyntax.mk_conj
             (quantified, Term.mk_comb (marker, parameter))
         val source_target = exact_source_term store raw_target
         val (source_left, source_right) =
           boolSyntax.dest_conj source_target
         val expected_left = normalize_exact_term source_left
         val expected_right = normalize_exact_term source_right
         val plain =
           {theorem = boolTheory.AND_INTRO_THM, elim = false}
         val selected =
           {theorem = boolTheory.AND_INTRO_THM, elim = false,
            major = NONE}
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [], w = raw_target}],
               store = store, level = 0},
            1)
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain selected
             input

         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val script =
                     clasetReplay.append (clasetReplay.empty 1) record
                   val grounded =
                     clasetReplay.ground (clasetGoal.store next) script
                 in
                   case clasetReplay.replay grounded
                          ([], source_target) of
                       clasetReplay.Replayed
                         (children as
                            [([], actual_left), ([], actual_right)],
                          validation) =>
                         let
                           val theorem =
                             validation
                               [ASSUME actual_left,
                                ASSUME actual_right]
                           val children_ok =
                             same_goals children
                               [([], expected_left), ([], expected_right)]
                           val conclusion_ok =
                             Term.term_eq (concl theorem) source_target
                           val hypotheses_ok =
                             HOLset.equal
                               (Thm.hypset theorem,
                                HOLset.fromList Term.compare
                                  [expected_left, expected_right])
                         in
                           children_ok andalso conclusion_ok andalso
                           hypotheses_ok
                         end
                     | _ => false
                 end
             | _ => false
       in
         not (Term.aconv quantified source_left) andalso
         List.all exact variants
       end)

val _ =
  test
    ("exact elim replay repairs a conclusion with an exact major",
     fn () =>
       let
         val parameter =
           Term.mk_var ("elim_target_collision_x", Type.ind)
         val bound =
           Term.mk_var ("elim_target_collision_x", Type.ind)
         val relation =
           Term.mk_var
             ("elim_target_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val left =
           Term.mk_var ("elim_target_collision_p", bool_ty)
         val right =
           Term.mk_var ("elim_target_collision_q", bool_ty)
         val major = boolSyntax.mk_conj (left, right)
         val (meta, store0) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val store =
           valOf (clasetMeta.bind (meta, parameter) store0)
         val raw_target =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [meta, bound]))
         val source_target = exact_source_term store raw_target
         val expected_child_target =
           normalize_exact_term source_target
         val plain =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true}
         val selected =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM,
            elim = true, major = SOME 1}
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [major],
                   w = raw_target}],
               store = store, level = 0},
            1)
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain selected
             input

         fun exact result =
           case result of
               [(record, next)] =>
                 let
                   val script =
                     clasetReplay.append (clasetReplay.empty 1) record
                   val grounded =
                     clasetReplay.ground (clasetGoal.store next) script
                 in
                   case clasetReplay.replay grounded
                          ([major], source_target) of
                       clasetReplay.Replayed
                         (children as
                            [([actual_right, actual_left],
                              actual_target)],
                          validation) =>
                         let
                           val theorem =
                             validation [ASSUME actual_target]
                         in
                           same_goals children
                             [([right, left], expected_child_target)]
                           andalso Term.aconv actual_left left
                           andalso Term.aconv actual_right right
                           andalso
                           Term.term_eq (concl theorem) source_target
                           andalso
                           HOLset.equal
                              (Thm.hypset theorem,
                               HOLset.fromList Term.compare
                                [major, expected_child_target])
                         end
                     | _ => false
                 end
             | _ => false
       in
         not (Term.aconv raw_target source_target) andalso
         List.all exact variants
       end)

val _ =
  test
    ("exact intro replay avoids capture confined to a minor",
     fn () =>
       let
         val parameter =
           Term.mk_var ("minor_collision_x", Type.ind)
         val schema =
           Term.mk_var ("minor_collision_schema", bool_ty)
         val bound =
           Term.mk_var ("minor_collision_x", Type.ind)
         val theorem =
           GEN schema (DISCH schema boolTheory.TRUTH)
         val plain = {theorem = theorem, elim = false}
         val selected =
           {theorem = theorem, elim = false, major = NONE}
         val relation =
           Term.mk_var
             ("minor_collision_R",
              Type.ind --> Type.ind --> bool_ty)
         val (dependency, initial_store) =
           clasetMeta.new_meta
             {allow = [parameter], ty = Type.ind}
             clasetMeta.empty
         val raw_minor =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [dependency, bound]))
         val source_minor =
           Term.subst
             [{redex = dependency, residue = parameter}] raw_minor
         val expected_minor = beta_eta_term source_minor
         val captured_minor =
           boolSyntax.mk_forall
             (bound,
              Term.list_mk_comb (relation, [bound, bound]))
         fun input () =
           (clasetGoal.create
              {goals =
                 [{params = [parameter], asl = [], w = boolSyntax.T}],
               store = initial_store, level = 0},
            1)
         val variants =
           exact_rule_api_variants clasetLib.empty_cs plain selected
             input

         fun exact result =
           case result of
               [(record, next)] =>
                 (case #terms (clasetStep.created_of record) of
                      [created] =>
                        let
                          val store_with_minor =
                            the_store
                              (clasetMeta.bind (created, raw_minor)
                                (clasetGoal.store next))
                          val replay_store =
                            the_store
                              (clasetMeta.bind
                                (dependency, parameter) store_with_minor)
                          val created_minor =
                            #w (the_singleton (clasetGoal.goals next))
                          val script =
                            clasetReplay.append
                              (clasetReplay.empty 1) record
                          val grounded =
                            clasetReplay.ground replay_store script
                        in
                          case clasetReplay.replay grounded
                                 ([], boolSyntax.T) of
                              clasetReplay.Replayed
                                (children as
                                   [([], actual_minor)],
                                 validation) =>
                                let
                                  val result =
                                    validation [ASSUME actual_minor]
                                in
                                  Term.aconv created_minor created andalso
                                  same_goals children
                                    [([], expected_minor)] andalso
                                  Term.aconv actual_minor
                                    expected_minor andalso
                                  Term.term_eq (concl result)
                                    boolSyntax.T andalso
                                  HOLset.equal
                                     (Thm.hypset result,
                                      HOLset.fromList Term.compare
                                       [expected_minor])
                                end
                            | _ => false
                        end
                    | _ => false)
             | _ => false
       in
         not (Term.aconv raw_minor source_minor) andalso
         not (Term.aconv captured_minor source_minor) andalso
         List.all exact variants
       end)

val _ =
  test
    ("dest-generated elim keeps a newly exposed implication intact",
     fn () =>
       let
         val left = Term.mk_var ("bounded_dest_left", bool_ty)
         val right = Term.mk_var ("bounded_dest_right", bool_ty)
         val atom = Term.mk_var ("bounded_dest_atom", bool_ty)
         val target = boolSyntax.mk_imp (atom, atom)
         val conjunction = boolSyntax.mk_conj (left, right)
         val original =
           DISCH conjunction
             (CONJUNCT1 (ASSUME conjunction))
         val specification =
           {kind = clasetRules.Dest, safe = true, prio = NONE}
         val {rl = (generated, _), ...} =
           clasetRules.ext_info specification original
         val cs =
           clasetLib.add_sdests
             [("bounded-dest-generated", original)]
             clasetLib.empty_cs
         val goal = ([conjunction], target)
         val variants =
           exact_transition_variants cs
             {theorem = generated, elim = true} goal

         fun exact result =
           case result of
               [(record, node)] =>
                 same_goals (rendered_goals node)
                   [([left], target)]
                 andalso
                 (case clasetStep.kind_of record of
                      clasetStep.RuleApplication
                        {variant = clasetStep.MakeElim, ...} => true
                    | _ => false)
                 andalso valid_open_replay goal (record, node)
             | _ => false
       in
         List.all exact variants
       end)

val _ =
  test
    ("measured exact rules preserve intro and elim sequence order",
     fn () =>
       let
         val p = Term.mk_var ("measured_exact_p", bool_ty)
         val q = Term.mk_var ("measured_exact_q", bool_ty)
         val r = Term.mk_var ("measured_exact_r", bool_ty)
         val conjunction = boolSyntax.mk_conj (p, q)
         val intro_goal = ([p, q], conjunction)
         val elim_goal = ([r, conjunction, conjunction], p)
         val cs =
           clasetLib.add_selims
             [("measured-exact-and-elim",
               clasetSeedTheory.CONJ_ELIM_THM)]
             clasetLib.empty_cs

         val intro_results =
           drain_exact
             (clasetStep.blast_rule_step cs
               {theorem = boolTheory.AND_INTRO_THM, elim = false}
               (clasetGoal.from_goal intro_goal, 1))
         val elim_specification =
           {theorem = clasetSeedTheory.CONJ_ELIM_THM, elim = true}
         val ordinary_elims =
           drain_exact
             (clasetStep.blast_rule_step cs elim_specification
               (clasetGoal.from_goal elim_goal, 1))
       in
         length intro_results = 1 andalso
         List.all (valid_open_replay intro_goal) intro_results andalso
         length ordinary_elims = 2 andalso
         map (clasetStep.consumed_of o #1) ordinary_elims =
           [SOME 2, SOME 3] andalso
         List.all (valid_open_replay elim_goal) ordinary_elims
       end)

val _ =
  test
    ("exact elimination premises preserve parent eigenparameters",
     fn () =>
       let
         val outer = Term.mk_var ("x", Type.ind)
         val witness = Term.mk_var ("y", Type.ind)
         val label =
           Term.mk_var ("capture_label", Type.ind --> bool_ty)
         val relation =
           Term.mk_var
             ("capture_relation",
              Type.ind --> Type.ind --> bool_ty)
         fun label_app argument = Term.mk_comb (label, argument)
         fun relation_app left right =
           Term.list_mk_comb (relation, [left, right])
         val major =
           boolSyntax.mk_exists
             (witness,
              boolSyntax.mk_conj
                (label_app witness, relation_app outer witness))
         val store =
           valOf (clasetMeta.register_eigen outer clasetMeta.empty)
         val node =
           clasetGoal.create
             {goals =
                [{params = [outer], asl = [major], w = boolSyntax.F}],
              store = store, level = 0}
         val transition =
           seq.cases
             (clasetStep.blast_rule_step clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true} (node, 1))
       in
         case transition of
             NONE => false
           | SOME ((record, next), _) =>
               let
                 val child = the_singleton (clasetGoal.goals next)
                 val fresh = List.nth (#params child, 1)
                 val expected =
                   boolSyntax.mk_conj
                     (label_app fresh, relation_app outer fresh)
               in
                 not (Term.aconv outer fresh) andalso
                 List.exists (fn assumption =>
                   Term.aconv assumption expected) (#asl child) andalso
                 clasetStep.consumed_of record = SOME 1 andalso
                 valid_step ([major], boolSyntax.F) (record, next)
               end
       end)

val _ =
  test
    ("exact two-binder replay preserves fresh order and collisions",
     fn () =>
       let
         val x = Term.mk_var ("static_eigen_x", Type.ind)
         val y = Term.mk_var ("static_eigen_y", bool_ty)
         val sibling_x = Term.variant [x] x
         val p =
           Term.mk_var ("static_eigen_P", Type.ind --> bool_ty)
         val q =
           Term.mk_var ("static_eigen_Q", bool_ty --> bool_ty)
         val premise =
           boolSyntax.list_mk_forall
             ([x, y],
              boolSyntax.mk_imp
                (Term.mk_comb (p, x),
                 boolSyntax.mk_imp (Term.mk_comb (q, y), boolSyntax.T)))
         val theorem = DISCH premise boolTheory.TRUTH
         val node =
           clasetGoal.create
             {goals =
                [{params = [x, sibling_x], asl = [], w = boolSyntax.T}],
              store = clasetMeta.empty, level = 0}
       in
         case seq.cases
           (clasetStep.blast_rule_step_at clasetLib.empty_cs
             {theorem = theorem, elim = false, major = NONE} (node, 1))
         of
             SOME ((record, next), _) =>
               (case clasetGoal.goals next of
                    {params, asl, w} :: _ =>
                      let
                        val fresh_x = List.nth (params, 2)
                        val fresh_y = List.nth (params, 3)
                        val names =
                          [fst (Term.dest_var fresh_x),
                           fst (Term.dest_var fresh_y)]
                      in
                        length params = 4 andalso
                        not (Term.aconv fresh_x x) andalso
                        not (Term.aconv fresh_x sibling_x) andalso
                        type_of fresh_x = Type.ind andalso
                        type_of fresh_y = bool_ty andalso
                        aconv_list asl
                          [Term.mk_comb (q, fresh_y),
                           Term.mk_comb (p, fresh_x)] andalso
                        Term.aconv w boolSyntax.T andalso
                        clasetStep.eigenvariables_of record = names andalso
                        valid_open_replay ([], boolSyntax.T) (record, next)
                      end
                  | _ => false)
           | NONE => false
       end)

val _ =
  test
    ("measured exact-rule observations and outputs are deterministic",
     fn () =>
       let
         val p = Term.mk_var ("measured_deterministic_p", bool_ty)
         val q = Term.mk_var ("measured_deterministic_q", bool_ty)
         val goal = ([p, q], boolSyntax.mk_conj (p, q))
         fun run () =
           map
             (fn (record, node) =>
               (clasetStep.consumed_of record,
                rendered_goals node,
                clasetReplay.to_string (clasetGoal.replay node)))
             (drain_exact
               (clasetStep.blast_rule_step
                 clasetLib.empty_cs
                 {theorem = boolTheory.AND_INTRO_THM, elim = false}
                 (clasetGoal.from_goal goal, 1)))
         val views1 = run ()
         val views2 = run ()
         fun same_view ((consumed1, goals1, replay1),
                        (consumed2, goals2, replay2)) =
           consumed1 = consumed2 andalso
           same_goals goals1 goals2 andalso replay1 = replay2
       in
         length views1 = length views2 andalso
         ListPair.allEq same_view (views1, views2)
       end)

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
    ("assumption replay recovers only through its recorded action",
     fn () =>
       let
         val goal = ([phase1_qa, phase1_pa], phase1_pa)
         val strict =
           clasetReplay.ASSUMPTION_TAC clasetMeta.empty 1
         val recovered =
           clasetReplay.assumption_action 1 clasetMeta.empty
         val strict_fails =
           (ignore (Tactical.VALID strict goal); false)
           handle HOL_ERR _ => true
         val (residues, _) = Tactical.VALID recovered goal
       in
         strict_fails andalso List.null residues
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
    ("wrapper-selected direct alternative keeps its store and action",
     fn () =>
       let
         val (meta, store) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val node =
           clasetGoal.create
             {goals =
                [{params = [], asl = [boolSyntax.T, boolSyntax.F],
                  w = meta},
                 {params = [], asl = [], w = meta}],
              store = store, level = 0}

         fun second base goal =
           seq.delay
             (fn () =>
               case seq.cases (base goal) of
                   NONE => seq.empty
                 | SOME (_, rest) =>
                     case seq.cases rest of
                         NONE => seq.empty
                       | SOME (result, _) => seq.result result)

         val cs =
           clasetLib.add_unsafe_wrapper ("second", second)
             clasetLib.empty_cs
       in
         case seq.cases (clasetStep.step cs (node, 1)) of
             NONE => false
           | SOME ((record, next), _) =>
               (case clasetStep.kind_of record of
                    clasetStep.Assumption 2 => true
                  | _ => false) andalso
               Term.aconv
                 (clasetMeta.norm (clasetGoal.store next) meta)
                 boolSyntax.F andalso
               same_goals (rendered_goals next) [([], boolSyntax.F)]
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
    ("swapped implication and universal builtins are valid safe steps",
     fn () =>
       let
         val x = Term.mk_var ("swapped_builtin_x", Type.ind)
         val predicate =
           Term.mk_var
             ("swapped_builtin_predicate", Type.ind --> Type.bool)
         val universal =
           boolSyntax.mk_forall (x, Term.mk_comb (predicate, x))
         val inputs =
           [([boolSyntax.mk_neg
                (boolSyntax.mk_imp (goal_p, goal_q))], goal_r),
            ([boolSyntax.mk_neg universal], goal_r)]
         val _ =
           List.app
             (fn input =>
               ignore
                 (Tactical.VALID
                   (classicalLib.SAFE_STEP_TAC []) input))
             inputs
         val beta_p = Term.mk_var ("swapped_beta_p", Type.bool)
         val abstraction =
           Term.mk_abs
             (beta_p, boolSyntax.mk_imp (beta_p, goal_q))
         val beta_implication = Term.mk_comb (abstraction, goal_p)
         val beta_goal =
           ([], boolSyntax.mk_imp
             (boolSyntax.mk_neg beta_implication,
              boolSyntax.mk_imp (goal_q, goal_p)))
         val (residues, _) =
           Tactical.VALID (classicalLib.FAST_TAC []) beta_goal
       in
         List.null residues
       end
       handle error as HOL_ERR _ =>
         (Feedback.HOL_MESG (Feedback.exn_to_string error); false))

(* -------------------------------------------------------------------------
 * TASK_16: Pelletier fast-parity corpus (BEGIN reusable corpus).
 *
 * These are direct HOL4 translations of Pelletier 1--17 and the
 * easy-quantifier problems for which Paulson's blast report Table 1 records
 * successful Isabelle Fast_tac runs: 24, 26, and 28.  Pelletier 18--23, 25,
 * 27, and 29--33 are retained for the complete TASK_23 blast corpus; Table 1
 * does not report Fast_tac results for them.  Problem 34 is explicitly
 * retained there as expected-unsolved by Fast_tac (Table 1 says "failed").
 * ------------------------------------------------------------------------- *)

val pelletier_fast_corpus : (int * term) list =
  [(1, “(P ==> Q) <=> (~Q ==> ~P)”),
   (2, “~~P <=> P”),
   (3, “~(P ==> Q) ==> (Q ==> P)”),
   (4, “(~P ==> Q) <=> (~Q ==> P)”),
   (5, “((P \/ Q) ==> (P \/ R)) ==> (P \/ (Q ==> R))”),
   (6, “P \/ ~P”),
   (7, “P \/ ~~~P”),
   (8, “((P ==> Q) ==> P) ==> P”),
   (9, “((P \/ Q) /\ (~P \/ Q) /\ (P \/ ~Q)) ==>
         ~(~P \/ ~Q)”),
   (10, “(Q ==> R) /\ (R ==> P /\ Q) /\ (P ==> Q \/ R) ==>
          (P <=> Q)”),
   (11, “P <=> P”),
   (12, “((P <=> Q) <=> R) <=> (P <=> (Q <=> R))”),
   (13, “(P \/ (Q /\ R)) <=> ((P \/ Q) /\ (P \/ R))”),
   (14, “(P <=> Q) <=> ((Q \/ ~P) /\ (~Q \/ P))”),
   (15, “(P ==> Q) <=> (~P \/ Q)”),
   (16, “(P ==> Q) \/ (Q ==> P)”),
   (17, “((P /\ (Q ==> R)) ==> ss) <=>
          ((~P \/ Q \/ ss) /\ (~P \/ ~R \/ ss))”),
   (24, “~(?x:'a. ss x /\ Q x) /\
          (!x. P x ==> Q x \/ R x) /\
          (~(?x. P x) ==> ?x. Q x) /\
          (!x. Q x \/ R x ==> ss x) ==>
          ?x. P x /\ R x”),
   (26, “((?x:'a. p x) <=> (?x. q x)) /\
          (!x y. p x /\ q y ==> (r x <=> s y)) ==>
          ((!x. p x ==> r x) <=> (!x. q x ==> s x))”),
   (28, “(!x:'a. P x ==> (!y. Q y)) /\
          ((!x. Q x \/ R x) ==> ?x. Q x /\ ss x) /\
          ((?x. ss x) ==> !x. L x ==> M x) ==>
          (!x. P x /\ L x ==> M x)”)]

(* TASK_16: Pelletier fast-parity corpus (END reusable corpus). *)

val pelletier_fast_budget = Time.fromSeconds 30
val pelletier_fast_solved = ref 0

fun run_pelletier_fast (number, proposition) =
  let
    val name = "FAST_TAC Pelletier " ^ Int.toString number
    val _ = tprint name
    val start = Time.now ()
    val timed_out = ref false
    val result =
      SOME
        (Timeout.apply pelletier_fast_budget
          (fn () =>
            Tactical.VALID
              (classicalLib.FAST_TAC []) ([], proposition)) ())
      handle Timeout.TIMEOUT _ => (timed_out := true; NONE)
           | HOL_ERR _ => NONE
    val elapsed = Time.- (Time.now (), start)
    val solved =
      case result of
          SOME (residues, _) => List.null residues
        | NONE => false
    val within_budget = Time.< (elapsed, pelletier_fast_budget)
  in
    if solved andalso within_budget then
      (pelletier_fast_solved := !pelletier_fast_solved + 1; OK ())
    else if !timed_out orelse not within_budget then
      die (name ^ " exceeded its 30 second budget")
    else
      die (name ^ " did not solve the goal")
  end

val _ = List.app run_pelletier_fast pelletier_fast_corpus

val _ =
  test
    ("FAST_TAC Pelletier solved-goal count",
     fn () =>
       !pelletier_fast_solved = length pelletier_fast_corpus andalso
       !pelletier_fast_solved = 20)

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
             (classicalLib.CS_DEEPEN_TAC (clasetLib.the_claset ())
               {start = 6})
       in
         tactic_solves tactic goal andalso
         tactic_solves (classicalLib.DEEPEN_TAC []) goal
       end)

val _ =
  test
    ("DEEPEN saturates safe siblings before bounded search",
     fn () =>
       let
         val x = Term.mk_var ("deepen_safe_x", Type.ind)
         val a = Term.mk_var ("deepen_safe_a", Type.ind)
         val b = Term.mk_var ("deepen_safe_b", Type.ind)
         val left =
           boolSyntax.mk_exists (x, boolSyntax.mk_eq (x, a))
         val right =
           boolSyntax.mk_exists (x, boolSyntax.mk_eq (x, b))
         val goal = ([], boolSyntax.mk_conj (left, right))
         val tactic =
           NTactical.DETERM
             (classicalLib.CS_DEEPEN_TAC (clasetLib.the_claset ())
               {start = 1})
       in
         tactic_solves tactic goal
       end)

fun depth_duplication_fixture () =
  let
    val bound = Term.mk_var ("depth_duplication_bound", Type.ind)
    val left = Term.mk_var ("depth_duplication_left", Type.ind)
    val right = Term.mk_var ("depth_duplication_right", Type.ind)
    val predicate =
      Term.mk_var
        ("depth_duplication_predicate", Type.ind --> Type.bool)
    val pbound = mk_comb (predicate, bound)
    val pleft = mk_comb (predicate, left)
    val pright = mk_comb (predicate, right)
    val target = boolSyntax.mk_eq (pleft, pright)
    val equality =
      TRANS (Drule.EQT_INTRO (ASSUME pleft))
        (SYM (Drule.EQT_INTRO (ASSUME pright)))
    val bridge = DISCH pleft (DISCH pright equality)
    val cs =
      clasetLib.add_elims
        [("depth-duplication-forall",
          clasetSeedTheory.FORALL_ELIM_THM),
         ("depth-duplication-bridge", bridge)]
        clasetLib.empty_cs
  in
    (cs, ([boolSyntax.mk_forall (bound, pbound)], target))
  end

val _ =
  test
    ("CS_DEPTH_SOLVE_TAC distinguishes duplication at one bound",
     fn () =>
       let
         val (cs, goal) = depth_duplication_fixture ()
         fun depth dup =
           NTactical.DETERM
             (classicalLib.CS_DEPTH_SOLVE_TAC {dup = dup} 3 cs)
       in
         tactic_solves (depth true) goal andalso
         tactic_fails (depth false) goal
       end)

val _ =
  test
    ("CS_DEEPEN_TAC retains duplicating bounded-search behavior",
     fn () =>
       let
         val (cs, goal) = depth_duplication_fixture ()
         val tactic =
           NTactical.DETERM
             (classicalLib.CS_DEEPEN_TAC cs {start = 3})
       in
         tactic_solves tactic goal
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
         val tactic = NTactical.DETERM (classicalLib.CS_FAST_TAC cs)
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
         val fast = NTactical.DETERM (classicalLib.CS_FAST_TAC cs)
         val slow = NTactical.DETERM (classicalLib.CS_SLOW_TAC cs)
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
         val tactic = NTactical.DETERM (classicalLib.CS_BEST_TAC cs)
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

val _ =
  test
    ("blast hyp-subst skips unsuitable equations and stably reorders",
     fn () =>
       let
         val x = Term.mk_var ("x", Type.bool)
         val y = Term.mk_var ("y", Type.bool)
         val a = Term.mk_var ("a", Type.bool)
         val f = Term.mk_var ("f", Type.bool --> Type.bool)
         val p = Term.mk_var ("P", Type.bool --> Type.bool)
         val q = Term.mk_var ("Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val unsuitable = boolSyntax.mk_eq (app f x, x)
         val selected = boolSyntax.mk_eq (x, y)
         val unchanged = app p a
         val px = app p x
         val qx = app q x
         val py = app p y
         val qy = app q y
         val original =
           ([unsuitable, selected, unchanged, px, qx], py)
         val node = clasetGoal.from_goal original
         val (_, substituted) =
           case seq.cases
             (clasetStep.blast_hyp_subst_step (node, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "blast hyp-subst did not apply"
         val expected =
           [boolSyntax.mk_eq (app f y, y), py, qy, unchanged]
         val order_ok =
           case clasetGoal.goals substituted of
               [{asl, ...}] =>
                 ListPair.allEq
                   (fn (left, right) => Term.aconv left right)
                   (asl, expected)
             | _ => false
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_assumption_step (substituted, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "substituted goal did not close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
         val (residuals, validation) =
           Tactical.VALID (clasetReplay.REPLAY_TAC grounded) original
       in
         order_ok andalso null residuals andalso
         (ignore (validation []); true)
       end)

val _ =
  test
    ("recorded hyp-subst mask survives a late metavariable binding",
     fn () =>
       let
         val x = Term.mk_var ("late_subst_x", Type.bool)
         val y = Term.mk_var ("late_subst_y", Type.bool)
         val p =
           Term.mk_var ("late_subst_P", Type.bool --> Type.bool)
         val q =
           Term.mk_var ("late_subst_Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val (meta, store0) =
           clasetMeta.new_meta {allow = [], ty = Type.bool}
             clasetMeta.empty
         val raw_goal =
           ([boolSyntax.mk_eq (x, y), app p meta, app q x, app p y],
            app q y)
         val root =
           clasetGoal.create
             {goals =
                [{params = [], asl = #1 raw_goal, w = #2 raw_goal}],
              store = store0, level = 0}
         val (_, substituted) =
           case seq.cases
             (clasetStep.blast_hyp_subst_step_at
               {equality = 1, changed = [false, true, false]}
               (root, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "recorded late-binding substitution"
         val store1 =
           the_store
             (clasetMeta.bind (meta, x) (clasetGoal.store substituted))
         val rebound = clasetGoal.set_store store1 substituted
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_assumption_step_at 1 (rebound, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "late-binding exact close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
         val original =
           (map (clasetMeta.norm store1) (#1 raw_goal),
            clasetMeta.norm store1 (#2 raw_goal))
       in
         case total
           (Tactical.VALID (clasetReplay.REPLAY_TAC grounded)) original of
             SOME ([], validation) =>
               (ignore (validation []); true)
           | _ => false
       end)

val _ =
  test
    ("blast hyp-subst does not beta-normalize equality orientation",
     fn () =>
       let
         val x = Term.mk_var ("beta_x", Type.bool)
         val y = Term.mk_var ("beta_y", Type.bool)
         val a = Term.mk_var ("beta_a", Type.bool)
         val z = Term.mk_var ("beta_z", Type.bool)
         val p = Term.mk_var ("beta_P", Type.bool --> Type.bool)
         val q = Term.mk_var ("beta_Q", Type.bool --> Type.bool)
         fun app operator operand = Term.mk_comb (operator, operand)
         val redex = app (Term.mk_abs (z, x)) a
         val equality = boolSyntax.mk_eq (redex, y)
         val px = app p x
         val qy = app q y
         val goal = ([equality, px, qy], qy)
         val (children, validation) =
           clasetReplay.BLAST_HYP_SUBST_TAC goal
         val expected = ([app q redex, px], app q redex)
         val child_ok =
           case children of
               [child] => same_goal (child, expected)
             | _ => false
         val theorem = ASSUME (app q redex)
         val replayed = validation [theorem]
       in
         child_ok andalso Term.aconv (concl replayed) qy
       end)

val _ =
  test
    ("recorded beta-redex hyp-subst and close replay exactly",
     fn () =>
       let
         val alpha = Type.mk_vartype "'beta_replay"
         val x = Term.mk_var ("beta_replay_x", alpha)
         val y = Term.mk_var ("beta_replay_y", alpha)
         val a = Term.mk_var ("beta_replay_a", alpha)
         val z = Term.mk_var ("beta_replay_z", alpha)
         val p = Term.mk_var ("beta_replay_P", alpha --> Type.bool)
         val redex = Term.mk_comb (Term.mk_abs (z, x), a)
         val goal =
           ([boolSyntax.mk_eq (redex, y), Term.mk_comb (p, y)],
            Term.mk_comb (p, redex))
         val root = clasetGoal.from_goal goal
         val (_, substituted) =
           case seq.cases
             (clasetStep.blast_hyp_subst_step (root, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "beta replay substitution"
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_assumption_step (substituted, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "beta replay close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
       in
         case total
           (Tactical.VALID (clasetReplay.REPLAY_TAC grounded)) goal of
             SOME ([], validation) =>
               let
                 val theorem = validation []
               in
                 Term.term_eq (concl theorem) (#2 goal) andalso
                 HOLset.equal
                   (Thm.hypset theorem,
                    HOLset.fromList Term.compare (#1 goal))
               end
           | _ => false
       end)

val _ =
  test
    ("recorded beta/eta target contradiction replay exactly",
     fn () =>
       let
         val alpha = Type.mk_vartype "'contradiction_replay"
         val x = Term.mk_var ("contradiction_replay_x", alpha)
         val a = Term.mk_var ("contradiction_replay_a", alpha)
         val z = Term.mk_var ("contradiction_replay_z", alpha)
         val f =
           Term.mk_var
             ("contradiction_replay_f", alpha --> Type.bool)
         val p = Term.mk_var ("contradiction_replay_p", Type.bool)
         val eta = Term.mk_abs (x, Term.mk_comb (f, x))
         val q = boolSyntax.mk_eq (eta, f)
         val target = Term.mk_comb (Term.mk_abs (z, q), a)
         val goal = ([boolSyntax.mk_neg p, p], target)
         val root = clasetGoal.from_goal goal
         val (_, closed) =
           case seq.cases
             (clasetStep.blast_contradiction_step (root, 1)) of
               SOME (result, _) => result
             | NONE => raise Fail "beta/eta contradiction close"
         val grounded =
           clasetReplay.ground (clasetGoal.store closed)
             (clasetGoal.replay closed)
       in
         case total
           (Tactical.VALID (clasetReplay.REPLAY_TAC grounded)) goal of
             SOME ([], validation) =>
               let
                 val theorem = validation []
               in
                 Term.term_eq (concl theorem) (#2 goal) andalso
                 HOLset.equal
                   (Thm.hypset theorem,
                    HOLset.fromList Term.compare (#1 goal))
               end
           | _ => false
       end)

(* Position-directed replay selectors are intentionally tested at this
   owning layer: duplicate syntax must not erase occurrence identity. *)

val _ =
  test
    ("exact intro sequences defer goal lookup until their first pull",
     fn () =>
       let
         val p = Term.mk_var ("exact_lazy_p", Type.bool)
         val theorem = Thm.ASSUME p
         val input = (clasetGoal.from_goal ([], p), 2)
         val specification = {theorem = theorem, elim = false}
         val ordinary =
           clasetStep.blast_rule_step clasetLib.empty_cs
             specification input
         val selected =
           clasetStep.blast_rule_step_at clasetLib.empty_cs
             {theorem = theorem, elim = false, major = NONE} input
       in
         seq.null ordinary andalso seq.null selected
       end)

val _ =
  test
    ("exact closure selectors preserve duplicate occurrence identity",
     fn () =>
       let
         val p = Term.mk_var ("exact_selector_p", Type.bool)
         val q = Term.mk_var ("exact_selector_q", Type.bool)
         val assumption_goal = ([p, p], p)
         val contradiction_goal =
           ([boolSyntax.mk_neg p, p, p], q)
         val assumption =
           drain_exact
             (clasetStep.blast_assumption_step_at 2
               (clasetGoal.from_goal assumption_goal, 1))
         val contradiction =
           drain_exact
             (clasetStep.blast_contradiction_step_at
               {negative = 1, positive = 3}
               (clasetGoal.from_goal contradiction_goal, 1))
         val wrong_assumption =
           seq.null
             (clasetStep.blast_assumption_step_at 1
               (clasetGoal.from_goal ([q, p], p), 1))
         val wrong_polarity =
           seq.null
             (clasetStep.blast_contradiction_step_at
               {negative = 2, positive = 1}
               (clasetGoal.from_goal contradiction_goal, 1))
       in
         case (assumption, contradiction) of
             ([(assumption_record, assumption_node)],
              [(contradiction_record, contradiction_node)]) =>
               clasetStep.consumed_of assumption_record = SOME 2 andalso
               (case clasetStep.kind_of assumption_record of
                    clasetStep.Assumption 2 => true
                  | _ => false) andalso
               (case clasetStep.kind_of contradiction_record of
                    clasetStep.Contradiction (1, 3) => true
                  | _ => false) andalso
               valid_grounded_replay assumption_goal assumption_node andalso
               valid_grounded_replay contradiction_goal
                 contradiction_node andalso
               wrong_assumption andalso wrong_polarity
           | _ => false
       end)

val _ =
  test
    ("strict assumption replay rejects selector drift while legacy recovers",
     fn () =>
       let
         val p = Term.mk_var ("strict_replay_p", Type.bool)
         val q = Term.mk_var ("strict_replay_q", Type.bool)
         val recorded_goal = ([q, p], p)
         val drifted_goal = ([p, q], p)
         val root = clasetGoal.from_goal recorded_goal
         val legacy =
           drain_exact (clasetStep.blast_assumption_step (root, 1))
         val strict =
           drain_exact
             (clasetStep.blast_assumption_step_at 2 (root, 1))
         fun grounded node =
           clasetReplay.ground (clasetGoal.store node)
             (clasetGoal.replay node)
         val legacy_result =
           case legacy of
               [(_, node)] =>
                 total
                   (Tactical.VALID
                     (clasetReplay.REPLAY_TAC (grounded node)))
                   drifted_goal
             | _ => NONE
         val strict_result =
           case strict of
               [(_, node)] => clasetReplay.replay (grounded node) drifted_goal
             | _ => raise Fail "missing strict assumption transition"
       in
         (case legacy_result of
              SOME ([], validation) =>
                (ignore (validation []); true)
            | _ => false) andalso
         (case strict_result of
              clasetReplay.ReplayFailed _ => true
            | _ => false)
       end)

val _ =
  test
    ("exact rule selector validates shape range and nonmatching major",
     fn () =>
       let
         val p = Term.mk_var ("exact_shape_p", Type.bool)
         val q = Term.mk_var ("exact_shape_q", Type.bool)
         val bound = Term.mk_var ("exact_shape_x", Type.ind)
         val predicate =
           Term.mk_var ("exact_shape_P", Type.ind --> Type.bool)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val theorem = clasetSeedTheory.EXISTS_ELIM_THM
         val node = clasetGoal.from_goal ([q, major], p)
         fun empty specification =
           seq.null
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               specification (node, 1))
       in
         empty {theorem = theorem, elim = false, major = SOME 1}
         andalso empty {theorem = theorem, elim = true, major = NONE}
         andalso
         empty {theorem = theorem, elim = true, major = SOME 0}
         andalso
         empty {theorem = theorem, elim = true, major = SOME 3}
         andalso
         empty {theorem = theorem, elim = true, major = SOME 1}
       end)

val _ =
  test
    ("selected exact rule has ordinary and timed-family parity",
     fn () =>
       let
         val p = Term.mk_var ("exact_parity_p", Type.bool)
         val bound = Term.mk_var ("exact_parity_x", Type.ind)
         val predicate =
           Term.mk_var ("exact_parity_P", Type.ind --> Type.bool)
         val major =
           boolSyntax.mk_exists
             (bound, Term.mk_comb (predicate, bound))
         val goal = ([major, major], p)
         val result =
           drain_exact
             (clasetStep.blast_rule_step_at clasetLib.empty_cs
               {theorem = clasetSeedTheory.EXISTS_ELIM_THM,
                elim = true, major = SOME 2}
               (clasetGoal.from_goal goal, 1))
       in
         case result of
             [(record, node)] =>
               clasetStep.consumed_of record = SOME 2 andalso
               valid_open_replay goal (record, node)
           | _ => false
       end)


val _ =
  test
    ("selected blast hyp-subst uses only the recorded equality",
     fn () =>
       let
         val x = Term.mk_var ("exact_subst_x", Type.bool)
         val y = Term.mk_var ("exact_subst_y", Type.bool)
         val z = Term.mk_var ("exact_subst_z", Type.bool)
         val p = Term.mk_var ("exact_subst_P", Type.bool --> Type.bool)
         fun app argument = Term.mk_comb (p, argument)
         val first = boolSyntax.mk_eq (x, y)
         val selected = boolSyntax.mk_eq (y, z)
         val transformed_first = boolSyntax.mk_eq (x, z)
         val unchanged = app z
         val goal = ([first, selected, unchanged, app y], app y)
         val node = clasetGoal.from_goal goal
         val results =
           drain_exact
             (clasetStep.blast_hyp_subst_step_at
               {equality = 2, changed = [true, false, true]}
               (node, 1))
         val wrong =
           seq.null
             (clasetStep.blast_hyp_subst_step_at
               {equality = 5, changed = []} (node, 1))
       in
         case results of
             [(record, next)] =>
               (case rendered_goals next of
                    [(assumptions, conclusion)] =>
                      List.exists (Term.aconv transformed_first)
                        assumptions andalso
                      List.exists (Term.aconv unchanged) assumptions andalso
                      not (List.exists (Term.aconv selected) assumptions)
                      andalso Term.aconv conclusion (app z) andalso
                      valid_open_replay goal (record, next) andalso wrong
                  | _ => false)
           | _ => false
       end)

val _ =
  test
    ("legacy closure and substitution enumeration keeps occurrence order",
     fn () =>
       let
         val p = Term.mk_var ("prepared_legacy_p", Type.bool)
         val q = Term.mk_var ("prepared_legacy_q", Type.bool)
         val assumption_goal = ([p, q, p], p)
         val assumption_node = clasetGoal.from_goal assumption_goal
         val assumptions =
           drain_exact
             (clasetStep.blast_assumption_step (assumption_node, 1))
         val selected_assumptions =
           List.concat
             (map
               (fn position =>
                 drain_exact
                   (clasetStep.blast_assumption_step_at position
                     (assumption_node, 1)))
               [1, 2, 3])
         val contradiction_goal = ([boolSyntax.mk_neg p, p, p], q)
         val contradictions =
           drain_exact
             (clasetStep.blast_contradiction_step
               (clasetGoal.from_goal contradiction_goal, 1))
         val x = Term.mk_var ("prepared_legacy_x", Type.bool)
         val y = Term.mk_var ("prepared_legacy_y", Type.bool)
         val z = Term.mk_var ("prepared_legacy_z", Type.bool)
         val predicate =
           Term.mk_var
             ("prepared_legacy_P", Type.bool --> Type.bool)
         val substitution_goal =
           ([boolSyntax.mk_eq (x, y), boolSyntax.mk_eq (y, z),
             Term.mk_comb (predicate, x)],
            Term.mk_comb (predicate, y))
         val substitution_node = clasetGoal.from_goal substitution_goal
         val substitutions =
           drain_exact
             (clasetStep.blast_hyp_subst_step
               (substitution_node, 1))
         val selected_substitutions =
           List.concat
             (map
               (fn (equality, changed) =>
                 drain_exact
                   (clasetStep.blast_hyp_subst_step_at
                     {equality = equality, changed = changed}
                     (substitution_node, 1)))
               [(1, [false, true]), (2, [true, false]), (3, [])])
         fun same_nodes ([], []) = true
           | same_nodes ((_, left) :: lefts, (_, right) :: rights) =
               clasetGoal.equal (left, right) andalso
               same_nodes (lefts, rights)
           | same_nodes _ = false
       in
         map (clasetStep.consumed_of o fst) assumptions =
           [SOME 1, SOME 3] andalso
         same_nodes (assumptions, selected_assumptions) andalso
         (case contradictions of
              [(record, _)] =>
                (case clasetStep.kind_of record of
                     clasetStep.Contradiction (1, 2) => true
                   | _ => false)
            | _ => false) andalso
         same_nodes (substitutions, selected_substitutions)
       end)
