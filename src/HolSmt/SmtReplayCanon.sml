(* Copyright (c) 2026 The HOL4 contributors. *)

(* Shared, proved normal forms used at checked-replay boundaries. *)

structure SmtReplayCanon =
struct

  open SmtReplayGraph SmtReplayCanonGraph
  structure G = SmtReplayGraph
  structure P = SmtReplayProof

  (* The SMT arithmetic sorts: Int and Real. *)
  fun is_arith_type ty =
    Type.compare (ty, intSyntax.int_ty) = EQUAL orelse
    Type.compare (ty, realSyntax.real_ty) = EQUAL

  val smt_ediv_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_ediv_total"}
  val smt_emod_total_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_emod_total"}
  val smt_rdiv_tm = Term.prim_mk_const
    {Thy = "HolSmt", Name = "smt_rdiv"}

  fun smt_rdiv_nonzero_conv tm =
    let
      val (head, arguments) = boolSyntax.strip_comb tm
      val _ = Term.same_const head smt_rdiv_tm orelse raise Conv.UNCHANGED
      val (numerator, denominator) =
        case arguments of
          [numerator, denominator] => (numerator, denominator)
        | _ => raise Conv.UNCHANGED
      val nonzero = simpLib.SIMP_PROVE (bossLib.srw_ss ()) []
        (boolSyntax.mk_neg
          (boolSyntax.mk_eq (denominator, realSyntax.zero_tm)))
    in
      Thm.MP (Drule.SPECL [numerator, denominator]
        HolSmtTheory.smt_rdiv_eq_div) nonzero
    end
    handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  val cpc_alias_rewrites = [
    Thm.CONJUNCT1 boolTheory.NOT_CLAUSES,
    Thm.CONJUNCT2 boolTheory.NOT_CLAUSES,
    boolTheory.COND_CLAUSES,
    integerTheory.INT_GT,
    integerTheory.INT_GE,
    integerTheory.int_sub,
    realTheory.real_gt,
    realTheory.real_ge,
    intrealTheory.real_of_int_add,
    intrealTheory.real_of_int_sub,
    intrealTheory.real_of_int_mul,
    intrealTheory.real_of_int_neg,
    intrealTheory.real_of_int_num,
    (* The SMT-LIB encoding spells to_int ceiling through negated to_int
       floor.  Canonicalize HOL's surface ceiling to that emitted form. *)
    HolSmtTheory.int_ceiling_floor,
    HolSmtTheory.smt_rdiv_lneg,
    HolSmtTheory.smt_rdiv_rneg
  ]

  open SmtReplayTermBridge

  val ERR = Feedback.mk_HOL_ERR "SmtReplayCanon"

  fun is_ground_total tm =
    let val (head,args) = boolSyntax.strip_comb tm in
      (Term.same_const head smt_ediv_total_tm orelse
       Term.same_const head smt_emod_total_tm) andalso
      List.length args = 2 andalso
      (admit_native "canon-ground-total" tm; null (Term.free_vars tm))
    end

  fun ground_total_conv tm =
    if is_ground_total tm then bossLib.EVAL tm else raise Conv.UNCHANGED

  (* Compose checked conversions without losing the caller's occurrence
     at the outer application rebuilt by ordinary conversion combinators. *)
  fun compose conversions root = exact_left root
    (Conv.QCONV (List.foldr Conv.THENC Conv.ALL_CONV conversions) root)

  (* Canonical orientation only permutes children.  Visit each physically
     shared input node once, normalize its children first, and cache the
     checked equality for this invocation.  Tree-depth conversions revisit
     exponentially many paths through solver-generated shared circuits. *)
  fun dag_conversion revisit orient root =
    let
      val bucket_count = 4093
      val cache = Array.array
        (bucket_count, [] : (Term.term * Thm.thm) list)
      val active = ref ([] : Term.term list)
      val order = new_term_order ()
      fun normalize term =
        let
          val index = SmtResource.pointer_bucket bucket_count term
          val bucket = Array.sub (cache, index)
        in
          case List.find
              (fn (saved, _) => Portable.pointer_eq (saved, term)) bucket of
            SOME (_, theorem) => theorem
          | NONE =>
              let
                val _ = not (List.exists
                    (fn prior => Portable.pointer_eq (prior, term))
                    (!active)) orelse
                  raise ERR "dag_conversion" "cyclic rewrite expansion"
                val _ = active := term :: !active
                val _ = admit_type (Term.type_of term)
                val children =
                  if Term.is_comb term then
                    let
                      val (operator, operand) = Term.dest_comb term
                      val operator_thm = normalize operator
                      val operand_thm = normalize operand
                    in
                      if Portable.pointer_eq (operator,
                           boolSyntax.rhs (Thm.concl operator_thm)) andalso
                         Portable.pointer_eq (operand,
                           boolSyntax.rhs (Thm.concl operand_thm)) then
                        checked_refl term
                      else anchor_left term
                        (Thm.MK_COMB (operator_thm, operand_thm))
                    end
                  else if Term.is_abs term then
                    let
                      val _ = admit_native "canon-binder-opening" term
                      val (variable, body) = Term.dest_abs term
                      val body_thm = normalize body
                    in
                      if Portable.pointer_eq
                           (body, boolSyntax.rhs (Thm.concl body_thm)) then
                        checked_refl term
                      else
                        let
                          val _ = List.app
                            (admit_native "canon-binder-hypothesis")
                            (Thm.hyp body_thm)
                          val _ = admit_body_result
                            (boolSyntax.rhs (Thm.concl body_thm))
                        in anchor_left term (Thm.ABS variable body_thm) end
                    end
                  else checked_refl term
                val current = boolSyntax.rhs (Thm.concl children)
                val orientation = exact_left current
                  (Conv.QCONV (Conv.TRY_CONV orient) current)
                val right = boolSyntax.rhs (Thm.concl orientation)
                val orientation =
                  if revisit andalso order (current,right) <> EQUAL then
                    Thm.TRANS orientation (normalize right)
                  else orientation
                val theorem =
                  if Portable.pointer_eq (term, current) then orientation
                  else if Portable.pointer_eq (current,
                      boolSyntax.rhs (Thm.concl orientation)) then children
                  else Thm.TRANS children orientation
                val _ = Array.update (cache, index,
                  (term, theorem) :: Array.sub (cache, index))
                val _ = active := tl (!active)
              in theorem end
        end
    in normalize root end

  val dag_orientation_conv = dag_conversion false
  val dag_rewrite_conv = dag_conversion true

  exception SHARE_LIMIT

  (* Do not first call the ordinary whole-source importer: an intern hit
     there can align two application trees with a whole-term ALPHA. Retain
     physical occurrences and prove each constructor/leaf bridge locally.
     Only opaque or admitted bounded binder islands use the import adapter.
     Required conversion has no new application-DAG admission allowance. *)
  fun import_nodewise graph scope allowance binder root =
    let
      val types = new_type_order ()
      val count = 4093
      val memo = Array.array (count,[] : (Term.term * G.source) list)
      val observed = ref 0
      fun visit term =
        let val bucket = SmtResource.pointer_bucket count term in
          case List.find (fn (old,_) => Portable.pointer_eq (old,term))
              (Array.sub (memo,bucket)) of
            SOME (_,source) => source
          | NONE =>
              let
                val _ = case allowance of NONE => ()
                  | SOME maximum =>
                      if !observed < maximum then () else raise SHARE_LIMIT
                val _ = case allowance of NONE => ()
                  | SOME _ => observed := !observed + 1
                val source =
                  if Term.is_comb term then
                    let
                      val (f,x) = Term.dest_comb term
                      val left = visit f and right = visit x
                      val node = G.application graph scope
                        (#node left,#node right)
                      val canonical = G.representative graph node
                      val bridge = application_bridge term canonical
                        (#bridge left) (#bridge right)
                    in {node = node,original = term,bridge = bridge} end
                  else if Term.is_abs term then binder term
                  else
                    let
                      val node = if Term.is_var term then
                          G.resolve_variable graph scope term
                        else G.constant graph scope term
                      val target = G.representative graph node
                      val theorem = if Portable.pointer_eq (term,target)
                          then checked_refl term
                        else leaf_equality types term target
                    in {node = node,original = term,bridge = theorem} end
                val _ = Array.update (memo,bucket,
                  (term,source) :: Array.sub (memo,bucket))
              in source end
        end
    in visit root end

  (* Binder interning is optional here. Keep the opaque fallback when its
     native island cannot be admitted, without opening an unadmitted body.
     Admitted small alpha-equivalent binders must still share an ID, so a
     reflexive schema sees a single hole for their two occurrences. *)
  fun import_binder_island graph scope maximum operation term =
    (admit_native operation term;
     G.admit_binder graph scope maximum term)
    handle Feedback.HOL_ERR detail =>
      if SmtResource.is_resource_gate detail andalso
          (String.isSubstring operation (Feedback.message_of detail) orelse
           String.isSubstring "canon-type-work"
             (Feedback.message_of detail)) then
        (admit_type (Term.type_of term);G.import graph scope 1 term)
      else raise Feedback.HOL_ERR detail

  (* Optional sharing retains the old DAG allowance and opaque-binder
     fallback. Exhaustion is still identity, never a new replay refusal. *)
  fun share_conv root =
    let
      val graph = G.new ()
      val scope = G.root_scope graph
      val maximum = SmtResource.max_bv_replay_term_nodes
      (* Preserve the old metadata-only refusal before any source proof. *)
      val _ = G.plan_import graph scope maximum root
      val binder = import_binder_island graph scope maximum
        "canon-binder-sharing"
    in #bridge (import_nodewise graph scope (SOME maximum) binder root) end
    handle SHARE_LIMIT => checked_refl root
      | Feedback.HOL_ERR error =>
          if Feedback.top_structure_of error = "SmtReplayGraph" andalso
             Feedback.top_function_of error = "import" andalso
             Feedback.message_of error =
               "application import DAG budget exhausted"
          then checked_refl root else raise Feedback.HOL_ERR error

  (* Expose exactly a declaration's constructor shape, not an arbitrary
     depth of the source DAG. Pattern variables are opaque typed holes;
     repeated source IDs share a hole at the same declaration Type, even
     across different pattern vars. Distinct generic Types must stay apart
     until specialization. This handles reflexivity without matching the
     expanded operand. *)
  fun schema_patterns theorem =
    List.map (boolSyntax.lhs o Thm.concl) (Rewrite.mk_rewrites theorem)

  val canonical_schema_patterns =
    let
      val laws = cpc_alias_rewrites @
        [boolTheory.EQ_SYM_EQ,boolTheory.CONJ_COMM,boolTheory.DISJ_COMM,
         boolTheory.REFL_CLAUSE,HolSmtTheory.COND_NEG,
         integerTheory.INT_NOT_LT,integerTheory.INT_NOT_LE,
         realTheory.REAL_NOT_LT,realTheory.REAL_NOT_LE,
         integerTheory.INT_ADD_COMM,realTheory.REAL_ADD_COMM]
      fun guarded theorem =
        let
          val guard = boolSyntax.rhs (Thm.concl (Drule.SPEC_ALL theorem))
          val left = Term.genvar Type.alpha
          val right = Term.genvar Type.alpha
        in boolSyntax.mk_cond (guard,left,right) end
    in List.concat (List.map schema_patterns laws) @
      [guarded integerTheory.INT_NOT_LT,guarded realTheory.REAL_NOT_LT]
    end

  fun compact_schema patterns graph scope conversion source =
    let
      exception Shape
      val template_limit = 4096
      fun attempt pattern =
        let
          val types = new_type_order ()
          val holes = ref (Redblackmap.mkDict
            (fn ((left,lty),(right,rty)) =>
              case Int.compare (left,right) of
                EQUAL => types (lty,rty) | order => order))
          val type_bindings = ref ([] : (Type.hol_type,Type.hol_type)
            Lib.subst)
          (* Match a bounded declaration Type, not a native annotation
             tree. A variable binds the opaque actual Type in one step. *)
          fun match_type expected actual =
            if Type.is_vartype expected then
              (case List.find (fn {redex,...} =>
                  Type.dest_vartype redex = Type.dest_vartype expected)
                  (!type_bindings) of
                 SOME {residue,...} =>
                   if types (residue,actual) = EQUAL then () else raise Shape
               | NONE => type_bindings :=
                   {redex = expected,residue = actual} :: !type_bindings)
            else if Type.is_vartype actual then raise Shape
            else
              let
                val a = Type.dest_thy_typeid expected
                val b = Type.dest_thy_typeid actual
                val _ = if KernelSig.id_compare (#Tyop a,#Tyop b) = EQUAL
                  then () else raise Shape
              in ListPair.appEq (fn (x,y) => match_type x y)
                (#Args a,#Args b) handle ListPair.UnequalLengths => raise Shape
              end
          fun operand pattern node =
            let val key = (G.node_id node,Term.type_of pattern) in
              case Redblackmap.peek (!holes,key) of
                SOME (_,term) => term
              | NONE =>
                  let val term = Term.genvar (Term.type_of pattern) in
                    holes := Redblackmap.insert
                      (!holes,key,(node,term));term
                  end
            end
          fun template pattern node =
            (match_type (Term.type_of pattern) (G.type_of graph node);
             if Term.is_var pattern then operand pattern node
             else if Term.is_const pattern then
               (case G.view graph node of
                  G.Constant id =>
                    if KernelSig.id_compare
                        (id,#Name (Term.dest_thy_constid pattern)) = EQUAL
                    then pattern else raise Shape
                | _ => raise Shape)
             else if Term.is_comb pattern then
               (case G.view graph node of
                  G.Application (f,x) =>
                    let val (pf,px) = Term.dest_comb pattern in
                      Term.mk_comb (template pf f,template px x)
                    end
                | _ => raise Shape)
             else raise Shape)
          (* Conversion/matching sees only the bounded declaration's own
             Types. Specialize this small, closed schema afterwards; never
             normalize or match an actual operand or its annotation. *)
          val term = template pattern source
          val _ = admit_native "canon-schema" term
          val generic = Conv.QCONV (Conv.TRY_CONV conversion) term
          val _ = admit_native "canon-schema-result" (Thm.concl generic)
          val theorem = Thm.INST_TYPE (!type_bindings) generic
          val pairs = List.map (fn (_, (node,hole)) =>
            (node,Term.inst (!type_bindings) hole))
            (Redblackmap.listItems (!holes))
          val schema = checked_graph_schema graph scope
            {theorem = theorem,holes = List.map #2 pairs,
             operands = List.map #1 pairs,template_limit = template_limit}
        in
          if graph_schema_source schema = graph_schema_result schema then
            NONE else SOME schema
        end
        handle Shape => NONE
      fun choose [] = NONE
        | choose (pattern::rest) =
            case attempt pattern of NONE => choose rest | some => some
    in choose patterns end

  (* Discover on IDs and prove only bounded constructor prefixes. The
     original operands enter neither matching nor schema INST: assembly
     uses graph names and realization happens once, after closing D.
     Bounded binder bodies use the same compact pass; only their opening
     and final ABS/alpha bridge are native island operations. *)
  fun compact_conversion_status patterns descend revisit propose root =
    let
      val graph = G.new ()
      val scope = G.root_scope graph
      val maximum = SmtResource.max_bv_replay_term_nodes
      val binder_changed = ref false
      fun binder term =
        if not descend then
          import_binder_island graph scope maximum "canon-binder-import" term
        else
          let
            (* Opening only needs the raw body and range classification.
               Name-only clash handling preserves native names without a
               full annotation admission. Unchanged binders need no ABS. *)
            val _ = admit_count_up_to "canon-binder-opening" maximum term
            val (variable,body) =
              SmtReplayImport.dest_abs_preserving_names term
            val (body_thm,changed) = compact_conversion_status patterns
              true revisit propose body
            val result = boolSyntax.rhs (Thm.concl body_thm)
          in
            if not changed then
              import_binder_island graph scope maximum
                "canon-binder-import" term
            else
              let
                (* ABS and the final alpha anchor can inspect BOTH sides,
                   including annotations erased by the body conversion. *)
                val _ = binder_changed := true
                val _ = admit_native "canon-binder-opening" term
                val _ = List.app (admit_native "canon-binder-hypothesis")
                  (Thm.hyp body_thm)
                val _ = admit_body_result result
                val theorem = anchor_left term (Thm.ABS variable body_thm)
                val target = boolSyntax.rhs (Thm.concl theorem)
                val _ = admit_native "canon-binder-import" target
                val imported = G.admit_binder graph scope maximum target
              in {node = #node imported,original = term,
                  bridge = Thm.TRANS theorem (#bridge imported)} end
          end
      val source = import_nodewise graph scope NONE binder root
      fun schema node =
        if not descend andalso node <> #node source then NONE
        else case propose (G.representative graph node) of NONE => NONE
          | SOME conversion =>
              compact_schema patterns graph scope conversion node
      val converted = graph_conversion graph scope revisit schema
        (#node source)
      val changed = !binder_changed orelse
        graph_source converted <> graph_result converted
      val theorem =
      if graph_source converted = graph_result converted then
        #bridge source
      else
        let
          val theorem = case realize_boolean_root_schema graph scope
              converted of SOME theorem => theorem
            | NONE =>
                let
                  val block = P.freeze graph
                    {scope = scope,roots = graph_roots converted,sources = [],
                     template_limit = SmtResource.max_metric}
                  val proof = graph_assemble graph block converted
                in P.realize block (graph_equality converted) proof end
          val realized = exact_left (G.representative graph (#node source))
            theorem
        in Thm.TRANS (#bridge source) realized end
    in (theorem,changed) end

  (* Import bridges may change representation without changing the normal
     form. Keep that distinction explicit, so unchanged binder bodies do
     not trigger native ABS/alpha work merely to install optional sharing. *)
  fun compact_conversion_with_patterns patterns descend revisit propose root =
    #1 (compact_conversion_status patterns descend revisit propose root)

  val compact_conversion =
    compact_conversion_with_patterns canonical_schema_patterns

  fun root_conversion_with_patterns patterns propose term =
    case propose term of NONE => raise Conv.UNCHANGED
    | SOME _ => compact_conversion_with_patterns patterns
        false false propose term

  val root_conversion =
    root_conversion_with_patterns canonical_schema_patterns

  fun orient_binary order dest comm term =
    let val (left,right) = dest term in
      if order (right,left) = LESS then SOME (Conv.REWR_CONV comm)
      else NONE
    end

  fun equality_orientation order term =
    if boolSyntax.is_eq term then
      orient_binary order boolSyntax.dest_eq boolTheory.EQ_SYM_EQ term
    else NONE

  fun boolean_orientation order term =
    if boolSyntax.is_conj term then
      orient_binary order boolSyntax.dest_conj boolTheory.CONJ_COMM term
    else if boolSyntax.is_disj term then
      orient_binary order boolSyntax.dest_disj boolTheory.DISJ_COMM term
    else NONE

  fun reorient_equality_conv term =
    let val _ = boolSyntax.dest_eq term in
      root_conversion (equality_orientation (new_term_order ())) term
    end

  fun reorient_binary_conv dest comm term =
    root_conversion_with_patterns (schema_patterns comm)
      (orient_binary (new_term_order ()) dest comm) term

  fun boolean_commute_conv term =
    root_conversion (boolean_orientation (new_term_order ())) term

  (* Build rewrite nets once, but run them only on compact prefixes (or
     already admitted native binder islands), never on an expanded DAG. *)
  val alias_schema_conv = Rewrite.PURE_REWRITE_CONV cpc_alias_rewrites
  val not_schema_conv = Rewrite.PURE_REWRITE_CONV
    [Thm.CONJUNCT1 boolTheory.NOT_CLAUSES,
     Thm.CONJUNCT2 boolTheory.NOT_CLAUSES]
  val cpc_alias_conv = compact_conversion true true
    (fn _ => SOME alias_schema_conv)
  val not_clauses_conv = compact_conversion true true
    (fn _ => SOME not_schema_conv)

  (* Kept for the arithmetic adapter below, not the selected graph pass. *)
  val real_div_conv = Rewrite.PURE_REWRITE_CONV [realTheory.real_div]

  (* Both disjoint orientations share one invocation-local ordering memo.
     The order is the public semantic order, not allocation order. *)
  fun z3_primary_rewrite_canon_conv term =
    let
      val order = new_term_order ()
      fun propose current = case equality_orientation order current of
          NONE => boolean_orientation order current | some => some
    in compact_conversion true false propose term end

  (* Z3 may express the same arithmetic rewrite through a dual relation,
     a negated conditional guard, or commuted addition.  These rules are
     deliberately separate from the primary canonicalizer: their broader
     normalization is accepted only when it closes the concrete difference
     between the two sides of the rewrite. *)
  val z3_cond_polarity_conv = compact_conversion_with_patterns
    (schema_patterns HolSmtTheory.COND_NEG) true false
    (fn term => if boolSyntax.is_cond term then
      SOME (Conv.REWR_CONV HolSmtTheory.COND_NEG) else NONE)

  val relation_dual_schema_conv =
    Conv.FIRST_CONV (List.map Conv.REWR_CONV
      [integerTheory.INT_GT,
       integerTheory.INT_GE,
       integerTheory.INT_NOT_LT,
       integerTheory.INT_NOT_LE,
       realTheory.real_gt,
       realTheory.real_ge,
       realTheory.REAL_NOT_LT,
       realTheory.REAL_NOT_LE])
  val z3_relation_dual_conv = compact_conversion true false
    (fn _ => SOME relation_dual_schema_conv)

  (* After relation aliases are normalized, a non-strict order in an ite
     guard is the complement of the reversed strict order.  Expose that
     negation only at the guard, then use the polymorphic polarity theorem
     to swap the branches. *)
  fun z3_order_cond_polarity_conv tm =
    let
      val (guard, _, _) = boolSyntax.dest_cond tm
      val expose_negation =
        if Lib.can intSyntax.dest_leq guard then
          Conv.REWR_CONV (Conv.GSYM integerTheory.INT_NOT_LT)
        else if Lib.can realSyntax.dest_leq guard then
          Conv.REWR_CONV (Conv.GSYM realTheory.REAL_NOT_LT)
        else
          raise Conv.UNCHANGED
    in
      Conv.THENC
        (Conv.RATOR_CONV
           (Conv.RATOR_CONV (Conv.RAND_CONV expose_negation)),
         Conv.REWR_CONV HolSmtTheory.COND_NEG) tm
    end
    handle Feedback.HOL_ERR _ => raise Conv.UNCHANGED

  fun additive_order_conv tm =
    if intSyntax.is_plus tm then
      reorient_binary_conv intSyntax.dest_plus
        integerTheory.INT_ADD_COMM tm
    else if realSyntax.is_plus tm then
      reorient_binary_conv realSyntax.dest_plus
        realTheory.REAL_ADD_COMM tm
    else
      raise Conv.UNCHANGED

  fun additive_orientation order term =
    if intSyntax.is_plus term then
      orient_binary order intSyntax.dest_plus integerTheory.INT_ADD_COMM term
    else if realSyntax.is_plus term then
      orient_binary order realSyntax.dest_plus realTheory.REAL_ADD_COMM term
    else NONE

  fun additive_canon_conv term =
    compact_conversion true false
      (additive_orientation (new_term_order ())) term

  val z3_difference_rewrite_canon_conv = compose
    [z3_relation_dual_conv,
     compact_conversion true false
       (fn _ => SOME z3_order_cond_polarity_conv),
     z3_cond_polarity_conv,
     additive_canon_conv,
     z3_primary_rewrite_canon_conv]

  fun equality_operands_alpha_equal tm =
    let val (left,right) = boolSyntax.dest_eq tm
    in new_term_order () (left,right) = EQUAL end

  fun z3_rewrite_canon_conv tm =
    let
      val primary = z3_primary_rewrite_canon_conv tm
      val primary_target = boolSyntax.rhs (Thm.concl primary)
    in
      if not (boolSyntax.is_eq primary_target) orelse
         equality_operands_alpha_equal primary_target then
        primary
      else
        let
          val secondary = z3_difference_rewrite_canon_conv primary_target
          val secondary_target = boolSyntax.rhs (Thm.concl secondary)
        in
          if equality_operands_alpha_equal secondary_target then
            Thm.TRANS primary secondary
          else
            primary
        end
    end

  fun reflexive_orientation order term =
    if boolSyntax.is_eq term then
      let val (left,right) = boolSyntax.dest_eq term in
        if order (left,right) = EQUAL then
          SOME (Conv.REWR_CONV boolTheory.REFL_CLAUSE)
        else NONE
      end
    else NONE

  fun reflexive_equality_conv term =
    let val _ = boolSyntax.dest_eq term in
      root_conversion (reflexive_orientation (new_term_order ())) term
    end

  fun reflexive_canon_conv term = compact_conversion true false
    (reflexive_orientation (new_term_order ())) term

  fun equality_canon_conv term = compact_conversion true false
    (equality_orientation (new_term_order ())) term

  (* Normalization below propositions: relation aliases, pushed real_of_int,
     ground total computation, and eta.  Symbolic totalized integer
     arithmetic requires per-translation provenance and is unfolded by the
     CPC strong canonicalizer instead. *)
  val cpc_term_canon_conv =
    compose
      [cpc_alias_conv,
       dag_rewrite_conv ground_total_conv,
       cpc_alias_conv,
       dag_orientation_conv Drule.ETA_CONV]

  val cpc_operand_canon_conv =
    compose
      [cpc_term_canon_conv,
       reflexive_canon_conv,
       equality_canon_conv,
       (* Reflexive reduction only replaces a Boolean equality by T.  Of the
          term canonicalizer's rules, this can expose only ~T/~F; avoid a
          second ground-arithmetic and eta traversal at every CPC step. *)
       not_clauses_conv,
       reflexive_canon_conv,
       equality_canon_conv]

  (* Preserve the outer equality needed by TRANS and EQ_MP.  Its operands use
     the same recursive orientation as CPC congruence sources, but only the
     structurally neutral Boolean reduction [x = x] -> T; a broad Boolean
     simplifier here could erase the very context a congruence step consumes.
     The semantic order remains deterministic and idempotent. *)
  fun cpc_canon_conv tm =
    if boolSyntax.is_eq tm then
      compose
        [Conv.BINOP_CONV cpc_operand_canon_conv,
         reorient_equality_conv]
        tm
    else
      cpc_operand_canon_conv tm

  fun cpc_canon_rule theorem = Conv.CONV_RULE cpc_canon_conv theorem

  fun polynomial_conv ty =
    if Type.compare (ty, intSyntax.int_ty) = EQUAL then
      intLib.INT_POLY_CONV
    else if Type.compare (ty, realSyntax.real_ty) = EQUAL then
      RealField.REAL_POLY_CONV
    else
      raise ERR "arith_poly_norm_prove"
        "polynomial equality is neither integer nor real"

  fun normalize_polynomial conv tm =
    compose
      [cpc_term_canon_conv,
       dag_rewrite_conv (Conv.FIRST_CONV (List.map Conv.REWR_CONV
         [integerTheory.INT_NEG_0, integerTheory.INT_NEGNEG,
          realTheory.REAL_NEG_0, realTheory.REAL_NEGNEG])),
       conv] tm

  fun normalize_polynomial_function tm =
    let
      val (domain, range) = Type.dom_rng (Term.type_of tm)
      val variable = Term.genvar domain
      val applied = Term.mk_comb (tm, variable)
      val body = polynomial_conv range applied
      val abstraction = Thm.ABS variable body
      val expansion = Term.mk_abs (variable, applied)
      val eta = Drule.ETA_CONV expansion
    in
      Thm.TRANS (Thm.SYM eta) abstraction
    end

  fun polynomial_subterm_conv tm =
    let val ty = Term.type_of tm in
      if is_arith_type ty andalso
         not (List.null (Term.free_vars tm)) then
        polynomial_conv ty tm
      else
        raise Conv.UNCHANGED
    end

  fun arith_poly_norm_conversion target =
    let val ty = Term.type_of target in
      if is_arith_type ty then
        polynomial_conv ty target
      else if Lib.can Type.dom_rng ty then
        normalize_polynomial_function target
      else
        Conv.QCONV (Conv.TOP_DEPTH_CONV polynomial_subterm_conv) target
    end

  fun prove_polynomial_equality target =
    let
      val (left, right) = boolSyntax.dest_eq target
      val ty = Term.type_of left
      val _ = Type.compare (ty, Term.type_of right) = EQUAL orelse
        raise ERR "arith_poly_norm_prove"
          "polynomial equality has different operand types"
      val conv = polynomial_conv ty
      val left_norm = normalize_polynomial conv left
      val right_norm = normalize_polynomial conv right
      val normalized_left = boolSyntax.rhs (Thm.concl left_norm)
      val normalized_right = boolSyntax.rhs (Thm.concl right_norm)
      val _ = Term.aconv normalized_left normalized_right orelse
        raise ERR "arith_poly_norm_prove"
          "polynomial canonical forms differ"
    in
      Thm.TRANS left_norm (Thm.SYM right_norm)
    end

  (* CPC and Z3 use "polynomial normalization" for both expression
     equalities and equivalent arithmetic atoms (including negated order
     relations).  Canonicalize aliases once, use the direct polynomial
     conversion when the target has that shape, and otherwise invoke the
     common proof-producing arithmetic normalizer.  This is intentionally
     one general path: its cost and coverage depend on the input polynomial,
     not on a catalogue of recorded proof shapes. *)
  fun arith_poly_norm_prove target =
    let val ty = Term.type_of target in
    if is_arith_type ty then
      polynomial_conv ty target
    else case Lib.total Type.dom_rng ty of
      SOME (_, range) =>
        if is_arith_type range then
          normalize_polynomial_function target
        else
          raise ERR "arith_poly_norm_prove"
            "polynomial function has a non-arithmetic result type"
    | NONE => let
      (* CPC's polynomial normalizer treats total real division by a
         demonstrably nonzero denominator as ordinary field division.  The
         simplifier discharges only proved nonzero side conditions (notably
         numerals), so the underspecified zero branch remains untouched. *)
      val target_norm =
        if Library.contains_const smt_rdiv_tm target then
          compose
            [cpc_term_canon_conv,
             Conv.TOP_DEPTH_CONV smt_rdiv_nonzero_conv,
             real_div_conv] target
        else cpc_term_canon_conv target
      val normalized = boolSyntax.rhs (Thm.concl target_norm)
      val proof =
        prove_polynomial_equality normalized
        handle Feedback.HOL_ERR _ =>
          Library.arith_prove_with_cases normalized
    in
      Thm.EQ_MP (Thm.SYM target_norm) proof
    end
    end

end
