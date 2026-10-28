(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for genuine SMT-LIB Seq lemmas. *)

structure SmtSeqProve :> SmtSeqProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtSeqProve"

  fun is_smtstr_value tm =
    Term.is_comb tm andalso
    let val (head, _) = Term.dest_comb tm in
        Term.is_const head andalso
        let val {Thy, Name, ...} = Term.dest_thy_const head
        in Thy = "smtstring" andalso Name = "SmtStr" end
    end

  fun list_element_type tm =
    Lib.total listSyntax.dest_list_type (Term.type_of tm)

  (* String remains on SmtStringProve's carrier.  A list type alone is not
     Seq provenance: ArrayEx lowering can contain list-typed implementation
     artefacts.  Require a sequence operation as well. *)
  fun has_seq_type t =
    let
      fun sequence_head tm =
        Term.is_const tm andalso
        let val {Thy, Name, ...} = Term.dest_thy_const tm in
          (Thy = "list" andalso List.exists (Lib.equal Name)
            ["APPEND", "LENGTH", "CONS", "NIL", "TAKE", "DROP", "EL",
             "MAP", "FOLDL", "REVERSE", "isPREFIX", "LUPDATE"])
          orelse (Thy = "rich_list" andalso
            List.exists (Lib.equal Name) ["IS_SUBLIST", "IS_SUFFIX"])
          orelse (Thy = "HolSmt" andalso
            List.exists (Lib.equal Name)
              ["smt_seq_nth", "smt_seq_extract", "smt_seq_at",
               "smt_seq_indexof", "smt_seq_replace", "smt_seq_replace_all",
               "smt_seq_update"])
        end
    in
      SmtResource.contains_with_pruning is_smtstr_value sequence_head t
    end

  val metis_limit : mlibMeter.limit = {time = SOME 1.0, infs = SOME 5000}
  fun with_metis_limit f = Lib.with_flag (metisTools.limit, metis_limit) f

  val list_rewrites = [
    listTheory.APPEND,
    listTheory.APPEND_ASSOC,
    listTheory.APPEND_11,
    listTheory.APPEND_eq_NIL,
    listTheory.CONS_11,
    listTheory.LENGTH_APPEND,
    integerTheory.INT_OF_NUM_ADD,
    listTheory.LENGTH_EQ_0,
    listTheory.LENGTH_EQ_1,
    listTheory.NOT_CONS_NIL,
    listTheory.EL,
    listTheory.MAP_APPEND,
    rich_listTheory.FOLDL_APPEND,
    integerTheory.INT_ADD_COMM,
    HolSmtTheory.smt_seq_nth_def,
    HolSmtTheory.smt_seq_extract_def,
    HolSmtTheory.smt_seq_at_def
  ]

  val seq_ss = simpLib.++ (bossLib.srw_ss(), intSimps.INT_RWTS_ss)

  fun named thy names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = thy andalso List.exists (Lib.equal Name) names end

  val mentions = SmtResource.contains

  fun is_append tm = named "list" ["APPEND"] tm
  fun is_length tm = named "list" ["LENGTH"] tm
  fun is_cons_or_nil tm = named "list" ["CONS", "NIL"] tm
  fun is_access tm =
    named "HolSmt" ["smt_seq_nth", "smt_seq_extract", "smt_seq_at"] tm
    orelse named "list" ["TAKE", "DROP", "EL"] tm

  (* Z3's native Seq certificate uses its internal `seq.eq` and `seq.tail`
     witnesses for this list fact.  The parser reconstructs them as equality
     and DROP, so one generic theorem handles all element types. *)
  val head_tail_thm = Library.prove
    (``(&(LENGTH (s : 'a list)):int) = 0 \/
        s = [EL 0 s] ++ DROP 1 s``,
     Tactical.THEN (bossLib.Cases_on `s`,
       bossLib.RW_TAC (bossLib.srw_ss()) []))

  val nth_of_unit_thm = Library.prove
    (``[x] = (s : 'a list) ==> EL 0 s = x``,
     bossLib.METIS_TAC [listTheory.EL, listTheory.HD])

  (* SMT sequence nth is deliberately unspecified out of range.  Z3 rewrites
     it to an if whose out-of-range branch preserves that same application.
     Split on the complete semantic boundary once, then compare the resulting
     canonical forms.  This covers every element type and symbolic index
     without assigning a value outside the specified range. *)
  val nth_boundary_thm = Library.prove
    (``smt_seq_nth (s : 'a list) i =
        if i < 0 \/ &(LENGTH s) <= i then smt_seq_nth s i
        else EL (Num i) s``,
     Tactical.THEN
       (bossLib.Cases_on `i < 0 \/ &(LENGTH s) <= i`,
        Tactical.THEN
          (bossLib.ASM_SIMP_TAC (bossLib.srw_ss()) [],
           Tactical.THEN
             (Tactic.irule HolSmtTheory.smt_seq_nth_def,
              intLib.ARITH_TAC))))

  (* The continuation belongs to the current compact replay invocation.
     Hide its exceptions from tactic/search filtering, restoring the exact
     primary exception only after all local alternatives have unwound. *)
  val scalar_compset = computeLib.copy (computeLib.the_compset ())

  fun checked_procedures check =
  let
    exception AdmissionFailure of exn
    val computing_elements = ref false
    fun admit tm = check tm handle primary => raise AdmissionFailure primary
    fun protect f x = f x handle AdmissionFailure primary => raise primary
    fun theorem th =
      (admit (Thm.concl th);List.app admit (Thm.hyp th);th)
    fun checked_tactic tactic (assumptions,goal) =
      (List.app admit (goal::assumptions);tactic (assumptions,goal))
    (* The ordinary simplifier cannot match SUC fuel against a literal
       numeral. Open JUST that numeral at the auxiliary replacement head;
       never recursively evaluate a realized sequence with CBV_CONV. *)
    fun replacement_step tm =
      let
        val (head,args) = boolSyntax.strip_comb tm
        val _ = if named "HolSmt" ["smt_seq_replace_all_aux"] head andalso
            length args = 4 andalso numSyntax.is_numeral (hd args) andalso
            not (Term.aconv (hd args) numSyntax.zero_tm)
          then () else raise Conv.UNCHANGED
        val clause = List.nth
          (Drule.CONJUNCTS HolSmtTheory.smt_seq_replace_all_aux_def,
           if listSyntax.is_nil (List.nth (args,1)) then 1 else 2)
        val _ = admit tm
        val _ = ignore (theorem clause)
        val unfold = Conv.RATOR_CONV (Conv.RATOR_CONV
          (Conv.RATOR_CONV (Conv.RAND_CONV numLib.num_CONV))) tm
        val _ = ignore (theorem unfold)
        val exposed = boolSyntax.rhs (Thm.concl unfold)
        val _ = admit exposed
        val step = theorem (Conv.REWR_CONV clause exposed)
      in theorem (Thm.TRANS unfold step) end
    (* List cancellation is a local shape law, not a reason to normalize
       a whole element DAG. Retain every explicit list constructor and one
       typed occurrence name per opaque element/list segment. Successful
       discovery precedes the single checked INST; Traverse sees only its
       admitted sides afterwards, never matches the realized theorem. *)
    val list_procedures = SmtDatatypeListConv.procedures admit
    fun list_step tm =
      let
        val equality = boolSyntax.is_eq tm
        val sides = if equality then
            let val (l,r) = boolSyntax.dest_eq tm
                val _ = if Lib.can listSyntax.dest_list_type (Term.type_of l)
                  then () else raise Conv.UNCHANGED
            in [l,r] end
          else if listSyntax.is_append tm orelse listSyntax.is_snoc tm then
            [tm] else raise Conv.UNCHANGED
        val _ = admit tm
        val bindings = ref (Redblackmap.mkDict Term.compare)
        fun atom term =
          case Redblackmap.peek (!bindings,term) of SOME hole => hole
          | NONE =>
              let val hole = Term.genvar (Term.type_of term)
              in bindings := Redblackmap.insert (!bindings,term,hole);
                 hole end
        fun spine term =
          let val (head,args) = boolSyntax.strip_comb term
          in if named "list" ["APPEND","CONS","SNOC","REVERSE"] head
               andalso not (null args) then
               Term.list_mk_comb (head,List.map (fn arg =>
                 if Type.compare (Term.type_of arg,Term.type_of term)=EQUAL
                 then spine arg else atom arg) args)
             else if listSyntax.is_nil term then term else atom term
          end
        val schema = case List.map spine sides of
            [l,r] => boolSyntax.mk_eq (l,r)
          | [term] => term | _ => raise Conv.UNCHANGED
        val _ = admit schema
        val result = if equality then
            (#closed_equality list_procedures schema
              handle Conv.UNCHANGED => #equality list_procedures schema
                | Feedback.HOL_ERR _ => #equality list_procedures schema)
          else #normalise list_procedures schema
        val _ = if Term.aconv (boolSyntax.lhs (Thm.concl result))
            (boolSyntax.rhs (Thm.concl result)) then raise Conv.UNCHANGED
          else ()
        val _ = if SmtResource.contains Term.is_abs (Thm.concl result)
          then raise Conv.UNCHANGED else ()
        val substitution = List.map (fn (actual,hole) =>
          {redex=hole,residue=actual}) (Redblackmap.listItems (!bindings))
        val result = Thm.INST substitution result
        val (left,right) = boolSyntax.dest_eq (Thm.concl result)
        val _ = List.app admit (left::right::Thm.hyp result)
      in result end
    (* Preserve the old closed element computation (including word/user
       computations), but never pass the surrounding sequence to CBV. The
       sequence spine, recursive fuel and list relationships stay with the
       checked constructor driver above. This is invocation-local policy. *)
    fun scalar_step tm =
      let
        val _ = if !computing_elements andalso Term.is_comb tm andalso
            not (SmtResource.contains (fn node =>
              Lib.can listSyntax.dest_list_type (Term.type_of node)) tm)
          then () else raise Conv.UNCHANGED
        val _ = admit tm
        val _ = if null (Term.free_vars tm) then ()
          else raise Conv.UNCHANGED
        val result = Conv.CHANGED_CONV
          (computeLib.CBV_CONV scalar_compset) tm
        val (left,right) = boolSyntax.dest_eq (Thm.concl result)
        val _ = List.app admit (left::right::Thm.hyp result)
      in result end
    fun local_step tm = replacement_step tm
      handle Conv.UNCHANGED =>
        (list_step tm handle Conv.UNCHANGED => scalar_step tm
          | Feedback.HOL_ERR _ => scalar_step tm)
        | Feedback.HOL_ERR _ =>
        (list_step tm handle Conv.UNCHANGED => scalar_step tm
          | Feedback.HOL_ERR _ => scalar_step tm)
    fun with_rewrites facts prove =
      (List.app (fn th => ignore (theorem th)) facts;
       SmtDatatypeProve.with_checked_rewrites_using admit
         (fn () => simpLib.++ (seq_ss,simpLib.rewrites facts))
         local_step prove)
    fun simplify facts tm =
      (admit tm;with_rewrites facts (fn ss =>
        let val result = simpLib.SIMP_CONV ss [] tm
            val (left,right) = boolSyntax.dest_eq (Thm.concl result)
            val _ = List.app admit (left::right::Thm.hyp result)
        in result end))

  fun simp_prove_with rewrites t =
    SmtResource.with_resource_step_time "Sequence" "seq-simp" (fn () =>
      let
        val _ = SmtResource.check_resource_goal "Sequence" "seq-simp" t
        val _ = admit t
        (* Discover a complete constructor/segment cancellation before
           building a general simplifier. This is the same checked list
           procedure used by its fallback, on the same occurrence schema. *)
        val local_result = SOME (list_step t)
          handle Conv.UNCHANGED => NONE | Feedback.HOL_ERR _ => NONE
        val normalized = case local_result of
            SOME th =>
              let val residual = boolSyntax.rhs (Thm.concl th)
              in if Term.aconv residual boolSyntax.T then th
                 else (Thm.TRANS th (simplify rewrites residual)
                   handle Conv.UNCHANGED => th) end
          | NONE => (simplify rewrites t
              handle Conv.UNCHANGED =>
                raise ERR "simp_prove_with" "no rewrite applies to this rung")
        val t' = boolSyntax.rhs (Thm.concl normalized)
        val _ = admit t'
        val thm = tautLib.TAUT_PROVE t'
          handle Feedback.HOL_ERR _ => intLib.ARITH_PROVE t'
      in theorem (Thm.EQ_MP (Thm.SYM normalized) thm) end) ()

  fun simp_prove t = simp_prove_with list_rewrites t

  fun nth_boundary_prove t =
    let
      fun is_nth_application tm =
        case boolSyntax.strip_comb tm of
          (head, [_, _]) => named "HolSmt" ["smt_seq_nth"] head
        | _ => false
      val _ = admit t
      val pattern = ``smt_seq_nth (s : 'a list) i``
      val _ = List.app admit [pattern,Thm.concl nth_boundary_thm]
      val application = HolKernel.find_term is_nth_application t
      val _ = admit application
      val instantiated = theorem (Drule.INST_TY_TERM
        (Term.match_term pattern application) nth_boundary_thm)
      val theorem = Thm.EQ_MP
        (simplify [] (Thm.concl instantiated)) instantiated
      val normalization = simplify [] t
        handle Conv.UNCHANGED =>
          raise ERR "nth_boundary_prove"
            "rewrite has no nth boundary normalization"
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val _ = Term.aconv (Thm.concl theorem) normalized orelse
        raise ERR "nth_boundary_prove"
          "rewrite is not the total nth semantic boundary"
    in
      Thm.EQ_MP (Thm.SYM normalization) theorem
    end

  fun nth_decomposition_prove t =
    if mentions is_access t then
      (admit t;ignore (theorem head_tail_thm);
       Drule.INST_TY_TERM
         (Term.match_term (Thm.concl head_tail_thm) t) head_tail_thm
       handle Feedback.HOL_ERR _ =>
         let
           fun witness_consequence () =
             let
               val (decomposition, rest) = boolSyntax.dest_imp t
               val (unit_equality, expected) = boolSyntax.dest_imp rest
               val (schema_premise, _) = boolSyntax.dest_imp
                 (Thm.concl nth_of_unit_thm)
               val _ = ignore (theorem nth_of_unit_thm)
               val _ = List.app admit [schema_premise,unit_equality,expected]
               val schema = theorem (Drule.INST_TY_TERM
                 (Term.match_term schema_premise unit_equality)
                 nth_of_unit_thm)
               val consequence = Thm.MP schema (Thm.ASSUME unit_equality)
               val consequence =
                 if Term.aconv (Thm.concl consequence) expected then
                   consequence
                 else
                   let val symmetric = Thm.SYM consequence in
                     if Term.aconv (Thm.concl symmetric) expected then
                       symmetric
                     else raise ERR "nth_decomposition_prove"
                       "singleton witness has the wrong conclusion"
                   end
             in
               Thm.DISCH decomposition
                 (Thm.DISCH unit_equality consequence)
             end
         in
           witness_consequence ()
         end
         handle Feedback.HOL_ERR _ =>
         let
           val normalized = simplify list_rewrites t
             handle Conv.UNCHANGED => Thm.REFL t
           val target = boolSyntax.rhs (Thm.concl normalized)
           val _ = List.app (fn th => ignore (theorem th))
             [head_tail_thm,nth_of_unit_thm]
           val _ = admit target
           val thm =
             if Term.aconv target boolSyntax.T then boolTheory.TRUTH
             else with_metis_limit (fn () => metisLib.METIS_PROVE
               [head_tail_thm, nth_of_unit_thm] target) ()
         in
           Thm.EQ_MP (Thm.SYM normalized) thm
         end)
    else
      raise ERR "nth_decomposition_prove" "not a Seq nth decomposition"

  fun is_prefix_suffix_contains tm =
    named "rich_list" ["IS_SUBLIST", "IS_SUFFIX"] tm orelse
    named "list" ["isPREFIX"] tm

  fun is_indexof_replace tm =
    named "HolSmt"
      ["smt_seq_indexof", "smt_seq_replace", "smt_seq_replace_all"] tm

  fun is_update_reverse tm =
    named "HolSmt" ["smt_seq_update"] tm orelse
    named "list" ["REVERSE", "LUPDATE"] tm

  (* Search witnesses at every append boundary.  Literal lists contribute one
     segment per element, so the search is bounded by the input list length;
     symbolic append trees contribute only their explicit leaves. *)
  fun contains_append_witness_prove t =
    let
      val _ = admit t
      val (head, args) = boolSyntax.strip_comb t
      val _ = named "rich_list" ["IS_SUBLIST"] head orelse
        raise ERR "contains_append_witness_prove" "not a positive IS_SUBLIST"
      val (whole, part) = case args of
          [whole, part] => (whole, part)
        | _ => raise ERR "contains_append_witness_prove"
            "IS_SUBLIST expects two arguments"
      val element_type = valOf (list_element_type whole)
      val empty = listSyntax.mk_list ([], element_type)
      fun segments tm =
        case Lib.total listSyntax.dest_append tm of
          SOME (left, right) => segments left @ segments right
        | NONE =>
            (case Lib.total listSyntax.dest_list tm of
               SOME (elements, _) => List.map (fn element =>
                 listSyntax.mk_list ([element], element_type)) elements
             | NONE => [tm])
      fun append [] = empty
        | append (first :: rest) =
            List.foldl (fn (next, accumulated) =>
              listSyntax.mk_append (accumulated, next)) first rest
      val pieces = segments whole
      val count = List.length pieces
      fun prove_split (start, finish) =
        let
          val prefix = append (List.take (pieces, start))
          val suffix = append (List.drop (pieces, finish))
        in
          let
            val _ = List.app admit [prefix,suffix]
            val _ = ignore (theorem rich_listTheory.IS_SUBLIST_APPEND)
            val conversion = Conv.REWR_CONV
              rich_listTheory.IS_SUBLIST_APPEND t
            val existential = boolSyntax.rhs (Thm.concl conversion)
            val _ = admit existential
            val (v,body) = boolSyntax.dest_exists existential
            val _ = List.app admit [v,body]
            val inner = Term.subst [{redex=v,residue=prefix}] body
            val _ = admit inner
            val (w,equation) = boolSyntax.dest_exists inner
            val _ = List.app admit [w,equation]
            val equation = Term.subst [{redex=w,residue=suffix}] equation
            val proof = simp_prove_with [listTheory.APPEND_ASSOC] equation
            val inner_proof = theorem (Thm.EXISTS (inner,suffix) proof)
            val proof = theorem (Thm.EXISTS
              (existential,prefix) inner_proof)
          in theorem (Thm.EQ_MP (Thm.SYM conversion) proof) end
        end
      val boundaries = List.concat (List.tabulate (count + 1, fn start =>
        List.tabulate (count - start + 1, fn width =>
          (start, start + width))))
      (* Choose literal/shared segment witnesses before blind search. This
         is discovery only: the selected equality and EXISTS steps above
         still prove the claim. Retain the complete original search when
         segment equality itself needs the checked procedure. *)
      val wanted = segments part
      fun same ([],[]) = true
        | same (x::xs,y::ys) = Term.aconv x y andalso same (xs,ys)
        | same _ = false
      fun likely (start,finish) = finish-start = length wanted andalso
        same (List.take (List.drop (pieces,start),finish-start),wanted)
      val (preferred,others) = List.partition likely boundaries
    in
      Lib.tryfind prove_split (preferred @ others)
    end

  val prefix_suffix_contains_rewrites = list_rewrites @ [
    listTheory.isPREFIX_THM,
    rich_listTheory.IS_SUBLIST,
    rich_listTheory.IS_SUBLIST_APPEND,
    rich_listTheory.IS_SUFFIX,
    rich_listTheory.IS_SUFFIX_APPEND,
    rich_listTheory.IS_PREFIX_IS_SUBLIST,
    rich_listTheory.IS_PREFIX_REFL
  ]

  val indexof_replace_rewrites = list_rewrites @ [
    HolSmtTheory.smt_seq_indexof_def,
    HolSmtTheory.smt_seq_indexof_aux_def,
    HolSmtTheory.smt_seq_replace_def,
    HolSmtTheory.smt_seq_replace_raw_def
  ]

  (* Unfold recursive replacement only for a closed obligation. Use the
     checked redex driver rather than a recursively computing conversion:
     every newly generated list/conditional must be admitted as well. *)
  val replace_all_rewrites = [HolSmtTheory.smt_seq_replace_all_def,
    HolSmtTheory.smt_seq_replace_all_aux_def,listTheory.DROP_compute,
    listTheory.TAKE_compute,listTheory.isPREFIX]

  fun ground_replace_all_prove t =
    (admit t;if List.null (Term.free_vars t) then
      SmtResource.with_resource_step_time "Sequence" "seq-replace-all"
        (Lib.with_flag (computing_elements,true)
          (fn t => Drule.EQT_ELIM (simplify replace_all_rewrites t))) t
    else
      raise ERR "ground_replace_all_prove" "replacement is not ground")

  val update_reverse_rewrites = list_rewrites @ [
    HolSmtTheory.smt_seq_update_def,
    integerTheory.INT_SUB,
    listTheory.LUPDATE_def,
    listTheory.REVERSE_DEF
  ]

  fun shape_of t =
    if mentions is_prefix_suffix_contains t then
      "prefix-suffix-contains"
    else if mentions is_indexof_replace t then
      "indexof-replace"
    else if mentions is_update_reverse t then
      "update-reverse"
    else if mentions is_access t then
      "extract-nth"
    else if mentions is_append t orelse mentions is_length t then
      "concat-length"
    else if mentions is_cons_or_nil t then
      "unit-empty"
    else
      "unrecognised"

  fun unsupported t =
    raise ERR "seq_prove"
      ("unsupported th-lemma shape: theory=seq; shape=" ^ shape_of t ^
       "; attempted rungs=[concat-length, unit-empty, extract-nth, " ^
       "prefix-suffix-contains, indexof-replace, update-reverse]; " ^
       "all rungs are bounded by the native list term structure; " ^
       "conclusion=" ^ Library.term_to_string t)

  fun concat_length_prove t =
    if mentions is_append t orelse mentions is_length t then simp_prove t
    else raise ERR "concat_length_prove" "not a concat/length shape"

  fun unit_empty_prove t =
    if mentions is_cons_or_nil t then simp_prove t
    else raise ERR "unit_empty_prove" "not a unit/empty shape"

  fun access_prove t =
    if mentions is_access t then simp_prove t
    else raise ERR "access_prove" "not an extract/nth shape"

  fun prefix_suffix_contains_prove t =
    if mentions is_prefix_suffix_contains t then
      contains_append_witness_prove t
      handle Feedback.HOL_ERR _ =>
        simp_prove_with prefix_suffix_contains_rewrites t
    else
      raise ERR "prefix_suffix_contains_prove"
        "not a prefix/suffix/contains shape"

  fun indexof_replace_prove t =
    if mentions is_indexof_replace t then
      if mentions (named "HolSmt" ["smt_seq_replace_all"]) t then
        ground_replace_all_prove t
      else
        simp_prove_with indexof_replace_rewrites t
    else
      raise ERR "indexof_replace_prove" "not an indexof/replace shape"

  fun update_reverse_prove t =
    if mentions is_update_reverse t then
      simp_prove_with update_reverse_rewrites t
    else
      raise ERR "update_reverse_prove" "not an update/reverse shape"

  fun seq_contextual_prove context t =
    if has_seq_type t then
      SmtResource.with_resource_step_time "Sequence" "seq-contextual"
        (fn () =>
          (List.app admit (t::context);
           with_rewrites (List.map Thm.ASSUME context @ list_rewrites)
             (fn ss => theorem (Tactical.TAC_PROOF ((context,t),
               checked_tactic (bossLib.ASM_SIMP_TAC ss [])))))) ()
    else
      unsupported t

  fun seq_prove t =
    if not (has_seq_type t) then
      unsupported t
    else
      SmtResource.with_resource_step_time "Sequence" "seq" (fn () =>
      let
        val _ = SmtResource.check_resource_goal "Sequence" "seq" t
        val _ = admit t
        fun next attempt fallback =
          attempt ()
          handle Feedback.HOL_ERR holerr =>
            if SmtResource.is_resource_gate holerr then
              raise Feedback.HOL_ERR holerr
            else
              fallback ()
      in
        next
          (fn () => Profile.profile_with_exn_name
            "seq(0)(nth-boundary)" nth_boundary_prove t)
          (fn () =>
        next (fn () => nth_decomposition_prove t) (fn () =>
        next (fn () => concat_length_prove t) (fn () =>
        next (fn () => unit_empty_prove t) (fn () =>
        next (fn () => access_prove t) (fn () =>
        next (fn () => prefix_suffix_contains_prove t) (fn () =>
        next (fn () => indexof_replace_prove t) (fn () =>
        next (fn () => update_reverse_prove t)
          (fn () => unsupported t))))))))
      end) ()
  in
    {prove=protect seq_prove,contextual=fn context =>
       protect (seq_contextual_prove context),
     concat_length=protect concat_length_prove,
     unit_empty=protect unit_empty_prove,access=protect access_prove,
     prefix_suffix_contains=protect prefix_suffix_contains_prove,
     indexof_replace=protect indexof_replace_prove,
     update_reverse=protect update_reverse_prove}
  end

  fun default () = checked_procedures
    (SmtReplayArithmetic.new_term_check
      {limit=SmtResource.max_bv_replay_term_nodes,observe=fn () => ()})
  fun seq_prove_with_admission admit = #prove (checked_procedures admit)
  fun seq_contextual_prove_with_admission admit =
    #contextual (checked_procedures admit)
  fun seq_prove t = #prove (default ()) t
  fun seq_contextual_prove context t = #contextual (default ()) context t
  fun concat_length_prove t = #concat_length (default ()) t
  fun unit_empty_prove t = #unit_empty (default ()) t
  fun access_prove t = #access (default ()) t
  fun prefix_suffix_contains_prove t = #prefix_suffix_contains (default ()) t
  fun indexof_replace_prove t = #indexof_replace (default ()) t
  fun update_reverse_prove t = #update_reverse (default ()) t
end
