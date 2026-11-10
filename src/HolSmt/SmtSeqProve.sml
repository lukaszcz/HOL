(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for genuine SMT-LIB Seq lemmas. *)

structure SmtSeqProve :> SmtSeqProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtSeqProve"

  (* Use the same terminal carrier as the bounded graph adapter, so its
     private callback envelope is removed before outer consumer restoration. *)
  val with_admission_errors = SmtReplayArithmetic.with_admission_errors

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

  (* The statements below are built, not parsed: a constant a client
     theory exports must not capture s, i, x or y. *)
  local
    open boolSyntax
    val element_ty = Type.alpha
    val s = Term.mk_var ("s", listSyntax.mk_list_type element_ty)
    val i = Term.mk_var ("i", intSyntax.int_ty)
    val x = Term.mk_var ("x", element_ty)
    val y = Term.mk_var ("y", element_ty)
    val e = Term.mk_var ("e", element_ty)
    fun seq_app name args =
      HolKernel.list_mk_icomb
        (Term.prim_mk_const {Thy = "HolSmt", Name = name}) args
    fun unit v = listSyntax.mk_list ([v], element_ty)
    val int_length = intSyntax.mk_injected (listSyntax.mk_length s)
    val nth_s_i = seq_app "smt_seq_nth" [s, i]
    (* i < 0 \/ &(LENGTH s) <= i *)
    val out_of_range =
      mk_disj (intSyntax.mk_less (i, intSyntax.zero_tm),
               intSyntax.mk_leq (int_length, i))
    (* MAP (\e. if x = e then y else e) s *)
    val unit_map =
      listSyntax.mk_map (Term.mk_abs (e, mk_cond (mk_eq (x, e), y, e)), s)
  in
  (* Z3's native Seq certificate uses its internal `seq.eq` and `seq.tail`
     witnesses for this list fact.  The parser reconstructs them as equality
     and DROP, so one generic theorem handles all element types.
     &(LENGTH s) = 0 \/ s = [EL 0 s] ++ DROP 1 s *)
  val head_tail_thm = Library.prove
    (mk_disj (mk_eq (int_length, intSyntax.zero_tm),
       mk_eq (s, listSyntax.mk_append
         (unit (listSyntax.mk_el (numSyntax.zero_tm, s)),
          listSyntax.mk_drop (numSyntax.term_of_int 1, s)))),
     Tactical.THEN (bossLib.tmCases_on s [],
       bossLib.RW_TAC (bossLib.srw_ss()) []))

  (* [x] = s ==> EL 0 s = x *)
  val nth_of_unit_thm = Library.prove
    (mk_imp (mk_eq (unit x, s),
             mk_eq (listSyntax.mk_el (numSyntax.zero_tm, s), x)),
     bossLib.METIS_TAC [listTheory.EL, listTheory.HD])

  (* smt_seq_nth [x] 0 = x *)
  val nth_unit_thm = Library.prove
    (mk_eq (seq_app "smt_seq_nth" [unit x, intSyntax.zero_tm], x),
     bossLib.RW_TAC (bossLib.srw_ss()) [HolSmtTheory.smt_seq_nth_def])

  (* SMT sequence nth is deliberately unspecified out of range.  Z3 rewrites
     it to an if whose out-of-range branch preserves that same application.
     Split on the complete semantic boundary once, then compare the resulting
     canonical forms.  This covers every element type and symbolic index
     without assigning a value outside the specified range.
     smt_seq_nth s i =
       if i < 0 \/ &(LENGTH s) <= i then smt_seq_nth s i else EL (Num i) s *)
  val nth_boundary_thm = Library.prove
    (mk_eq (nth_s_i,
       mk_cond (out_of_range, nth_s_i,
                listSyntax.mk_el (intSyntax.mk_Num i, s))),
     Tactical.THEN
       (bossLib.tmCases_on out_of_range [],
        Tactical.THEN
          (bossLib.ASM_SIMP_TAC (bossLib.srw_ss()) [],
           Tactical.THEN
             (Tactic.irule HolSmtTheory.smt_seq_nth_def,
              intLib.ARITH_TAC))))

  (* smt_seq_nth s i, the shape nth_boundary_thm is instantiated at *)
  val nth_pattern = nth_s_i

  (* A singleton-for-singleton replacement is a map, independently of
     element values. This checked shape law avoids repeated suffix/fuel
     discovery on wide concrete sequences.
     !s. smt_seq_replace_all_aux (LENGTH s) s [x] [y] =
         MAP (\e. if x = e then y else e) s *)
  val replacement_unit_aux_thm = Drule.SPEC_ALL (Library.prove
    (mk_forall (s,
       mk_eq (seq_app "smt_seq_replace_all_aux"
                [listSyntax.mk_length s, s, unit x, unit y],
              unit_map)),
     Tactical.THEN (bossLib.Induct,
       Tactical.THEN (bossLib.RW_TAC bossLib.std_ss
         [HolSmtTheory.smt_seq_replace_all_aux_def,listTheory.isPREFIX_THM,
          listTheory.LENGTH,listTheory.DROP_compute,listTheory.MAP,
          listTheory.APPEND],Rewrite.ASM_REWRITE_TAC []))))
  (* smt_seq_replace_all s [x] [y] = MAP (\e. if x = e then y else e) s *)
  val replacement_unit_thm = Library.prove
    (mk_eq (seq_app "smt_seq_replace_all" [s, unit x, unit y], unit_map),
     bossLib.SIMP_TAC bossLib.std_ss
       [HolSmtTheory.smt_seq_replace_all_def,replacement_unit_aux_thm,
        listTheory.NOT_CONS_NIL])
  end

  (* The continuation belongs to the current compact replay invocation.
     Hide its exceptions from tactic/search filtering, restoring the exact
     primary exception only after all local alternatives have unwound. *)
  val scalar_compset =
    let
      val local_set = computeLib.copy (computeLib.the_compset ())
      fun remove (((name,thy),_),set) =
        if thy="HolSmt" andalso String.isPrefix "smt_seq_" name then
          computeLib.scrub_const set
            (Term.prim_mk_const {Thy=thy,Name=name})
        else set
      (* Also stop Seq operations introduced by a scalar definition, not
         just operations visible in the original scalar operand. Never
         mutate the ordinary computation set. *)
    in List.foldl remove local_set (computeLib.listItems local_set) end

  val scalar_rewrite_rules = Redblackmap.fromList
    (Portable.pair_compare (String.compare,String.compare))
    (List.map (fn (key,actions) => (key,List.concat (List.map
      (fn clauses.RRules ths => ths | clauses.Conversion _ => []) actions)))
      (computeLib.listItems scalar_compset))

  fun checked_procedures check =
  let
    exception AdmissionFailure of exn
    val interrupted = ref (NONE : exn option)
    val computing_scalars = ref false
    val matching_lists = ref true
    fun admit tm = check tm handle primary => raise AdmissionFailure primary
    fun protect f x = f x handle AdmissionFailure primary =>
      SmtReplayArithmetic.propagate_admission_error primary
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
        val _ = if !matching_lists then () else raise Conv.UNCHANGED
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
    fun scalar_literal tm = numSyntax.is_numeral tm orelse
      intSyntax.is_int_literal tm orelse realSyntax.is_real_literal tm orelse
      wordsSyntax.is_word_literal tm
    fun scalar_operand tm =
      let
        val (head,_) = boolSyntax.strip_comb tm
        (* Compute scalar elements in every rung, not only replacement.
           A scalar computation may consume a list (word_from_bin_list is
           one example). Its admitted operand is not the enclosing sequence
           obligation. Leave list spines, accessors and Boolean structure
           with the checked constructor/rewrite driver. *)
        val _ = if Term.is_comb tm andalso
            not (scalar_literal tm) andalso
            not (Lib.can Type.dom_rng (Term.type_of tm)) andalso
            not (Lib.can listSyntax.dest_list_type (Term.type_of tm)) andalso
            not (named "min" ["=","==>"] head) andalso
            not (named "list" ["LENGTH","EL","HD","LAST","NULL",
              "isPREFIX","FOLDL","FOLDR"] head) andalso
            not (named "rich_list" ["IS_SUBLIST","IS_SUFFIX"] head) andalso
            not (named "HolSmt" ["smt_seq_nth","smt_seq_indexof"] head)
            andalso not (named "bool" ["=","COND","/\\","\\/",
              "==>","~","!","?"] head)
          then () else raise Conv.UNCHANGED
        val _ = if null (Term.free_vars tm) then ()
          else raise Conv.UNCHANGED
        (* A scalar wrapper must not smuggle a recursive Seq computation
           into CBV. Traverse first reduces those children with the checked
           constructor driver. Literal list arguments remain supported. *)
        fun sequence_computation node =
          Term.is_const node andalso
          let val {Thy,Name,...} = Term.dest_thy_const node
          in (Thy="HolSmt" andalso String.isPrefix "smt_seq_" Name) orelse
             (Thy="list" andalso List.exists (Lib.equal Name)
               ["APPEND","LENGTH","TAKE","DROP","EL","MAP","FOLDL",
                "FOLDR","REVERSE","isPREFIX","LUPDATE","HD","LAST",
                "NULL","SNOC"]) orelse
             (Thy="rich_list" andalso List.exists (Lib.equal Name)
               ["IS_SUBLIST","IS_SUFFIX"])
          end
      in if mentions sequence_computation tm then
          raise Conv.UNCHANGED else () end
    fun scalar_step tm =
      let
        val _ = if !computing_scalars then () else raise Conv.UNCHANGED
        val _ = scalar_operand tm
        val _ = admit tm
        val result = Conv.CHANGED_CONV
          (computeLib.CBV_CONV scalar_compset) tm
        val (left,right) = boolSyntax.dest_eq (Thm.concl result)
        val _ = List.app admit (left::right::Thm.hyp result)
      in result end
    (* Optional shape discovery must also compose with small controllers
       (e.g. LENGTH (TAKE (I 0) xs)). Use rewrite equations only: arbitrary
       computation conversions could expand EXP in one opaque native call.
       Every beta/rewrite substitution is prospectively bounded. Exhaustion
       is a private probe miss, never an admission/Work callback failure. *)
    fun bounded_scalar () =
      let
        exception Miss
        exception Exhausted
        val remaining = ref 4096
        val allowance = 128
        fun require true = () | require false = raise Miss
        fun attempt f = SOME (f ()) handle Miss => NONE
        fun fits sigma tm =
          let
            (* Stock dest_abs opens its entire body. Establish the raw
               bound without opening any binder before the substitution
               forecast below uses the native view. *)
            val _ = require (Option.isSome
              (SmtReplayImport.bounded_raw_size allowance tm))
            val left = ref allowance
            fun scan sigma tm =
              let val _ = require (!left > 0)
                  val _ = left := !left - 1
              in if Term.is_var tm then
                   (case List.find
                       (fn {redex,...} => Term.aconv redex tm) sigma of
                      NONE => ()
                    | SOME {residue,...} => scan [] residue)
                 else if Term.is_comb tm then
                   let val (f,x) = Term.dest_comb tm
                   in scan sigma f;scan sigma x end
                 else if Term.is_abs tm then
                   scan sigma (#2 (Term.dest_abs tm))
                 else () end
          in (scan sigma tm;true) end handle Miss => false
        fun types_fit types tm =
          let
            fun annotation ty =
              let val left = ref allowance
                  fun scan substitutions ty =
                    (require (!left > 0);left := !left - 1;
                     if Type.is_vartype ty then
                       (case List.find (fn {redex,...} =>
                           Type.compare (redex,ty)=EQUAL) substitutions of
                          NONE => ()
                        | SOME {residue,...} => scan [] residue)
                     else List.app (scan substitutions)
                       (#2 (Type.dest_type ty)))
              in scan types ty end
            fun walk tm =
              (annotation (Term.type_of tm);
               if Term.is_comb tm then
                 let val (f,x) = Term.dest_comb tm in walk f;walk x end
               else if Term.is_abs tm then
                 let val (v,b) = Term.dest_abs tm in walk v;walk b end
               else ())
          in walk tm;true end handle Miss => false
        fun probe tm =
          let
            val local_left = ref 2048
            fun spend () =
              if !remaining = 0 orelse !local_left = 0 then raise Exhausted
              else (remaining := !remaining - 1;
                    local_left := !local_left - 1)
            fun checked th =
              let val (l,r) = boolSyntax.dest_eq (Thm.concl th)
                  val _ = require (fits [] r)
                  val _ = List.app admit (l::r::Thm.hyp th)
                  val _ = require (not (Term.aconv l r))
              in th end
            fun rewrite tm fact =
              let
                val _ = spend ()
                val _ = require (null (Thm.hyp fact) andalso
                  fits [] (Thm.concl fact))
                val _ = admit (Thm.concl fact)
                val fact = Drule.SPEC_ALL fact
                val (l,r) = case Lib.total boolSyntax.dest_eq
                    (Thm.concl fact) of SOME sides => sides
                  | NONE => raise Miss
                val (sigma,types) = Term.match_term l tm
                  handle Feedback.HOL_ERR _ => raise Miss
                val _ = require (types_fit types (Thm.concl fact))
                val typed_rhs = Term.inst types r
                val _ = require (fits sigma typed_rhs)
                val _ = admit typed_rhs
                val result = Thm.INST sigma (Thm.INST_TYPE types fact)
                val left = boolSyntax.lhs (Thm.concl result)
              in checked (Thm.TRANS (Thm.ALPHA tm left) result) end
            fun root tm =
              if Term.is_comb tm andalso Term.is_abs (Term.rator tm) then
                let val (v,body) = Term.dest_abs (Term.rator tm)
                    val _ = require (fits
                      [{redex=v,residue=Term.rand tm}] body)
                in checked (Thm.BETA_CONV tm) end
              else
                let
                  val head = #1 (boolSyntax.strip_comb tm)
                  val _ = require (Term.is_const head)
                  val {Name,Thy,...} = Term.dest_thy_const head
                  val facts = Option.getOpt
                    (Redblackmap.peek (scalar_rewrite_rules,(Name,Thy)),[])
                  fun first [] = raise Miss
                    | first (th::ths) = rewrite tm th
                        handle Miss => first ths
                in first facts end
            fun step tm =
              let val _ = spend ()
                  val _ = require (fits [] tm)
                  val _ = require (not (scalar_literal tm))
                  val _ = admit tm
                  val direct = attempt (fn () => root tm)
                  fun projection th =
                    let val result = boolSyntax.rhs (Thm.concl th)
                    in scalar_literal result orelse
                       Term.aconv result boolSyntax.T orelse
                       Term.aconv result boolSyntax.F orelse
                       List.exists (Term.aconv result)
                         (#2 (boolSyntax.strip_comb tm)) end
                  fun descend () =
                    if Term.is_comb tm then
                      let val (f,x) = Term.dest_comb tm
                      in case attempt (fn () => step f) of
                          SOME th => checked (Thm.MK_COMB (th,Thm.REFL x))
                        | NONE => checked (Thm.MK_COMB (Thm.REFL f,step x))
                      end
                    else raise Miss
              in case direct of SOME th =>
                   if projection th then th
                   else (descend () handle Miss => th)
                 | NONE => descend () end
            fun normalise tm = case attempt (fn () => step tm) of
                NONE => Thm.REFL tm
              | SOME th => Thm.TRANS th
                  (normalise (boolSyntax.rhs (Thm.concl th)))
            val _ = require (fits [] tm)
            val _ = scalar_operand tm handle Conv.UNCHANGED => raise Miss
            val _ = admit tm
          in SOME (checked (normalise tm)) end
          handle Miss => NONE | Exhausted => NONE
      in probe end

    (* Compute bounded scalar occurrences before asking the list matcher to
       compare spines. Otherwise every element rewrite restarts discovery
       on all the remaining unequal list suffixes. Reuse checked equalities
       for shared syntax; never run a recursive CBV/SIMP on the sequence.
       Application transport is kernel congruence, not matching/INST. *)
    fun scalar_occurrences_raw tm =
      Lib.with_flag (computing_scalars,true) (fn tm =>
      let
        val saved = ref (Redblackmap.mkDict Term.compare)
        fun walk term =
          case Redblackmap.peek (!saved,term) of SOME result => result
          | NONE =>
            let
              val literal = scalar_literal term
              val direct = if literal then NONE else SOME (scalar_step term)
                handle Conv.UNCHANGED => NONE | Feedback.HOL_ERR _ => NONE
              (* Only explicit sequence constructors are strict here.
                 In particular, LENGTH/TAKE/COND nested in an element must
                 first use their demand-driven constructor laws, not force
                 values that those laws can discard. Partial applications
                 retain the same head while MK_COMB transports each child. *)
              val (head,_) = boolSyntax.strip_comb term
              val strict = named "list"
                  ["CONS","APPEND","SNOC","REVERSE"] head orelse
                named "HolSmt" ["smt_seq_replace_all"] head
              val result = case direct of SOME th => SOME th
                | NONE => if strict andalso Term.is_comb term then
                    let
                      val (f,x) = Term.dest_comb term
                      val left = walk f val right = walk x
                    in case (left,right) of (NONE,NONE) => NONE
                      | _ =>
                        let
                          val th = Thm.MK_COMB
                            (Option.getOpt (left,Thm.REFL f),
                             Option.getOpt (right,Thm.REFL x))
                        in SOME th end
                    end
                  else NONE
              val _ = saved := Redblackmap.insert (!saved,term,result)
            in result end
        (* The batch selector admits only equalities. Do not recurse into
           arbitrary Boolean elements as though their children were strict. *)
        val (l,r) = boolSyntax.dest_eq tm
        val left = walk l val right = walk r
        val result = case (left,right) of (NONE,NONE) => NONE
          | _ => SOME (Thm.MK_COMB
              (Thm.AP_TERM (Term.rator (Term.rator tm))
                (Option.getOpt (left,Thm.REFL l)),
               Option.getOpt (right,Thm.REFL r)))
        (* MK_COMB only transports the checked scalar equalities. It does
           not match, simplify or open binders on its application operands.
           Admit the completed sides ONCE before the next generic operation,
           rather than rescan every growing list suffix along the way. *)
        val _ = Option.app (fn th =>
          let val (l,r) = boolSyntax.dest_eq (Thm.concl th)
          in List.app admit (l::r::Thm.hyp th) end) result
      in result end) tm
    fun local_step tm =
      (replacement_step tm
        handle Conv.UNCHANGED =>
          (list_step tm handle Conv.UNCHANGED => scalar_step tm
            | Feedback.HOL_ERR _ => scalar_step tm)
          | Feedback.HOL_ERR _ =>
          (list_step tm handle Conv.UNCHANGED => scalar_step tm
            | Feedback.HOL_ERR _ => scalar_step tm))
      handle AdmissionFailure primary =>
        (* Traverse discards arbitrary conversion exceptions. Its supported
           interrupt escape must be translated outside that boundary. *)
        (interrupted := SOME primary;raise Portable.Interrupt)
    fun with_rewrites facts prove =
      let
        fun restore () = case !interrupted of NONE => ()
          | SOME primary =>
              (interrupted := NONE;raise AdmissionFailure primary)
        val _ = List.app (fn th => ignore (theorem th)) facts
        val result = SmtDatatypeProve.with_checked_rewrites_using admit
          (fn () => simpLib.++ (seq_ss,simpLib.rewrites facts))
          local_step prove handle primary => (restore ();raise primary)
        val _ = restore ()
      in result end
    fun simplify_raw facts tm =
      (admit tm;with_rewrites facts (fn ss =>
        let val result = simpLib.SIMP_CONV ss [] tm
            val (left,right) = boolSyntax.dest_eq (Thm.concl result)
            val _ = List.app admit (left::right::Thm.hyp result)
        in result end))

    (* Keep elements opaque while retaining the checked list relationships.
       The caller selects the non-computational or full demanded procedure. *)
    fun length_step safe term =
          let
            val (head,args) = boolSyntax.strip_comb term
            val _ = if is_length head andalso length args=1 then ()
              else raise Conv.UNCHANGED
            val bindings = ref (Redblackmap.mkDict Term.compare)
            fun atom actual = case Redblackmap.peek (!bindings,actual) of
                SOME hole => hole
              | NONE => let val hole = Term.genvar (Term.type_of actual)
                  in bindings := Redblackmap.insert
                       (!bindings,actual,hole);hole end
            (* The speculative pass uses only shape equations and opaque
               scalar computations and large literals. Small literals keep
               index/constructor relationships without duplicating a large
               beta argument. This is optional discovery, not a new input
               limit. Preserve generic application/binder syntax; there is
               no whitelist of controllers or list wrappers. *)
            fun skeleton bound actual =
              if List.exists (fn v => Term.aconv v actual) bound orelse
                  Term.aconv actual boolSyntax.T orelse
                  Term.aconv actual boolSyntax.F orelse
                  (scalar_literal actual andalso Term.term_size actual <= 32)
                then actual
              else if listSyntax.is_nil actual then actual
              else if not (Lib.can listSyntax.dest_list_type
                    (Term.type_of actual)) andalso
                  not (Lib.can Type.dom_rng (Term.type_of actual)) andalso
                  not (List.exists (fn v => Term.free_in v actual) bound)
                then atom actual
              else if listSyntax.is_cons actual then
                let val (h,t) = listSyntax.dest_cons actual
                in listSyntax.mk_cons
                  (skeleton bound h,skeleton bound t) end
              else if Term.is_abs actual then
                let val (v,body) = Term.dest_abs actual
                    val fresh = Term.variant (Term.all_vars term @ bound @
                      List.map #2 (Redblackmap.listItems (!bindings))) v
                    val body = Term.subst [{redex=v,residue=fresh}] body
                in Term.mk_abs (fresh,skeleton (fresh::bound) body) end
              else if Term.is_comb actual then
                let val (f,x) = Term.dest_comb actual
                in Term.mk_comb (skeleton bound f,skeleton bound x) end
              else if Term.is_const actual andalso
                  Lib.can Type.dom_rng (Term.type_of actual) then actual
              else atom actual
            val shapes = ref (Redblackmap.mkDict Term.compare)
            fun shape actual =
              case Redblackmap.peek (!shapes,actual) of SOME result => result
              | NONE =>
                let val result =
                  if listSyntax.is_cons actual then
                    let val (h,t) = listSyntax.dest_cons actual
                    in listSyntax.mk_cons (atom h,shape t) end
                  else if safe then skeleton [] actual
                  else if Term.is_comb actual andalso
                      not (scalar_literal actual) then
                    let val (f,x) = Term.dest_comb actual
                    in Term.mk_comb (shape f,shape x) end
                  else actual
                  val _ = shapes := Redblackmap.insert
                    (!shapes,actual,result)
                in result end
            val schema = Term.mk_comb (head,shape (hd args))
            val _ = admit schema
            val result = Lib.with_flag (computing_scalars,false)
              (simplify_raw list_rewrites) schema
            val _ = if Term.aconv (boolSyntax.lhs (Thm.concl result))
                (boolSyntax.rhs (Thm.concl result))
              then raise Conv.UNCHANGED else ()
            val result = Thm.INST (List.map (fn (actual,hole) =>
              {redex=hole,residue=actual})
              (Redblackmap.listItems (!bindings))) result
            val (l,r) = boolSyntax.dest_eq (Thm.concl result)
            val _ = if Term.aconv l term then () else
              raise ERR "length_step" "shape restoration changed its source"
            val _ = List.app admit (l::r::Thm.hyp result)
          in result end

    (* First expose guard-independent shapes without computing scalars.
       Then normalize demanded controllers on opaque branch/list operands
       before walking anything those controllers may discard. *)
    fun shape_lengths tm =
      let
        (* Prove only a root projection or constant result on opaque
           operands. Never inspect the list discarded by prefix/TAKE/COND. *)
        fun project term =
          let
            val (head,args) = boolSyntax.strip_comb term
            val conditional = named "bool" ["COND"] head andalso
              length args=3
            val indexed = named "list" ["TAKE","DROP"] head andalso
              length args=2
            val _ = if conditional orelse indexed orelse
                named "list" ["isPREFIX"] head orelse
                named "rich_list" ["IS_SUBLIST","IS_SUFFIX"] head
              then () else raise Conv.UNCHANGED
            val bindings = ref (Redblackmap.mkDict Term.compare)
            fun operand actual =
              if listSyntax.is_nil actual orelse scalar_literal actual
                  orelse Term.aconv actual boolSyntax.T orelse
                  Term.aconv actual boolSyntax.F then actual
              else case Redblackmap.peek (!bindings,actual) of
                  SOME hole => hole
                | NONE => let val hole = Term.genvar (Term.type_of actual)
                    in bindings := Redblackmap.insert
                         (!bindings,actual,hole);hole end
            val schema = Term.list_mk_comb (head,List.map operand args)
            val _ = admit schema
            val proof = Lib.with_flag (computing_scalars,false)
              (simplify_raw (listTheory.isPREFIX_THM :: list_rewrites))
              schema
            val result = boolSyntax.rhs (Thm.concl proof)
            val holes = Redblackmap.listItems (!bindings)
            val _ = if Term.aconv result boolSyntax.T orelse
                Term.aconv result boolSyntax.F orelse
                listSyntax.is_nil result orelse scalar_literal result orelse
                List.exists (fn (_,hole) => Term.aconv result hole) holes
              then () else raise Conv.UNCHANGED
            val proof = Thm.INST (List.map (fn (actual,hole) =>
              {redex=hole,residue=actual}) holes) proof
            val (l,r) = boolSyntax.dest_eq (Thm.concl proof)
            val _ = List.app admit (l::r::Thm.hyp proof)
          in proof end
        (* Only non-computational branch shapes are visited eagerly.
           Recheck projection after child transport, before any controller
           or unreachable scalar is handed to the ordinary simplifier. *)
        val safe_saved = ref (Redblackmap.mkDict Term.compare)
        val scalar_probe = bounded_scalar ()
        fun safe_step term =
          project term handle Conv.UNCHANGED =>
          (length_step true term handle Conv.UNCHANGED =>
            case scalar_probe term of SOME th => th
              | NONE => raise Conv.UNCHANGED)
        fun safe_walk term =
          case Redblackmap.peek (!safe_saved,term) of SOME th => th
          | NONE =>
              let
                val direct = SOME (safe_step term)
                  handle Conv.UNCHANGED => NONE | Feedback.HOL_ERR _ => NONE
                val result = case direct of SOME th => SOME th
                  | NONE => if Term.is_comb term andalso
                      not (scalar_literal term) then
                      let
                        val (f,x) = Term.dest_comb term
                        val left = safe_walk f
                        val start = Option.map
                          (fn th => Thm.MK_COMB (th,Thm.REFL x)) left
                        (* A newly exposed controller may erase x. Do not
                           even spend the bounded scalar-probe allowance
                           on that unreachable operand. *)
                        val erased = case start of NONE => NONE
                          | SOME th => SOME (Thm.TRANS th
                              (project (boolSyntax.rhs (Thm.concl th))))
                              handle Conv.UNCHANGED => NONE
                                | Feedback.HOL_ERR _ => NONE
                      in case erased of SOME th => SOME th
                        | NONE =>
                          let val right = safe_walk x
                          in case (left,right) of (NONE,NONE) => NONE
                            | _ => SOME (Thm.MK_COMB
                                (Option.getOpt (left,Thm.REFL f),
                                 Option.getOpt (right,Thm.REFL x))) end
                      end
                    else NONE
                val result = case result of NONE => NONE | SOME th =>
                  let val target = boolSyntax.rhs (Thm.concl th)
                      val rest = SOME (safe_step target)
                        handle Conv.UNCHANGED => NONE
                          | Feedback.HOL_ERR _ => NONE
                  in case rest of NONE => SOME th
                    | SOME rest =>
                        let val proof = Thm.TRANS th rest
                        in case safe_walk (boolSyntax.rhs (Thm.concl rest)) of
                            NONE => SOME proof
                          | SOME final => SOME (Thm.TRANS proof final) end
                  end
                val _ = safe_saved := Redblackmap.insert
                  (!safe_saved,term,result)
              in result end
        val saved = ref (Redblackmap.mkDict Term.compare)
        fun discard_step term =
          project term handle Conv.UNCHANGED =>
          let
            val (head,args) = boolSyntax.strip_comb term
            val _ = if (named "bool" ["COND"] head andalso length args=3)
                orelse (named "list" ["TAKE","DROP"] head andalso
                  length args=2) then () else raise Conv.UNCHANGED
            (* This controller is now demanded, after non-forcing branch
               shape discovery and root projection. Use the complete old
               checked procedure, not a finite controller grammar. Never
               descend into the operands it might erase. *)
            val original = hd args
            val _ = admit original
            val guard = simplify_raw list_rewrites original
            val _ = if Term.aconv original
                (boolSyntax.rhs (Thm.concl guard)) then
                raise Conv.UNCHANGED else ()
            val preparation = List.foldl (fn (arg,th) =>
                Thm.MK_COMB (th,Thm.REFL arg))
              (Thm.MK_COMB (Thm.REFL head,guard)) (tl args)
            val prepared = boolSyntax.rhs (Thm.concl preparation)
            val _ = admit prepared
          in Thm.TRANS preparation (project prepared)
               handle Conv.UNCHANGED => preparation end
        fun walk term =
          case Redblackmap.peek (!saved,term) of SOME result => result
          | NONE =>
            let
              fun length () = SOME (length_step false term)
                handle Conv.UNCHANGED => NONE | Feedback.HOL_ERR _ => NONE
              val direct = SOME (discard_step term)
                handle Conv.UNCHANGED => length ()
                  | Feedback.HOL_ERR _ => length ()
              val result = case direct of SOME th =>
                    (case walk (boolSyntax.rhs (Thm.concl th)) of
                       NONE => SOME th
                     | SOME rest => SOME (Thm.TRANS th rest))
                | NONE => if Term.is_comb term andalso
                    not (scalar_literal term) then
                    let
                      val (f,x) = Term.dest_comb term
                      val left = walk f
                      val start = Option.map
                        (fn th => Thm.MK_COMB (th,Thm.REFL x)) left
                      val discarded = case start of NONE => NONE
                        | SOME th => SOME (discard_step
                            (boolSyntax.rhs (Thm.concl th)))
                            handle Conv.UNCHANGED => NONE
                              | Feedback.HOL_ERR _ => NONE
                    in case discarded of SOME th =>
                        let val proof = Thm.TRANS (valOf start) th
                            val rest = walk (boolSyntax.rhs (Thm.concl th))
                        in SOME (case rest of NONE => proof
                          | SOME rest => Thm.TRANS proof rest) end
                      | NONE =>
                        let val right = walk x
                        in case (left,right) of (NONE,NONE) => NONE
                          | _ => SOME (Thm.MK_COMB
                              (Option.getOpt (left,Thm.REFL f),
                               Option.getOpt (right,Thm.REFL x))) end
                    end
                  else NONE
              val _ = saved := Redblackmap.insert (!saved,term,result)
            in result end
      in if mentions is_length tm then
           let val preliminary = safe_walk tm
               val target = case preliminary of NONE => tm
                 | SOME th => boolSyntax.rhs (Thm.concl th)
               val _ = admit target
               val result = case (preliminary,walk target) of
                   (NONE,rest) => rest
                 | (shape,NONE) => shape
                 | (SOME shape,SOME rest) => SOME (Thm.TRANS shape rest)
               val _ = Option.app (fn th =>
                 let val (l,r) = boolSyntax.dest_eq (Thm.concl th)
                 in List.app admit (l::r::Thm.hyp th) end) result
           in result end
         else NONE end
    fun after_shapes conversion tm =
      case shape_lengths tm of NONE => conversion tm
      | SOME shape =>
          let val target = boolSyntax.rhs (Thm.concl shape)
              val rest = conversion target
                handle Conv.UNCHANGED => Thm.REFL target
          in Thm.TRANS shape rest end
    fun simplify facts = after_shapes (simplify_raw facts)
    fun scalar_occurrences tm =
      case shape_lengths tm of NONE => scalar_occurrences_raw tm
      | SOME shape =>
          (case scalar_occurrences_raw (boolSyntax.rhs (Thm.concl shape)) of
             NONE => SOME shape
           | SOME scalar => SOME (Thm.TRANS shape scalar))

    (* Bulk scalar computation is safe only for a plain list equality with
       no shared computation to cancel, or a concrete nonempty replacement
       whose pattern/replacement have no computations. Other searches,
       predicates, accessors and conditionals use demand-driven rewriting:
       rewriting a guard can discard an arbitrarily expensive element.
       This is discovery, never proof authority; list_step still proves the
       result after the checked scalar equalities have been transported. *)
    fun scalar_batch_candidate tm =
      if not (boolSyntax.is_eq tm) then false else
      let
        val (l,r) = boolSyntax.dest_eq tm
        fun spine term =
          if Term.is_var term orelse listSyntax.is_nil term then true
          else if listSyntax.is_cons term then
            spine (#2 (listSyntax.dest_cons term))
          else if listSyntax.is_append term then
            let val (a,b) = listSyntax.dest_append term
            in spine a andalso spine b end
          else if listSyntax.is_reverse term then
            spine (listSyntax.dest_reverse term)
          else if listSyntax.is_snoc term then
            spine (#2 (listSyntax.dest_snoc term))
          else false
        fun computations term saved =
          if scalar_literal term then saved
          else if Lib.can scalar_operand term then Redblackset.add (saved,term)
          else if Term.is_comb term then
            let val (f,x) = Term.dest_comb term
            in computations x (computations f saved) end
          else saved
        fun replacement term =
          let
            val (head,args) = boolSyntax.strip_comb term
            val (source,pattern,residue) = case args of [s,p,r] => (s,p,r)
              | _ => raise Conv.UNCHANGED
            val _ = if named "HolSmt" ["smt_seq_replace_all"] head then ()
              else raise Conv.UNCHANGED
            val (elements,_) = listSyntax.dest_list source
            val (wanted,_) = listSyntax.dest_list pattern
            val _ = ignore (listSyntax.dest_list residue)
          in not (null elements) andalso not (null wanted) andalso
             length wanted <= length elements andalso
             Redblackset.isEmpty (computations pattern
               (computations residue (Redblackset.empty Term.compare)))
          end handle Conv.UNCHANGED => false | Feedback.HOL_ERR _ => false
      in Lib.can listSyntax.dest_list_type (Term.type_of l) andalso
         (spine l orelse replacement l) andalso
         (spine r orelse replacement r) andalso
         not (mentions (fn t => Term.is_abs t orelse
           named "bool" ["COND"] t) tm) andalso
         Redblackset.isEmpty (Redblackset.intersection
           (computations l (Redblackset.empty Term.compare),
            computations r (Redblackset.empty Term.compare)))
      end

  (* Cheap discovery only: flattened constructor tokens can select an
     opaque-element cancellation without evaluating those elements. A
     mismatch must not enter the expensive checked list matcher before
     scalar computation. The selected proof still comes from list_step. *)
  fun structural_candidate t =
    if not (boolSyntax.is_eq t) then false else
    let
      val (l,r) = boolSyntax.dest_eq t
      val _ = if Lib.can listSyntax.dest_list_type (Term.type_of l) then ()
        else raise Conv.UNCHANGED
      val holes = ref (Redblackmap.mkDict Term.compare)
      fun atom tm = case Redblackmap.peek (!holes,tm) of SOME v => v
        | NONE => let val v = Term.genvar (Term.type_of tm)
                  in holes := Redblackmap.insert (!holes,tm,v);v end
      fun walk reversed term rest =
        if listSyntax.is_nil term then rest
        else if listSyntax.is_append term then
          let val (a,b) = listSyntax.dest_append term
          in if reversed then walk true b (walk true a rest)
             else walk false a (walk false b rest) end
        else if listSyntax.is_cons term then
          let val (a,b) = listSyntax.dest_cons term
              val token = (0,atom a)
          in if reversed then walk true b (token::rest)
             else token::walk false b rest end
        else if listSyntax.is_reverse term then
          walk (not reversed) (listSyntax.dest_reverse term) rest
        else if listSyntax.is_snoc term then
          let val (a,b) = listSyntax.dest_snoc term
              val token = (0,atom a)
          in if reversed then token::walk true b rest
             else walk false b (token::rest) end
        else (if reversed then 2 else 1,atom term)::rest
      fun same ([],[]) = true
        | same ((k,a)::xs,(j,b)::ys) =
            k=j andalso Term.compare (a,b)=EQUAL andalso same (xs,ys)
        | same _ = false
    in same (walk false l [],walk false r []) end
    handle Conv.UNCHANGED => false

  fun simp_prove_with rewrites t =
    SmtResource.with_resource_step_time "Sequence" "seq-simp" (fn () =>
      let
        val _ = SmtResource.check_resource_goal "Sequence" "seq-simp" t
        val _ = admit t
        (* Discover a complete constructor/segment cancellation before
           building a general simplifier. This is the same checked list
           procedure used by its fallback, on the same occurrence schema. *)
        fun local_result target = SOME (list_step target)
          handle Conv.UNCHANGED => NONE | Feedback.HOL_ERR _ => NONE
        val structural = if structural_candidate t then local_result t
          else NONE
        fun computing () =
          let
            val residual = case structural of NONE => t
              | SOME th => boolSyntax.rhs (Thm.concl th)
            fun compute () = Lib.with_flag (computing_scalars,true)
              (fn () =>
              let
                val scalars = if scalar_batch_candidate residual then
                    scalar_occurrences residual else NONE
                val target = case scalars of NONE => residual
                  | SOME th => boolSyntax.rhs (Thm.concl th)
                val normalized = if Term.aconv target boolSyntax.T then
                    Thm.REFL target
                  else case local_result target of
                    SOME th =>
                      let val rest = boolSyntax.rhs (Thm.concl th)
                      in if Term.aconv rest boolSyntax.T then th
                         else (Thm.TRANS th (simplify rewrites rest)
                           handle Conv.UNCHANGED => th) end
                  | NONE => (simplify rewrites target
                      handle Conv.UNCHANGED => raise ERR "simp_prove_with"
                        "no rewrite applies to this rung")
              in case scalars of NONE => normalized
                | SOME th => Thm.TRANS th normalized end) ()
            val normalized = compute ()
          in case structural of NONE => normalized
            | SOME th => Thm.TRANS th normalized end
        (* A cancelling opaque element need never be computed. In
           particular its value may exceed this invocation's admission. *)
        val normalized = case structural of SOME th =>
            if Term.aconv (boolSyntax.rhs (Thm.concl th)) boolSyntax.T
            then th else computing ()
          | NONE => computing ()
        val t' = boolSyntax.rhs (Thm.concl normalized)
        val _ = admit t'
        val thm = tautLib.TAUT_PROVE t'
          handle Feedback.HOL_ERR _ => intLib.ARITH_PROVE t'
      in theorem (Thm.EQ_MP (Thm.SYM normalized) thm) end) ()

  fun simp_prove t = simp_prove_with list_rewrites t

  fun nth_unit_prove t =
    let
      val _ = admit t
      val (lhs,rhs) = boolSyntax.dest_eq t
      val (head,args) = boolSyntax.strip_comb lhs
      val (sequence,index) = case args of [s,i] => (s,i)
        | _ => raise Conv.UNCHANGED
      val _ = if named "HolSmt" ["smt_seq_nth"] head andalso
          Term.aconv index ``0:int`` then () else raise Conv.UNCHANGED
      val (elements,ty) = listSyntax.dest_list sequence
      val element = case elements of [x] => x | _ => raise Conv.UNCHANGED
      val _ = List.app admit [element,rhs,index]
      val x = Term.genvar ty
      val y = if Term.compare (element,rhs)=EQUAL then x else Term.genvar ty
      val schema = boolSyntax.mk_eq
        (Term.list_mk_comb (head,[listSyntax.mk_list ([x],ty),index]),y)
      val _ = admit schema
      val _ = ignore (theorem nth_unit_thm)
      val local_proof = theorem (Drule.INST_TY_TERM
        (Term.match_term (Thm.concl nth_unit_thm) schema) nth_unit_thm)
      val result = Thm.INST [{redex=x,residue=element}] local_proof
    in theorem result end
    handle Conv.UNCHANGED => raise ERR "nth_unit_prove"
      "not a singleton nth equality"

  fun nth_boundary_prove t =
    let
      fun is_nth_application tm =
        case boolSyntax.strip_comb tm of
          (head, [_, _]) => named "HolSmt" ["smt_seq_nth"] head
        | _ => false
      val _ = admit t
      val pattern = nth_pattern
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
      fun search [] = raise ERR "contains_append_witness_prove"
            "no checked append witness"
        | search (candidate::rest) = prove_split candidate
            handle Feedback.HOL_ERR detail =>
              if SmtResource.is_resource_gate detail then
                raise Feedback.HOL_ERR detail else search rest
              | Conv.UNCHANGED => search rest
    in
      search (preferred @ others)
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
        (fn t =>
          let
            val scalars = if scalar_batch_candidate t then
                scalar_occurrences t else NONE
            val target = case scalars of NONE => t
              | SOME th => boolSyntax.rhs (Thm.concl th)
            fun wide_unit term =
              let
                val (head,args) = boolSyntax.strip_comb term
                val (s,p,r) = case args of [s,p,r] => (s,p,r)
                  | _ => raise Conv.UNCHANGED
                val _ = if named "HolSmt" ["smt_seq_replace_all"] head
                  then () else raise Conv.UNCHANGED
                val (elements,_) = listSyntax.dest_list s
              in length elements >= 8 andalso
                 length (#1 (listSyntax.dest_list p)) = 1 andalso
                 length (#1 (listSyntax.dest_list r)) = 1
              end handle Conv.UNCHANGED => false | Feedback.HOL_ERR _ => false
            val facts = if mentions wide_unit target then
                replacement_unit_thm::listTheory.MAP::
                  (list_rewrites @ replace_all_rewrites)
              else replace_all_rewrites
            fun normalise matching =
              Lib.with_flag (matching_lists,matching) (fn () =>
                let val th = Lib.with_flag (computing_scalars,true)
                      (simplify facts) target
                in if Term.aconv (boolSyntax.rhs (Thm.concl th)) boolSyntax.T
                   then th
                   else raise ERR "ground_replace_all_prove"
                     "constructor simplification did not close" end) ()
            (* Concrete replacement reduces by its constructor laws. Avoid
               rediscovering a full list match at every changing suffix.
               Retain the original matcher for actual proof misses. *)
            val normalized = normalise false
              handle Feedback.HOL_ERR detail =>
                if SmtResource.is_resource_gate detail then
                  raise Feedback.HOL_ERR detail else normalise true
                | Conv.UNCHANGED => normalise true
            val normalized = case scalars of NONE => normalized
              | SOME th => Thm.TRANS th normalized
          in Drule.EQT_ELIM normalized end) t
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
             (fn ss =>
               let val shape = shape_lengths t
                   val target = case shape of NONE => t
                     | SOME th => boolSyntax.rhs (Thm.concl th)
                   val result = theorem (Tactical.TAC_PROOF ((context,target),
                     checked_tactic (bossLib.ASM_SIMP_TAC ss [])))
               in case shape of NONE => result
                 | SOME th => theorem (Thm.EQ_MP (Thm.SYM th) result)
               end))) ()
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
        (* Recursive replacement has its own checked driver. Do not first
           spend the same Work on generic unit/append rungs that lack its
           defining laws, only to rediscover the same suffixes there. *)
        next (fn () =>
          if mentions (named "HolSmt" ["smt_seq_replace_all"]) t then
            ground_replace_all_prove t
          else raise ERR "seq_prove" "not a replacement") (fn () =>
        next (fn () => nth_unit_prove t) (fn () =>
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
          (fn () => unsupported t))))))))))
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
