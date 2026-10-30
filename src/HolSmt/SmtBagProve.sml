(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for Z3's Int-array bag encoding. *)

structure SmtBagProve :> SmtBagProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtBagProve"

  fun named thy names tm =
    Term.is_const tm andalso
    let val {Thy, Name, ...} = Term.dest_thy_const tm
    in Thy = thy andalso List.exists (Lib.equal Name) names end

  (* Classification keeps the ordinary non-family bypass. Before either
     the predicate or the shared DAG walker opens a binder, admit its full
     annotation under the existing primitive-Type allowance. This is local
     syntax policy, not a process-wide admission hook. *)
  fun mentions predicate root =
    let
      exception Found
      val maximum = SmtResource.max_bv_replay_term_nodes
      val check_type = SmtReplayArithmetic.new_type_check (fn () => ())
      fun children tm = if not (Term.is_abs tm) then
          SmtResource.term_children tm
        else
          (case SmtReplayImport.bounded_raw_size_with_type_check
              check_type maximum tm of
             NONE =>
               (SmtResource.check_term_size_for "BitVector" "binder-opening"
                  (maximum+1);[])
           | SOME _ =>
               [#2 (SmtReplayImport.dest_abs_preserving_names tm)])
      fun inspect tm =
        (if Term.is_abs tm then check_type (Term.type_of tm) else ();
         if predicate tm then raise Found else ())
      fun search () =
        (let val summary = SmtResource.bounded_structure_with_children
               children inspect maximum root
             val _ = if #complete summary then () else
               SmtResource.check_dag_size_with_limit "Skeleton"
                 "theory-classification" maximum (#dag_nodes summary)
         in false end) handle Found => true
    in search () end

  fun is_bag_constant tm =
    named "bag"
      ["BAG_IN", "BAG_INN", "BAG_INSERT", "BAG_UNION", "BAG_DIFF", "BAG_MERGE",
       "BAG_INTER", "SUB_BAG", "EMPTY_BAG", "BAG_CARD", "BAG_FILTER",
       "BAG_CHOICE", "BAG_IMAGE", "BAG_EVERY", "ITBAG", "SET_OF_BAG",
       "BAG_OF_SET"] tm

  (* The proof parser turns Z3's [(_ map +) a b] into
     [\x. a x + b x].  Do not classify arbitrary Int-valued lambdas as bags:
     array and arithmetic lemmas use those too. *)
  fun is_int_count_lambda tm =
    Term.is_abs tm andalso
    let
      (* Recognition is not authority to open an unbounded native binder.
         Use the existing public resource metric and primitive-Type gate. *)
      val check_type = SmtReplayArithmetic.new_type_check (fn () => ())
      val _ = case SmtReplayImport.bounded_raw_size_with_type_check
          check_type SmtResource.max_bv_replay_term_nodes tm of
          SOME _ => ()
        | NONE => SmtResource.check_term_size_for "BitVector" "binder-opening"
            (SmtResource.max_bv_replay_term_nodes+1)
      val (x, body) = SmtReplayImport.dest_abs_preserving_names tm
      val (head, args) = boolSyntax.strip_comb body
      fun selected_at_x array =
        let val (_, index) = Term.dest_comb array
            val _ = check_type (Term.type_of index)
        in Term.aconv index x end
    in
      Library.same_const intSyntax.plus_tm head andalso
      (case args of
         [left, right] => selected_at_x left andalso selected_at_x right
       | _ => false)
    end
    handle Feedback.HOL_ERR detail =>
      if SmtResource.is_resource_gate detail then raise Feedback.HOL_ERR detail
      else false

  fun has_bag_encoding t =
    mentions is_bag_constant t orelse mentions is_int_count_lambda t

  fun has_native_bag_encoding t = mentions is_bag_constant t

  fun bag_const name = Term.prim_mk_const {Thy = "bag", Name = name}

  (* Each admitted bag head has its own count/pointwise characterization.
     In particular CARD, FILTER, IMAGE and ITBAG are not admitted merely
     because the recognizer can name them. *)
  val bag_fact_table = [
    ("BAG_IN", bag_const "BAG_IN",
      [bagTheory.BAG_IN, bagTheory.BAG_INN]),
    ("BAG_INN", bag_const "BAG_INN", [bagTheory.BAG_INN]),
    ("BAG_INSERT", bag_const "BAG_INSERT", [bagTheory.BAG_INSERT]),
    ("BAG_UNION", bag_const "BAG_UNION", [bagTheory.BAG_UNION]),
    ("BAG_DIFF", bag_const "BAG_DIFF", [bagTheory.BAG_DIFF]),
    ("BAG_MERGE", bag_const "BAG_MERGE", [bagTheory.BAG_MERGE]),
    ("BAG_INTER", bag_const "BAG_INTER", [bagTheory.BAG_INTER]),
    ("SUB_BAG", bag_const "SUB_BAG", [bagTheory.SUB_BAG]),
    ("EMPTY_BAG", bag_const "EMPTY_BAG", [bagTheory.EMPTY_BAG]),
    ("BAG_CARD", bag_const "BAG_CARD",
      [bagTheory.BAG_CARD_THM, bagTheory.BAG_CARD_EMPTY,
       bagTheory.BAG_CARD_UNION, bagTheory.BAG_CARD_DIFF,
       bagTheory.BAG_CARD_BAG_INN]),
    ("BAG_FILTER", bag_const "BAG_FILTER",
      [bagTheory.BAG_FILTER_DEF, bagTheory.BAG_INN_BAG_FILTER,
       bagTheory.BAG_IN_BAG_FILTER]),
    ("BAG_IMAGE", bag_const "BAG_IMAGE",
      [bagTheory.BAG_IMAGE_DEF, bagTheory.BAG_IN_FINITE_BAG_IMAGE]),
    ("ITBAG", bag_const "ITBAG",
      [bagTheory.ITBAG_THM, bagTheory.ITBAG_EMPTY, bagTheory.ITBAG_INSERT]),
    ("BAG_CHOICE", bag_const "BAG_CHOICE", [bagTheory.BAG_CHOICE_DEF]),
    ("BAG_EVERY", bag_const "BAG_EVERY", [bagTheory.BAG_EVERY_THM]),
    ("SET_OF_BAG", bag_const "SET_OF_BAG", [bagTheory.SET_OF_BAG]),
    ("BAG_OF_SET", bag_const "BAG_OF_SET", [bagTheory.BAG_OF_SET])
  ]

  val supported_bag_operator_names_for_test =
    List.map (fn (name, _, _) => name) bag_fact_table

  fun bag_rewrites_for t =
    Library.goal_directed_rewrites bag_fact_table t @
    [integerTheory.INT_GE,
     integerTheory.INT_OF_NUM,
     integerTheory.NUM_OF_INT,
     integerTheory.INT_LE,
     integerTheory.INT_OF_NUM_LE,
     integerTheory.INT_OF_NUM_LT,
     integerTheory.INT_OF_NUM_ADD,
     combinTheory.UPDATE_def,
     combinTheory.APPLY_UPDATE_THM,
     (* srw's set-membership conversion, expressed as its checked equation. *)
     boolTheory.IN_DEF,
     boolTheory.FUN_EQ_THM]

  (* Preserve the bag portfolio and its constructor/count equations. Only
     free graph variables may be named by the caller: counts, elements and
     guards are not independent holes. Admission is invocation-local, and
     failures must survive both tactic and consumer fallback handlers. *)
  fun checked_procedures check =
  let
    exception AdmissionFailure of exn
    val admitted_source_size = ref 0
    fun admit tm = check tm handle primary => raise AdmissionFailure primary
    fun protect f x = f x handle AdmissionFailure primary =>
      SmtReplayArithmetic.propagate_admission_error primary
    fun goal tactic (assumptions,conclusion) =
      (List.app admit (conclusion::assumptions);
       tactic (assumptions,conclusion))
    fun theorem th =
      (List.app admit (Thm.concl th :: Thm.hyp th);th)
    fun cases decide input = goal (fn input as (context,conclusion) =>
      let
        val conditional = HolKernel.find_term
          (fn tm => boolSyntax.is_cond tm andalso
            not (Term.is_const (#1 (boolSyntax.dest_cond tm))) andalso
            Term.free_in tm conclusion) conclusion
        val (condition,_,_) = boolSyntax.dest_cond conditional
        (* Split only the guard. COND_CASES_TAC specializes BOTH arms into
           one conjunction before extracting either equation. That unused
           intermediate can be twice the admitted goal. The checked simp
           driver below reduces each branch under its actual assumption. *)
        fun branch value intro th (assumptions,target) =
          let
            val equation = boolSyntax.mk_eq (condition,value)
            val _ = List.app admit [condition,value,equation,Thm.concl th]
            (* Replacing a guard by T/F cannot enlarge the admitted native
               operands. Admit the actual substituted goals before SUBST's
               proof construction, not just the subsequent simp branches. *)
            val sigma = [{redex=condition,residue=value}]
            val _ = List.app (admit o Term.subst sigma)
              (target::assumptions)
          in Tactical.THEN
            (Tactic.SUBST1_TAC (intro th),Tactic.ASSUME_TAC th)
            (assumptions,target) end
        fun equation h =
          if not (boolSyntax.is_eq h) then NONE else
            let val (l,r) = boolSyntax.dest_eq h
                fun boolean value = Term.aconv value boolSyntax.T orelse
                  Term.aconv value boolSyntax.F
                val orientation =
                  if Term.aconv l condition andalso boolean r
                    then SOME (r,false)
                  else if Term.aconv r condition andalso boolean l
                    then SOME (l,true) else NONE
            in case orientation of NONE => NONE
              | SOME (value,symmetric) =>
                  let val _ = List.app admit
                        [h,condition,boolSyntax.mk_eq (condition,value),
                         if Term.aconv value boolSyntax.T then condition
                         else boolSyntax.mk_neg condition]
                      val law = Thm.ASSUME h
                      val law = if symmetric then Thm.SYM law else law
                      val fact = if Term.aconv value boolSyntax.T then
                          Drule.EQT_ELIM law else Drule.EQF_ELIM law
                  in SOME (branch value (fn _ => law) fact) end end
        fun known [] = NONE
          | known (h::hs) =
              (admit boolSyntax.T;
               if Term.aconv h condition then SOME
                 (branch boolSyntax.T Drule.EQT_INTRO (Thm.ASSUME h))
               else if boolSyntax.is_neg h andalso
                   Term.aconv (boolSyntax.dest_neg h) condition then SOME
                 (branch boolSyntax.F Drule.EQF_INTRO (Thm.ASSUME h))
               else case equation h of SOME tactic => SOME tactic
                 | NONE => known hs)
        fun reflexive () =
          if not (boolSyntax.is_eq condition) then NONE else
            let val (l,r) = boolSyntax.dest_eq condition
            in if not (Term.aconv l r) then NONE else
              let val _ = List.app admit
                    [l,r,condition,boolSyntax.mk_eq (condition,boolSyntax.T)]
              in SOME (branch boolSyntax.T Drule.EQT_INTRO (Thm.REFL l))
              end end
        (* Decide the demanded guard before constructing excluded middle.
           Reflexivity and normalized context equations can decide a fitting
           guard whose duplicated disjunction would not fit. A simplifier
           miss retains the original split, never an unchecked fallback. *)
        fun decided () =
          let val equation = decide context condition
              val value = boolSyntax.rhs (Thm.concl equation)
          in if Term.aconv value boolSyntax.T then SOME
               (branch value (fn _ => equation) (Drule.EQT_ELIM equation))
             else if Term.aconv value boolSyntax.F then SOME
               (branch value (fn _ => equation) (Drule.EQF_ELIM equation))
             else NONE end
          handle Feedback.HOL_ERR _ => NONE | Conv.UNCHANGED => NONE
      in case (case known context of SOME tactic => SOME tactic
                 | NONE => case reflexive () of SOME tactic => SOME tactic
                     | NONE => decided ()) of
          SOME tactic => tactic input
        | NONE =>
            let val law = theorem boolTheory.EXCLUDED_MIDDLE
                val _ = admit (boolSyntax.mk_disj
                  (condition,boolSyntax.mk_neg condition))
            in Thm_cont.DISJ_CASES_THEN2
                 (branch boolSyntax.T Drule.EQT_INTRO)
                 (branch boolSyntax.F Drule.EQF_INTRO)
                 (Thm.SPEC condition law) input end end) input

    (* Forecast native rewrite instantiation with syntax only. Matching
       operands, actual Hyp, type substitutions and binder bodies are all
       admitted before the corresponding native operation. Constructing a
       small DAG of syntax here does not instantiate a theorem or establish
       an equality. Each consumed side/condition gets its original cap. *)
    fun substitution check types sigma =
      let
        fun tick () = check boolSyntax.T
        (* Use the protected caller continuation for Type gates too. A
           checker-owned HOL_ERR must not become a rewrite search miss. *)
        fun check_type ty =
          check (Term.mk_var ("__smt_bag_annotation",ty))
        val _ = List.app (fn {redex,residue} =>
          (check_type redex;check_type residue)) types
        val _ = List.app (fn {redex,residue} =>
          (check redex;check residue)) sigma
        fun type_syntax ty =
          (tick ();
           if Type.is_vartype ty then
             (case List.find (fn {redex,...} => redex = ty) types of
                SOME {residue,...} => residue | NONE => ty)
           else
             let val {Thy,Tyop,Args} = Type.dest_thy_type ty
             in Type.mk_thy_type
               {Thy=Thy,Tyop=Tyop,Args=List.map type_syntax Args} end)
        fun typed ty =
          let val result = type_syntax ty
              val _ = check_type result
          in result end
        fun build avoids bound tm =
          (tick ();
           if Term.is_var tm then
             (case List.find (fn (v,_) => Term.aconv v tm) bound of
                SOME (_,v) => v
              | NONE =>
                  let val v = Term.mk_var (#1 (Term.dest_var tm),
                        typed (Term.type_of tm))
                  in case List.find (fn {redex,...} => Term.aconv redex v)
                      sigma of SOME {residue,...} => residue | NONE => v end)
           else if Term.is_const tm then
             let val {Thy,Name,...} = Term.dest_thy_const tm
             in Term.mk_thy_const
               {Thy=Thy,Name=Name,Ty=typed (Term.type_of tm)} end
           else if Term.is_comb tm then
             let val (f,x) = Term.dest_comb tm
             in Term.mk_comb (build avoids bound f,build avoids bound x) end
           else
             let val _ = check tm
                 val (v,b) = SmtReplayImport.dest_abs_preserving_names tm
                 val fresh = Term.variant (avoids @ List.map #2 bound)
                   (Term.mk_var (#1 (Term.dest_var v),
                     typed (Term.type_of v)))
             in Term.mk_abs
               (fresh,build avoids ((v,fresh)::bound) b) end)
        fun instantiate root =
          if null types andalso null sigma then (check root;root) else
          let val _ = check root
              (* Avoid ORIGINAL free names as well as residue names. This
                 prevents capture by freshening, including when distinct
                 source variable types collapse under INST_TYPE. Bound
                 lookup above still uses the original typed identity. *)
              val avoids = Term.free_varsl
                (root :: List.map #residue sigma)
          in build avoids [] root end
      in instantiate end
    (* A canonical equation is an operator envelope, not a new operand.
       In particular importing an admitted p as p=T must not charge those
       four wrapper nodes against p's allowance. Admit every consumed side,
       condition and actual Hyp independently, including typed forecasts. *)
    fun formula check term =
      let val (conditions,equation) = boolSyntax.strip_imp term
          val (l,r) = boolSyntax.dest_eq equation
      in List.app check (Term.rator (Term.rator equation)::l::r::conditions)
      end
    fun rule check th =
      (formula check (Thm.concl th);List.app check (Thm.hyp th);th)
    fun preflight check th tm =
      let
        val _ = rule check th
        val left = boolSyntax.lhs
          (#2 (boolSyntax.strip_imp (Thm.concl th)))
        (* Ho_Net is intentionally untyped. Reject a Type-incompatible
           wildcard (notably unit's v=()) before rescanning a whole raw
           target suffix. Admit BOTH annotations before native Type work;
           an actual term match still gets full operand admission below. *)
        val _ = List.app (fn t => check
          (Term.mk_var ("__smt_bag_annotation",Term.type_of t))) [left,tm]
        val _ = Type.match_type (Term.type_of left) (Term.type_of tm)
        val _ = check tm
        val rigid = Thm.hyp_frees th
        val types = HOLset.listItems (Thm.hyp_tyvars th)
        val (sigma,types) = HolKernel.ho_match_term types rigid left tm
        val instantiate = substitution check types sigma
        (* INST_TYPE precedes term INST, so admit that intermediate too. *)
        val typed = substitution check types []
        fun forecast instantiate term =
          let val (conditions,equation) = boolSyntax.strip_imp term
              val (l,r) = boolSyntax.dest_eq equation
          in boolSyntax.list_mk_imp (List.map instantiate conditions,
               boolSyntax.mk_eq (instantiate l,instantiate r)) end
        val _ = formula check (forecast typed (Thm.concl th))
        val _ = List.app (check o typed) (Thm.hyp th)
        val source = Thm.concl th
        val initial = forecast instantiate source
        val _ = formula check initial
        val _ = List.app (check o instantiate) (Thm.hyp th)
        (* HO_PART_MATCH also applies BETA_VAR at the flexible function
           occurrences of the ORIGINAL rule. Forecast those exact paths,
           including each beta intermediate, rather than only the smaller
           pre-beta substitution. Do not normalize arbitrary lambda syntax
           carried by an actual operand. *)
        fun beta term =
          if Term.is_comb term andalso Term.is_abs (Term.rator term) then
            let val _ = check term
                val (v,body) = SmtReplayImport.dest_abs_preserving_names
                  (Term.rator term)
                val result = substitution check []
                  [{redex=v,residue=Term.rand term}] body
                val _ = check result
            in result end
          else term
        fun betas 1 term = beta term
          | betas n term =
              let val (f,x) = Term.dest_comb term
              in beta (Term.mk_comb (betas (n-1) f,x)) end
        (* BETA_VAR compiles selective paths on the ORIGINAL rule, then
           HO_PART_MATCH runs them in match-substitution order. A previous
           phase may erase an unselected sibling: never traverse it against
           the old pattern. A missing SELECTED path rolls back the entire
           phase, as native TRY_CONV does; admission failures do not. *)
        datatype path = Betas of int | Body of path
          | Rator of path | Rand of path | Both of path * path
        fun plan variable pattern =
          (check boolSyntax.T;
           if Term.is_abs pattern then
             let val (v,b) =
                   SmtReplayImport.dest_abs_preserving_names pattern
             in if Term.aconv v variable then NONE
                else Option.map Body (plan variable b) end
           else if Term.is_comb pattern then
             let val (head,args) = boolSyntax.strip_comb pattern
             in if Term.aconv head variable then SOME (Betas (length args))
                else let val (f,x) = Term.dest_comb pattern
                     in case (plan variable f,plan variable x) of
                         (NONE,NONE) => NONE
                       | (SOME p,NONE) => SOME (Rator p)
                       | (NONE,SOME p) => SOME (Rand p)
                       | (SOME p,SOME q) => SOME (Both (p,q)) end end
           else NONE)
        fun apply (Betas n) actual = betas n actual
          | apply (Body p) actual =
              let val _ = check actual
                  val (v,b) =
                    SmtReplayImport.dest_abs_preserving_names actual
                  val result = Term.mk_abs (v,apply p b)
                  val _ = check result
              in result end
          | apply (Rator p) actual =
              let val (f,x) = Term.dest_comb actual
              in Term.mk_comb (apply p f,x) end
          | apply (Rand p) actual =
              let val (f,x) = Term.dest_comb actual
              in Term.mk_comb (f,apply p x) end
          | apply (Both (p,q)) actual =
              let val (f,x) = Term.dest_comb actual
              in Term.mk_comb (apply p f,apply q x) end
        val plans = List.mapPartial (fn variable =>
          Option.map (fn p => (typed variable,p)) (plan variable source))
          (List.filter (fn v => not (HOLset.member (rigid,v)))
            (Term.free_vars source))
        fun phase ({redex,...},actual) =
          case List.find (fn (v,_) => Term.aconv v redex) plans of
            NONE => actual
          | SOME (_,p) =>
              let val result = apply p actual
                    handle Feedback.HOL_ERR _ => actual
                  val _ = formula check result
              in result end
        val _ = List.foldl phase initial sigma
      in () end
    fun small tm = Option.isSome
      (SmtReplayImport.bounded_raw_size_with_type_check_observed
        {limit=128,observe=fn () => admit boolSyntax.T,
         check_type=fn _ => ()} tm)

    (* The simplifier normally imports assumptions through its own rewrite
       net, bypassing exported conversions. Replace that reducer locally,
       retaining its canonicalization, Ho_Net priority and traversal, with
       prospective checks before every native context match.
       Congruence-local facts stay in the reducer's lexical context, not in
       a mutable global or invocation-wide assumption pool. *)
    fun with_context_rewrites ss prove =
      let
        exception Context of
          (Thm.thm option *
           ((Term.term list -> Term.term -> Thm.thm) ->
             Term.term list -> Term.term -> Thm.thm)) Ho_Net.net *
          Thm.thm list
        val compose = ref
          (fn (_:Thm.thm,_:exn,_:Term.term) => NONE:Thm.thm option)
        val interrupted = ref NONE
        fun guarded f x = f x handle AdmissionFailure primary =>
          (interrupted := SOME primary;raise Portable.Interrupt)
        fun add (Context (net,previous),facts) = guarded (fn () =>
          let
            fun canonical th =
              (ignore (theorem th);
               Cond_rewr.mk_cond_rewrs
                 (th,BoundedRewrites.UNBOUNDED))
            fun conversion (th,_) =
              let val _ = ignore (rule admit th)
                  val th = Drule.SPEC_ALL th
                  val _ = ignore (rule admit th)
                  val left = boolSyntax.lhs
                    (#2 (boolSyntax.strip_imp (Thm.concl th)))
                  val _ = admit left
                  val conv = Cond_rewr.COND_REWR_CONV
                    ("bag context rewrite",th) false
                  fun apply solver stack tm =
                    (preflight admit th tm;
                     let val result = conv solver stack tm
                         val (l,r) = boolSyntax.dest_eq (Thm.concl result)
                         val _ = List.app admit (l::r::Thm.hyp result)
                     in result end)
              in (HOLset.listItems (Thm.hyp_frees th),left,
                   (SOME th,apply)) end
            val rules = List.map conversion
              (List.concat (List.map canonical facts))
          in Context (List.foldr (fn (rule,net) => Ho_Net.enter rule net)
               net rules,facts @ previous) end) ()
        fun apply compact
            {solver,context=context as Context (net,_),stack,...} tm =
              guarded (fn () =>
                let fun checked_solver assumptions condition =
                      (List.app admit assumptions;admit condition;
                       solver assumptions condition)
                    fun checked_result result =
                      let val (l,r) = boolSyntax.dest_eq (Thm.concl result)
                          val _ = List.app admit (l::r::Thm.hyp result)
                      in result end
                    fun selected (source,conv) = guarded (fn () =>
                      case source of SOME th =>
                        if not compact andalso not (small tm) andalso
                            small (Thm.concl th) andalso
                            boolSyntax.is_eq (Thm.concl th) then
                          (case (!compose) (th,context,tm) of
                             NONE => conv checked_solver stack tm
                           | SOME result => checked_result result)
                        else conv checked_solver stack tm
                      | NONE => conv checked_solver stack tm) ()
                in Lib.tryfind selected (Ho_Net.lookup tm net) end) ()
          | apply _ _ _ = raise Fail "bag rewrite context"
        val data = simpLib.traversedata_for_ss ss
        val original = Traverse.dest_reducer (hd (#rewriters data))
        (* The exported-rule dispatcher is the original net's one wildcard
           conversion. Enter it FIRST, just as native addcontext extends
           that initial net. Specificity and equal-key source order thus
           remain native, including context overrides of bag equations. *)
        fun fallback solver stack tm = #apply original
          {solver=solver,conv=fn _ => Conv.NO_CONV,
           context= #initial original,stack=stack,
           relation=(boolSyntax.equality,Thm.REFL)} tm
        val initial = Ho_Net.enter
          ([],Term.genvar Type.alpha,(NONE,fallback)) Ho_Net.empty
        fun reducer compact initial = Traverse.REDUCER
          {name=SOME "admitted bag context",initial=Context (initial,[]),
           addcontext=add,apply=apply compact}
        fun traverse compact net = Traverse.TRAVERSE
          {rewriters=[reducer compact net],dprocs= #dprocs data,
           travrules= #travrules data,relation= #relation data,
           limit= #limit data}
        (* Close a demanded context rewrite on a small checked obligation
           BEFORE inserting its large match residues. Name the SAME syntax
           in the target and actual context facts, retaining specificity,
           repeated arguments and rigid namesakes. These are schematic
           assumptions, not new laws: lift once, then discharge them with
           their original checked theorems. No expanded g large large is
           ever instantiated when the compact proof has already erased it.

           If a context pattern needs the structure of an opaque residue,
           refine its frontier by one application or abstraction layer and
           retry discovery. A dependent field is a FUNCTION hole applied
           to its live binders, not an independent value. Realization closes
           that field and retracts only the introduced beta paths, with
           prospective admission before INST and every checked conversion.
           Refinement visits finite source syntax, never closure wrappers.
           Small actual matches retain their original path and order. *)
        fun compose_rule (th,Context (_,facts),tm) =
          let
            val _ = List.app admit (tm::Thm.concl th::Thm.hyp th)
            val left = boolSyntax.lhs (Thm.concl th)
            val _ = admit left
            val (sigma,_) = HolKernel.ho_match_term
              (HOLset.listItems (Thm.hyp_tyvars th)) (Thm.hyp_frees th) left tm
            val roots = List.map #residue sigma
            val source_names = Term.free_varsl
              (tm :: List.concat (List.map
                (fn law => Thm.concl law::Thm.hyp law) facts))
            val avoids = ref source_names
            fun tick () = admit boolSyntax.T
            (* Syntax-only arena. App keys contain child IDs, never native
               suffixes. Leaf syntax is bounded by the unchanged small-term
               frontier (128 nodes); its comparisons cannot rescan a large
               suffix. Dependencies are computed bottom-up, not by repeated
               structural-map occurrence queries on each dependent suffix.
               A bounded physical cache is only a reuse hint; misses still
               visit/pay source syntax and cannot identify different terms.
               All semantic retractions below remain checked separately. *)
            datatype node = Node of
              int * Term.term * int * int list * view
            and view = Leaf | App of node * node | Abs of Term.term * node
            fun id (Node (i,_,_,_,_)) = i
            fun syntax (Node (_,t,_,_,_)) = t
            fun size (Node (_,_,n,_,_)) = n
            fun deps (Node (_,_,_,vs,_)) = vs
            fun view (Node (_,_,_,_,v)) = v
            val next = ref 0
            fun compare_id pair = (tick ();Int.compare pair)
            fun compare_leaf pair = (tick ();Term.compare pair)
            val leaves = ref (Redblackmap.mkDict compare_leaf)
            fun compare_pair ((a,b),(c,d)) = case compare_id (a,c) of
                EQUAL => compare_id (b,d) | order => order
            val apps = ref (Redblackmap.mkDict compare_pair)
            val abstractions = ref (Redblackmap.mkDict compare_pair)
            val binders = ref (Redblackmap.mkDict compare_leaf)
            val variables = ref (Redblackmap.mkDict compare_id)
            fun pay n = if n=0 then () else (tick ();pay (n-1))
            val cache = Array.array (257,[]:(Term.term * node) list)
            fun union [] ys = ys
              | union xs [] = xs
              | union (x::xs) (y::ys) =
                  (tick ();if x=y then x::union xs ys
                   else if x<y then x::union xs (y::ys)
                   else y::union (x::xs) ys)
            fun make t n vs v =
              (next := !next+1;Node (!next,t,n,vs,v))
            fun build term =
              let val _ = tick ()
                  val bucket = SmtReplayImport.pointer_bucket_observed
                    pay 2 257 term
                  val saved = Array.sub (cache,bucket)
                  val hit = List.find (fn (old,_) =>
                    (tick ();Portable.pointer_eq (old,term))) saved
              in case hit of SOME (_,n) => n | NONE =>
                let
                  val bounded =
                    SmtReplayImport.bounded_raw_size_with_type_check_observed
                      {limit=128,observe=tick,check_type=fn ty =>
                         admit (Term.mk_var ("__smt_bag_annotation",ty))} term
                  fun leaf count =
                    case Redblackmap.peek (!leaves,term) of SOME n => n
                    | NONE =>
                        let val _ = admit term
                            val vs = List.foldl (fn (v,vs) =>
                              (tick ();case Redblackmap.peek (!binders,v) of
                                 NONE => vs | SOME i => union [i] vs))
                              [] (Term.free_vars term)
                            val n = make term count vs Leaf
                        in leaves := Redblackmap.insert (!leaves,term,n);n end
                  val result = case bounded of SOME count => leaf count
                  | NONE => if Term.is_comb term then
                    let val (f,x) = Term.dest_comb term
                        val l = build f val r = build x
                        val key = (id l,id r)
                    in case Redblackmap.peek (!apps,key) of
                        SOME n => n
                      | NONE =>
                          let val n = make
                                (Term.mk_comb (syntax l,syntax r))
                                (1+size l+size r) (union (deps l) (deps r))
                                (App (l,r))
                          in apps := Redblackmap.insert (!apps,key,n);n end
                    end
                  else if Term.is_abs term then
                    let val _ = admit term
                        val (old,body) =
                          SmtReplayImport.dest_abs_preserving_names term
                        (* A lexical canonical name, fresh for all source
                           frees and this abstraction's actual outer frees.
                           Independent alpha copies share IDs; live outer
                           binders cannot be captured or identified. *)
                        val v = Term.variant
                          (source_names @ Term.free_vars term)
                          (Term.mk_var ("__smt_bag_bound",Term.type_of old))
                        val _ = avoids := v :: !avoids
                        val _ = admit body
                        val b = Term.subst [{redex=old,residue=v}] body
                        val _ = admit b
                        val index = case Redblackmap.peek (!binders,v) of
                            SOME i => i
                          | NONE =>
                              (next := !next+1;
                               binders := Redblackmap.insert
                                 (!binders,v,!next);
                               variables := Redblackmap.insert
                                 (!variables,!next,v);!next)
                        val child = build b
                        val vs = List.filter
                          (fn i => (tick ();i<>index)) (deps child)
                        val key = (index,id child)
                    in case Redblackmap.peek (!abstractions,key) of
                        SOME n => n
                      | NONE =>
                          let val n = make (Term.mk_abs (v,syntax child))
                                (1+size child) vs (Abs (v,child))
                          in abstractions := Redblackmap.insert
                               (!abstractions,key,n);n end end
                  else leaf 1
                    val _ = Array.update (cache,bucket,
                      (term,result)::List.take (saved,Int.min (3,length saved)))
                in result end end
            val roots = List.map (fn t => (t,build t)) roots
            val bindings = ref (Redblackmap.mkDict compare_id)
            fun arguments n = List.map (fn i =>
              (tick ();valOf (Redblackmap.peek (!variables,i)))) (deps n)
            fun atom n = case Redblackmap.peek (!bindings,id n) of
                SOME (_,hole,_) => hole
              | NONE =>
                  let val vs = arguments n
                      val ty = List.foldr
                        (fn (v,ty) => Type.mk_type
                          ("fun",[Term.type_of v,ty]))
                        (Term.type_of (syntax n)) vs
                      val hole = Term.variant (!avoids) (Term.genvar ty)
                      val _ = admit hole
                  in avoids := hole :: !avoids;
                     bindings := Redblackmap.insert
                       (!bindings,id n,(n,hole,ref false));hole end
            val _ = List.app (fn (_,n) =>
              if size n<=128 then () else ignore (atom n)) roots
            val represented = ref (Redblackmap.mkDict compare_id)
            fun represent n =
              case Redblackmap.peek (!bindings,id n) of
                NONE => syntax n
              | SOME (_,hole,expanded) =>
                  if not (!expanded) then
                    Term.list_mk_comb (hole,arguments n)
                  else case Redblackmap.peek (!represented,id n) of
                    SOME result => result
                  | NONE =>
                      let
                        fun field x = if size x<=128 then syntax x
                          else (ignore (atom x);represent x)
                        fun spine x args = case view x of
                            App (f,a) => spine f (field a::args)
                          | _ => Term.list_mk_comb (syntax x,args)
                        val result = case view n of
                            Abs (v,b) => Term.mk_abs (v,field b)
                          | App _ => spine n []
                          | Leaf => syntax n
                      in represented := Redblackmap.insert
                           (!represented,id n,result);result end
            fun count variable term =
              (admit boolSyntax.T;
               if Term.aconv variable term then 1
               else if Term.is_comb term then
                 let val (f,x) = Term.dest_comb term
                 in count variable f + count variable x end
               else if Term.is_abs term then
                 let val _ = admit term
                     val (_,body) =
                       SmtReplayImport.dest_abs_preserving_names term
                 in count variable body end
               else 0)
            fun attempt () =
              let
                val _ = represented := Redblackmap.mkDict compare_id
                val _ = List.app (fn (_,n) => ignore (represent n)) roots
                val entries = Redblackmap.listItems (!bindings)
                (* Only CLOSED source fields can be substituted globally.
                   Dependent fields occur inside their enclosing projection. *)
                val naming = List.map (fn (actual,n) =>
                    {redex=actual,residue=represent n}) roots @
                  List.mapPartial (fn (_,(n,_,_)) =>
                    if null (deps n) then SOME
                      {redex=syntax n,residue=represent n} else NONE) entries
                val _ = List.app (fn {redex,residue} =>
                  List.app admit [redex,residue]) naming
                fun compact term =
                  let val _ = admit term
                      val result = Term.subst naming term
                      val _ = admit result
                  in result end
                val target = compact tm
                val context = List.map (Thm.ASSUME o compact o Thm.concl) facts
                val proof = Conv.TRY_CONV
                  (traverse true initial context) target
                val (l,r) = boolSyntax.dest_eq (Thm.concl proof)
                val holes = List.map (fn (_,(_,hole,_)) => hole)
                  (Redblackmap.listItems (!bindings))
                (* An exported rule's retained Hyp is not one of our
                   schematic context assumptions. Never substitute through
                   a coincidentally named rigid source variable there. *)
                val safe_hyp = List.all (fn h =>
                  List.exists (Term.aconv h o Thm.concl) context orelse
                  List.all (fn hole => not (Term.free_in hole h)) holes)
                  (Thm.hyp proof)
                val shrinks = safe_hyp andalso not (Term.aconv l r) andalso
                  Term.term_size r < Term.term_size l andalso
                  List.all (fn hole => count hole r <= count hole l) holes
                val actual_roots = l::r::Thm.hyp proof @
                  List.map Thm.concl context
                val dependent = List.exists (fn (_,(n,hole,_)) =>
                  not (null (deps n)) andalso
                  List.exists (Term.free_in hole) actual_roots)
                  (Redblackmap.listItems (!bindings))
              in if not shrinks then NONE
                else if not dependent then
                  (* Preserve the original one-INST path when all retained
                     holes are independent. Unused dependent frontiers are
                     not substitutions and need no closure realization. *)
                  let val realization = List.mapPartial
                        (fn (_,(n,hole,_)) => if null (deps n) then SOME
                          {redex=hole,residue=syntax n} else NONE)
                        (Redblackmap.listItems (!bindings))
                      val instantiate = substitution admit [] realization
                      val _ = List.app (admit o instantiate) actual_roots
                      val _ = if Term.aconv (instantiate l) tm andalso
                          ListPair.allEq (fn (law,abstract) =>
                            Term.aconv (Thm.concl law)
                              (instantiate (Thm.concl abstract)))
                              (facts,context)
                        then () else raise Conv.UNCHANGED
                      val lifted = Thm.INST realization proof
                      fun discharge (law,result) =
                        if List.exists (Term.aconv (Thm.concl law))
                            (Thm.hyp result)
                        then Drule.PROVE_HYP law result else result
                  in SOME (List.foldl discharge lifted facts) end
                else let
                    val entries = Redblackmap.listItems (!bindings)
                    val open_abs =
                      SmtReplayImport.dest_abs_preserving_names
                    fun rhs th = boolSyntax.rhs (Thm.concl th)
                    fun checked th = (ignore (rule admit th);th)
                    fun equality_type term =
                      let val ty = Term.type_of term
                      in admit (Term.mk_var ("__smt_bag_annotation",
                           Type.mk_type ("fun",[ty,
                             Type.mk_type ("fun",[ty,Type.bool])]))) end
                    fun refl term =
                      (admit term;equality_type term;Thm.REFL term)
                    fun combine (left,right) =
                      let val l = boolSyntax.lhs (Thm.concl left)
                          val r = boolSyntax.lhs (Thm.concl right)
                          val input = Term.mk_comb (l,r)
                          val _ = List.app admit
                            [input,Term.mk_comb (rhs left,rhs right)]
                          val _ = equality_type input
                      in checked (Thm.MK_COMB (left,right)) end
                    fun apply_function f law =
                      let val input = Term.mk_comb
                            (f,boolSyntax.lhs (Thm.concl law))
                          val _ = List.app admit
                            [f,input,Term.mk_comb (f,rhs law)]
                          val _ = equality_type input
                      in checked (Thm.AP_TERM f law) end
                    fun apply_argument law x =
                      let val input = Term.mk_comb
                            (boolSyntax.lhs (Thm.concl law),x)
                          val _ = List.app admit
                            [x,input,Term.mk_comb (rhs law,x)]
                          val _ = equality_type input
                      in checked (Thm.AP_THM law x) end
                    (* Do not insert a large closure into a whole operand
                       and THEN beta-reduce it: that administrative redex
                       can exceed an otherwise fitting source's allowance.
                       Realize through small, ordinary definitional Hyp.
                       Reduce each small constructor equation locally before
                       lifting its checked children through congruence.
                       Finally CHOOSE away definitions, parents first; no
                       expanded definition or large pre-beta INST is made. *)
                    (* The admitted source supplies a lower bound on the
                       caller's allowance, not permission to raise it. Stop
                       factoring as soon as a whole field AND its definition,
                       existential closure and local beta operands fit that
                       bound. In particular a long unary suffix needs only
                       a bounded fringe, not one growing Hyp per source node. *)
                    val raw_size =
                      SmtReplayImport.bounded_raw_size_with_type_check_observed
                    val source_size = Int.max (!admitted_source_size,
                      valOf (raw_size
                        {limit=SmtResource.max_bv_replay_term_nodes,
                         observe=tick,check_type=fn ty => admit
                           (Term.mk_var ("__smt_bag_annotation",ty))} tm))
                    val names = ref (Redblackmap.mkDict compare_leaf)
                    val definitions = ref (Redblackmap.mkDict compare_id)
                    val _ = List.app (fn (_,(n,hole,_)) =>
                      names := Redblackmap.insert (!names,hole,n)) entries
                    fun name n =
                      case Redblackmap.peek (!definitions,id n) of
                        SOME (q,_,_,_) => q
                      | NONE =>
                          let val vs = arguments n
                              val q = case Redblackmap.peek
                                  (!bindings,id n) of
                                  SOME (_,hole,_) => hole
                                | NONE =>
                                    let val ty = List.foldr
                                          (fn (v,t) => Type.mk_type
                                            ("fun",[Term.type_of v,t]))
                                          (Term.type_of (syntax n)) vs
                                        val q = Term.variant (!avoids)
                                          (Term.genvar ty)
                                    in avoids := q :: !avoids;q end
                              val _ = admit q
                              val _ = names := Redblackmap.insert
                                (!names,q,n)
                              fun reference child = Term.list_mk_comb
                                (name child,arguments child)
                              val arity = length vs
                              val opaque = size n + arity +
                                Int.max (7,2*arity) <= source_size
                              val body = if opaque then syntax n else
                                case view n of
                                  Leaf => syntax n
                                | App (f,x) => Term.mk_comb
                                    (reference f,reference x)
                                | Abs (v,b) => Term.mk_abs (v,reference b)
                              val witness = Term.list_mk_abs (vs,body)
                              val equation = boolSyntax.mk_eq (q,witness)
                              val _ = List.app admit [witness,equation]
                              val _ = definitions := Redblackmap.insert
                                (!definitions,id n,
                                 (q,witness,equation,opaque))
                          in q end
                    val saved = ref (Redblackmap.mkDict compare_leaf)
                    (* NONE is unchanged syntax, not a reflexivity proof.
                       Visit it once without reflecting/admitting every
                       suffix. Only a changed parent's congruence demands
                       reflection of an unchanged child. In particular an
                       unrelated context needs no intermediate equality at
                       its element/function Types. *)
                    fun convert term = case conversion term of
                        SOME law => law | NONE => refl term
                    and conversion term =
                      let val _ = tick ()
                          (* Only bounded compact keys, never realized
                             suffixes, enter this conversion memo. *)
                          val cacheable = small term
                      in case if cacheable then
                          Redblackmap.peek (!saved,term) else NONE of
                        SOME result => result
                      | NONE =>
                        let
                          val (head,args) = boolSyntax.strip_comb term
                          val result = case if Term.is_var head then
                              Redblackmap.peek (!names,head) else NONE of
                            SOME n =>
                              let val _ = admit term
                                  val q = name n
                                  val (_,_,equation,opaque) = valOf
                                    (Redblackmap.peek (!definitions,id n))
                                  val arg_bridges = List.map convert args
                                  val prefix = List.foldl
                                    (fn (arg,f) => combine (f,arg))
                                    (refl q) arg_bridges
                                  val actuals = List.map rhs arg_bridges
                                  val arity = Int.min
                                    (length (deps n),length actuals)
                                  val (front,back) =
                                    (List.take (actuals,arity),
                                     List.drop (actuals,arity))
                                  fun apply (arg,law) =
                                    let val law = combine (law,refl arg)
                                        val redex = rhs law
                                        val (f,x) = Term.dest_comb redex
                                        val _ = admit f
                                        val (v,b) = open_abs f
                                        val output = substitution admit []
                                          [{redex=v,residue=x}] b
                                        val _ = admit output
                                    in checked (Thm.TRANS law
                                         (Thm.BETA_CONV redex)) end
                                  val local_law = List.foldl apply
                                    (Thm.ASSUME equation) front
                                  (* Leaf source syntax stays verbatim:
                                     source beta-redexes are NOT ours. *)
                                  val body = if opaque then
                                      refl (rhs local_law)
                                    else case view n of Leaf =>
                                      refl (rhs local_law)
                                    | _ => convert (rhs local_law)
                                  val expanded = checked
                                    (Thm.TRANS local_law body)
                                  val applied = List.foldl
                                    (fn (arg,f) => combine (f,refl arg))
                                    expanded back
                              in SOME (checked
                                   (Thm.TRANS prefix applied)) end
                          | NONE =>
                              let
                                fun abstraction () =
                                  if not (Term.is_abs head) then NONE else
                                  let val _ = admit head
                                      val (old,b) = open_abs head
                                      (* Source binders stay lexical, never
                                         interpreted as graph holes. *)
                                      val v = Term.variant
                                        (!avoids @ Term.free_vars b) old
                                      val _ = avoids := v :: !avoids
                                      val _ = admit b
                                      val renamed = Term.subst
                                        [{redex=old,residue=v}] b
                                      val _ = admit renamed
                                  in case conversion renamed of NONE => NONE
                                    | SOME body =>
                                      let val input = Term.mk_abs
                                            (v,boolSyntax.lhs
                                              (Thm.concl body))
                                          val _ = List.app admit
                                            [input,Term.mk_abs (v,rhs body)]
                                          val _ = equality_type input
                                      in SOME (checked (Thm.ABS v body)) end
                                  end
                                (* Strip each application spine only once,
                                   including unchanged many-argument heads. *)
                                fun application (x,(f,bridge)) =
                                  let val arg = conversion x
                                      val input = Term.mk_comb (f,x)
                                      val result = case (bridge,arg) of
                                          (NONE,NONE) => NONE
                                        | (NONE,SOME law) =>
                                            SOME (apply_function f law)
                                        | (SOME law,NONE) =>
                                            SOME (apply_argument law x)
                                        | (SOME l,SOME r) =>
                                            SOME (combine (l,r))
                                  in (input,result) end
                              in #2 (List.foldl application
                                   (head,abstraction ()) args) end
                          val _ = if cacheable then saved :=
                            Redblackmap.insert (!saved,term,result) else ()
                        in result end end
                    val left = convert l val right = convert r
                    (* Only actual compact Hyp require transport. Unused
                       context still passed all source/pattern gates and
                       participated in discovery in its original order. *)
                    val contexts = List.mapPartial (fn (law,abstract) =>
                      if List.exists (Term.aconv (Thm.concl abstract))
                          (Thm.hyp proof) then
                        SOME (law,convert (Thm.concl abstract)) else NONE)
                      (ListPair.zip (facts,context))
                    val _ = if Term.aconv (rhs left) tm andalso
                        List.all (fn (source,bridge) =>
                          Term.aconv (Thm.concl source) (rhs bridge)) contexts
                      then () else raise Conv.UNCHANGED
                    val result = checked (Thm.TRANS (Thm.SYM left)
                      (Thm.TRANS proof right))
                    fun discharge ((law,bridge),result) =
                      let val compact = boolSyntax.lhs (Thm.concl bridge)
                      in if List.exists (Term.aconv compact) (Thm.hyp result)
                         then checked (Drule.PROVE_HYP
                           (Thm.EQ_MP (Thm.SYM bridge) law) result)
                         else result end
                    val result = List.foldl discharge result contexts
                    fun close ((_,(q,witness,equation,_)),result) =
                      if not (List.exists (Term.aconv equation)
                          (Thm.hyp result)) then result else
                      let val existence = boolSyntax.mk_exists (q,equation)
                          val _ = List.app admit
                            (existence::witness::Thm.hyp result)
                          val exists = Thm.EXISTS (existence,witness)
                            (refl witness)
                      in checked (Thm.CHOOSE (q,exists) result) end
                in SOME (List.foldl close result
                     (List.rev (Redblackmap.listItems (!definitions))))
                end end
            fun discover () =
              case (attempt () handle Conv.UNCHANGED => NONE) of
                SOME proof => SOME proof
              | NONE =>
                  let val frontier = List.filter
                        (fn (_,(n,_,expanded)) =>
                          not (!expanded) andalso
                          (case view n of Leaf => false | _ => true))
                        (Redblackmap.listItems (!bindings))
                  in if null frontier then NONE else
                    (List.app (fn (_,(_,_,expanded)) => expanded := true)
                       frontier;discover ()) end
          in if Redblackmap.numItems (!bindings) = 0 then NONE
             else discover () end
          | compose_rule _ = NONE
        val _ = compose := compose_rule
        fun restore () = case !interrupted of NONE => ()
          | SOME primary => raise AdmissionFailure primary
        fun protect f x =
          let val result = f x handle primary => (restore ();raise primary)
              val _ = restore ()
          in result end
        fun convert facts = protect (fn tm =>
          (List.app (fn th => ignore (theorem th)) facts;admit tm;
           Conv.TRY_CONV (traverse false initial facts) tm))
        fun simp input = goal (Tactic.CONV_TAC (convert [])) input
        fun asm_simp input = goal (Tactical.ASSUM_LIST
          (fn facts => Tactic.CONV_TAC (convert facts))) input
        (* The ordinary FULL_SIMP_TAC [] schedule, using the local checked
           conversion also when simplifying the assumptions themselves.
           No directives or caller-added simp facts enter these Bag rungs. *)
        fun full_simp input = goal (Tactical.ASSUM_LIST (fn facts =>
          let fun simplify (th,earlier) =
                Conv.CONV_RULE (convert earlier) th :: earlier
              fun keep th = Tactical.FIRST
                  [Tactic.CONTR_TAC th,Tactic.ACCEPT_TAC th,
                   Tactic.ASSUME_TAC th]
              fun drop current = Tactical.MAP_EVERY Tactic.ASSUME_TAC
                (List.rev (List.take (current,length current-length facts)))
          in Tactical.THEN
            (Tactical.MAP_EVERY (Thm_cont.STRIP_ALL_THEN keep)
               (List.foldl simplify [] facts),
             Tactical.THEN (Tactical.POP_ASSUM_LIST drop,asm_simp)) end)) input
      in prove {convert=convert,simp=simp,full_simp=full_simp,
           prove=fn tm => Drule.EQT_ELIM (convert [] tm)} end
    fun with_rewrites facts prove =
      let
        (* ++ canonicalizes and indexes its added patterns eagerly. The
           dispatcher is too late to admit these first source operands. *)
        val _ = List.app (fn th => ignore (theorem th))
          (facts @ simpLib.frag_rewrites intSimps.INT_RWTS_ss)
      in SmtDatatypeProve.with_checked_rewrites_preflight admit
        (fn () => simpLib.++
          (simpLib.++ (bossLib.srw_ss(),intSimps.INT_RWTS_ss),
           simpLib.rewrites facts)) preflight
        (fn ss => with_context_rewrites ss prove) end

    (* Demand the constructor guard BEFORE expanding INSERT's lambda. Keep
       constructor identities and shared element relationships in a small
       checked schema; only opaque constructor fields are named. A success
       is a universally proved equation, not authority from graph naming.
       Lift it once, after admitting the substituted sides, never the
       duplicated branch which the small proof has already discarded. *)
    fun erasure allow_insert tm =
      let
        val (head,args) = boolSyntax.strip_comb tm
        val insert = allow_insert andalso
          named "bag" ["BAG_INSERT"] head andalso length args=3
        val conditional = boolSyntax.is_cond tm
        val _ = if insert orelse conditional then ()
          else raise Conv.UNCHANGED
        val _ = admit tm
        (* Small terms retain their ordinary path and fallback order. *)
        val _ = if small tm then raise Conv.UNCHANGED else ()
        val bindings = ref (Redblackmap.mkDict Term.compare)
        fun atom actual = case Redblackmap.peek (!bindings,actual) of
            SOME hole => hole
          | NONE =>
              let val hole = Term.genvar (Term.type_of actual)
              in bindings := Redblackmap.insert (!bindings,actual,hole);
                 hole end
        fun constructor actual =
          let val _ = admit boolSyntax.T
              val (con,fields) = boolSyntax.strip_comb actual
              (* Read declaration identities, not a type-instantiated
                 constructor bundle. Discovery is syntax, not a theorem. *)
              val constructors = case TypeBase.fetch (Term.type_of actual) of
                  NONE => []
                | SOME info => TypeBasePure.constructors_of info
          in if Term.is_const con andalso List.exists
              (fn ctor => (admit boolSyntax.T;Term.same_const con ctor))
              constructors then SOME (con,fields) else NONE end
        (* Demand BOTH outer constructors before their fields. Keep only a
           path witnessing disjointness; fields off that path are opaque.
           A fixed discovery fuel must not hide a fitting discriminator.
           Shared/opaque fields terminate discovery, so a large payload
           below SOME versus NONE is never explored or duplicated. *)
        fun distinguish (left,right) =
          (admit boolSyntax.T;
           if Term.aconv left right then NONE else
           case (constructor left,constructor right) of
             (SOME (l,ls),SOME (r,rs)) =>
               if not (Term.same_const l r) then SOME
                 (Term.list_mk_comb (l,List.map atom ls),
                  Term.list_mk_comb (r,List.map atom rs))
               else
                 let fun fields prefix [] [] = NONE
                       | fields prefix (x::xs) (y::ys) =
                           (case distinguish (x,y) of
                              NONE => fields ((atom x,atom y)::prefix) xs ys
                            | SOME pair =>
                                let val pairs = List.rev prefix @ [pair] @
                                      ListPair.map (fn (a,b) => (atom a,atom b))
                                        (xs,ys)
                                in SOME
                                  (Term.list_mk_comb (l,List.map #1 pairs),
                                   Term.list_mk_comb (r,List.map #2 pairs)) end)
                       | fields _ _ _ = NONE
                 in fields [] ls rs end
           | _ => NONE)
        (* Retain one outer constructor even without disjointness. For
           equal SOME fields, for example, the checked count equation can
           erase a constructor occurrence as well as its guard. Naming the
           whole element would lose that non-growth proof. *)
        fun shallow actual = case constructor actual of
            NONE => atom actual
          | SOME (con,fields) =>
              Term.list_mk_comb (con,List.map atom fields)
        val schema = if insert then
            let val element = hd args val query = List.nth (args,2)
                val (e,q) = case distinguish (element,query) of
                    SOME pair => pair
                  | NONE => (shallow element,shallow query)
            in Term.list_mk_comb (head,[e,atom (List.nth (args,1)),q]) end
          else let val (p,l,r) = boolSyntax.dest_cond tm
               in boolSyntax.mk_cond (atom p,atom l,atom r) end
        val _ = admit schema
        val result = with_rewrites (bag_rewrites_for schema)
          (fn {convert,...} => convert [] schema)
        val (left,right) = boolSyntax.dest_eq (Thm.concl result)
        val _ = if Term.aconv left right orelse
            SmtResource.contains Term.is_abs (Thm.concl result)
          then raise Conv.UNCHANGED else ()
        (* This is an optional erasure, not an eager normalization pass.
           Never duplicate an opaque field. Usually fixed syntax shrinks as
           well; otherwise require actual unfolded non-growth below. Thus a
           reflexive fitting INSERT cannot expand into a duplicated guard,
           but removing a large repeated element can pay for numeral 1. *)
        val holes = List.map #2 (Redblackmap.listItems (!bindings))
        fun occurrences needle term =
          (admit boolSyntax.T;
           if Term.aconv needle term then 1
           else if Term.is_comb term then
             let val (f,x) = Term.dest_comb term
             in occurrences needle f + occurrences needle x end
           else 0)
        fun fixed term =
          (admit boolSyntax.T;
           if List.exists (Term.aconv term) holes then 0
           else if Term.is_comb term then
             let val (f,x) = Term.dest_comb term
             in 1 + fixed f + fixed x end
           else 1)
        val _ = if List.all
            (fn hole => occurrences hole right <= occurrences hole left)
            holes then () else raise Conv.UNCHANGED
        val fixed_shrinks = fixed right <= fixed left
        val sigma = List.map (fn (actual,hole) =>
          {redex=hole,residue=actual}) (Redblackmap.listItems (!bindings))
        val instantiate = substitution admit [] sigma
        val l = instantiate left val r = instantiate right
        fun size term =
          SmtReplayImport.bounded_raw_size_with_type_check_observed
            {limit=SmtResource.max_bv_replay_term_nodes,
             observe=fn () => admit boolSyntax.T,check_type=fn _ => ()} term
        val _ = if fixed_shrinks then () else
          (case (size l,size r) of (SOME n,SOME m) =>
             if m <= n then () else raise Conv.UNCHANGED
           | _ => raise Conv.UNCHANGED)
        val _ = List.app admit (l::r::List.map instantiate (Thm.hyp result))
      in Thm.INST sigma result end
    fun simplify_erased allow_insert prove t =
      let
        val _ = admit t
        (* Physical reuse only avoids repeating discovery on shared input
           syntax. Every change is transported by its checked equality. *)
        val saved = ref []
        fun erase tm =
          case List.find (fn (old,_) => Portable.pointer_eq (old,tm))
              (!saved) of SOME (_,result) => result
          | NONE =>
              let
                val _ = admit boolSyntax.T
                fun descend () = if Term.is_comb tm then
                    let val (f,x) = Term.dest_comb tm
                        val l = erase f val r = erase x
                    in case (l,r) of (NONE,NONE) => NONE
                      | _ => SOME (Thm.MK_COMB
                          (Option.getOpt (l,Thm.REFL f),
                           Option.getOpt (r,Thm.REFL x))) end
                  else if Term.is_abs tm then
                    let val _ = admit tm
                        val (v,b) =
                          SmtReplayImport.dest_abs_preserving_names tm
                    in case erase b of NONE => NONE
                      | SOME bridge =>
                          let val result = Term.mk_abs
                                (v,boolSyntax.rhs (Thm.concl bridge))
                              val _ = admit result
                          in SOME (Thm.ABS v bridge) end end
                  else NONE
                val result = SOME (erasure allow_insert tm)
                  handle Conv.UNCHANGED => descend ()
                    | Feedback.HOL_ERR _ => descend ()
                val _ = saved := (tm,result) ::
                  List.take (!saved,Int.min (15,length (!saved)))
              in result end
      in case (if small t then NONE else erase t) of NONE => prove t
        | SOME bridge =>
            let val result = boolSyntax.rhs (Thm.concl bridge)
                val _ = admit result
            in Thm.EQ_MP (Thm.SYM bridge) (prove result) end
      end
    fun simp_prove t =
      simplify_erased true (fn t => with_rewrites (bag_rewrites_for t)
        (fn {prove,...} => prove t)) t
    fun pointwise_prove t =
      SmtResource.with_resource_step_time "Bag" "bag-condition-splitting"
        (fn t =>
          (admit t;with_rewrites (bag_rewrites_for t)
            (fn {convert,simp,full_simp,...} => Tactical.prove (t,
              Tactical.THEN (simp,
                Tactical.THEN (Tactical.REPEAT (goal Tactic.STRIP_TAC),
                  Tactical.THEN
                    (Tactical.REPEAT (Tactical.THEN
                       (cases (fn context =>
                          convert (List.map Thm.ASSUME context)),full_simp)),
                     Tactical.THEN (full_simp,
                       goal intLib.ARITH_TAC)))))))) t
    (* CPC's scoped fallback deliberately uses its old srw portfolio, not
       extra bag equations. Admit every actual Hyp and generated branch. *)
    fun contextual (context,t) =
      SmtResource.with_resource_step_time "Bag" "contextual" (fn () =>
        (List.app admit (t::context);
         SmtResource.check_resource_goal "Bag" "contextual" t;
         (* Retain the already admitted original source's raw allowance
            witness across simplifier descent. This is a lower bound on
            the caller's cap, never a larger admission policy. *)
         (if small t then () else admitted_source_size := valOf
           (SmtReplayImport.bounded_raw_size_with_type_check_observed
             {limit=SmtResource.max_bv_replay_term_nodes,
              observe=fn () => admit boolSyntax.T,
              check_type=fn ty => admit
                (Term.mk_var ("__smt_bag_annotation",ty))} t));
         (* Discard provably unused guards before splitting. Restrict this
            erasure to conditionals: CPC retains its original srw portfolio,
            rather than acquiring the ordinary Bag rung's extra equations. *)
         simplify_erased false (fn t =>
           SmtDatatypeProve.with_checked_rewrites_preflight admit
             bossLib.srw_ss preflight
             (fn ss => with_context_rewrites ss
               (fn {convert,full_simp,...} =>
                 Tactical.TAC_PROOF ((context,t),
                   Tactical.THEN (Tactical.REPEAT
                     (cases (fn context =>
                       convert (List.map Thm.ASSUME context))),
                     Tactical.THEN (full_simp,
                       goal intLib.ARITH_TAC)))))) t)) ()

    fun unsupported t =
      raise ERR "bag_prove"
        ("unsupported bag encoding shape; checked replay handles native " ^
         "bag count characterizations and Z3 (_ map +) Int-array " ^
         "normalization; conclusion=" ^ Library.term_to_string t)

    fun bag_prove_with_arith_unbounded arith_prove t =
      if not (has_bag_encoding t) then unsupported t
      else
        simp_prove t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else pointwise_prove t
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else (admit t;arith_prove t)
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else unsupported t

    fun bag_prove_with_arith arith_prove t =
      if not (has_bag_encoding t) then unsupported t
      else
        SmtResource.with_resource_step_time "Bag" "bag-replay"
          (fn t =>
            (SmtResource.check_resource_goal "Bag" "bag-replay" t;
             bag_prove_with_arith_unbounded arith_prove t)) t

  in
    {prove=fn arith => protect (bag_prove_with_arith arith),
     contextual=protect contextual}
  end

  fun default_admission () = SmtReplayArithmetic.new_term_check
    {limit=SmtResource.max_bv_replay_term_nodes,observe=fn () => ()}
  fun bag_prove_with_admission admit arith =
    #prove (checked_procedures admit) arith
  fun bag_contextual_prove_with_admission admit context t =
    #contextual (checked_procedures admit) (context,t)
  fun bag_prove_with_arith arith t =
    bag_prove_with_admission (default_admission ()) arith t
  fun bag_prove t = bag_prove_with_arith intLib.ARITH_PROVE t

end
