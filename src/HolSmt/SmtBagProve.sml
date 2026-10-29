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
    fun admit tm = check tm handle primary => raise AdmissionFailure primary
    fun protect f x = f x handle AdmissionFailure primary =>
      SmtReplayArithmetic.propagate_admission_error primary
    fun goal tactic (assumptions,conclusion) =
      (List.app admit (conclusion::assumptions);
       tactic (assumptions,conclusion))
    fun theorem th =
      (List.app admit (Thm.concl th :: Thm.hyp th);th)
    fun cases input = goal (fn input as (_,conclusion) =>
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
        val law = theorem boolTheory.EXCLUDED_MIDDLE
        val _ = admit (boolSyntax.mk_disj
          (condition,boolSyntax.mk_neg condition))
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
      in Thm_cont.DISJ_CASES_THEN2
           (branch boolSyntax.T Drule.EQT_INTRO)
           (branch boolSyntax.F Drule.EQF_INTRO)
           (Thm.SPEC condition law) input end) input

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
        val avoids = Term.free_varsl (List.map #residue sigma)
        fun build bound tm =
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
             in Term.mk_comb (build bound f,build bound x) end
           else
             let val _ = check tm
                 val (v,b) = SmtReplayImport.dest_abs_preserving_names tm
                 val fresh = Term.variant (avoids @ List.map #2 bound)
                   (Term.mk_var (#1 (Term.dest_var v),
                     typed (Term.type_of v)))
             in Term.mk_abs (fresh,build ((v,fresh)::bound) b) end)
      in build [] end
    fun preflight check th tm =
      let
        val _ = List.app check (tm :: Thm.concl th :: Thm.hyp th)
        val left = boolSyntax.lhs
          (#2 (boolSyntax.strip_imp (Thm.concl th)))
        val rigid = Thm.hyp_frees th
        val types = HOLset.listItems (Thm.hyp_tyvars th)
        val (sigma,types) = HolKernel.ho_match_term types rigid left tm
        val instantiate = substitution check types sigma
        (* INST_TYPE precedes term INST, so admit that intermediate too. *)
        val typed = substitution check types []
        val _ = List.app (check o typed) (Thm.concl th :: Thm.hyp th)
        fun formula term =
          let val (conditions,equation) = boolSyntax.strip_imp term
              val (l,r) = boolSyntax.dest_eq equation
          in List.app check (l::r::conditions) end
        val source = Thm.concl th
        val initial = instantiate source
        val _ = formula initial
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
        fun paths variable pattern actual =
          (check boolSyntax.T;
           if Term.is_abs pattern then
             let val (v,body) =
                   SmtReplayImport.dest_abs_preserving_names pattern
             in if Term.aconv v variable then actual else
                 let val _ = check actual
                     val (w,b) =
                       SmtReplayImport.dest_abs_preserving_names actual
                 in Term.mk_abs (w,paths variable body b) end end
           else if Term.is_comb pattern then
             let val (head,args) = boolSyntax.strip_comb pattern
             in if Term.aconv head variable then betas (length args) actual
               else let val (f,x) = Term.dest_comb pattern
                        val (g,y) = Term.dest_comb actual
                    in Term.mk_comb
                      (paths variable f g,paths variable x y) end end
           else actual)
        fun substituted_lambda variable =
          let val variable = typed variable
          in List.exists (fn {redex,residue} =>
               Term.aconv redex variable andalso Term.is_abs residue) sigma
          end
        val functions = List.filter (fn variable =>
          Lib.can Type.dom_rng (Term.type_of variable) andalso
          substituted_lambda variable) (Term.free_vars source)
        fun phase (variable,actual) =
          let val result = paths variable source actual
                handle Feedback.HOL_ERR _ => actual
              val _ = formula result
          in result end
        val _ = List.foldl phase initial functions
      in () end
    fun with_rewrites facts prove =
      let
        (* ++ canonicalizes and indexes its added patterns eagerly. The
           dispatcher is too late to admit these first source operands. *)
        val _ = List.app (fn th => ignore (theorem th))
          (facts @ simpLib.frag_rewrites intSimps.INT_RWTS_ss)
      in SmtDatatypeProve.with_checked_rewrites_preflight admit
        (fn () => simpLib.++
          (simpLib.++ (bossLib.srw_ss(),intSimps.INT_RWTS_ss),
           simpLib.rewrites facts)) preflight prove end

    (* Demand the constructor guard BEFORE expanding INSERT's lambda. Keep
       constructor identities and shared element relationships in a small
       checked schema; only opaque constructor fields are named. A success
       is a universally proved equation, not authority from graph naming.
       Lift it once, after admitting the substituted sides, never the
       duplicated branch which the small proof has already discarded. *)
    fun small tm = Option.isSome
      (SmtReplayImport.bounded_raw_size_with_type_check_observed
        {limit=128,observe=fn () => admit boolSyntax.T,
         check_type=fn _ => ()} tm)
    fun erasure tm =
      let
        val (head,args) = boolSyntax.strip_comb tm
        val insert = named "bag" ["BAG_INSERT"] head andalso length args=3
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
        val remaining = ref 32
        fun constructor actual =
          if !remaining = 0 then atom actual else
          let val _ = admit boolSyntax.T
              val _ = remaining := !remaining-1
              val (con,fields) = boolSyntax.strip_comb actual
              (* Declaration identity is enough for shape discovery. Do
                 not type-instantiate a whole constructor bundle merely to
                 decide which syntax to keep in the checked schema. *)
              val constructors = case TypeBase.fetch (Term.type_of actual) of
                  NONE => []
                | SOME info => TypeBasePure.constructors_of info
          in if Term.is_const con andalso List.exists
              (fn ctor => (admit boolSyntax.T;Term.same_const con ctor))
              constructors then
               Term.list_mk_comb (con,List.map constructor fields)
             else atom actual end
          handle Feedback.HOL_ERR _ => atom actual
        val schema = if insert then
            Term.list_mk_comb (head,
              [constructor (hd args),atom (List.nth (args,1)),
               constructor (List.nth (args,2))])
          else let val (p,l,r) = boolSyntax.dest_cond tm
               in boolSyntax.mk_cond (atom p,atom l,atom r) end
        val _ = admit schema
        val result = with_rewrites (bag_rewrites_for schema)
          (fn ss => simpLib.SIMP_CONV ss [] schema)
        val (left,right) = boolSyntax.dest_eq (Thm.concl result)
        val _ = if Term.aconv left right orelse
            SmtResource.contains Term.is_abs (Thm.concl result)
          then raise Conv.UNCHANGED else ()
        (* This is an optional erasure, not an eager normalization pass.
           Require componentwise non-growth (each opaque field and the
           fixed syntax). Thus a reflexive fitting INSERT cannot be expanded
           into a duplicated conditional before reflexivity gets its turn. *)
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
        val _ = if fixed right <= fixed left andalso List.all
            (fn hole => occurrences hole right <= occurrences hole left)
            holes then () else raise Conv.UNCHANGED
        val sigma = List.map (fn (actual,hole) =>
          {redex=hole,residue=actual}) (Redblackmap.listItems (!bindings))
        val instantiate = substitution admit [] sigma
        val _ = List.app (admit o instantiate)
          (left::right::Thm.hyp result)
      in Thm.INST sigma result end
    fun simplify_erased prove t =
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
                  else NONE
                val result = SOME (erasure tm)
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
      simplify_erased (fn t => with_rewrites (bag_rewrites_for t)
        (fn ss => simpLib.SIMP_PROVE ss [] t)) t
    fun pointwise_prove t =
      SmtResource.with_resource_step_time "Bag" "bag-condition-splitting"
        (fn t =>
          (admit t;with_rewrites (bag_rewrites_for t) (fn ss =>
            Tactical.prove (t,
              Tactical.THEN (goal (simpLib.SIMP_TAC ss []),
                Tactical.THEN (Tactical.REPEAT (goal Tactic.STRIP_TAC),
                  Tactical.THEN
                    (Tactical.REPEAT (Tactical.THEN
                       (cases,
                        goal (simpLib.FULL_SIMP_TAC ss []))),
                     Tactical.THEN (goal (simpLib.FULL_SIMP_TAC ss []),
                       goal intLib.ARITH_TAC)))))))) t
    (* CPC's scoped fallback deliberately uses its old srw portfolio, not
       extra bag equations. Admit every actual Hyp and generated branch. *)
    fun contextual (context,t) =
      SmtResource.with_resource_step_time "Bag" "contextual" (fn () =>
        (List.app admit (t::context);
         SmtResource.check_resource_goal "Bag" "contextual" t;
         SmtDatatypeProve.with_checked_rewrites admit bossLib.srw_ss
           (fn ss => Tactical.TAC_PROOF ((context,t),
             Tactical.THEN (Tactical.REPEAT cases,
               Tactical.THEN (goal (bossLib.FULL_SIMP_TAC ss []),
                 goal intLib.ARITH_TAC)))))) ()

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
