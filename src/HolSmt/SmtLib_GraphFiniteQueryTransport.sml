(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphFiniteQueryTransport :>
    SmtLib_GraphFiniteQueryTransport =
struct
  structure L = SmtLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure LawDAG = SmtLib_GraphFiniteLawDAG
  structure Scope = SmtReplayOwnedScopeReceipt
  structure GP = SmtLib_GraphPreprocess
  structure Q = SmtLib_GraphQueryAnalysis
  structure B = SmtLib_GraphBackendSelection
  structure NC = SmtReplayNativeContract
  structure A = SmtReplayFocusAdmission
  structure C = SmtReplayCanonGraph
  structure Core = SmtReplayOwnedLargeProofCore
  structure Congruence = SmtLib_GraphScopedCongruence
  structure Recording = SmtLib_GraphConditionalLambdaLaw
  structure P = SmtReplayProof
  type scoped = Q.scoped_node
  datatype requirement = CheckedBinderBody of scoped
    | CheckedAlphaEvidence of {subject:scoped,saved:scoped}
    | CheckedParsedLiteral of scoped
    | CheckedOpening of {original:scoped,opened:scoped}
  type backend =
    {set_backend:L.outbound_set_backend,bag_backend:L.outbound_bag_backend,
     sequence_emission:bool,has_set_terms:bool,has_bag_terms:bool}
  type markers = {sets:scoped list,bags:scoped list,raw_numbers:scoped list}
  datatype finite = Finite of
    {identity:int,family:L.outbound_finite_family,subject:scoped,
     branch:finite_branch}
  and finite_branch = Domain of Type.hol_type | Evidence of V.fact
    | Empty | Insert of finite | Delete of finite
    | Union of finite * finite | InterLeft of finite
    | InterRight of finite | Difference of finite | Merge of finite * finite
    | Pending
  datatype syntax = Syntax of
    {identity:int,source:scoped,row:syntax_row}
  and syntax_row = Retain | Erase of finite | App of syntax * syntax
    | Binder of int
  datatype body_direction = FunctionChild | ArgumentChild | BinderBody
  datatype body_plan = BodyPlan of
    {identity:int,family:unit ref,work:W.portfolio,validation:V.validation,
     graph:G.graph,scope:G.scope,
     sources:S.sources,epoch:int,symbols:int,contract:NC.contract,
     ordinal:int,check_type:Type.hol_type -> unit,
     position:A.current_query_position,path:body_direction list,
     original:scoped,binder:scoped,body:scoped,syntax:syntax,
     requirements:requirement list,used:bool ref,
     recording:Recording.recorded option ref,
     completed:{equation:G.node,condition:G.node option,
       evidence:V.fact list} option ref}
  type body_description =
    {position:A.current_query_position,path:body_direction list,
     original:scoped,binder:scoped,body:scoped,
     requirements:requirement list,contract:NC.contract,ordinal:int}
  datatype body_program = BodyNeeds of requirement list
    | BodyLaw of {fact:P.closed_fact,condition:G.node option,
                  evidence:V.fact list,target:G.node}
  datatype plan = Plan of
    {work:W.portfolio,validation:V.validation,graph:G.graph,scope:G.scope,
     sources:S.sources,epoch:int,symbols:int,contract:NC.contract,
     ordinal:int,check_type:Type.hol_type -> unit,backend:backend,
     markers:markers,assumptions:(V.fact * syntax) list,goal:syntax,
     focus:A.policy_focus list,used:bool ref}
  datatype preparation = Ready of plan | Needs of requirement list
  datatype body_query_plan = BodyQueryPlan of
    {plan:plan,bodies:body_plan list,requirements:requirement list}
  type body_binding =
    {plan:body_plan,fact:P.closed_fact,condition:G.node,
     source:G.node,target:G.node,evidence:V.fact list}
  datatype nested_binding = NestedBinding of
    {binding:body_binding,frame:Scope.receipt,
     opening:P.scoped_generated_equality option,
     recording:Recording.recorded}
  datatype body_query_result = QueryNeeds of requirement list
    | QueryRewritten of
        {validation:V.validation,preprocessing:GP.validation,
         backend:backend,markers:markers}
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphFiniteQueryTransport"
  fun family_order L.FiniteSet = 0 | family_order L.FiniteBag = 1
  fun same_scoped (a:scoped,b:scoped) =
    #scope a= #scope b andalso #node a= #node b
  fun same_requirement (CheckedBinderBody a,CheckedBinderBody b) =
        same_scoped (a,b)
    | same_requirement (CheckedParsedLiteral a,CheckedParsedLiteral b) =
        same_scoped (a,b)
    | same_requirement (CheckedAlphaEvidence a,CheckedAlphaEvidence b) =
        same_scoped (#subject a,#subject b) andalso
        same_scoped (#saved a,#saved b)
    | same_requirement (CheckedOpening a,CheckedOpening b) =
        same_scoped (#original a,#original b) andalso
        same_scoped (#opened a,#opened b)
    | same_requirement _ = false
  fun compare_key ((a,b),(c,d)) = case Int.compare (a,c) of
      EQUAL => Int.compare (b,d) | order => order
  fun compare_trace ((a,b),(c,d)) = case Int.compare (a,c) of
      EQUAL => compare_key (b,d) | order => order
  fun source_of (Syntax {source,...}) = source
  fun unchanged (Syntax {row=Retain,...}) = true | unchanged _ = false

  fun body_guard expected (BodyPlan held) =
    (if Portable.pointer_eq (expected,#work held) then () else
       raise ERR "body_plan" "different original Work";
     V.validate_with_policy expected (#validation held);
     NC.validate_for expected (#contract held);
     if Type.type_epoch ()= #epoch held andalso
         Term.term_epoch ()= #symbols held then () else
       raise ERR "body_plan" "body declaration lifetime changed";
     List.app (fn ({scope,node}:scoped) =>
       (G.validate_scope (#graph held) scope;
        ignore (G.closure_root (#graph held) scope node)))
       [#original held,#binder held,#body held])
  fun body_description_with_policy_for expected
      (plan as BodyPlan
        {position,path,original,binder,body,requirements,contract,ordinal,
         ...}) =
    ((body_guard expected plan;
      {position=position,path=path,original=original,binder=binder,body=body,
       requirements=requirements,contract=contract,
       ordinal=ordinal}:body_description)
     handle primary => (W.close expected;raise primary))
  fun body_check_type_with_policy_for expected
      (plan as BodyPlan {check_type,...}) ty =
    ((body_guard expected plan;W.spend_policy expected 0;check_type ty;
      body_guard expected plan)
     handle primary => (W.close expected;raise primary))

  fun prepare_internal retain_bodies retain_query work
      (context:Q.outbound_context)
      {validation,operations,target,emit_sequences,native_contract,ordinal,
       check_type} finish =
    ((let
      val body_family = ref ()
      val current = V.current_facts_with_policy_for work validation
      val sources = W.original_sources work
      val graph = S.owning_graph sources val scope = S.owning_scope sources
      val _ = NC.validate_for work native_contract
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val pending = ref ([]:requirement list)
      val bodies = if retain_bodies then SOME (ref ([]:body_plan list))
        else NONE
      fun need item = pending := item :: !pending
      fun direction step path = if retain_bodies then step::path else path
      fun scoped current = case (#graph_node context) current of
          SOME result => result
        | NONE => raise ERR "prepare" "query operand is an outbound recipe"
      fun authentic current original =
        let val actual = scoped current in
          if #node actual=original then () else
          let val opened = G.cached_opened_view graph scope original
              val _ = G.validate_opened_view graph scope original opened
          in if #node opened= #node actual then () else raise ERR "prepare"
              "borrow belongs to a different current query" end
        end
      val _ = authentic (#goal context) (#goal current)
      val facts = #assumptions current
      val _ = if ListPair.allEq (fn (term,fact) =>
          (authentic term (V.endpoint fact);true))
            (#assumptions context,facts) then () else
        raise ERR "prepare" "different ordered current assumption list"
      val _ = authentic (#denied context) (V.endpoint (#denied current))
      val counter = ref 0
      fun fresh () =
        let val answer = !counter val _ = counter := answer+1 in answer end
      val raw = ref (Redblackmap.mkDict compare_trace :
        ((int * (int * int)),Q.carrier L.outbound_finite_report)
          Redblackmap.dict)
      fun trace (report:Q.carrier L.outbound_finite_report) =
        let val key = (family_order (#family report),
              (#key context) (#subject report))
            val _ = (#step context) ()
        in raw := Redblackmap.insert (!raw,key,report) end
    in B.with_finite_trace context trace
      {operations=operations,target=target,emit_sequences=emit_sequences}
      (fn {selection,finite_set_term,finite_bag_term,
           finite_set_hypothesis,finite_bag_hypothesis} =>
      let
        val finite_memo = ref (Redblackmap.mkDict compare_trace :
          ((int * (int * int)),finite) Redblackmap.dict)
        val syntax_memo = ref (Redblackmap.mkDict compare_key :
          ((int * int),syntax) Redblackmap.dict)
        fun filtered recognize = List.mapPartial (fn (term,fact) =>
          case recognize term of NONE => NONE | SOME operand =>
            SOME (operand,fact)) (ListPair.zip (#assumptions context,facts))
        val set_facts = filtered finite_set_hypothesis
        val bag_facts = filtered finite_bag_hypothesis
        fun checked_opening (original:scoped) (opened:scoped) =
          if #node original= #node opened then () else
          let
            val source = G.cached_opened_view graph (#scope original)
              (#node original)
            val _ = G.validate_opened_view graph (#scope original)
              (#node original) source
          in if #node source= #node opened then need (CheckedOpening
              {original=original,opened=opened})
            else raise ERR "prepare" "different registered syntax opening"
          end
        fun arguments node =
          let fun walk current result = case G.view graph current of
                  G.Application (head,argument) => walk head (argument::result)
                | _ => result
          in walk node [] end
        fun pair node = case arguments node of [left,right] => (left,right)
          | _ => raise ERR "prepare" "selected finite branch has wrong arity"
        fun predicate_operand node = case G.view graph node of
            G.Application (_,argument) => argument
          | _ => raise ERR "prepare" "finite evidence is not an application"
        fun nth [] _ = raise ERR "prepare" "finite evidence index absent"
          | nth (item::rest) index =
              if index=0 then item else nth rest (index-1)
        fun finite family subject (incoming:scoped) =
          let
            val key = (family_order family,
              (G.scope_id (#scope incoming),G.node_id (#node incoming)))
            val trace_key = (family_order family,(#key context) subject)
            val actual = scoped subject
          in case Redblackmap.peek (!finite_memo,key) of
              SOME result => result
            | NONE =>
              let
                val report = case Redblackmap.peek (!raw,trace_key) of
                    SOME result => result
                  | NONE => raise ERR "prepare"
                      "successful finite decision has no branch report"
                val _ = if #node (scoped (#subject report))= #node actual
                    then () else raise ERR "prepare"
                      "finite branch changed its actual scoped endpoint"
                val _ = case #branch report of L.Evidence _ => ()
                  | L.Domain _ => () | L.UniverseDomain _ => ()
                  | L.ComplementDomain _ => ()
                  | _ => checked_opening incoming actual
                fun child current original = finite family current
                  {scope= #scope actual,node=original}
                fun first current = child current (#1 (pair (#node actual)))
                fun second current = child current (#2 (pair (#node actual)))
                val branch = case #branch report of
                    L.Domain ty => Domain ty
                  | L.UniverseDomain ty => Domain ty
                  | L.ComplementDomain {element_type,...} =>
                      Domain element_type
                  | L.Evidence {saved,index} =>
                    let
                      val evidence = case family of L.FiniteSet => set_facts
                        | L.FiniteBag => bag_facts
                      val (operand,fact) = nth evidence index
                      val held = scoped saved
                      val _ = if #node (scoped operand)= #node held then ()
                        else raise ERR "prepare"
                          "different original finite evidence occurrence"
                      val original = predicate_operand (V.endpoint fact)
                      val _ = if #node incoming=original then () else
                        need (CheckedAlphaEvidence
                          {subject=incoming,
                           saved={scope=scope,node=original}})
                    in Evidence fact end
                  | L.Empty => Empty
                  | L.Insert (_,tail) => Insert (second tail)
                  | L.Delete (base,_) => Delete (first base)
                  | L.Union (left,right) => Union (first left,second right)
                  | L.InterLeft (left,_) => InterLeft (first left)
                  | L.InterRight (_,right) => InterRight (second right)
                  | L.Difference (left,_) => Difference (first left)
                  | L.Merge (left,right) => Merge (first left,second right)
                  | L.ParsedLiteral =>
                      (need (CheckedParsedLiteral actual);Pending)
                val result = Finite {identity=fresh (),family=family,
                  subject=incoming,branch=branch}
                val _ = (#step context) ()
                val _ = finite_memo :=
                  Redblackmap.insert (!finite_memo,key,result)
              in result end
          end
        val native_set = #set_backend selection=L.CVC5NativeSet
        val native_bag = #bag_backend selection=L.CVC5NativeBag
        fun erased family current operand =
          let val actual = scoped current
          in finite family operand
            {scope= #scope actual,node=predicate_operand (#node actual)} end
        fun erase current =
          case finite_set_hypothesis current of
            SOME operand => if native_set andalso finite_set_term operand
                then SOME (erased L.FiniteSet current operand)
                else NONE
          | NONE => (case finite_bag_hypothesis current of
              SOME operand => if native_bag andalso finite_bag_term operand
                  then SOME (erased L.FiniteBag current operand) else NONE
            | NONE => NONE)
        fun syntax current (original:scoped) position path =
          let val key =
                (G.scope_id (#scope original),G.node_id (#node original))
              val actual = scoped current
          in case Redblackmap.peek (!syntax_memo,key) of
              SOME result => result
            | NONE =>
              let
                val row = case erase current of SOME proof => Erase proof
                  | NONE => (case (#view context) current of
                      Q.ApplicationView (left,right) =>
                        let
                          val (f,x) = case G.view graph (#node actual) of
                              G.Application pair => pair
                            | _ => raise ERR "prepare"
                                "opened application view differs"
                          val a = syntax left
                            {scope= #scope actual,node=f} position
                            (direction FunctionChild path)
                          val b = syntax right
                            {scope= #scope actual,node=x} position
                            (direction ArgumentChild path)
                        in if unchanged a andalso unchanged b then Retain
                          else App (a,b) end
                    | Q.AbstractionView (_,body) =>
                        let val prior_pending = !pending
                            val body_node = scoped body
                            val result = syntax body body_node position
                              (direction BinderBody path)
                            val body_pending = !pending
                            val _ = if unchanged result then () else
                              need (CheckedBinderBody original)
                            val row = case bodies of NONE => Retain
                              | SOME saved =>
                              if unchanged result then Retain else
                              let
                                fun added remaining =
                                  if Portable.pointer_eq
                                      (remaining,prior_pending)
                                  then [] else case remaining of [] =>
                                    raise ERR "prepare"
                                      "body requirement suffix changed"
                                  | item::rest =>
                                      ((#step context) ();
                                       item::added rest)
                                val requirements =
                                  List.rev (added body_pending)
                                val identity = if retain_query then fresh ()
                                  else 0
                                val plan = BodyPlan
                                  {identity=identity,family=body_family,
                                   work=work,validation=validation,
                                   graph=graph,scope=scope,sources=sources,
                                   epoch=epoch,symbols=symbols,
                                   contract=native_contract,ordinal=ordinal,
                                   check_type=check_type,position=position,
                                   path=List.rev path,original=original,
                                   binder=actual,body=body_node,syntax=result,
                                   requirements=requirements,used=ref false,
                                   completed=ref NONE,recording=ref NONE}
                                val _ = (#step context) ()
                              in saved := plan:: !saved;
                                if retain_query then Binder identity
                                else Retain end
                        in row end
                    | _ => Retain)
                val _ = case row of Retain => ()
                  | _ => checked_opening original actual
                val result = Syntax
                  {identity=fresh (),source=original,row=row}
                val _ = (#step context) ()
                val _ = syntax_memo :=
                  Redblackmap.insert (!syntax_memo,key,result)
              in result end
          end
        fun dropped term =
          (native_set andalso Option.isSome (finite_set_hypothesis term))
          orelse
          (native_bag andalso Option.isSome (finite_bag_hypothesis term))
        (* The native programme filters the WHOLE assumption list before
           beginning replacement. Do not interleave later filter callbacks
           with an earlier retained assumption's recursive rewrite. *)
        fun retained [] _ = []
          | retained ((term,fact)::rest) index =
              if dropped term then retained rest (index+1)
              else (term,fact,index)::retained rest (index+1)
        val retained = retained
          (ListPair.zip (#assumptions context,facts)) (0:IntInf.int)
        fun selected [] = ([],[])
          | selected ((term,fact,index)::rest) =
              let
                val admission = A.current_query_with_policy work validation
                  (A.CurrentAssumption index)
                val result = syntax term
                  {scope=scope,node=V.endpoint fact}
                  (A.CurrentAssumption index) []
                val (tail,focus) = selected rest
              in ((fact,result)::tail,admission::focus) end
        val (assumptions,focus) = selected retained
        val admission =
          A.current_query_with_policy work validation A.CurrentGoal
        val goal = syntax (#goal context) {scope=scope,node= #goal current}
          A.CurrentGoal []
        val markers:markers =
          {sets=List.map scoped (#sets selection),
           bags=List.map scoped (#bags selection),
           raw_numbers=List.map scoped (#raw_numbers selection)}
        val backend:backend =
          {set_backend= #set_backend selection,
           bag_backend= #bag_backend selection,
           sequence_emission= #sequence_emission selection,
           has_set_terms=not (null (#sets selection)),
           has_bag_terms=not (null (#bags selection))}
        val _ = ignore ((#key context) (#goal context))
        fun query_plan () = Plan
        {work=work,validation=validation,graph=graph,scope=scope,
         sources=sources,epoch=epoch,symbols=symbols,
         contract=native_contract,ordinal=ordinal,check_type=check_type,
         backend=backend,markers=markers,assumptions=assumptions,goal=goal,
         focus=admission::focus,used=ref false}
        val requirements = List.rev (!pending)
        val saved = case bodies of NONE => []
          | SOME saved => List.rev (!saved)
        val retained = if retain_query then SOME (query_plan ()) else NONE
      in finish selection (if null (!pending) then Ready
          (case retained of SOME plan => plan | NONE => query_plan ())
        else Needs requirements) saved
        (Option.map (fn plan => BodyQueryPlan
          {plan=plan,bodies=saved,requirements=requirements}) retained) end)
    end) handle primary => (W.close work;raise primary))

  fun prepare_with_selection work context input finish =
    prepare_internal false false work context input
      (fn selection => fn result => fn _ => fn _ => finish selection result)
  fun prepare_with_bodies work context input finish =
    prepare_internal true false work context input
      (fn selection => fn result => fn bodies => fn _ =>
        finish selection result bodies)
  fun prepare_with_body_query work context input finish =
    prepare_internal true true work context input
      (fn selection => fn result => fn bodies => fn held =>
        case held of SOME query => finish selection result bodies query
          | NONE => raise ERR "prepare" "missing retained body programme")

  fun prepare work context input =
    prepare_with_selection work context input (fn _ => fn result => result)

  (* These are fixed, bounded declaration schemas, never query theorems.
     Only their type variables and graph-named holes are instantiated. *)
  fun specialize theorem =
    if boolSyntax.is_forall (Thm.concl theorem) then
      specialize (Drule.SPEC_ALL theorem)
    else if boolSyntax.is_imp (Thm.concl theorem) then
      let val antecedent = #1 (boolSyntax.dest_imp (Thm.concl theorem))
      in Thm.DISCH antecedent (specialize (Drule.UNDISCH theorem)) end
    else theorem
  fun backwards theorem = #2 (Thm.EQ_IMP_RULE (specialize theorem))
  fun curry theorem =
    let val (antecedent,_) = boolSyntax.dest_imp (Thm.concl theorem)
        val (left,right) = boolSyntax.dest_conj antecedent
    in Thm.DISCH left (Thm.DISCH right
      (Thm.MP theorem (Thm.CONJ (Thm.ASSUME left) (Thm.ASSUME right)))) end
  fun chosen left theorem =
    let val theorem = specialize theorem
        val (antecedent,_) = boolSyntax.dest_imp (Thm.concl theorem)
        val (a,b) = boolSyntax.dest_disj antecedent
    in if left then Thm.DISCH a (Thm.MP theorem
        (Thm.DISJ1 (Thm.ASSUME a) b))
      else Thm.DISCH b (Thm.MP theorem (Thm.DISJ2 a (Thm.ASSUME b))) end

  local
    val alpha = Type.mk_vartype "'finite_a"
    val beta = Type.mk_vartype "'finite_b"
    val x = Term.mk_var ("finite_x",alpha)
    val y = Term.mk_var ("finite_y",alpha)
    val z = Term.mk_var ("finite_z",alpha)
    val f = Term.mk_var ("finite_f",Type.--> (alpha,beta))
    val g = Term.mk_var ("finite_g",Type.--> (alpha,beta))
    val p = Term.mk_var ("finite_p",Type.bool)
    val q = Term.mk_var ("finite_q",Type.bool)
    val equality = boolSyntax.mk_eq (p,q)
    val fg = boolSyntax.mk_eq (f,g) val xy = boolSyntax.mk_eq (x,y)
    val yz = boolSyntax.mk_eq (y,z)
  in
    val reflexivity = Thm.REFL x
    val congruence = Thm.DISCH fg (Thm.DISCH xy
      (Thm.MK_COMB (Thm.ASSUME fg,Thm.ASSUME xy)))
    val transitivity = Thm.DISCH xy (Thm.DISCH yz
      (Thm.TRANS (Thm.ASSUME xy) (Thm.ASSUME yz)))
    val eq_true = Thm.DISCH p (Drule.EQT_INTRO (Thm.ASSUME p))
    val forward = Thm.DISCH equality (Thm.DISCH p
      (Thm.EQ_MP (Thm.ASSUME equality) (Thm.ASSUME p)))
    val conjunction_intro = Thm.DISCH p (Thm.DISCH q
      (Thm.CONJ (Thm.ASSUME p) (Thm.ASSUME q)))
    val negative = Thm.DISCH equality (Thm.DISCH (boolSyntax.mk_neg p)
      (Thm.EQ_MP (Thm.AP_TERM boolSyntax.negation (Thm.ASSUME equality))
        (Thm.ASSUME (boolSyntax.mk_neg p))))
  end
  val set_empty = specialize pred_setTheory.FINITE_EMPTY
  val set_insert = backwards pred_setTheory.FINITE_INSERT
  val set_delete = backwards pred_setTheory.FINITE_DELETE
  val set_union = curry (backwards pred_setTheory.FINITE_UNION)
  val set_left = chosen true pred_setTheory.FINITE_INTER
  val set_right = chosen false pred_setTheory.FINITE_INTER
  val set_difference = specialize pred_setTheory.FINITE_DIFF
  val bag_empty = specialize bagTheory.FINITE_EMPTY_BAG
  val bag_insert = backwards (Thm.CONJUNCT2 bagTheory.FINITE_BAG_THM)
  val bag_union = curry (backwards bagTheory.FINITE_BAG_UNION)
  val bag_left = chosen true bagTheory.BAG_INTER_FINITE
  val bag_right = chosen false bagTheory.BAG_INTER_FINITE
  val bag_difference = specialize bagTheory.FINITE_BAG_DIFF
  val bag_merge = curry (backwards bagTheory.FINITE_BAG_MERGE)
  val word_domain = specialize wordsTheory.WORD_FINITE
  val bool_domain =
    let
      val universe = pred_setSyntax.mk_univ Type.bool
      val variable = Term.mk_var
        ("finite_bool_set",Type.--> (Type.bool,Type.bool))
      val finite_universe = Drule.EQT_ELIM
        (Rewrite.PURE_REWRITE_CONV
          [pred_setTheory.UNIV_BOOL,pred_setTheory.FINITE_INSERT,
           pred_setTheory.FINITE_EMPTY] (pred_setSyntax.mk_finite universe))
      val subset = Thm.MP
        (Drule.ISPEC universe pred_setTheory.SUBSET_FINITE) finite_universe
    in Thm.MP (Thm.SPEC variable subset)
      (Drule.ISPEC variable pred_setTheory.SUBSET_UNIV) end
  fun bag_domain theorem =
    let
      val set = case Term.free_vars (Thm.concl theorem) of
          [variable] => variable
        | _ => raise ERR "bag_domain" "domain schema has unexpected holes"
      val (element,_) = Type.dom_rng (Term.type_of set)
      val bag = Term.mk_var
        ("finite_domain_bag",Type.--> (element,numSyntax.num))
      val generic = Term.prim_mk_const {Thy="bag",Name="SET_OF_BAG"}
      val head = Term.inst (Type.match_type
        (#1 (Type.dom_rng (Term.type_of generic))) (Term.type_of bag)) generic
      val set_of_bag = Term.mk_comb (head,bag)
      val finite_set = Thm.INST [{redex=set,residue=set_of_bag}] theorem
    in Rewrite.PURE_REWRITE_RULE [bagTheory.FINITE_SET_OF_BAG] finite_set end
  val word_bag_domain = bag_domain word_domain
  val bool_bag_domain = bag_domain bool_domain

  (* Typed atomic construction and native quotation shared by both
     instances of the finite proof programme. *)
  fun node_operations {work,graph,scope,contract,ordinal,check_type,guard} =
    let
      val native = NC.for_work work contract
      val template = #template_limit (#semantic_limits native)
      val type_ceiling = IntInf.fromInt (#type_work_limit native)
      fun tick () = (guard ();W.spend_policy work 1)
      fun type_weight theta substitute ty =
        let
          val _ = tick ()
          val found = if substitute then List.find
            (fn {redex,...} => Type.compare (redex,ty)=EQUAL) theta
            else NONE
        in case found of SOME {residue,...} =>
              type_weight theta false residue
          | NONE => if Type.is_vartype ty then 1 else
              List.foldl (fn (argument,total) =>
                let val result = total+type_weight theta substitute argument
                in if result<=type_ceiling then result else
                  raise ERR "schema" "native Type work exceeds cap"
                end) (1:IntInf.int) (#2 (Type.dest_type ty))
        end
      fun quoted amount =
        let val issued = W.unused_policy_ordinal work
              {role=W.LawInstance,minimum=ordinal}
            val allowance = W.reserve_policy work
              {role=W.LawInstance,ordinal=issued,amount=amount}
        in W.consume_policy work allowance amount end
      fun checked_type ty = (guard ();check_type ty;guard ())
      fun typed_constant generic argument_type =
        let
          val original_type = Term.type_of generic
          val theta = Type.match_type
            (#1 (Type.dom_rng original_type)) argument_type
          val input = type_weight [] false original_type
          val output = type_weight theta true original_type
          val _ = if input+output<=type_ceiling then () else
            raise ERR "schema" "atomic Type instance exceeds native cap"
          val _ = quoted (5+input+output)
          val _ = checked_type (Type.type_subst theta original_type)
          val result = Term.inst theta generic
          val _ = guard ()
        in result end
      fun node (position:scoped) =
        (guard ();G.validate_scope graph (#scope position);
         ignore (G.view graph (#node position));#node position)
      fun root position =
        let val result = node position
        in if G.scope_visible graph scope (G.node_scope graph result) then
            result else raise ERR "execute"
              "finite programme requires a checked private body" end
      fun equality left right =
        let val operator = G.constant graph scope
              (typed_constant boolSyntax.equality (G.type_of graph left))
        in G.application graph scope
          (G.application graph scope (operator,left),right) end
      fun negate input = G.application graph scope
        (G.constant graph scope boolSyntax.negation,input)
      val truth = G.constant graph scope boolSyntax.T
      fun finite_node family operand =
        let val generic = case family of L.FiniteSet =>
                pred_setSyntax.finite_tm
              | L.FiniteBag => Term.prim_mk_const
                  {Thy="bag",Name="FINITE_BAG"}
            val operator = typed_constant generic (G.type_of graph operand)
        in G.application graph scope
          (G.constant graph scope operator,operand) end

    in {tick=tick,root=root,equality=equality,negate=negate,truth=truth,
      finite_node=finite_node} end

  (* One finite branch and syntax programme, with either original V facts
     or source-free conditional body laws as its fact algebra. *)
  fun proof_program
      {tick,root,equality,finite_node,truth,application,schema,evidence,
       endpoint,binder} =
    let
      val finite_cache = ref (Redblackmap.mkDict Int.compare)
      val syntax_cache = ref (Redblackmap.mkDict Int.compare)
      fun prove (Finite {identity,family,subject,branch}) =
        let val _ = tick () val subject = root subject
            val target = finite_node family subject
        in case Redblackmap.peek (!finite_cache,identity) of
            SOME result =>
              (if endpoint result=target then result else
                 raise ERR "prove" "cached finite endpoint changed")
          | NONE =>
            let
              fun unary set bag child =
                schema (case family of L.FiniteSet => set
                  | L.FiniteBag => bag) [prove child] target
              fun binary set bag (left,right) =
                schema (case family of L.FiniteSet => set
                  | L.FiniteBag => bag) [prove left,prove right] target
              val result = case branch of Evidence fact =>
                  evidence fact target
                | Domain ty =>
                  let val boolean = Type.compare (ty,Type.bool)=EQUAL
                      val theorem = case family of L.FiniteSet =>
                            if boolean then bool_domain else word_domain
                        | L.FiniteBag => if boolean then bool_bag_domain
                            else word_bag_domain
                  in schema theorem [] target end
                | Empty => schema (case family of L.FiniteSet => set_empty
                    | L.FiniteBag => bag_empty) [] target
                | Insert child => unary set_insert bag_insert child
                | Delete child => unary set_delete bag_difference child
                | Union pair => binary set_union bag_union pair
                | InterLeft child => unary set_left bag_left child
                | InterRight child => unary set_right bag_right child
                | Difference child =>
                    unary set_difference bag_difference child
                | Merge pair => binary set_union bag_merge pair
                | Pending => raise ERR "prove"
                    "unchecked finite requirement in a Ready plan"
              val _ = tick ()
              val _ = finite_cache :=
                Redblackmap.insert (!finite_cache,identity,result)
            in result end
        end
      fun transformed (Syntax {identity,source,row}) =
        let val _ = tick () val original = root source
        in case Redblackmap.peek (!syntax_cache,identity) of
            SOME result => result
          | NONE =>
            let
              val result = case row of Retain => (original,NONE)
                | Binder identity => binder identity original
                | Erase proof => (truth,SOME
                    (schema eq_true [prove proof]
                      (equality original truth)))
                | App (left,right) =>
                  let
                    val (f,feq) = transformed left
                    val (x,xeq) = transformed right
                    val target = application (f,x)
                    fun relation old NONE =
                          schema reflexivity [] (equality old old)
                      | relation _ (SOME proof) = proof
                    val first = relation (root (source_of left)) feq
                    val second = relation (root (source_of right)) xeq
                  in (target,SOME (schema congruence [first,second]
                    (equality original target))) end
              val _ = tick ()
              val _ = syntax_cache :=
                Redblackmap.insert (!syntax_cache,identity,result)
            in result end
        end
    in {prove=prove,transformed=transformed} end

  fun execute expected (Plan {work,validation,graph,scope,sources,epoch,
      symbols,contract,ordinal,check_type,backend,markers,assumptions,goal,
      focus,used}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "execute" "different original Work";
      let val law_frame = Scope.root_with_policy expected
      in W.with_step expected (fn () =>
      let
        val limits = W.semantic_policy work
        val owner = {work=work,graph=graph,scope=scope,sources=sources}
        fun guard () =
          (W.validate_policy work graph scope sources limits;
           NC.validate_for work contract;
           if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
             then () else raise ERR "execute" "query declaration changed")
        val _ = guard ()
        val current = V.current_facts_with_policy_for work validation
        val _ = List.app (A.validate_with_policy_for owner) focus
        val _ = if !used then raise ERR "execute" "finite plan consumed"
          else used := true
        val {tick,root,equality,negate,truth,finite_node} = node_operations
          {work=work,graph=graph,scope=scope,contract=contract,
           ordinal=ordinal,check_type=check_type,guard=guard}

        (* The same quoted declaration matcher also constructs source-free
           conditional laws in genuine body frames. Only this final Apply
           consumes the actual current root facts on the old path. *)
        val law_context = LawDAG.create_with_policy work
          {frame=law_frame,native_contract=contract,
           profiles=[],ordinal=ordinal,check_type=check_type}
        fun schema theorem premises target =
          let val law = LawDAG.schema_with_policy work law_context
                {theorem=theorem,premises=List.map V.endpoint premises,
                 target=target}
          in V.apply_with_policy work
            {law=law,premises=premises,target=target} end

        fun evidence fact target =
          if V.endpoint fact=target then fact else
            raise ERR "prove" "finite evidence is not exact"
        val {transformed,...} = proof_program
          {tick=tick,root=root,equality=equality,finite_node=finite_node,
           truth=truth,application=G.application graph scope,schema=schema,
           evidence=evidence,endpoint=V.endpoint,
           binder=fn _ => fn _ => raise ERR "execute"
             "unchecked binder in a Ready plan"}
        fun assertion (fact,syntax) =
          let val (target,equality) = transformed syntax
          in case equality of NONE => fact
            | SOME proof => schema forward [proof,fact] target end
        val selected = List.map assertion assumptions
        val (positive,goal_equality) = transformed goal
        val denied = case goal_equality of NONE => #denied current
          | SOME proof => schema negative [proof,#denied current]
              (negate positive)
        val validation = V.validate_portfolio_with_policy work
          {assumptions=selected,goal=positive,denied=denied}
        val preprocessing = GP.from_portfolio_with_policy work validation
        val _ = guard ()
      in {validation=validation,preprocessing=preprocessing,
          backend=backend,markers=markers} end) end)
     handle primary => (W.close expected;raise primary))

  (* Retained body traces use the same branch and congruence programme.
     Conditions retain the original parent facts as DATA; the closed law
     proves only their conditional consequence, never those Source facts. *)
  fun binary_statement graph constant node =
    case G.view graph node of G.Application (partial,right) =>
      (case G.view graph partial of G.Application (head,left) =>
         (case G.view graph head of G.Constant _ =>
            if Term.same_const (G.representative graph head) constant
            then (left,right) else
              raise ERR "nested_binding" "different statement declaration"
          | _ => raise ERR "nested_binding" "nonconstant statement head")
       | _ => raise ERR "nested_binding" "partial statement")
    | _ => raise ERR "nested_binding" "absent statement"

  (* This retains an actual completed body programme and its genuine
     parent-frame law. It does not accept an arbitrary theorem/Ready flag. *)
  fun nested_data expected
      (NestedBinding {binding={plan=plan as BodyPlan
          {identity,family,graph,scope=root,sources,binder,body,original,
           validation,completed,contract,recording=retained_recording,...},
           fact,condition,source,target,evidence},frame,opening,recording}) =
    let
      val _ = body_guard expected plan
      val _ = case !retained_recording of SOME actual =>
            if Portable.pointer_eq (actual,recording) then () else
              raise ERR "nested_binding" "different actual recording programme"
        | NONE => raise ERR "nested_binding"
            "body binding has no actual recording programme"
      val owner = Scope.description_with_policy_for expected frame
      val scope = #scope owner
      fun tick () = (body_guard expected plan;W.spend_policy expected 1)
      val _ = if Portable.pointer_eq (#graph owner,graph) andalso
          Portable.pointer_eq (#sources owner,sources) andalso
          #root owner=root andalso scope= #scope binder andalso
          scope= #scope original andalso source= #node binder then () else
        raise ERR "nested_binding" "different authentic parent frame"
      val recorded = Recording.recorded_with_policy_for expected recording
      val _ = if Portable.pointer_eq (#native_contract recorded,contract)
          andalso Portable.pointer_eq (#fact recorded,fact) andalso
          Portable.pointer_eq (#frame recorded,frame) andalso
          #source recorded=source andalso #target recorded=target andalso
          #condition recorded=condition then () else
        raise ERR "nested_binding" "different actual recording programme"
      val _ = P.validate_closed_fact_in_scope_with_policy_for expected
        {frame=frame,fact= #fact recorded}
      val actual = case !completed of SOME value => value
        | NONE => raise ERR "nested_binding" "body has no completed programme"
      val (old,new) = binary_statement graph boolSyntax.equality
        (#equation actual)
      val prior = G.binder_closure_data graph scope
        (G.binder_closure graph scope source)
      val next = G.binder_closure_data graph scope
        (G.binder_closure graph scope target)
      val exact_condition = case #condition actual of SOME saved =>
            saved=condition
        | NONE => (case G.view graph condition of G.Constant _ =>
            Term.same_const (G.representative graph condition) boolSyntax.T
          | _ => false)
      val _ = if old= #node body andalso #body prior=old andalso
          #body_frame prior= #scope body andalso
          #binder prior= #binder next andalso
          #body_frame prior= #body_frame next andalso #body next=new andalso
          exact_condition andalso ListPair.allEq (fn (a,b) =>
            (tick ();Portable.pointer_eq (a,b)))
            (#evidence actual,evidence) then () else
        raise ERR "nested_binding" "different actual completed body result"
      val (antecedent,conclusion) = binary_statement graph
        boolSyntax.implication (P.closed_node fact)
      val (left,right) = binary_statement graph boolSyntax.equality conclusion
      val current = V.current_facts_with_policy_for expected validation
      val _ = if antecedent=condition andalso left=source andalso
          right=target andalso List.all (fn item =>
            List.exists (fn saved => (tick ();
              Portable.pointer_eq (item,saved))) (#assumptions current))
              evidence then () else
        raise ERR "nested_binding" "different conditional law or evidence"
      val opened = case opening of NONE =>
            if #node original=source then NONE else
              raise ERR "nested_binding" "missing genuine scoped opening"
        | SOME saved =>
            let val actual = P.scoped_generated_equality_with_policy_for
                  expected {frame=frame,equality=saved}
                val _ = if #source actual= #node original andalso
                    #target actual=source then () else
                  raise ERR "nested_binding" "different scoped opening"
                val _ = P.validate_closed_fact_in_scope_with_policy_for
                  expected {frame=frame,fact= #fact actual}
            in SOME (#fact actual) end
      val _ = tick ()
    in {identity=identity,family=family,scope=scope,original=original,
      source=source,target=target,fact=fact,condition=condition,
      evidence=evidence,opening=opened} end

  fun retain_recorded_with_policy expected
      (plan as BodyPlan {recording,completed,contract,binder,body,...})
      receipt =
    ((W.with_step expected (fn () =>
      let
        val _ = body_guard expected plan
        val _ = case !recording of NONE => ()
          | SOME actual => if Portable.pointer_eq (actual,receipt) then () else
              raise ERR "recorded_body" "body recording already retained"
        val actual = Recording.recorded_with_policy_for expected receipt
        val frame = #frame actual
        val owner = Scope.description_with_policy_for expected frame
        val graph = #graph owner val scope = #scope owner
        val result = case !completed of SOME value => value
          | NONE => raise ERR "recorded_body" "body programme not completed"
        val (left,right) = binary_statement graph boolSyntax.equality
          (#equation result)
        val target = G.binder_closure_data graph scope
          (G.binder_closure graph scope (#target actual))
        val source = G.binder_closure_data graph scope
          (G.binder_closure graph scope (#source actual))
        val exact_condition = case #condition result of SOME held =>
              held= #condition actual
          | NONE => (case G.view graph (#condition actual) of G.Constant _ =>
              Term.same_const (G.representative graph (#condition actual))
                boolSyntax.T | _ => false)
        val _ = if Portable.pointer_eq (#native_contract actual,contract)
            andalso scope= #scope binder andalso
            #source actual= #node binder andalso left= #node body andalso
            #body source=left andalso #body target=right andalso
            #body_frame source= #scope body andalso
            #body_frame target= #scope body andalso
            #binder source= #binder target andalso exact_condition then ()
          else raise ERR "recorded_body"
            "recording differs from actual completed body programme"
        val _ = W.spend_policy expected 1
      in recording := SOME receipt end))
      handle primary => (W.close expected;raise primary))

  fun seal_nested_with_policy expected plan
      {recording,evidence,opening} =
    ((let val recorded = W.with_step expected (fn () =>
            (body_guard expected plan;
             Recording.recorded_with_policy_for expected recording))
          val held = NestedBinding
        {binding={plan=plan,fact= #fact recorded,
           condition= #condition recorded,source= #source recorded,
           target= #target recorded,evidence=evidence},frame= #frame recorded,
         opening=opening,recording=recording}
          val _ = W.with_step expected (fn () =>
            ignore (nested_data expected held))
      in held end) handle primary => (W.close expected;raise primary))

  fun realize_body_internal nested expected
      (plan as BodyPlan {work,graph,scope=root,sources,contract,ordinal,
        check_type,binder,body,syntax,requirements,used,completed,family,...})
      {validation,root_frame,parent_frame,body_frame,admission,profiles} =
    ((let
      val _ = W.with_step expected (fn () =>
        (body_guard expected plan;
         ignore (V.current_facts_with_policy_for expected validation)))
      val supplied = case nested of NONE => [] | SOME bindings =>
        W.with_step expected (fn () =>
          List.map (nested_data expected) bindings)
      fun supported position = List.exists (fn item =>
        Portable.pointer_eq (family,#family item) andalso
        #scope (#original item)= #scope position andalso
        #node (#original item)= #node position) supplied
      fun pending (CheckedAlphaEvidence _) = false
        | pending (CheckedBinderBody position) = not (supported position)
        | pending (CheckedOpening {original,opened}) = not
            (List.exists (fn item =>
              Portable.pointer_eq (family,#family item) andalso
              #scope (#original item)= #scope original andalso
              #node (#original item)= #node original andalso
              #scope item= #scope opened andalso #source item= #node opened)
              supplied)
        | pending _ = true
      val pending = if null requirements then [] else
        List.filter pending requirements
    in if not (null pending) then BodyNeeds requirements else
      let
        val parent = Scope.description_with_policy_for expected parent_frame
        val parent_scope = #scope parent
        val owner = {graph=graph,scope=parent_scope,sources=sources,work=work}
        val actual = A.describe_with_policy_for owner admission
        val closure = G.closure_child_binder graph parent_scope (#child actual)
        val captured = G.binder_closure_data graph parent_scope closure
        val inner = Scope.description_with_policy_for expected body_frame
        val outer = Scope.description_with_policy_for expected root_frame
        val _ = if #node actual= #node binder andalso
            parent_scope= #scope binder andalso
            #body captured= #node body andalso
            #body_frame captured= #scope body andalso
            #scope inner= #body_frame captured andalso
            #scope outer=root andalso #root inner=root andalso
            #root parent=root andalso
            List.all (fn value =>
              Portable.pointer_eq (#graph value,graph) andalso
              Portable.pointer_eq (#sources value,sources))
              [parent,inner,outer] then () else
          raise ERR "realize_body" "different authentic binder frames"
        val body_scope = #scope inner
        fun guard () =
          (body_guard expected plan;
           A.validate_with_policy_for owner admission;
           ignore (Scope.description_with_policy_for expected root_frame);
           ignore (Scope.description_with_policy_for expected parent_frame);
           ignore (Scope.description_with_policy_for expected body_frame);
           List.app (G.validate_policy_opaque_profile graph) profiles)
        val _ = guard ()
        val _ = if !used then raise ERR "realize_body" "body plan consumed"
          else ()
        fun action compute = W.with_step work (fn () =>
          let val _ = guard () val result = compute ()
              val _ = guard () in result end)
        val (nodes,context,requests) = action (fn () =>
          let
            val nodes = node_operations
              {work=work,graph=graph,scope=body_scope,contract=contract,
               ordinal=ordinal,check_type=check_type,guard=guard}
            val context = LawDAG.create_with_condition_frame_with_policy work
              {frame=body_frame,condition_frame=root_frame,
               native_contract=contract,profiles=profiles,ordinal=ordinal,
               check_type=check_type}
            val seen = ref (Redblackset.empty Int.compare)
            val requests = ref ([]:(V.fact * G.node * scoped) list)
            fun finite (Finite {identity,family,subject,branch}) =
              ((#tick nodes) ();
               if Redblackset.member (!seen,identity) then () else
               (seen := Redblackset.add (!seen,identity);
                case branch of Evidence fact =>
                    let val target = (#finite_node nodes) family
                          ((#root nodes) subject)
                    in requests := (fact,target,subject):: !requests end
                  | Insert child => finite child | Delete child => finite child
                  | Union (left,right) => (finite left;finite right)
                  | InterLeft child => finite child
                  | InterRight child => finite child
                  | Difference child => finite child
                  | Merge (left,right) => (finite left;finite right)
                  | _ => ()))
            fun visit (Syntax {row,...}) = case row of Retain => ()
              | Erase proof => finite proof
              | App (left,right) => (visit left;visit right)
              | Binder _ => ()
            val _ = visit syntax
          in (nodes,context,List.rev (!requests)) end)
        fun matching (fact,target,_) = action (fn () =>
          let val source = V.endpoint fact
          in if source=target then true else
            case (G.view graph source,G.view graph target) of
                (G.Application (f,x),G.Application (g,y)) => f=g andalso x=y
              | _ => false end)
        fun prepare_alignment (request as (fact,target,subject)) =
          if matching request then (request,NONE,NONE) else
          case Congruence.prepare_with_policy work
              {frame=body_frame,source=V.endpoint fact,target=target,
               native_contract=contract,profiles=profiles,ordinal=ordinal,
               check_type=check_type} of
            Congruence.Prepared held => (request,SOME held,NONE)
          | Congruence.DifferentShape =>
              let val saved = case G.view graph (V.endpoint fact) of
                      G.Application (_,operand) => operand
                    | _ => raise ERR "realize_body" "evidence is not finite"
              in (request,NONE,SOME (CheckedAlphaEvidence
                {subject=subject,saved={scope=root,node=saved}})) end
        val prepared = List.map prepare_alignment requests
        val unfinished = List.mapPartial #3 prepared
      in if not (null unfinished) then BodyNeeds unfinished else
        let
          val _ = used := true
          fun align ((fact,target,_),prepared,_) =
            let val source = V.endpoint fact in
              case prepared of SOME held =>
                let val fact_proof = Congruence.execute_with_policy work held
                    val _ = guard ()
                in (fact,target,SOME fact_proof) end
              | NONE => if source=target then (fact,target,NONE) else
              let
                val recipe = action (fn () =>
                  let fun observe () = (#tick nodes) ()
                      val (f,x) = case G.view graph source of
                          G.Application pair => pair
                        | _ => raise ERR "realize_body"
                            "finite evidence lost its application"
                      val a = C.graph_identity graph body_scope
                        {observe=observe} f
                      val b = C.graph_identity graph body_scope
                        {observe=observe} x
                      val recipe = C.graph_application graph body_scope
                        {source=source,left=a,right=b,observe=observe}
                      val _ = if C.graph_result recipe=target then () else
                        raise ERR "realize_body"
                          "checked evidence correspondence differs"
                  in recipe end)
                val fresh = action (fn () => W.unused_policy_ordinal work
                  {role=W.FinalFreeze,minimum=ordinal})
                val result = Core.execute_with_policy work
                  (Core.prepare_in_scope_with_policy work
                    {frame=body_frame,conversion=recipe,ordinal=fresh,
                     native_contract=contract,profiles=profiles,
                     check_type=check_type})
                val converted = Core.conversion_description_with_policy_for
                  work result
                val _ = if #source converted=source andalso
                    #target converted=target then () else
                  raise ERR "realize_body" "evidence proof endpoints changed"
                val closed = P.policy_source_realization_closed_fact_for work
                  (Core.realization_with_policy_for work result)
                val _ = guard ()
              in (fact,target,SOME closed) end
            end
          val alignments = List.map align prepared
          val (program,description,evidence) = action (fn () =>
            let
              fun data ({program,...}:
                  {program:LawDAG.conditional,evidence:V.fact list}) =
                LawDAG.description_with_policy_for work context program
              fun schema theorem premises target =
                let val law = LawDAG.schema_with_policy work context
                      {theorem=theorem,
                       premises=List.map (fn item => #target (data item))
                         premises,target=target}
                    val program = LawDAG.apply_with_policy work context
                      {law=law,premises=List.map #program premises,
                       target=target}
                in {program=program,
                  evidence=List.concat (List.map #evidence premises)} end
              fun evidence fact target =
                let
                  val original = V.endpoint fact
                  val first =
                    {program=LawDAG.evidence_with_policy work context original,
                     evidence=[fact]}
                  fun seek [] = raise ERR "realize_body"
                        "missing checked evidence correspondence"
                    | seek ((held,node,proof)::rest) =
                        ((#tick nodes) ();
                         if Portable.pointer_eq (held,fact) andalso node=target
                         then proof else seek rest)
                in case seek alignments of NONE => first
                  | SOME proof =>
                      let val law = V.scoped_recorded_closed_with_policy work
                            body_frame proof
                          val equality =
                            {program=LawDAG.of_closed_with_policy work context
                               law,evidence=[]}
                      in schema forward [equality,first] target end
                end
              fun inner_binder identity actual =
                let
                  fun seek [] = raise ERR "realize_body"
                        "missing genuine nested binder law"
                    | seek (item::rest) =
                        ((#tick nodes) ();
                         if Portable.pointer_eq (family,#family item)
                             andalso identity= #identity item then item
                         else seek rest)
                  val item = seek supplied
                  val _ = if #scope item=body_scope andalso
                      #scope (#original item)=body_scope andalso
                      #node (#original item)=actual then () else
                    raise ERR "realize_body"
                      "different actual nested body slot"
                  fun condition node [] =
                        if node= #truth nodes then
                          (schema boolTheory.TRUTH [] node,[]) else
                          raise ERR "realize_body" "missing nested evidence"
                    | condition node (facts as fact::rest) =
                        if node=V.endpoint fact then
                          ({program=LawDAG.evidence_with_policy work context
                              node,evidence=[fact]},rest)
                        else
                          let
                            val (a,b) = binary_statement graph
                              boolSyntax.conjunction node
                            val (left,remaining) = condition a facts
                            val (right,remaining) = condition b remaining
                          in (schema conjunction_intro [left,right] node,
                              remaining) end
                  val (premise,remaining) = condition (#condition item)
                    (#evidence item)
                  val _ = if null remaining then () else
                    raise ERR "realize_body" "unused nested ordered evidence"
                  val law = V.scoped_recorded_closed_with_policy work
                    body_frame (#fact item)
                  val target = (#equality nodes) (#source item) (#target item)
                  val applied = LawDAG.apply_with_policy work context
                    {law=law,premises=[#program premise],target=target}
                  val result = {program=applied,evidence= #evidence premise}
                  val result = case #opening item of NONE => result
                    | SOME fact =>
                        let
                          val opening =
                            {program=LawDAG.of_closed_with_policy work context
                               (V.scoped_recorded_closed_with_policy work
                                  body_frame fact),evidence=[]}
                        in schema transitivity [opening,result]
                          ((#equality nodes) actual (#target item)) end
                in (#target item,SOME result) end
              val {transformed,...} = proof_program
                {tick= #tick nodes,root= #root nodes,
                 equality= #equality nodes,finite_node= #finite_node nodes,
                 truth= #truth nodes,
                 application=G.application graph body_scope,
                 schema=schema,evidence=evidence,
                 endpoint=fn item => #target (data item),
                 binder=case nested of NONE =>
                   (fn _ => fn _ => raise ERR "realize_body"
                     "unchecked nested binder body")
                   | SOME _ => inner_binder}
              val (_,changed) = transformed syntax
              val result = case changed of SOME value => value
                | NONE => raise ERR "realize_body" "retained body is unchanged"
              val description = data result
              val _ = if #evidence description=
                  List.map V.endpoint (#evidence result) then () else
                raise ERR "realize_body" "ordered body evidence differs"
            in (#program result,description,#evidence result) end)
          val fact = LawDAG.realize_with_policy work context program
          val _ = guard ()
          val _ = completed := SOME {equation= #target description,
            condition= #condition description,evidence=evidence}
        in BodyLaw {fact=fact,condition= #condition description,
          evidence=evidence,target= #target description} end
      end
    end) handle primary => (W.close expected;raise primary))

  fun realize_body_with_policy expected plan input =
    realize_body_internal NONE expected plan input

  fun realize_body_with_nested_with_policy expected plan
      {validation,root_frame,parent_frame,body_frame,admission,profiles,
       bindings} =
    realize_body_internal (SOME bindings) expected plan
      {validation=validation,root_frame=root_frame,parent_frame=parent_frame,
       body_frame=body_frame,admission=admission,profiles=profiles}

  fun execute_body_query_with_policy expected
      (BodyQueryPlan {plan=Plan {work,validation,graph,scope,sources,epoch,
        symbols,contract,ordinal,check_type,backend,markers,assumptions,goal,
        focus,used},bodies,requirements})
      {opening:SmtLib_GraphCheckedQueryOpening.opened_query,bindings} =
    ((if Portable.pointer_eq(expected,work) then () else
        raise ERR "execute_body_query" "different original Work";
      let val frame = Scope.root_with_policy expected
      in W.with_step expected (fn () =>
      let
        val limits = W.semantic_policy work
        fun guard () =
          (W.validate_policy work graph scope sources limits;
           NC.validate_for work contract;
           ignore (Scope.description_with_policy_for work frame);
           if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
             then () else raise ERR "execute_body_query"
               "original declaration lifetime changed")
        fun tick () = (guard ();W.spend_policy work 1)
        val _ = guard ()
        val original = V.current_facts_with_policy_for work validation
        val current = V.current_facts_with_policy_for work
          (#validation opening)
        val owner = {work=work,graph=graph,scope=scope,sources=sources}
        val _ = List.app (A.validate_with_policy_for owner) focus
        fun conversion old fresh NONE =
              if old=fresh then () else raise ERR "execute_body_query"
                "changed current root has no checked opening conversion"
          | conversion old fresh (SOME proof) =
              (P.validate_conversion_for work proof;
               P.validate_conversion_with_policy graph scope
                 (#template_limit limits) proof;
               if P.conversion_source proof=old andalso
                   P.conversion_target proof=fresh then () else
                 raise ERR "execute_body_query"
                   "different actual checked opening endpoints")
        fun assumptions_check [] [] [] _ = ()
          | assumptions_check (old::olds) (fresh::news)
              ({occurrence,conversion=proof}::ports) index =
              (tick ();
               if occurrence=index then () else raise ERR "execute_body_query"
                 "different ordered opening occurrence";
               conversion (V.endpoint old) (V.endpoint fresh) proof;
               assumptions_check olds news ports (index+1:IntInf.int))
          | assumptions_check _ _ _ _ = raise ERR "execute_body_query"
              "different ordered opening assumption list"
        val _ = assumptions_check (#assumptions original)
          (#assumptions current) (#assumptions opening) 0
        val _ = conversion (#goal original) (#goal current) (#goal opening)
        val _ = conversion (V.endpoint (#denied original))
          (V.endpoint (#denied current)) (#denied opening)

        (* The conversion ports establish the root correspondence. Follow
           actual paired App edges to locate its internal original/opened
           endpoints; a name, Q.same or copied Scope never substitutes. *)
        val aliases = ref (Redblackmap.mkDict Int.compare :
          (int,G.node*G.node) Redblackmap.dict)
        fun paired [] = ()
          | paired ((left,right)::rest) =
            let
              val _ = tick ()
              val _ = ignore (G.closure_root graph scope left)
              val _ = ignore (G.closure_root graph scope right)
              val index = G.node_id left
            in case Redblackmap.peek (!aliases,index) of
                SOME (saved,target) =>
                  if saved=left andalso target=right then paired rest else
                    raise ERR "execute_body_query"
                      "incoherent actual opening correspondence"
              | NONE =>
                let val _ = aliases := Redblackmap.insert
                      (!aliases,index,(left,right))
                    val children = if left=right then [] else
                      case (G.view graph left,G.view graph right) of
                          (G.Application (f,x),G.Application (g,y)) =>
                            [(f,g),(x,y)]
                        | (G.OpaqueRetained,G.AdmittedBinder _) =>
                            let val source = G.cached_opened_view graph scope
                                  left
                                val _ = G.validate_opened_view graph scope
                                  left source
                            in if #node source=right then [] else
                              raise ERR "execute_body_query"
                                "different registered opening leaf" end
                        | _ => raise ERR "execute_body_query"
                            "different actual opening constructor"
                in paired (children @ rest) end
            end
        val root_pairs = ListPair.mapEq
          (fn (old,fresh) => (V.endpoint old,V.endpoint fresh))
          (#assumptions original,#assumptions current)
        val _ = paired (root_pairs @ [(#goal original,#goal current),
          (V.endpoint (#denied original),V.endpoint (#denied current))])
        fun mapped (position:scoped) =
          let val _ = tick ()
              val _ = G.validate_scope graph (#scope position)
          in if #scope position<>scope then raise ERR "execute_body_query"
              "root programme contains a private body operand"
            else case Redblackmap.peek (!aliases,G.node_id (#node position)) of
                SOME (saved,current) =>
                  if saved= #node position then current else
                    raise ERR "execute_body_query" "different original node"
              | NONE => #node position end
        fun member_plan plan = List.exists
          (fn saved => (tick ();Portable.pointer_eq (plan,saved))) bodies
        fun condition_fact fact = List.exists
          (fn saved => (tick ();Portable.pointer_eq (fact,saved)))
          (#assumptions original)
        fun equation node = case G.view graph node of
            G.Application (partial,right) =>
              (case G.view graph partial of G.Application (head,left) =>
                (case G.view graph head of G.Constant _ =>
                  if Term.same_const (G.representative graph head)
                      boolSyntax.equality then (left,right) else
                    raise ERR "execute_body_query" "body law is not equality"
                | _ => raise ERR "execute_body_query"
                    "body law has no equality declaration")
              | _ => raise ERR "execute_body_query" "body equality is partial")
          | _ => raise ERR "execute_body_query" "body equality is absent"
        fun implication node = case G.view graph node of
            G.Application (partial,right) =>
              (case G.view graph partial of G.Application (head,left) =>
                (case G.view graph head of G.Constant _ =>
                  if Term.same_const (G.representative graph head)
                      boolSyntax.implication then (left,right) else
                    raise ERR "execute_body_query"
                      "body law is not conditional"
                | _ => raise ERR "execute_body_query"
                    "body law has no implication declaration")
              | _ => raise ERR "execute_body_query" "body law is partial")
          | _ => raise ERR "execute_body_query" "body law has no statement"
        fun binding (held as {plan=body as BodyPlan
              {identity,binder,body=old_body,original=prior,completed,
               recording,contract,...},
               fact,condition,source,
               target,evidence}:body_binding) =
          let
            val _ = body_guard work body
            val _ = if member_plan body then () else
              raise ERR "execute_body_query" "different retained body plan"
          in if #scope binder<>scope orelse #scope prior<>scope then NONE else
          let
            val _ = if mapped prior= #node binder andalso
                source= #node binder then () else
              raise ERR "execute_body_query" "different actual root body slot"
            val actual_recording = case !recording of SOME receipt =>
                  Recording.recorded_with_policy_for work receipt
              | NONE => raise ERR "execute_body_query"
                  "body binding has no actual recording programme"
            val recorded_owner = Scope.description_with_policy_for work
              (#frame actual_recording)
            val _ = if Portable.pointer_eq (#fact actual_recording,fact)
                andalso Portable.pointer_eq
                  (#native_contract actual_recording,contract) andalso
                Portable.pointer_eq (#graph recorded_owner,graph) andalso
                #scope recorded_owner=scope andalso
                Portable.pointer_eq (#sources recorded_owner,sources)
              then ()
              else raise ERR "execute_body_query"
                "body binding differs from actual recording programme"
            val _ = P.validate_closed_fact_in_scope_with_policy_for work
              {frame=frame,fact= #fact actual_recording}
            val actual = case !completed of SOME result => result
              | NONE => raise ERR "execute_body_query"
                  "retained body programme has no checked result"
            val (old,new) = equation (#equation actual)
            val before_closure = G.binder_closure_data graph scope
              (G.binder_closure graph scope source)
            val after_closure = G.binder_closure_data graph scope
              (G.binder_closure graph scope target)
            val exact_condition = case #condition actual of
                SOME old => old=condition
              | NONE => (case G.view graph condition of G.Constant _ =>
                  Term.same_const (G.representative graph condition)
                    boolSyntax.T | _ => false)
            val _ = if old= #node old_body andalso
                #body_frame before_closure= #scope old_body andalso
                #body before_closure=old andalso
                #binder before_closure= #binder after_closure andalso
                #body_frame before_closure= #body_frame after_closure andalso
                #body after_closure=new andalso exact_condition andalso
                ListPair.allEq (fn (a,b) =>
                  (tick ();Portable.pointer_eq (a,b)))
                  (#evidence actual,evidence) then () else
              raise ERR "execute_body_query"
                "body binding differs from actual checked finite programme"
            val _ = if #source actual_recording=source andalso
                #target actual_recording=target andalso
                #condition actual_recording=condition then () else
              raise ERR "execute_body_query"
                "body binding differs from actual recording programme"
            val (antecedent,conclusion) = implication (P.closed_node fact)
            val (left,right) = equation conclusion
            val _ = if antecedent=condition andalso left=source andalso
                right=target andalso List.all condition_fact evidence then ()
              else raise ERR "execute_body_query"
                "different genuine conditional body law or evidence"
          in SOME (identity,held) end end
        val supplied = List.mapPartial binding bindings
        (* Only already validated genuine root laws reach supplied. Their
           exact private body programme completed before the lambda law;
           no caller resolved flag or scope ancestry discharges a port. *)
        fun discharged requirement = List.exists
          (fn (_,({plan=BodyPlan {requirements,...},...}:body_binding)) =>
            List.exists (fn actual =>
              (tick ();same_requirement (requirement,actual))) requirements)
          supplied
        fun lookup identity =
          List.find (fn (saved,_) => (tick ();saved=identity)) supplied
        fun supported (position:scoped) = List.exists
          (fn (_,({plan=BodyPlan {original,...},...}:body_binding)) =>
            (tick ();#scope original= #scope position andalso
             #node original= #node position)) supplied
        fun pending requirement = if discharged requirement then false else
          case requirement of
            CheckedBinderBody position => not (supported position)
          | CheckedOpening {original,opened} =>
              #scope original<>scope orelse #scope opened<>scope orelse
              mapped original<> #node opened
          | _ => true
        val remaining = List.filter pending requirements
      in if not (null remaining) then QueryNeeds remaining else
        let
          val _ = if !used then raise ERR "execute_body_query"
              "finite body query consumed" else used := true
          val nodes = node_operations
            {work=work,graph=graph,scope=scope,contract=contract,
             ordinal=ordinal,check_type=check_type,guard=guard}
          fun root position = (#root nodes)
            {scope=scope,node=mapped position}
          val context = LawDAG.create_with_policy work
            {frame=frame,native_contract=contract,profiles=[],ordinal=ordinal,
             check_type=check_type}
          fun schema theorem premises target =
            let val law = LawDAG.schema_with_policy work context
                  {theorem=theorem,premises=List.map V.endpoint premises,
                   target=target}
            in V.apply_with_policy work
              {law=law,premises=premises,target=target} end
          fun condition node [] =
                if node= #truth nodes then
                  (schema boolTheory.TRUTH [] node,[]) else
                  raise ERR "execute_body_query" "missing original evidence"
            | condition node (facts as fact::rest) =
                if V.endpoint fact=node then (fact,rest) else
                let
                  val (left,right) = case G.view graph node of
                      G.Application (partial,right) =>
                        (case G.view graph partial of
                           G.Application (head,left) =>
                             (case G.view graph head of G.Constant _ =>
                               if Term.same_const (G.representative graph head)
                                   boolSyntax.conjunction then (left,right)
                               else raise ERR "execute_body_query"
                                 "condition is not the actual conjunction"
                             | _ => raise ERR "execute_body_query"
                                 "condition has no conjunction declaration")
                         | _ => raise ERR "execute_body_query"
                             "condition conjunction is partial")
                    | _ => raise ERR "execute_body_query"
                        "condition has no original evidence"
                  val (a,remaining) = condition left facts
                  val (b,remaining) = condition right remaining
                in (schema conjunction_intro [a,b] node,remaining) end
          fun body identity actual = case lookup identity of
              NONE => raise ERR "execute_body_query" "missing checked body law"
            | SOME (_,({fact,condition=antecedent,source,target,evidence,...}:
                         body_binding)) =>
              let
                val _ = if source=actual then () else
                  raise ERR "execute_body_query"
                    "different current body source"
                val law = V.scoped_recorded_closed_with_policy work frame fact
                val (premise,rest) = condition antecedent evidence
                val _ = if null rest then () else
                  raise ERR "execute_body_query" "unused ordered body evidence"
                val proof = V.apply_with_policy work
                  {law=law,premises=[premise],
                   target=(#equality nodes) source target}
              in (target,SOME proof) end
          fun evidence fact target =
            if V.endpoint fact=target then fact else
              raise ERR "execute_body_query" "finite evidence is not exact"
          val {transformed,...} = proof_program
            {tick= #tick nodes,root=root,equality= #equality nodes,
             finite_node= #finite_node nodes,truth= #truth nodes,
             application=G.application graph scope,schema=schema,
             evidence=evidence,endpoint=V.endpoint,binder=body}
          fun current_fact saved =
            let fun seek [] [] = raise ERR "execute_body_query"
                      "original selected occurrence is absent"
                  | seek (old::olds) (fresh::news) =
                      (tick ();if Portable.pointer_eq (saved,old) then fresh
                       else seek olds news)
                  | seek _ _ = raise ERR "execute_body_query"
                      "different current occurrence portfolio"
            in seek (#assumptions original) (#assumptions current) end
          fun assertion (fact,syntax) =
            let val (target,equality) = transformed syntax
                val incoming = current_fact fact
            in case equality of NONE => incoming
              | SOME proof => schema forward [proof,incoming] target end
          val selected = List.map assertion assumptions
          val (positive,equality) = transformed goal
          val denied = case equality of NONE => #denied current
            | SOME proof => schema negative [proof,#denied current]
                ((#negate nodes) positive)
          val validation = V.validate_portfolio_with_policy work
            {assumptions=selected,goal=positive,denied=denied}
          val preprocessing = GP.from_portfolio_with_policy work validation
          val _ = guard ()
        in QueryRewritten {validation=validation,preprocessing=preprocessing,
          backend=backend,markers=markers} end
      end) end)handle primary=>(W.close expected;raise primary))
end
