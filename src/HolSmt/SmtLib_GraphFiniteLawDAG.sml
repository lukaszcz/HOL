(* Closed conditional laws over graph names, never query assumptions. *)
structure SmtLib_GraphFiniteLawDAG :> SmtLib_GraphFiniteLawDAG =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure P = SmtReplayProof
  structure R = SmtReplayRules
  structure Scope = SmtReplayOwnedScopeReceipt
  structure NC = SmtReplayNativeContract
  structure RP = SmtReplayResourcePolicy
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphFiniteLawDAG"
  datatype context = Context of
    {work:W.portfolio,frame:Scope.receipt,graph:G.graph,scope:G.scope,
     root:G.scope,sources:S.sources,contract:NC.contract,
     limits:RP.semantic_policy,profiles:G.policy_opaque_profile list,
     ordinal:int,check_type:Type.hol_type -> unit,epoch:int,symbols:int,
     condition_owner:(Scope.receipt * G.scope) option}
  datatype conditional = Conditional of
    {context:context,fact:V.fact,condition:G.node option,
     evidence:G.node list,target:G.node}
  fun protect expected action = action ()
    handle primary => (W.close expected;raise primary)
  fun guard expected (Context held) =
    (if Portable.pointer_eq (expected,#work held) then () else
       raise ERR "guard" "different original Work";
     let val actual = Scope.description_with_policy_for expected (#frame held)
         val _ = NC.validate_for expected (#contract held)
     in if Portable.pointer_eq (#graph actual,#graph held) andalso
         #root actual= #root held andalso #scope actual= #scope held andalso
         Portable.pointer_eq (#sources actual,#sources held) andalso
         #limits actual= #limits held andalso
         Type.type_epoch ()= #epoch held andalso
         Term.term_epoch ()= #symbols held then () else
       raise ERR "guard" "different lexical owner or epoch";
       case #condition_owner held of NONE => ()
       | SOME (frame,scope) =>
           let val parent = Scope.description_with_policy_for expected frame
           in if Portable.pointer_eq (#graph parent,#graph held) andalso
               #root parent= #root held andalso #scope parent=scope andalso
               Portable.pointer_eq (#sources parent,#sources held) andalso
               #limits parent= #limits held andalso
               G.scope_visible (#graph held) (#scope held) scope then () else
             raise ERR "guard" "different ancestor condition frame" end
     end)
  fun create_with_policy work
      {frame,native_contract,profiles,ordinal,check_type} =
    protect work (fn () =>
      let val actual = Scope.description_with_policy_for work frame
          val _ = NC.validate_for work native_contract
          val _ = if ordinal>=0 then () else
            raise ERR "create" "negative law ordinal"
          val context = Context
            {work=work,frame=frame,graph= #graph actual,scope= #scope actual,
             root= #root actual,sources= #sources actual,
             contract=native_contract,limits= #limits actual,profiles=profiles,
             ordinal=ordinal,check_type=check_type,
             epoch=Type.type_epoch (),symbols=Term.term_epoch (),
             condition_owner=NONE}
          val _ = guard work context
      in context end)

  fun create_with_condition_frame_with_policy work
      {frame,condition_frame,native_contract,profiles,ordinal,check_type} =
    protect work (fn () =>
      let
        val Context {work,frame,graph,scope,root,sources,contract,limits,
                     profiles,ordinal,check_type,epoch,symbols,...} =
          create_with_policy work
            {frame=frame,native_contract=native_contract,profiles=profiles,
             ordinal=ordinal,check_type=check_type}
        val parent = Scope.description_with_policy_for work condition_frame
        val result = Context
          {work=work,frame=frame,graph=graph,scope=scope,root=root,
           sources=sources,contract=contract,limits=limits,profiles=profiles,
           ordinal=ordinal,check_type=check_type,epoch=epoch,symbols=symbols,
           condition_owner=SOME (condition_frame,#scope parent)}
        val _ = guard work result
      in result end)

  fun condition_scope (Context {scope,condition_owner,...}) =
    case condition_owner of NONE => scope | SOME (_,parent) => parent
  fun visible_condition context node =
    case context of Context {condition_owner=NONE,...} => ()
    | Context {graph,...} =>
        if G.scope_visible graph (condition_scope context)
            (G.node_scope graph node) then () else
          raise ERR "conditional" "evidence outside condition frame"

  fun schema_using statement expected
      (context as Context {work,frame,graph,scope,contract,ordinal,
                           check_type,...}) {theorem,premises,target} =
    protect expected (fn () =>
    let
      val _ = guard expected context
      val active = fn () => guard expected context
      fun guard () = active ()
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
      (* A schema matcher inspects bounded native declaration syntax and
         graph views only. It never reconstructs a target HOL term. *)
      fun schema theorem premises target =
        let
          val _ = tick ()
          val (antecedents,conclusion) =
            boolSyntax.strip_imp_only (Thm.concl theorem)
          val inputs = premises
          val _ = if List.length inputs=List.length antecedents then ()
            else raise ERR "schema" "ordered schema premise arity"
          val bindings = ref ([]:(Term.term * G.node) list)
          val substitutions = ref
            (([]:(Type.hol_type,Type.hol_type) Lib.subst),
             ([]:Type.hol_type list))
          fun match_type pattern actual =
            substitutions :=
              Type.raw_match_type pattern actual (!substitutions)
          fun match pattern actual =
            (tick ();match_type (Term.type_of pattern)
              (G.type_of graph actual);
             if Term.is_var pattern then
               (case List.find (fn (saved,_) => Term.aconv saved pattern)
                   (!bindings) of
                  SOME (_,held) => if held=actual then () else
                    raise ERR "schema" "schema hole endpoint differs"
                | NONE => bindings := (pattern,actual) :: !bindings)
             else if Term.is_const pattern then
               (case G.view graph actual of G.Constant identity =>
                  if identity= #Name (Term.dest_thy_constid pattern) then ()
                  else raise ERR "schema" "schema constant differs"
                | _ => raise ERR "schema" "schema constant shape differs")
             else if Term.is_comb pattern then
               (case G.view graph actual of G.Application (f,x) =>
                  let val (pf,px) = Term.dest_comb pattern
                  in match pf f;match px x end
                | _ => raise ERR "schema" "schema application differs")
             else raise ERR "schema" "schema contains an unquoted binder")
          val _ = ListPair.appEq (fn (pattern,actual) =>
            match pattern actual) (antecedents,inputs)
          val _ = match conclusion target
          val theta = #1 (!substitutions)
          val holes = List.rev (!bindings)
          (* Count substituted annotations without constructing their
             output Types. Residues are simultaneous, not recursively
             substituted. All caps and the whole native portfolio precede
             INST_TYPE, instantiated hole atoms and EQT_INTRO. *)
          val type_weight = type_weight theta
          val annotations = ref ([]:Type.hol_type list)
          fun inspect [] count amount = (count,amount)
            | inspect (term::rest) count amount =
              let
                val _ = tick ()
                val count = count+1
                val _ = if count+4<=template then () else
                  raise ERR "schema" "native schema exceeds template cap"
                val ty = Term.type_of term
                val amount = amount+type_weight false ty+
                  type_weight true ty
                val _ = if amount<=type_ceiling then () else
                  raise ERR "schema" "native Type portfolio exceeds cap"
                val _ = annotations := ty :: !annotations
                val children = if Term.is_comb term then
                    let val (f,x) = Term.dest_comb term in f::x::rest end
                  else if Term.is_abs term then raise ERR "schema"
                    "native schema requires bounded binder producer"
                  else rest
              in inspect children count amount end
          val (raw,law_annotations) = inspect [Thm.concl theorem] 0 0
          fun inspect_holes [] count amount = (count,amount)
            | inspect_holes ((term,_)::rest) count amount =
              let val (raw,weight) = inspect [term] 0 amount
              in inspect_holes rest (count+raw) weight end
          val (hole_raw,annotations_weight) =
            inspect_holes holes 0 law_annotations
          val partial_type = Type.--> (Type.bool,Type.bool)
          val equality_type = Type.--> (Type.bool,partial_type)
          val extras = 2*type_weight false Type.bool +
            type_weight false partial_type +
            type_weight false equality_type
          val complete_annotations = annotations_weight+extras
          val _ = if complete_annotations<=type_ceiling then () else
            raise ERR "schema" "native EQT Type portfolio exceeds cap"
          val amount = 2*(2*IntInf.fromInt (raw+hole_raw+4)+
            complete_annotations)+1
          val _ = quoted amount
          fun checked ty = checked_type (Type.type_subst theta ty)
          val _ = List.app checked (List.rev (!annotations))
          val _ = checked_type Type.bool
          val _ = checked_type partial_type
          val _ = checked_type equality_type
          val instantiated = Thm.INST_TYPE theta theorem
          val typed_holes = List.map (Term.inst theta o #1) holes
          val _ = guard ()
          val law = case statement of NONE=>
              V.scoped_closed_with_policy work frame
                {theorem=instantiated,holes=typed_holes,
                 operands=List.map #2 holes,template_limit=template}
            | SOME actual=>V.scoped_closed_at_with_policy work frame
                {theorem=instantiated,holes=typed_holes,
                 operands=List.map #2 holes,statement=actual,
                 template_limit=template,
                 type_work_limit= #type_work_limit native}
          val _ = guard ()
        in law end
    in schema theorem premises target end)
  (* Existing public callers retain their exact schema programme. *)
  fun schema_with_policy expected context input =
    schema_using NONE expected context input

  fun implication graph scope first last =
    R.implication graph scope [first] last
  fun conjunction graph scope (left,right) =
    G.application graph scope
      (G.application graph scope
        (G.constant graph scope boolSyntax.conjunction,left),right)
  fun implication_parts expected (context as Context {graph,scope,...}) node =
    let val _ = guard expected context
        val _ = W.spend_policy expected 3
    in case G.view graph node of G.Application (partial,right) =>
        (case G.view graph partial of G.Application (head,left) =>
          (case G.view graph head of G.Constant _ =>
             if Term.same_const (G.representative graph head)
                 boolSyntax.implication then (left,right) else
               raise ERR "implication" "different implication head"
           | _ => raise ERR "implication" "nonconstant implication head")
        | _ => raise ERR "implication" "missing implication operands")
      | _ => raise ERR "implication" "missing implication application"
    end
  (* Split only the bounded template's implication prefix. The actual
     endpoint may itself be an implication matched by a template variable. *)
  fun schema_node expected context theorem endpoint =
    let
      fun split pattern actual inputs =
        if boolSyntax.is_imp_only pattern then
          let val (_,rest) = boolSyntax.dest_imp_only pattern
              val (premise,result) = implication_parts expected context actual
          in split rest result (premise::inputs) end
        else schema_using (SOME endpoint) expected context
          {theorem=theorem,premises=List.rev inputs,target=actual}
    in split (Thm.concl theorem) endpoint [] end

  (* Fixed closed propositional laws. No query syntax is inserted into
     these native templates, including under their binders (there are none). *)
  local
    val a = Term.mk_var ("finite_law_a",Type.bool)
    val b = Term.mk_var ("finite_law_b",Type.bool)
    val p = Term.mk_var ("finite_law_p",Type.bool)
    val q = Term.mk_var ("finite_law_q",Type.bool)
    fun imp left right = boolSyntax.mk_imp (left,right)
    fun assumes terms finish =
      List.foldr (fn (term,proof) => Thm.DISCH term proof) finish terms
    val left = imp a (imp p q) val right = imp b p
    val both = boolSyntax.mk_conj (a,b)
  in
    val identity = Thm.DISCH p (Thm.ASSUME p)
    val conditional_left = assumes [left,p,a]
      (Thm.MP (Thm.MP (Thm.ASSUME left) (Thm.ASSUME a)) (Thm.ASSUME p))
    val conditional_right = assumes [imp p q,right,b]
      (Thm.MP (Thm.ASSUME (imp p q))
        (Thm.MP (Thm.ASSUME right) (Thm.ASSUME b)))
    val conditional_both = assumes [left,right,both]
      (Thm.MP
        (Thm.MP (Thm.ASSUME left) (Thm.CONJUNCT1 (Thm.ASSUME both)))
        (Thm.MP (Thm.ASSUME right) (Thm.CONJUNCT2 (Thm.ASSUME both))))
  end
  fun conditional_data expected context
      (Conditional {context=held,fact,condition,evidence,target}) =
    let val _ = guard expected context
        val _ = if Portable.pointer_eq (context,held) then () else
          raise ERR "conditional" "different law context"
        val Context {graph,scope,frame,...} = context
        val _ = ignore (V.closed_program_with_policy expected frame [fact])
        val wanted = case condition of NONE => target
          | SOME premise => implication graph scope premise target
        val _ = if V.endpoint fact=wanted then () else
          raise ERR "conditional" "conditional law endpoint differs"
        val _ = guard expected context
    in {fact=fact,condition=condition,evidence=evidence,target=target} end
  fun description_with_policy_for expected context conditional =
    protect expected (fn () => conditional_data expected context conditional)
  fun of_closed_with_policy expected (context as Context {frame,...}) fact =
    protect expected (fn () =>
      let val _ = guard expected context
          val _ = ignore (V.closed_program_with_policy expected frame [fact])
      in Conditional {context=context,fact=fact,condition=NONE,evidence=[],
        target=V.endpoint fact} end)
  fun evidence_with_policy expected
      (context as Context {graph,scope,...}) evidence =
    protect expected (fn () =>
      let val _ = guard expected context
          val _ = visible_condition context evidence
          val endpoint = implication graph scope evidence evidence
          val fact = schema_node expected context identity endpoint
      in Conditional {context=context,fact=fact,condition=SOME evidence,
        evidence=[evidence],target=evidence} end)
  fun apply_with_policy expected
      (context as Context {graph,scope,frame,...}) {law,premises,target} =
    protect expected (fn () =>
      let
        val _ = guard expected context
        val initial = of_closed_with_policy expected context law
        fun step (premise,current) =
          let
            val first = conditional_data expected context current
            val second = conditional_data expected context premise
            val (input,result) = implication_parts expected context
              (#target first)
            val _ = if input= #target second then () else
              raise ERR "apply" "conditional premise endpoint differs"
            val condition = case (#condition first,#condition second) of
                (NONE,NONE) => NONE
              | (SOME a,NONE) => SOME a
              | (NONE,SOME b) => SOME b
              | (SOME a,SOME b) =>
                  (visible_condition context a;visible_condition context b;
                   SOME (conjunction graph (condition_scope context) (a,b)))
            val endpoint = case condition of NONE => result
              | SOME antecedent => implication graph scope antecedent result
            val fact = case (#condition first,#condition second) of
                (NONE,NONE) => V.scoped_apply_with_policy expected frame
                  {law= #fact first,premises=[#fact second],target=endpoint}
              | cases =>
                let val theorem = case cases of
                        (SOME _,NONE) => conditional_left
                      | (NONE,SOME _) => conditional_right
                      | _ => conditional_both
                    val parents = [#fact first,#fact second]
                    val rule = schema_node expected context theorem
                      (R.implication graph scope
                        (List.map V.endpoint parents) endpoint)
                in V.scoped_apply_with_policy expected frame
                  {law=rule,premises=parents,target=endpoint} end
          in Conditional {context=context,fact=fact,condition=condition,
            evidence= #evidence first @ #evidence second,target=result} end
        val result = List.foldl step initial premises
        val data = conditional_data expected context result
        val _ = if #target data=target then () else
          raise ERR "apply" "conditional conclusion endpoint differs"
      in result end)

  (* An actual finite native quote, separate from metadata policy. A
     generic implication uses the generic realization theorem accessor;
     the equality-only conversion getter cannot certify this result. *)
  fun realize_with_policy expected
      (context as Context {work,frame,graph,scope,contract,limits,profiles,
                           ordinal,check_type,...}) conditional =
    protect expected (fn () =>
    let
      val _ = guard expected context
      val (program,freeze,target) = W.with_step work (fn () =>
        let
          val data = conditional_data expected context conditional
          val fact = #fact data val target = V.endpoint fact
          val program = V.closed_program_with_policy work frame [fact]
          val input = V.closed_program_data_with_policy_for work program
          val frontier = P.prepare_realization_frontier_with_policy work
            {frame=frame,roots= #roots input,
             closed_facts= #closed_facts input,conversions= #conversions input}
          val actual = P.realization_frontier_data_with_policy_for work
            frontier
          val _ = if null (#sources actual) then () else
            raise ERR "realize" "closed frontier contains Source leaves"
          val tables = P.prepare_owned_realization_tables_with_policy work
            frontier
          fun checked ty = (guard expected context;check_type ty;
            guard expected context)
          val freeze_ordinal = W.unused_policy_ordinal work
            {role=W.FinalFreeze,minimum=ordinal}
          val freeze = P.prepare_native_realization_freeze_with_policy work
            {tables=tables,contract=contract,profiles=profiles,
             ordinal=freeze_ordinal,check_type=checked}
          val forecast = P.native_realization_freeze_data_for work freeze
          val native = NC.for_work work contract
          val cap = IntInf.fromInt
            (#template_limit (#semantic_limits native))
          val type_cap = IntInf.fromInt (#type_work_limit native)
          fun require label NONE = raise ERR "realize"
                (label^" lacks an authentic expanded native profile")
            | require label (SOME (raw,inc,ann)) =
                if raw<=cap andalso inc<=cap andalso ann<=type_cap andalso
                    RP.allows (#template_limit limits) raw andalso
                    RP.allows (#template_limit limits) inc then (raw,inc,ann)
                else raise ERR "realize" (label^" exceeds native law cap")
          val (cr,ci,ca) = require "closed Context"
            (#actual_context forecast)
          val result = case List.find (fn (node,_) => node=target)
              (#actual_results forecast) of SOME (_,value) => value
            | NONE => raise ERR "realize" "law target absent from frontier"
          val (tr,ti,ta) = require "closed law" result
          val closing = require "closed instantiation"
            (SOME (3+cr+tr,3+ci+ti,9+ca+ta))
          (* The compact closing/INST port deliberately retains expanded
             residues. Recording this bounded law adds a distinct native
             REFL/EQ_MP bridge over the actual target. Admit its inputs
             and outputs before freeze, callbacks or proof effects. *)
          val record_equation = require "closed record equation"
            (SOME (3+2*tr,3+2*ti,9+2*ta))
          val input_cap = IntInf.fromInt
            (#input_limit (#semantic_limits native))
          val output_cap = IntInf.fromInt
            (#output_limit (#semantic_limits native))
          fun record_bound label cap (raw,inc,_) =
            if raw<=cap andalso inc<=cap then () else
              raise ERR "realize" (label^" exceeds native law cap")
          val _ = record_bound "closed record target input" input_cap
            (tr,ti,ta)
          val _ = record_bound "closed record equation output" output_cap
            record_equation
          val _ = record_bound "closed record equation input" input_cap
            record_equation
          val _ = record_bound "closed record target output" output_cap
            (tr,ti,ta)
          (* The actual witness/projection tree has at most 2*leaves+1
             nodes. Every native witness/subtree is bounded by its full
             Context, including its repeated Type annotation incidence. *)
          val count = 2*IntInf.fromInt (#leaf_count forecast)+1
          val (lr,li,la) = closing
          val (er,ei,ea) = record_equation
          val record_amount = 2*(tr+ti+ta)+2*(er+ei+ea)
          val amount = count*(cr+ci+ca)+(lr+li+la)+(tr+ti+ta)+
            record_amount
          val _ = if amount<=type_cap then () else
            raise ERR "realize" "closed law Type portfolio exceeds cap"
          val issued = W.unused_policy_ordinal work
            {role=W.ClosedRecord,minimum=ordinal}
          val token = W.reserve_policy work
            {role=W.ClosedRecord,ordinal=issued,amount=amount}
          val _ = W.consume_policy work token amount
          val _ = guard expected context
        in (program,freeze,target) end)
      val block = W.with_step work (fn () =>
        (guard expected context;
         P.freeze_owned_realization_tables_with_policy work freeze))
      val assemble = V.closed_assembler_with_policy work program block
      val edge = case assemble target of SOME result => result
        | NONE => raise ERR "realize" "closed law assembler lost its target"
      val fact = W.with_step work (fn () =>
        let
          val _ = guard expected context
          val receipt = P.execute_realization_with_policy work
            (P.prepare_realization_with_policy work block target edge)
          val theorem = P.policy_source_realization_theorem_for work receipt
          val (tags,_) = Tag.dest_tag (Thm.tag theorem)
          val _ = if null (Thm.hyp theorem) andalso
              null (Tag.axioms_of (Thm.tag theorem)) andalso
              List.all (fn tag => tag="DISK_THM") tags then () else
            raise ERR "realize" "law realization is not clean and closed"
          val result = P.record_closed_with_policy_scoped_profiles graph scope
            {node=target,theorem=theorem,
             template_limit= #template_limit limits,
             profiles=profiles,check_type=fn ty =>
               (guard expected context;check_type ty;guard expected context)}
          val _ = P.validate_closed_fact_with_policy graph scope
            (#template_limit limits) result
          val _ = guard expected context
        in result end)
    in fact end)
end
