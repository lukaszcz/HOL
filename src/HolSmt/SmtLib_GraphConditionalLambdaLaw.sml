(* Existing authenticated lambda proof; no theorem or endpoint proposal. *)
structure SmtLib_GraphConditionalLambdaLaw :>
    SmtLib_GraphConditionalLambdaLaw =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure Scope = SmtReplayOwnedScopeReceipt
  structure NC = SmtReplayNativeContract
  structure L = SmtReplayOwnedLambda
  structure P = SmtReplayProof
  structure RP = SmtReplayResourcePolicy
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphConditionalLambdaLaw"
  type size = {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int}
  type recording_request =
    {frame:Scope.receipt,native_contract:NC.contract,
     conversion:L.conditional_policy_conversion,
     profiles:G.policy_opaque_profile list,ordinal:int,
     check_type:Type.hol_type -> unit}
  type recorded_data =
    {frame:Scope.receipt,native_contract:NC.contract,
     conversion:L.conditional_policy_conversion,fact:P.closed_fact,
     condition:G.node,source:G.node,target:G.node}
  datatype recorded = Recorded of
    {work:W.portfolio,guard:unit -> unit,data:recorded_data}

  fun record_internal finish expected
      {frame,native_contract,conversion,profiles,ordinal,check_type} =
    ((let
      val owner = Scope.description_with_policy_for expected frame
      val graph = #graph owner val scope = #scope owner
      val sources = #sources owner val root = #root owner
      val request = {graph=graph,caller=scope,scope=scope,
                     sources=sources,work=expected}
      val _ = L.validate_conditional_with_policy_for request conversion
      val held_contract =
        L.conditional_native_contract_with_policy_for request conversion
      val _ = if Portable.pointer_eq (held_contract,native_contract) then ()
        else raise ERR "record" "different original native contract"
      val _ = NC.validate_for expected native_contract
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val metric_guards = ref ([]:G.profiled_metric list)
      fun guard () =
        let
          val actual = Scope.description_with_policy_for expected frame
          val _ = if Portable.pointer_eq (#graph actual,graph) andalso
              #scope actual=scope andalso #root actual=root andalso
              Portable.pointer_eq (#sources actual,sources) andalso
              Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
            then () else raise ERR "record" "different lexical owner or epoch"
          val _ = L.validate_conditional_with_policy_for request conversion
          val contract =
            L.conditional_native_contract_with_policy_for request conversion
          val _ = if Portable.pointer_eq (contract,native_contract) then ()
            else raise ERR "record" "different original native contract"
          val _ = List.app (G.validate_policy_opaque_profile graph) profiles
          val _ = List.app (fn capture => ignore
            (G.profiled_metric_data graph scope capture)) (!metric_guards)
        in NC.validate_for expected native_contract end
    in W.with_step expected (fn () =>
      let
        fun tick () = (guard ();W.spend_policy expected 1)
        fun run action =
          (guard ();let val answer = action () val _ = guard () in answer end)
        val _ = guard ()
        val _ = if ordinal>=0 then () else
          raise ERR "record" "negative recording ordinal"
        val data = L.endpoints_conditional_with_policy_for request conversion
        fun visible label node =
          (tick ();if G.scope_visible graph scope (G.node_scope graph node)
             then () else raise ERR "record" (label^" outside parent frame"))
        val _ = visible "condition" (#condition data)
        val _ = visible "source lambda" (#source data)
        val _ = visible "target lambda" (#target data)
        val native = NC.for_work expected native_contract
        val finite = #semantic_limits native
        val cap = #template_limit finite
        val input_cap = Int.min (cap,#input_limit finite)
        val type_cap = IntInf.fromInt (#type_work_limit native)
        val metadata = #template_limit (#limits owner)
        val theorem = #theorem data
        val input = Thm.concl theorem
        (* The receipt authenticates the whole implication and its exact
           lambda operands. Count their genuine guarded graph syntax first;
           the STANDARD count-only binder helper itself runs kernel rules. *)
        val _ = if null (Thm.hyp theorem) andalso
            null (Tag.axioms_of (Thm.tag theorem)) andalso
            List.all (fn name => name="DISK_THM")
              (#1 (Tag.dest_tag (Thm.tag theorem))) then () else
          raise ERR "record" "conditional receipt is not clean and closed"
        val (condition,equality) = boolSyntax.dest_imp_only input
        val (left,right) = boolSyntax.dest_eq equality
        val _ = if Portable.pointer_eq
              (condition,run (fn () =>
                G.representative graph (#condition data)))
            andalso Portable.pointer_eq
              (left,run (fn () =>
                G.representative graph (#source data))) andalso
            Portable.pointer_eq
              (right,run (fn () => G.representative graph (#target data)))
          then () else raise ERR "record" "actual conditional endpoints differ"
        fun metric node =
          let val capture = run (fn () =>
                G.prepare_scoped_profiled_metric_observed graph scope
                  {node=node,profiles=profiles,
                   observe=fn () => W.spend_policy expected 1})
              val actual = run (fn () =>
                G.profiled_metric_data graph scope capture)
              val _ = if #node actual=node then () else
                raise ERR "record" "different actual metric endpoint"
              val _ = tick ()
              val _ = metric_guards := capture :: !metric_guards
          in actual end
        val condition_size = metric (#condition data)
        val left_size = metric (#source data)
        val right_size = metric (#target data)
        val input_raw = 6+ #raw condition_size+ #raw left_size+ #raw right_size
        val input_inc = 6+ #inc condition_size+ #inc left_size+ #inc right_size
        val _ = if input_raw<=IntInf.fromInt input_cap andalso
            input_inc<=IntInf.fromInt input_cap then () else
          raise ERR "record" "actual conditional input exceeds cap"
        val types = ref ([]:Type.hol_type list)
        val type_memo = ref ([]:(Type.hol_type * IntInf.int) list)
        fun known _ [] = NONE
          | known ty ((held,amount)::rest) =
              (tick ();if Portable.pointer_eq (ty,held) then SOME amount
               else known ty rest)
        fun weight ty = case known ty (!type_memo) of SOME amount => amount
          | NONE =>
            let
              fun forest [] total = total
                | forest (pending::more) total =
                    (tick ();case pending of [] => forest more total
                     | current::rest =>
                       let
                         val bytes = if run (fn () => Type.is_vartype current)
                           then IntInf.fromInt (String.size
                             (run (fn () => Type.dest_vartype current))) else 0
                         val next = total+1+bytes
                         val _ = if next<=type_cap then () else
                           raise ERR "record" "native Type weight exceeds cap"
                       in if run (fn () => Type.is_vartype current) then
                           forest (rest::more) next
                         else forest
                           ((run (fn () => #2 (Type.dest_type current)))::
                             rest::more) next end)
              val amount = forest [[ty]] 0
              val _ = tick ()
              val _ = type_memo := (ty,amount):: !type_memo
              val _ = types := ty :: !types
            in amount end
        fun inspect [] (result:size) = result
          | inspect (current::rest) ({raw,inc,ann}:size) =
            let
              val _ = tick ()
              val raw = raw+1 val inc = inc+1
              val _ = if raw<=IntInf.fromInt cap andalso
                  inc<=IntInf.fromInt cap then () else
                raise ERR "record" "actual native input count changed"
              val ty = run (fn () => Term.type_of current)
              val ann = ann+weight ty
              val _ = if ann<=type_cap then () else
                raise ERR "record" "native annotation portfolio exceeds cap"
            in if run (fn () => Term.is_comb current) then
                let val (f,x) = run (fn () => Term.dest_comb current)
                in inspect (f::x::rest) {raw=raw,inc=inc,ann=ann} end
              else if run (fn () => Term.is_abs current) then
                let val (domain,_) = run (fn () => Type.dom_rng ty)
                    val ann = ann+weight domain
                    val _ = if inc+1<=IntInf.fromInt cap andalso ann<=type_cap
                      then () else raise ERR "record"
                        "native binder/annotation portfolio exceeds cap"
                    (* The complete raw/binder input was admitted above.
                       This ordinary bounded view creates no theorem. *)
                    val body = run (fn () => #2 (Term.dest_abs current))
                in inspect (body::rest) {raw=raw,inc=inc+1,ann=ann} end
              else inspect rest {raw=raw,inc=inc,ann=ann} end
        val actual = inspect [input] {raw=0,inc=0,ann=0}
        val _ = if #raw actual=input_raw andalso #inc actual=input_inc then ()
          else raise ERR "record" "actual native input count changed"
        val source_type = run (fn () => G.type_of graph (#source data))
        val generic_type = Term.type_of boolSyntax.equality
        val theta = Type.match_type
          (#1 (Type.dom_rng generic_type)) source_type
        (* Type shape follows only the bounded receipt/input portfolio.
           Substitution planning precedes construction of the typed head. *)
        fun substituted ty = case List.find
            (fn {redex,...} => Type.compare (redex,ty)=EQUAL) theta of
              SOME {residue,...} => weight residue
            | NONE => if Type.is_vartype ty then weight ty else
                List.foldl (fn (child,total) => total+substituted child)
                  (1:IntInf.int) (#2 (Type.dest_type ty))
        val head_types = weight generic_type+substituted generic_type
        val boolean = weight Type.bool
        val partial = 1+2*boolean
        val boolean_equality = 1+boolean+partial
        val equation:size =
          {raw=3+2* #raw actual,inc=3+2* #inc actual,
           ann=boolean_equality+partial+boolean+2* #ann actual}
        fun admit label native_cap ({raw,inc,ann}:size) =
          if raw<=IntInf.fromInt (Int.min (cap,native_cap)) andalso
              inc<=IntInf.fromInt (Int.min (cap,native_cap)) andalso
              RP.allows metadata raw andalso RP.allows metadata inc andalso
              ann<=type_cap then () else
            raise ERR "record" (label^" exceeds actual native cap")
        val _ = admit "conditional statement input"
          (#input_limit finite) actual
        val _ = admit "canonical statement output"
          (#output_limit finite) actual
        val _ = admit "ALPHA/record equation output"
          (#output_limit finite) equation
        val _ = admit "EQ_MP/record equation input"
          (#input_limit finite) equation
        (* ALPHA result, EQ_MP result, P.record's identity REFL and final
           EQ_MP, plus original and graph statement input occurrences. *)
        fun size_weight ({raw,inc,ann}:size) = raw+inc+ann
        val amount = 2*size_weight equation+4*size_weight actual+head_types
        val _ = if amount<=type_cap then () else
          raise ERR "record" "native recording Type portfolio exceeds cap"
        val issued = W.unused_policy_ordinal expected
          {role=W.ClosedRecord,minimum=ordinal}
        val token = W.reserve_policy expected
          {role=W.ClosedRecord,ordinal=issued,amount=amount}
        val _ = W.consume_policy expected token amount
        val _ = List.app (fn ty =>
          (guard ();check_type ty;guard ())) (List.rev (!types))
        val head_type = run (fn () => Type.type_subst theta generic_type)
        val _ = run (fn () => check_type head_type)
        val equality_head = run (fn () => Term.inst theta boolSyntax.equality)
        val equation_node = G.application graph scope
          (G.application graph scope
            (G.constant graph scope equality_head,#source data),#target data)
        val statement = G.application graph scope
          (G.application graph scope
            (G.constant graph scope boolSyntax.implication,#condition data),
           equation_node)
        val capture = G.prepare_scoped_profiled_metric graph scope
          {node=statement,profiles=profiles}
        fun recording_guard () =
          (guard ();ignore (G.profiled_metric_data graph scope capture))
        val actual_statement = G.profiled_metric_data graph scope capture
        val _ = if #node actual_statement=statement andalso
            #raw actual_statement= #raw actual andalso
            #inc actual_statement= #inc actual then () else
          raise ERR "record" "actual graph statement count differs"
        val _ = recording_guard ()
        val canonical = Thm.EQ_MP
          (Thm.ALPHA input (G.representative graph statement)) theorem
        val _ = recording_guard ()
        val result = P.record_closed_with_policy_scoped_profiles graph scope
          {node=statement,theorem=canonical,template_limit=metadata,
           profiles=profiles,check_type=fn ty =>
             (recording_guard ();check_type ty;recording_guard ())}
        val _ = P.validate_closed_fact_in_scope_with_policy_for expected
          {frame=frame,fact=result}
        val _ = guard ()
      in finish {work=expected,guard=recording_guard,
        data={frame=frame,native_contract=native_contract,
          conversion=conversion,fact=result,condition= #condition data,
          source= #source data,target= #target data}} end)
    end) handle primary => (W.close expected;raise primary))

  fun record_with_policy expected input =
    record_internal (fn {data,...} => #fact data) expected input

  fun record_receipt_with_policy expected input =
    record_internal Recorded expected input

  fun recorded_with_policy_for expected
      (Recorded {work,guard,data as {frame,fact,...}}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "recorded" "different original Work";
      W.spend_policy expected 1;
      guard ();
      P.validate_closed_fact_in_scope_with_policy_for expected
        {frame=frame,fact=fact};
      data) handle primary => (W.close expected;raise primary))
end
