(* Copyright (c) 2026 The HOL4 contributors. *)

(* Discovery and compact checked normalization of typed replay graphs. *)
structure SmtReplayCanonGraph :> SmtReplayCanonGraph =
struct
  val _ = SmtReplayProof.prepare_primitive
  open SmtReplayGraph SmtReplayProof SmtLib_GraphBackend
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure B = SmtLib_GraphBackend
  structure W = SmtReplayInvocationWork
  val _ = SmtReplayProof.realization_data_for
  val ERR = Feedback.mk_HOL_ERR "SmtReplayCanonGraph"
  type schema_statistics =
    {created_schemas : IntInf.int,schema_raw_nodes : IntInf.int,
     applied_schemas : IntInf.int,applied_schema_raw_nodes : IntInf.int,
     schema_inst_calls : IntInf.int}
  datatype schema_observation = SchemaObservation of
    {graph : G.graph,created : IntInf.int ref,size : IntInf.int ref,
     applied : IntInf.int ref,applied_size : IntInf.int ref,
     inst : IntInf.int ref}
  val schema_observation = ref (NONE : schema_observation option)
  fun observe_schema graph count size inst application =
    case !schema_observation of NONE => ()
    | SOME (SchemaObservation fields) =>
        if Portable.pointer_eq (graph,#graph fields) then
          (if application then
             (#applied fields := !(#applied fields)+count;
              #applied_size fields := !(#applied_size fields)+size)
           else (#created fields := !(#created fields)+count;
                 #size fields := !(#size fields)+size);
           #inst fields := !(#inst fields)+inst)
        else ()
  fun with_schema_statistics graph scope action =
    let
      val _ = G.validate_scope graph scope
      val _ = case !schema_observation of NONE => ()
        | SOME _ => raise ERR "with_schema_statistics" "observation reentry"
      val fields = {graph = graph,created = ref (0 : IntInf.int),
        size = ref (0 : IntInf.int),applied = ref (0 : IntInf.int),
        applied_size = ref (0 : IntInf.int),inst = ref (0 : IntInf.int)}
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      val _ = schema_observation := SOME (SchemaObservation fields)
      val outcome = Exn.capture (fn () =>
        let val result = action () val _ = G.validate_scope graph scope
            val _ = if Type.type_epoch () = epoch andalso
                Term.term_epoch () = symbols then () else
              raise ERR "with_schema_statistics" "observation epoch retired"
        in result end) ()
      val _ = schema_observation := NONE
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res result =>
        let
      val counts : schema_statistics =
        {created_schemas = !(#created fields),
         schema_raw_nodes = !(#size fields),
         applied_schemas = !(#applied fields),
         applied_schema_raw_nodes = !(#applied_size fields),
         schema_inst_calls = !(#inst fields)}
        in (result,counts) end
    end

  (* Graph canonicalization discovers syntax and checked small operator
     schemas before freezing. Callers supply their existing admitted
     small-term conversions to obtain those schemas. *)
  datatype graph_template = Operand of G.node
    | Literal of G.node * Term.term
    | Constructor of G.node * graph_template * graph_template
  fun template_node (Operand node) = node
    | template_node (Literal (node,_)) = node
    | template_node (Constructor (node,_,_)) = node
  datatype graph_schema = GraphSchema of
    {left : graph_template, right : graph_template,
     holes : Term.term list, operands : G.node list, theorem : Thm.thm,
     admitted_size : int}
  datatype graph_step = GraphStep of
    {source : G.node, current : G.node, result : G.node,
     children : (G.node * G.node) option,
     schema : graph_schema option, closed : P.closed_fact option,
     conversion : P.closed_conversion option,continuation : G.node option}
  datatype graph_conversion = GraphConversion of
    {source : G.node, result : G.node, equality : G.node,
     steps : (int,graph_step) Redblackmap.dict,
     guard_slots : P.closed_conversion list option ref}
    | SequenceGraphConversion of
      {source : G.node,result : G.node,equality : G.node,
       first : graph_conversion,second : graph_conversion,
       guard_leaves : graph_conversion list option ref}
    | DirectRealizedSequence of
      {source : G.node,result : G.node,equality : G.node,
       first : graph_conversion,second : graph_conversion,
       first_slot : P.closed_conversion,second_slot : P.closed_conversion,
       guard_leaves : graph_conversion list option ref}
    | ApplicationGraphConversion of
      {source : G.node,result : G.node,equality : G.node,
       left : graph_conversion,right : graph_conversion,
       guard_leaves : graph_conversion list option ref}
    | RealizedGraphConversion of
      {legacy : graph_conversion,realization : P.realization}
    | PolicyGraphConversion of
      {work:W.portfolio,frame:SmtReplayOwnedScopeReceipt.receipt,
       legacy:graph_conversion,slot:P.closed_conversion,
       realization:P.policy_source_realization option,
       canonical_cut:P.policy_closed_fact_cut option}
    | PolicySequenceGraphConversion of
      {work:W.portfolio,frame:SmtReplayOwnedScopeReceipt.receipt,
       source:G.node,result:G.node,equality:G.node,
       first:graph_conversion,second:graph_conversion}

  fun clean_schema theorem =
    let val (oracles,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn oracle => oracle = "DISK_THM") oracles andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end

  fun checked_graph_schema graph scope
      {theorem,holes,operands,template_limit} =
    let
      val _ = G.validate_scope graph scope
      (* This grammar has no binders. Reject them on the syntax frontier,
         before a count-only opener can execute native range-Type work. *)
      fun size [] count = count
        | size (term :: rest) count =
            if count >= template_limit then
              raise ERR "checked_graph_schema" "expanded operator schema"
            else if Term.is_comb term then
              let val (operator,operand) = Term.dest_comb term
              in size (operator :: operand :: rest) (count + 1) end
            else if Term.is_abs term then
              raise ERR "checked_graph_schema"
                "binder schema requires a bounded local proof block"
            else size rest (count + 1)
      val admitted_size = size [Thm.concl theorem] 0
      val _ = if List.null (Thm.hyp theorem) andalso clean_schema theorem then
          () else raise ERR "checked_graph_schema"
            "operator schema has assumptions or unexpected tags"
      val _ = List.app (fn node =>
        if G.scope_visible graph scope (G.node_scope graph node) then ()
        else raise ERR "checked_graph_schema" "operand outside active scope")
        operands
      val (left,right) = Term.dest_eq (Thm.concl theorem)
      val _ = if List.length holes = List.length operands then () else
        raise ERR "checked_graph_schema" "operator schema arity mismatch"
      (* Schema variables are declarations, not lexical references. Two
         distinct holes may intentionally denote the same scoped operand. *)
      val declaration = G.declaration_variable_key graph scope
      val _ = List.foldl (fn (hole,seen) =>
        let
          val _ = if Term.is_var hole then () else
            raise ERR "checked_graph_schema" "non-variable schema hole"
          val identity = declaration hole
        in
          if List.exists (fn prior => prior = identity) seen then
            raise ERR "checked_graph_schema" "duplicate typed schema hole"
          else identity :: seen
        end) [] holes
      val _ = G.reserve_schema_holes graph (ListPair.zip (holes,operands))
      val hole_ids = List.map declaration holes
      fun hole term =
        let val identity = declaration term
            fun seek [] [] = NONE
              | seek (name::names) (node::nodes) =
                  if identity = name then SOME node else seek names nodes
              | seek _ _ = raise ERR "checked_graph_schema"
                  "operator schema arity mismatch"
        in seek hole_ids operands end
      fun tree term =
        if Term.is_var term then
          (case hole term of SOME node => Operand node
           | NONE => raise ERR "checked_graph_schema"
               "unowned schema variable")
        else if Term.is_const term then
          Literal (G.constant graph scope term,term)
        else if Term.is_comb term then
          let
            val (operator,operand) = Term.dest_comb term
            val left = tree operator and right = tree operand
            val node = G.application graph scope
              (template_node left,template_node right)
          in Constructor (node,left,right) end
        else raise ERR "checked_graph_schema"
          "binder schema requires a bounded local proof block"
      val left_tree = tree left
      val right_tree = tree right
      val _ = ListPair.appEq (fn (hole,node) =>
        ignore (G.resolve_reference graph scope hole node)) (holes,operands)
      (* The typed graph constructors check every application and hole.
         Do not reconstruct the same recipe through the ordinary backend:
         its native Type.compare can unfold a huge annotation on a tiny
         schema. Owned IDs validate syntax, never prove the schema law. *)
      val _ = observe_schema graph 1 (IntInf.fromInt admitted_size) 0 false
    in GraphSchema {left = left_tree,right = right_tree,
      holes = holes,operands = operands,theorem = theorem,
      admitted_size = admitted_size} end

  (* Match one bounded CLOSED declaration against its genuine graph
     statement. Retain every authenticated constructor identity, including
     ancestor applications visible in this child scope. No operand term is
     reconstructed, normalized or opened by this operation. *)
  fun checked_closed_graph_schema_at graph scope
      {theorem,holes,operands,source,template_limit,type_work_limit,
       observe,pay} =
    let
      val _=G.validate_scope graph scope
      val epoch=Type.type_epoch () val symbols=Term.term_epoch ()
      fun guard ()=
        (G.validate_scope graph scope;
         if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols then
           () else raise ERR "checked_closed_graph_schema_at"
             "retired declaration")
      fun step ()=(guard ();observe ();guard ())
      fun charge amount=(step ();pay amount;guard ())
      fun failure message=raise ERR "checked_closed_graph_schema_at" message
      fun text_equal (left,right)=
        (charge(1+IntInf.fromInt(String.size left)+
          IntInf.fromInt(String.size right));left=right)
      fun same_id (left,right)=
        let val _=step ()
            val a=KernelSig.name_of_id left
            val b=KernelSig.name_of_id right
        in text_equal(#Thy a,#Thy b) andalso
          text_equal(#Name a,#Name b) andalso
          (step ();KernelSig.epoch_of left=KernelSig.epoch_of right) end
      val ceiling=IntInf.fromInt type_work_limit
      fun type_weight ty=
        let val used=ref(0:IntInf.int)
            fun visit ty=
              let val _=step () val _=used:= !used+1
                  val _=if !used<=ceiling then () else
                    failure "native Type work exceeds cap"
              in if Type.is_vartype ty then
                  let val name=Type.dest_vartype ty
                  in charge(IntInf.fromInt(String.size name)) end
                else
                  let val fields=Type.dest_thy_type ty
                      val _=charge(IntInf.fromInt(String.size(#Thy fields))+
                        IntInf.fromInt(String.size(#Tyop fields)))
                      fun args []=step ()
                        | args (child::rest)=(step ();visit child;args rest)
                  in args (#Args fields) end
              end
            val _=visit ty
        in !used end
      fun same_type expected actual=
        let val used=ref(0:IntInf.int)
            fun compare left right=
              let val _=step () val _=used:= !used+1
                  val _=if !used<=ceiling then () else
                    failure "graph Type work exceeds cap"
              in if Type.is_vartype left then
                  Type.is_vartype right andalso
                    text_equal(Type.dest_vartype left,Type.dest_vartype right)
                else if Type.is_vartype right then false else
                  let val a=Type.dest_thy_typeid left
                      val b=Type.dest_thy_typeid right
                      fun args [] []=(step ();true)
                        | args (x::xs) (y::ys)=
                            (step ();compare x y andalso args xs ys)
                        | args _ _=(step ();false)
                  in same_id(#Tyop a,#Tyop b) andalso
                    args (#Args a) (#Args b) end
              end
        in compare expected actual end
      fun visible node=
        (step ();if G.scope_visible graph scope (G.node_scope graph node)
          then () else failure "operand outside active scope")
      val _=visible source
      val statement=Thm.concl theorem
      val _=step ()
      val _=if null(Thm.hyp theorem) then () else
        failure "operator schema has assumptions"
      val (tags,_)=Tag.dest_tag(Thm.tag theorem)
      fun clean []=step ()
        | clean (tag::rest)=
            if text_equal(tag,"DISK_THM") then clean rest else
              failure "unexpected schema oracle"
      val _=clean tags
      val _=step ()
      val _=if null(Tag.axioms_of(Thm.tag theorem)) then () else
        failure "unexpected schema axioms"
      (* Quote the ACTUAL declaration, including the four EQT constructor
         slots and their Types, before EQT_INTRO or graph publication. *)
      fun profile [] raw ann=(raw,ann)
        | profile (term::rest) raw ann=
            let val _=step () val raw=raw+1
                val _=if raw<=template_limit-4 then () else
                  failure "expanded operator schema"
                val ann=ann+type_weight(Term.type_of term)
                val _=if ann<=ceiling then () else
                  failure "native Type portfolio exceeds cap"
            in if Term.is_abs term then
                failure "binder schema needs its bounded local programme"
              else if Term.is_comb term then
                let val (f,x)=Term.dest_comb term
                in profile (f::x::rest) raw ann end
              else profile rest raw ann
            end
      val (raw,annotations)=profile [statement] 0 (0:IntInf.int)
      val arrow=Type.--> (Type.bool,Type.bool)
      val equality_type=Type.--> (Type.bool,arrow)
      val extras=2*type_weight Type.bool+type_weight arrow+
        type_weight equality_type
      val _=if annotations+extras<=ceiling then () else
        failure "native EQT Type portfolio exceeds cap"
      val _=if same_type Type.bool (G.type_of graph source) then () else
        failure "statement is not Boolean"
      fun pairs [] []=(step ();[])
        | pairs (hole::rest) (operand::more)=
            let val _=step () val _=visible operand
                val _=if Term.is_var hole then () else
                  failure "schema hole is not a variable"
                val _=if same_type (Term.type_of hole)
                    (G.type_of graph operand) then () else
                  failure "schema hole Type differs"
            in (hole,operand)::pairs rest more end
        | pairs _ _=failure "operator schema arity mismatch"
      val bindings=pairs holes operands
      fun hole pattern=
        let val (name,ty)=Term.dest_var pattern
            fun seek []=(step ();failure "unowned schema variable")
              | seek ((saved,node)::rest)=
                  let val _=step () val (other,sty)=Term.dest_var saved
                  in if text_equal(name,other) andalso same_type ty sty then
                      node else seek rest end
        in seek bindings end
      fun tree pattern actual=
        let val _=visible actual
            val _=if same_type (Term.type_of pattern)
                (G.type_of graph actual) then () else
              failure "matched constructor Type differs"
        in if Term.is_var pattern then
            let val expected=hole pattern val _=step ()
            in if expected=actual then Operand actual else
              failure "schema hole endpoint differs" end
          else if Term.is_const pattern then
            (case G.view graph actual of G.Constant id=>
               if same_id(id,#Name(Term.dest_thy_constid pattern)) then
                 Literal(actual,pattern)
               else failure "schema constant differs"
             | _=>failure "schema constant shape differs")
          else if Term.is_comb pattern then
            (case G.view graph actual of G.Application(f,x)=>
               let val (pf,px)=Term.dest_comb pattern
                   val left=tree pf f val right=tree px x
                   val _=step ()
               in Constructor(actual,left,right) end
             | _=>failure "schema application differs")
          else failure "binder schema needs its bounded local programme"
        end
      val left=tree statement source
      (* Preserve the existing namespace reservation for native INST holes;
         this is metadata only, after all actual endpoint checks above. *)
      val _=step () val _=G.reserve_schema_holes graph bindings
      (* The matcher above resolves duplicate typed declarations to their
         FIRST binding. Native INST need not do so. Publish that same
         substitution without duplicates for every schema consumer, not
         merely the Boolean root shortcut. All supplied pairs have already
         passed visibility/Type checks and namespace reservation above.
         Their cached operand Type IDs therefore identify declaration Types
         without another native Type traversal or lexical scope lookup. *)
      fun compare_binding ((name,ty),(other,sty))=
        (charge(1+IntInf.fromInt(String.size name)+
          IntInf.fromInt(String.size other));
         case String.compare(name,other) of
           EQUAL=>(step ();Int.compare(ty,sty))
         | order=>order)
      fun first_bindings [] seen=(step ();([],[]))
        | first_bindings ((hole,node)::rest) seen=
            let val _=step ()
                val identity=(#1(Term.dest_var hole),G.type_id graph node)
            in case Redblackmap.peek(seen,identity) of
                SOME ()=>first_bindings rest seen
              | NONE=>
                  let val _=step ()
                      val seen=Redblackmap.insert(seen,identity,())
                      val (holes,operands)=first_bindings rest seen
                      val _=step ()
                  in (hole::holes,node::operands) end
            end
      val (holes,operands)=first_bindings bindings
        (Redblackmap.mkDict compare_binding)
      val _=step () val truth=G.constant graph scope boolSyntax.T
      val _=step () val right=Literal(truth,boolSyntax.T)
      val _=step () val equality=Drule.EQT_INTRO theorem
      val _=step ()
      val _=observe_schema graph 1 (IntInf.fromInt(raw+4)) 0 false
    in GraphSchema {left=left,right=right,holes=holes,operands=operands,
      theorem=equality,admitted_size=raw+4} end

  (* This fast realization is intentionally restricted to fixed Boolean
     annotations. Hard Types and multi-step recipes keep the existing
     compact assembly and annotation-sharing boundary. The checked closed
     declaration itself is the complete compact proof: no definition for
     an unchanged hole's interior is a premise of that proof. *)
  fun realize_boolean_root_schema graph scope
      (GraphConversion {source,result,steps,...}) =
    let
      val _ = G.validate_scope graph scope
      fun key ty = #2 (G.declaration_variable_key graph scope
        (Term.genvar ty))
      val boolean = key Type.bool
      fun arrows 0 = Type.bool
        | arrows n = Type.--> (Type.bool,arrows (n-1))
      val grammar = List.tabulate (4,key o arrows)
      fun visible node =
        if G.scope_visible graph scope (G.node_scope graph node) then ()
        else raise ERR "realize_boolean_root_schema" "retired operand"
      fun bounded (Operand node) =
            (visible node;G.type_id graph node = boolean)
        | bounded (Literal (node,_)) =
            (visible node;List.exists (fn id => id = G.type_id graph node)
              grammar)
        | bounded (Constructor (node,left,right)) =
            (visible node;List.exists (fn id => id = G.type_id graph node)
              grammar andalso bounded left andalso bounded right)
    in case Redblackmap.peek (steps,G.node_id source) of
      SOME (GraphStep {current,continuation = NONE,
        schema = SOME (GraphSchema {left,right,holes,operands,theorem,
                                   admitted_size}),...}) =>
        if current = source andalso template_node left = source andalso
            template_node right = result andalso
            List.length holes <= admitted_size andalso
            List.all (fn node => (visible node;
              G.type_id graph node = boolean)) operands andalso
            bounded left andalso bounded right then
          let
            val substitution = ListPair.mapEq (fn (hole,node) =>
              {redex = hole,residue = G.representative graph node})
              (holes,operands)
            (* Every redex/residue has Boolean Type and every declaration
               annotation is in the fixed grammar above. INST needs no
               hard-Type sharing/preparation of expanded operand interiors. *)
            val _ = observe_schema graph 1 (IntInf.fromInt admitted_size)
              1 true
          in SOME (SmtReplayRuleObservation.INST substitution theorem) end
        else NONE
    | _ => NONE end
    | realize_boolean_root_schema _ _ _ = NONE

  fun realize_typed_root_schema graph scope type_limit
      (GraphConversion {source,result,steps,...}) =
    let
      val _ = G.validate_scope graph scope
      val remaining = ref type_limit
      exception LargeType
      fun visit_type ty =
        if !remaining <= 0 then raise LargeType
        else (remaining := !remaining-1;
          if Type.is_vartype ty then ()
          else List.app visit_type (#2 (Type.dest_type ty)))
      fun term tm =
        (visit_type (Term.type_of tm);
         if Term.is_comb tm then
           let val (f,x) = Term.dest_comb tm in term f; term x end
         else ())
    in (case Redblackmap.peek (steps,G.node_id source) of
        SOME (GraphStep {current,continuation=NONE,
          schema=SOME (GraphSchema {left,right,holes,operands,theorem,
                                    admitted_size}),...}) =>
          if current=source andalso template_node left=source andalso
              template_node right=result then
            let
              val _ = List.app (fn node =>
                if G.scope_visible graph scope (G.node_scope graph node)
                then visit_type (G.type_of graph node)
                else raise ERR "realize_typed_root_schema" "retired operand")
                operands
              val _ = term (Thm.concl theorem)
              val substitution = ListPair.mapEq (fn (hole,node) =>
                {redex=hole,residue=G.representative graph node})
                (holes,operands)
              val _ = observe_schema graph 1 (IntInf.fromInt admitted_size)
                1 true
            in SOME (SmtReplayRuleObservation.INST substitution theorem) end
          else NONE
      | _ => NONE) handle LargeType => NONE
    end
    | realize_typed_root_schema _ _ _ _ = NONE

  fun graph_schema_source (GraphSchema {left,...}) = template_node left
  fun graph_schema_result (GraphSchema {right,...}) = template_node right

  fun closed_endpoints graph scope limit fact =
    let
      val _ = P.validate_closed_fact graph scope limit fact
      val equality = P.closed_node fact
      val (partial,right) = case G.view graph equality of
          G.Application pair => pair
        | _ => raise ERR "graph_conversion" "closed leaf is not equality"
      val (head,left) = case G.view graph partial of
          G.Application pair => pair
        | _ => raise ERR "graph_conversion" "closed leaf is not equality"
      (* Inspect only the cached typed operator, never either expanded
         operand. Matching graph application shape alone is insufficient. *)
      val constant = G.representative graph head
      val _ = if Term.is_const constant andalso
          Term.same_const constant boolSyntax.equality andalso
          G.type_id graph left = G.type_id graph right then () else
        raise ERR "graph_conversion" "closed leaf is not typed equality"
    in (left,right) end

  fun graph_conversion_internal graph scope revisit propose
      propose_closed propose_conversion observe pre_propose source =
    let
      val _ = G.validate_scope graph scope
      val _ = if G.scope_visible graph scope (G.node_scope graph source)
        then () else raise ERR "graph_conversion" "source outside active scope"
      val steps = ref (Redblackmap.mkDict Int.compare)
      val active = ref (Redblackset.empty Int.compare)
      fun normalize node =
        (observe ();case Redblackmap.peek (!steps,G.node_id node) of
          SOME (GraphStep {result,...}) => result
        | NONE =>
          let
            val _ = if Redblackset.member (!active,G.node_id node) then
                raise ERR "graph_conversion" "cyclic checked rewrite expansion"
              else active := Redblackset.add (!active,G.node_id node)
            val early = pre_propose node
            val (current,children) = if Option.isSome early then (node,NONE)
              else case G.view graph node of
                G.Application (operator,operand) =>
                  let val left = normalize operator
                      val right = normalize operand
                  in (observe (); (G.application graph scope (left,right),
                      SOME (operator,operand))) end
              | _ => (node,NONE)
            val closed = if Option.isSome early then NONE
              else propose_closed current
            val conversion = if Option.isSome early then NONE else
              case closed of NONE => propose_conversion current
                | SOME _ => NONE
            val schema = case early of SOME schema => SOME schema
              | NONE => (case (closed,conversion) of
                  (NONE,NONE) => propose current | _ => NONE)
            val next = case conversion of SOME (plan,limit) =>
                (P.validate_conversion graph scope limit plan;
                 if P.conversion_source plan = current then
                   P.conversion_target plan else
                   raise ERR "graph_conversion" "wrong typed leaf endpoint")
              | NONE => (case closed of SOME (fact,limit) =>
                let val (left,right) = closed_endpoints graph scope limit fact
                in if left = current then right else
                  raise ERR "graph_conversion" "wrong closed leaf endpoint"
                end
              | NONE => (case schema of NONE => current
              | SOME schema =>
                let
                  val _ = ignore (G.type_of graph (graph_schema_source schema))
                  val _ = ignore (G.type_of graph (graph_schema_result schema))
                  val _ = if graph_schema_source schema = current then () else
                    raise ERR "graph_conversion"
                      "wrong checked schema endpoint"
                in graph_schema_result schema end))
            val continuation = if revisit andalso next <> current then
                SOME next else NONE
            val result = case continuation of NONE => next
              | SOME next => normalize next
            val step = GraphStep {source = node,current = current,
              result = result,children = children,schema = schema,
              closed = Option.map #1 closed,
              conversion = Option.map #1 conversion,continuation =
                continuation}
            val _ = steps := Redblackmap.insert (!steps,G.node_id node,step)
            val _ = active := Redblackset.delete (!active,G.node_id node)
          in result end)
      val result = normalize source
      (* Discover the Boolean endpoint needed by the single realization too.
         Only small typed operator syntax enters the graph here. *)
      val marker = Term.genvar (G.type_of graph source)
      val equality_operator = Term.rator (Term.rator
        (boolSyntax.mk_eq (marker,marker)))
      val _ = observe ()
      val operator = G.constant graph scope equality_operator
      val _ = observe ()
      val partial = G.application graph scope (operator,source)
      val _ = observe ()
      val equality = G.application graph scope (partial,result)
    in GraphConversion
      {source = source,result = result,equality = equality,steps = !steps,
       guard_slots = ref NONE} end

  fun graph_conversion graph scope revisit propose source =
    graph_conversion_internal graph scope revisit propose (fn _ => NONE)
      (fn _ => NONE) (fn () => ()) (fn _ => NONE) source

  fun graph_conversion_with_schema_leaves graph scope
      {revisit,template_limit,propose,pre_propose,local_conversion,observe} =
    if template_limit <= 0 then
      raise ERR "graph_conversion" "nonpositive original template cap"
    else graph_conversion_internal graph scope revisit propose (fn _ => NONE)
      (fn node => Option.map (fn plan => (plan,template_limit))
        (local_conversion node)) observe pre_propose

  fun graph_conversion_with_schemas graph scope {revisit,propose,observe} =
    graph_conversion_internal graph scope revisit propose (fn _ => NONE)
      (fn _ => NONE) observe (fn _ => NONE)

  fun graph_conversion_with_closed graph scope
      {template_limit,revisit,propose,observe} source =
    if template_limit <= 0 then
      raise ERR "graph_conversion" "nonpositive original template cap"
    else graph_conversion_internal graph scope revisit (fn _ => NONE)
      (fn node => Option.map (fn fact => (fact,template_limit))
        (propose node)) (fn _ => NONE) observe (fn _ => NONE) source

  fun graph_conversion_with_conversions graph scope
      {template_limit,revisit,propose,observe} source =
    if template_limit <= 0 then
      raise ERR "graph_conversion" "nonpositive original template cap"
    else graph_conversion_internal graph scope revisit (fn _ => NONE)
      (fn _ => NONE)
      (fn node => Option.map (fn plan => (plan,template_limit))
        (propose node)) observe (fn _ => NONE) source

  fun legacy_graph_conversions (GraphConversion {steps,...}) =
    Redblackmap.foldl
      (fn (_,GraphStep {conversion,...},rest) => case conversion of
          NONE => rest | SOME plan => plan :: rest) [] steps

  type application_step =
    {source : G.node,current : G.node,result : G.node,
     children : (G.node * G.node) option,closed : P.closed_fact option,
     conversion : P.closed_conversion option,continuation : G.node option}
  fun graph_application_steps graph scope
      (GraphConversion {source,result,equality,steps,...}) =
    let
      val _ = G.validate_scope graph scope
      fun node current =
        if G.scope_visible graph scope (G.node_scope graph current) then ()
        else raise ERR "graph_application_steps" "node outside active Scope"
      val _ = List.app node [source,result,equality]
      fun row (_,GraphStep {source,current,result,children,schema,closed,
                            conversion,continuation},rest) =
        let
          val _ = case schema of NONE => () | SOME _ =>
            raise ERR "graph_application_steps" "schema quote unavailable"
          val _ = List.app node [source,current,result]
          val _ = case children of NONE => ()
            | SOME (left,right) => List.app node [left,right]
          val _ = case continuation of NONE => () | SOME next => node next
        in {source = source,current = current,result = result,
          children = children,closed = closed,conversion = conversion,
          continuation = continuation} :: rest end
    in Redblackmap.foldr row [] steps end
    | graph_application_steps _ _ _ = raise ERR "graph_application_steps"
        "composed recipe requires graph_recipe_steps"

  fun legacy_graph_closed_facts (GraphConversion {steps,...}) =
    Redblackmap.foldl
      (fn (_,GraphStep {closed,...},rest) => case closed of NONE => rest
        | SOME fact => fact :: rest) [] steps

  (* Private immutable ports; callers authenticate before consuming them. *)
  fun policy_graph_ports
      (PolicyGraphConversion {frame,legacy=GraphConversion
        {source,result,equality,...},...}) =
        {frame=frame,source=source,result=result,equality=equality}
    | policy_graph_ports (PolicySequenceGraphConversion
        {frame,source,result,equality,...}) =
        {frame=frame,source=source,result=result,equality=equality}
    | policy_graph_ports _=raise ERR "policy_graph" "not a policy wrapper"
  fun policy_graph_realized (PolicyGraphConversion
        {realization=SOME _,...})=true
    | policy_graph_realized (PolicyGraphConversion
        {canonical_cut=SOME _,...})=true
    | policy_graph_realized (PolicySequenceGraphConversion _)=true
    | policy_graph_realized _=false
  (* This call-local memo is discarded before any caller callback. Every
     later metadata query rechecks actual lifetimes and receipt backing. *)
  fun policy_graph_guard expected root =
    ((let
        val completed=ref ([]:graph_conversion list)
        fun tick ()=W.spend_guard_policy expected 1
        fun member _ []=(tick ();false)
          | member saved (old::rest)=
              (tick ();Portable.pointer_eq(saved,old) orelse
                member saved rest)
        fun visit saved=
          let val work=case saved of PolicyGraphConversion {work,...}=>work
                | PolicySequenceGraphConversion {work,...}=>work
                | _=>raise ERR "policy_graph" "not a policy wrapper"
              val _=if Portable.pointer_eq(expected,work) then () else
                raise ERR "policy_graph" "different original Work"
              (* Immutable ownership wins even on exhausted Work. The
                 private recursion and memo probes are real guard work,
                 including when entered by a held-wrapper getter in Idle. *)
              val _=W.spend_guard_policy expected 8
          in if member saved (!completed) then () else
            (check saved;tick ();completed:=saved:: !completed) end
        and check (PolicyGraphConversion
            {work,frame,legacy,slot,realization,canonical_cut}) =
          let
        val data=SmtReplayOwnedScopeReceipt.description_with_policy_for
          expected frame
        val _=P.validate_conversion_for expected slot
        val maximum= #template_limit(W.semantic_policy expected)
        val _=P.validate_conversion_with_policy (#graph data) (#scope data)
          maximum slot
        val GraphConversion {source,result,equality,...}=legacy
        val _=if source=P.conversion_source slot andalso
            result=P.conversion_target slot then () else
          raise ERR "policy_graph" "different retained conversion endpoints"
        val _=case realization of NONE=>()
          | SOME receipt=>
            let val actual=P.policy_source_realization_data_for
                  expected receipt
            in if Portable.pointer_eq(frame,#frame actual) andalso
                Portable.pointer_eq(#graph data,#graph actual) andalso
                Portable.pointer_eq(#sources data,#sources actual) andalso
                #root data= #root actual andalso
                #scope data= #scope actual andalso
                source= #source actual andalso result= #target actual andalso
                equality= #equality actual then () else
              raise ERR "policy_graph" "different actual realization" end
        val _=case canonical_cut of NONE=>()|SOME cut=>
          let val actual=P.closed_fact_cut_data_with_policy_for expected cut
          in if not(Option.isSome realization)andalso
              Portable.pointer_eq(frame,#frame actual)andalso
              Portable.pointer_eq(slot,#conversion actual)andalso
              Portable.pointer_eq(#graph data,#graph actual)andalso
              Portable.pointer_eq(#sources data,#sources actual)andalso
              #root data= #root actual andalso #scope data= #scope actual
              andalso source= #source actual andalso result= #target actual
              andalso equality= #equality actual then ()else
            raise ERR "policy_graph_cut" "different actual canonical cut"
          end
          in () end
          | check (PolicySequenceGraphConversion
              {work,frame,source,result,equality,first,second}) =
          let
          val data=SmtReplayOwnedScopeReceipt.description_with_policy_for
            expected frame
          val _=visit first
          val _=visit second
          val _=if policy_graph_realized first andalso
              policy_graph_realized second then () else
            raise ERR "policy_graph" "sequence requires realized wrappers"
          val a=policy_graph_ports first and b=policy_graph_ports second
          fun same actual=
            let val other=
                  SmtReplayOwnedScopeReceipt.description_with_policy_for
                    expected actual
            in Portable.pointer_eq(#graph data,#graph other) andalso
              Portable.pointer_eq(#sources data,#sources other) andalso
              #root data= #root other andalso #scope data= #scope other end
          val _=if same (#frame a) andalso same (#frame b) andalso
              source= #source a andalso result= #result b andalso
              #result a= #source b then () else
            raise ERR "policy_graph" "different actual sequence endpoints"
          in () end
          | check _=raise ERR "policy_graph" "not a policy wrapper"
      in visit root end)
     handle primary=>(W.close expected;raise primary))
  fun policy_graph_active
      (saved as PolicyGraphConversion {work,...}) =
        policy_graph_guard work saved
    | policy_graph_active
        (saved as PolicySequenceGraphConversion {work,...}) =
          policy_graph_guard work saved
    | policy_graph_active _=()

  fun graph_source (GraphConversion {source,...}) = source
    | graph_source (DirectRealizedSequence {source,...}) = source
    | graph_source (SequenceGraphConversion {source,...}) = source
    | graph_source (ApplicationGraphConversion {source,...}) = source
    | graph_source (RealizedGraphConversion {legacy,...}) = graph_source legacy
    | graph_source (saved as PolicyGraphConversion {legacy,...}) =
        (policy_graph_active saved;graph_source legacy)
    | graph_source (saved as PolicySequenceGraphConversion
        {source,...}) =
        (policy_graph_active saved;source)
  fun graph_result (GraphConversion {result,...}) = result
    | graph_result (DirectRealizedSequence {result,...}) = result
    | graph_result (SequenceGraphConversion {result,...}) = result
    | graph_result (ApplicationGraphConversion {result,...}) = result
    | graph_result (RealizedGraphConversion {legacy,...}) = graph_result legacy
    | graph_result (saved as PolicyGraphConversion {legacy,...}) =
        (policy_graph_active saved;graph_result legacy)
    | graph_result (saved as PolicySequenceGraphConversion
        {result,...}) =
        (policy_graph_active saved;result)
  fun graph_equality (GraphConversion {equality,...}) = equality
    | graph_equality (DirectRealizedSequence {equality,...}) = equality
    | graph_equality (SequenceGraphConversion {equality,...}) = equality
    | graph_equality (ApplicationGraphConversion {equality,...}) = equality
    | graph_equality (RealizedGraphConversion {legacy,...}) = graph_equality
      legacy
    | graph_equality (saved as PolicyGraphConversion {legacy,...}) =
        (policy_graph_active saved;graph_equality legacy)
    | graph_equality (saved as PolicySequenceGraphConversion
        {equality,...}) =
        (policy_graph_active saved;equality)
  fun legacy_graph_roots (GraphConversion {source,result,equality,steps,...}) =
    equality :: source :: result :: Redblackmap.foldl
      (fn (_,GraphStep {current,schema,closed,conversion,...},roots) =>
        current :: (case closed of NONE => []
          | SOME fact => [P.closed_node fact]) @
        (case conversion of NONE => [] | SOME plan =>
          [P.conversion_source plan,P.conversion_target plan]) @
        (case schema of NONE => roots
          | SOME schema => graph_schema_source schema ::
              graph_schema_result schema :: roots)) [] steps


  (* Inventory traversal also copies lists and probes physical memos.
     Pay before every link/terminal dispatch, not merely emitted witnesses.
     Map size is retained O(1) metadata; this quote covers the complete
     tree walk, empty branches and bounded per-row projection/list copies. *)
  fun inventory_step_map pay steps =
    pay (4+16*IntInf.fromInt (Redblackmap.numItems steps))
  fun inventory_legacy pay project
      (current as GraphConversion {steps,...}) =
    (inventory_step_map pay steps;project current)
  fun inventory_append (pay : IntInf.int -> unit) [] right =
        (pay 1;right)
    | inventory_append pay (item::rest) right =
        (pay 1;item::inventory_append pay rest right)
  fun inventory_map (pay : IntInf.int -> unit) project [] = (pay 1;[])
    | inventory_map pay project (item::rest) =
        (pay 1;project item::inventory_map pay project rest)
  fun inventory_concat pay [] = (pay 1;[])
    | inventory_concat pay (items::rest) =
        (pay 1;inventory_append pay items (inventory_concat pay rest))

  (* Identity memoization concerns proof recipes, not semantic Work credit.
     Every new call builds its own cache; legacy projection order is intact.
     A direct sequence's children are absent only from the root inventory. *)
  fun recipe_nodes_using pay header roots conversion =
    let val seen = ref ([] : graph_conversion list)
        fun member _ []=(pay 1;false)
          | member current (old::rest)=
              (pay 1;Portable.pointer_eq(current,old) orelse
                member current rest)
        fun visit current =
          (header current;pay 8;
           if member current (!seen) then []
           else (pay 1;seen := current :: !seen;
             current :: (case current of GraphConversion _ => []
               | RealizedGraphConversion _ => []
               | saved as PolicyGraphConversion _ =>
                   (policy_graph_active saved;[])
               | saved as PolicySequenceGraphConversion
                   {first,second,...} =>
                   (policy_graph_active saved;children first second)
               | SequenceGraphConversion {first,second,...} =>
                   children first second
               | DirectRealizedSequence {first,second,...} =>
                   if roots then [] else children first second
               | ApplicationGraphConversion {left,right,...} =>
                   children left right)))
        and children first second =
          inventory_append pay (visit first) (visit second)
    in visit conversion end
  fun graph_conversions_using pay header conversion =
    inventory_concat pay (inventory_map pay
      (fn current as GraphConversion _ =>
            inventory_legacy pay legacy_graph_conversions current
        | RealizedGraphConversion {legacy,...} =>
            inventory_legacy pay legacy_graph_conversions legacy
        | saved as PolicyGraphConversion {slot,...} =>
            (policy_graph_active saved;[slot])
        | _ => []) (recipe_nodes_using pay header false conversion))
  fun graph_conversions conversion =
    graph_conversions_using (fn _ => ()) (fn _ => ()) conversion
  (* Cache only the immutable slot projection, never witness validity or
     Work credit. A fresh map starts cold, including an all-NONE map.
     numItems is O(1); the cold quote pays the original complete map walk.
     Publish only after every guard and paid list construction/reversal
     succeeds, retaining the original ascending-map validation order. *)
  fun validate_step_map pay expected steps guard_slots =
    case !guard_slots of
      SOME slots =>
        let fun validate [] = pay 1
              | validate (slot::rest) =
                  (pay 1;P.validate_conversion_for expected slot;
                   validate rest)
        in validate slots end
    | NONE =>
        let
          val _ = pay (4+8*IntInf.fromInt (Redblackmap.numItems steps))
          val slots = ref []
          val _ = Redblackmap.app (fn (_,GraphStep {conversion,...}) =>
            case conversion of NONE => () | SOME slot =>
              (P.validate_conversion_for expected slot;
               pay 1;slots := slot :: !slots)) steps
          fun reverse [] result = (pay 1;result)
            | reverse (slot::rest) result =
                (pay 1;reverse rest (slot::result))
          val ordered = reverse (!slots) []
        in guard_slots := SOME ordered end
  (* A wrapper's immutable Work header has priority over guard payment,
     even for exhausted live legacy Work. This is not a lifetime check. *)
  fun conversion_header expected saved =
    let val owner=case saved of
            PolicyGraphConversion {work,...}=>SOME work
          | PolicySequenceGraphConversion {work,...}=>SOME work
          | _=>NONE
    in case owner of NONE=>() | SOME work=>
      if Portable.pointer_eq(expected,work) then () else
        raise ERR "policy_graph" "different original Work" end
  (* A plain terminal has no Work header or witness outside its immutable
     slot projection. Move its existing dispatch quote (8) before the cache
     read: it covers constructor/field selection, ref read, option/list
     tests and return. SOME [] is the published all-NONE map projection,
     not a cached guard result. The paid entry still guards original Work
     on EVERY call, before this read, even for a shared empty terminal.
     Cold/nonempty fallback retains the original empty-memo probe (1),
     map validation and remember (1), with no extra payment or payload.
     Only the callback-free first two payments exchange order (1,8 -> 8,1).
     Composite visits below keep their original memo/de-dup itinerary. *)
  fun legacy_validate_conversion_using pay expected
      (saved as GraphConversion _) =
    let
      val _ = pay 8
      val GraphConversion {steps,guard_slots,...} = saved
    in case !guard_slots of SOME [] => ()
      | _ => (pay 1;validate_step_map pay expected steps guard_slots;pay 1)
    end
    | legacy_validate_conversion_using pay expected conversion =
    let
      (* Only an ordinary root owns this structural projection. A cold
         root keeps the original traversal and first-error order, even if
         children already have projections. Retain actual guard owners,
         never guard success: their receipts and private guards stay live. *)
      val projection=case conversion of
          SequenceGraphConversion {guard_leaves,...}=>SOME guard_leaves
        | DirectRealizedSequence {guard_leaves,...}=>SOME guard_leaves
        | ApplicationGraphConversion {guard_leaves,...}=>SOME guard_leaves
        | _=>NONE
      val compiling=case projection of
          SOME cache=>not(Option.isSome(!cache)) | NONE=>false
      val leaves=ref ([]:graph_conversion list)
      fun retain saved=if compiling then
          (pay 1;leaves:=saved:: !leaves) else ()
      fun reverse [] result=(pay 1;result)
        | reverse (saved::rest) result=
            (pay 1;reverse rest (saved::result))
      (* This validation is callback-free. Shared legacy recipes need only
         one successful check per call, just like policy wrappers; do not
         expand their immutable DAG into an occurrence tree. No guard
         success or lifetime waiver escapes. Every memo probe is paid. *)
      val completed=ref ([]:graph_conversion list)
      fun member _ []=(pay 1;false)
        | member saved (old::rest)=
            (pay 1;Portable.pointer_eq(saved,old) orelse member saved rest)
      fun visit saved =
        ((conversion_header expected saved
          handle primary=>(W.close expected;raise primary));
         if member saved (!completed) then () else
           (check saved;pay 1;completed:=saved:: !completed))
      and check saved =
        (pay 8;
         case saved of
            GraphConversion {steps,guard_slots,...} =>
              (validate_step_map pay expected steps guard_slots;
               case !guard_slots of SOME (_::_)=>retain saved | _=>())
          | SequenceGraphConversion {first,second,...} =>
              (visit first;visit second)
          | DirectRealizedSequence {first,second,...} =>
              (visit first;visit second)
          | ApplicationGraphConversion {left,right,...} =>
              (visit left;visit right)
          | RealizedGraphConversion {realization,...} =>
              (P.validate_realization_for expected realization;retain saved)
          | saved as PolicyGraphConversion _ =>
              (policy_graph_guard expected saved;retain saved)
          | saved as PolicySequenceGraphConversion _ =>
              (policy_graph_guard expected saved;retain saved))
      (* A hit visits every retained leaf with the same header, paid
         dispatch and call-local memo, but never walks the root tree. *)
      fun validate_leaves []=pay 1
        | validate_leaves (saved::rest)=
            (pay 1;visit saved;validate_leaves rest)
    in case projection of NONE=>visit conversion
      | SOME cache=>(case !cache of
          SOME ordered=>validate_leaves ordered
        | NONE=>
            let val _=visit conversion
                val ordered=reverse (!leaves) []
            in cache:=SOME ordered end)
    end
  val _=SmtReplayInvocationWork.ordinary_policy_guard_mode
  val _=SmtReplayInvocationWork.spend_ordinary_guard_policy
  (* No validation memo escapes this callback-free call; only immutable
     structural projections persist. In policy mode, until an actual
     policy-wrapper guard succeeds, retain the old no-memo itinerary: an
     ordinary composite has no immutable Work header. The independent pay
     hook meters traversal only at authenticated replay-owner boundaries. *)
  fun validate_conversion_using pay expected conversion =
    if not(W.ordinary_policy_guard_mode expected)then
      legacy_validate_conversion_using pay expected conversion
    else
      ((let
          val completed=ref([]:graph_conversion list)
          val enabled=ref false
          fun charge()=W.spend_ordinary_guard_policy expected 1
          fun member _ []=(charge();false)
            | member saved(old::rest)=
                (charge();Portable.pointer_eq(saved,old)orelse
                  member saved rest)
          fun remember saved=(charge();completed:=saved:: !completed)
          fun visit saved=
            (conversion_header expected saved;
             if !enabled then
               if member saved(!completed)then ()else
                 (check saved;remember saved)
             else
               (check saved;if !enabled then remember saved else ()))
          and check saved =
            (pay 8;
             case saved of
                GraphConversion {steps,guard_slots,...} =>
                  (* The common dispatch payment precedes this projection
                     read too; a warm empty terminal has no slot guard. *)
                  (case !guard_slots of SOME [] => ()
                   | _ => validate_step_map pay expected steps guard_slots)
              | SequenceGraphConversion {first,second,...} =>
                  (visit first;visit second)
              | DirectRealizedSequence {first,second,...} =>
                  (visit first;visit second)
              | ApplicationGraphConversion {left,right,...} =>
                  (visit left;visit right)
              | RealizedGraphConversion {realization,...} =>
                  P.validate_realization_for expected realization
              | saved as PolicyGraphConversion _ =>
                  (policy_graph_guard expected saved;enabled:=true)
              | saved as PolicySequenceGraphConversion _ =>
                  (policy_graph_guard expected saved;enabled:=true))
        in visit conversion end)
       handle primary=>(W.close expected;raise primary))

  (* Dormant metadata validation retains its old activation/exception order.
     Authenticated replay owners use the paid entry even for legacy recipes
     without a policy wrapper. Either entry may warm structural projections,
     but later paid calls still pay each link/terminal and recheck witnesses.
     No validation success or Work credit escapes either call. *)
  fun validate_conversion_header_for expected conversion =
    (conversion_header expected conversion
     handle primary => (W.close expected;raise primary))
  fun validate_conversion_for expected conversion =
    validate_conversion_using (fn _ => ()) expected conversion
  fun validate_conversion_with_policy expected conversion =
    (validate_conversion_using (W.spend_guard_policy expected)
       expected conversion
     handle primary => (W.close expected;raise primary))

  fun graph_closed_facts_using pay header conversion =
    inventory_concat pay (inventory_map pay
      (fn current as GraphConversion {steps,...} =>
          (inventory_step_map pay steps;legacy_graph_closed_facts current)
        | _ => []) (recipe_nodes_using pay header false conversion))
  fun graph_closed_facts conversion =
    graph_closed_facts_using (fn _ => ()) (fn _ => ()) conversion
  (* Direct children consume their exact typed conversion slots. Their
     equality-name wrappers are not executed and are not constructor roots.
     The containing sequence's own named equality remains an ordinary root. *)
  fun graph_roots_using pay header conversion =
    inventory_concat pay (inventory_map pay
    (fn current as GraphConversion {steps,...} =>
          (inventory_step_map pay steps;legacy_graph_roots current)
      | RealizedGraphConversion {legacy,...} => [graph_equality legacy]
      | saved as PolicyGraphConversion {legacy,realization,canonical_cut,...}=>
          (policy_graph_active saved;case canonical_cut of
             SOME _=>[graph_equality legacy]
           | NONE=>(case realization of
               SOME _=>[graph_equality legacy]
             | NONE=>[graph_equality legacy,graph_source legacy,
                       graph_result legacy]))
      | saved as PolicySequenceGraphConversion {equality,...} =>
          (policy_graph_active saved;[equality])
      | current => [graph_equality current,graph_source current,
                    graph_result current])
      (recipe_nodes_using pay header true conversion))
  fun graph_roots conversion =
    graph_roots_using (fn _ => ()) (fn _ => ()) conversion

  (* An ordinary legacy recipe has no held Work. Selected replay owners
     must pass their original expected portfolio; never infer a counter
     from an optional policy leaf or use a fresh per-inventory allowance.
     These callback-free DATA walks are legal in Idle as well as Busy. *)
  fun inventory_for inventory expected conversion =
    (inventory (W.spend_guard_policy expected)
       (conversion_header expected) conversion
     handle primary => (W.close expected;raise primary))
  val graph_conversions_for = inventory_for graph_conversions_using
  val graph_closed_facts_for = inventory_for graph_closed_facts_using
  val graph_roots_for = inventory_for graph_roots_using

  fun legacy_assemble graph block
      (conversion as GraphConversion {source,equality,steps,...}) =
    let
      val _ = List.app (P.validate_closed_fact graph (P.scope block)
        (P.template_limit block))
        (graph_closed_facts conversion)
      val _ = List.app (P.validate_conversion graph (P.scope block)
        (P.template_limit block)) (graph_conversions conversion)
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun reflexive node = P.checked block (SmtReplayRuleObservation.REFL
        (P.name block node))
      fun trans left right = P.compose block
        (fn [left,right] =>
          SmtReplayRuleObservation.TRANS left
            (SmtReplayTermBridge.exact_left
              (boolSyntax.rhs (Thm.concl left)) right)
          | _ => raise Fail "graph trans premises") [left,right]
      fun expansion (Operand node) = reflexive node
        | expansion (Literal (node,_)) = P.definition block node
        | expansion (Constructor (node,left,right)) =
            let val combined = P.compose block
              (fn [left,right] => SmtReplayRuleObservation.MK_COMB (left,right)
                | _ => raise Fail "graph constructor premises")
              [expansion left,expansion right]
            in trans (P.definition block node) combined end
      fun schema_proof
          (GraphSchema {left,right,holes,operands,theorem,admitted_size}) =
        let
          val substitution = ListPair.mapEq
            (fn (hole,node) => {redex = hole,residue = P.name block node})
            (holes,operands)
          (* The theorem is still a bounded schema; residues are compact
             names. This is not an INST of a realized graph theorem. *)
          val _ = observe_schema graph 1 (IntInf.fromInt admitted_size) 1 true
          val _ = SmtReplayTermBridge.prepare_schema_substitution
            admitted_size theorem substitution
          val instantiated = P.checked block
            (SmtReplayRuleObservation.INST substitution theorem)
          val backwards = P.compose block
            (fn [proof] => SmtReplayRuleObservation.SYM proof
              | _ => raise Fail "graph schema symmetry") [expansion right]
        in trans (expansion left) (trans instantiated backwards) end
      fun assemble node =
        case Redblackmap.peek (!memo,G.node_id node) of SOME edge => edge
        | NONE =>
          let
            val GraphStep
              {current,children,schema,closed,conversion,continuation,...} =
              Redblackmap.find (steps,G.node_id node)
            val initial = case children of NONE => reflexive node
              | SOME (operator,operand) =>
                if current = node then reflexive node else
                let
                  val combined = P.compose block
                    (fn [left,right] => SmtReplayRuleObservation.MK_COMB
                      (left,right)
                      | _ => raise Fail "graph child congruence")
                    [assemble operator,assemble operand]
                  val backwards = P.compose block
                    (fn [proof] => SmtReplayRuleObservation.SYM proof
                      | _ => raise Fail "graph parent symmetry")
                    [P.definition block current]
                in trans (P.definition block node)
                  (trans combined backwards) end
            val oriented = case conversion of SOME plan =>
                trans initial (P.conversion block plan)
              | NONE => (case closed of SOME fact =>
                let val equality = P.closed_node fact
                    val named = P.compose block
                      (fn [proof,constructor] => SmtReplayRuleObservation.EQ_MP
                        constructor proof
                        | _ => raise Fail "graph closed leaf premises")
                      [P.closed block fact,P.constructor block equality]
                in trans initial named end
              | NONE => (case schema of NONE => initial
                | SOME schema => trans initial (schema_proof schema)))
            val result = case continuation of NONE => oriented
              | SOME next => trans oriented (assemble next)
            val _ = memo := Redblackmap.insert (!memo,G.node_id node,result)
          in result end
      val proof = assemble source
      val (operator,right) = case G.view graph equality of
          G.Application pair => pair | _ => raise Fail "graph equality root"
      val (head,left) = case G.view graph operator of
          G.Application pair => pair | _ => raise Fail "graph equality head"
      val actual = P.compose block
        (fn [head,inner,outer] =>
          let
            val inner = SmtReplayRuleObservation.TRANS inner
              (SmtReplayRuleObservation.AP_THM head (P.name block left))
          in SmtReplayRuleObservation.TRANS outer
            (SmtReplayRuleObservation.AP_THM inner (P.name block right)) end
          | _ => raise Fail "graph equality expansion")
        [P.definition block head,P.definition block operator,
         P.definition block equality]
    in P.compose block
      (fn [expansion,proof] => SmtReplayRuleObservation.EQ_MP
        (SmtReplayRuleObservation.SYM expansion) proof
        | _ => raise Fail "graph equality naming") [actual,proof] end

  fun assemble_finite_named graph block
      (converted as GraphConversion {source,equality,steps,...}) =
    let
      (* Reject owned blocks before ANY native rule. This is the existing
         unowned checked-edge gate, not a second Work/native permission. *)
      val _ = P.checked block boolTheory.TRUTH
      val scope = P.scope block
      val limit = P.template_limit block
      val _ = List.app (P.validate_closed_fact graph scope limit)
        (graph_closed_facts converted)
      val _ = List.app (P.validate_conversion graph scope limit)
        (graph_conversions converted)
      val memo = ref (Redblackmap.mkDict Int.compare)
      val definitions = ref (Redblackmap.mkDict Int.compare)
      val premises = ref []
      fun theorem edge =
        (premises := edge :: !premises;P.theorem block edge)
      fun definition node =
        case Redblackmap.peek (!definitions,G.node_id node) of
          SOME theorem => theorem
        | NONE =>
            let val theorem = theorem (P.definition block node)
            in definitions := Redblackmap.insert
              (!definitions,G.node_id node,theorem); theorem end
      fun refl node = SmtReplayRuleObservation.REFL (P.name block node)
      val trans = SmtReplayRuleObservation.TRANS
      val sym = SmtReplayRuleObservation.SYM
      val comb = SmtReplayRuleObservation.MK_COMB
      fun expansion (Operand node) = refl node
        | expansion (Literal (node,_)) = definition node
        | expansion (Constructor (node,left,right)) =
            trans (definition node) (comb (expansion left,expansion right))
      fun schema_proof (GraphSchema
          {left,right,holes,operands,theorem,admitted_size}) =
        let
          val substitution = ListPair.mapEq (fn (hole,node) =>
            {redex=hole,residue=P.name block node}) (holes,operands)
          val _ = SmtReplayTermBridge.prepare_schema_substitution
            admitted_size theorem substitution
          val _ = observe_schema graph 1 (IntInf.fromInt admitted_size) 1 true
          val law = SmtReplayRuleObservation.INST substitution theorem
        in trans (expansion left) (trans law (sym (expansion right))) end
      fun assemble node =
        case Redblackmap.peek (!memo,G.node_id node) of SOME theorem => theorem
        | NONE =>
          let
            val GraphStep
              {current,children,schema,closed,conversion,continuation,...} =
              Redblackmap.find (steps,G.node_id node)
            val initial = case children of NONE => refl node
              | SOME (operator,operand) => if current=node then refl node else
                  trans (definition node)
                    (trans (comb (assemble operator,assemble operand))
                      (sym (definition current)))
            val oriented = case conversion of SOME plan =>
                trans initial (theorem (P.conversion block plan))
              | NONE => (case closed of SOME fact =>
                  trans initial (SmtReplayRuleObservation.EQ_MP
                    (theorem
                      (P.constructor block (P.closed_node fact)))
                    (theorem (P.closed block fact)))
                | NONE => (case schema of NONE => initial
                  | SOME schema => trans initial (schema_proof schema)))
            val result = case continuation of NONE => oriented
              | SOME next => trans oriented (assemble next)
            val _ = memo := Redblackmap.insert (!memo,G.node_id node,result)
          in result end
      val proof = assemble source
      val (operator,right) = case G.view graph equality of
          G.Application pair => pair | _ => raise Fail "word equality root"
      val (head,left) = case G.view graph operator of
          G.Application pair => pair | _ => raise Fail "word equality head"
      val inner = trans (definition operator)
        (SmtReplayRuleObservation.AP_THM (definition head) (P.name block left))
      val actual = trans (definition equality)
        (SmtReplayRuleObservation.AP_THM inner (P.name block right))
      val proof = SmtReplayRuleObservation.EQ_MP (sym actual) proof
      (* These are the actual same-block inputs used above, not external
         leaf assumptions. Compose checks the final named Hyp directly and
         records their edges; lifting each Hyp through its own projection
         would repeat a proof already held by this block. *)
    in P.compose block (fn _ => proof) (!premises) end
    | assemble_finite_named _ _ _ =
        raise ERR "graph_assemble_named" "not a finite named conversion"

  fun visible graph scope node =
    if G.scope_visible graph scope (G.node_scope graph node) then () else
      raise ERR "recipe" "node outside active Scope"
  fun equality_node graph scope observe source target =
    let val _ = observe ()
        val _ = List.app (visible graph scope) [source,target]
        val _ = if G.type_id graph source = G.type_id graph target then () else
          raise ERR "recipe" "different typed endpoints"
        val marker = Term.genvar (G.type_of graph source)
        val head = Term.rator (Term.rator (boolSyntax.mk_eq (marker,marker)))
        val _ = observe () val operator = G.constant graph scope head
        val _ = observe () val partial = G.application graph scope
          (operator,source)
        val _ = observe ()
    in G.application graph scope (partial,target) end
  fun graph_schema_leaf graph scope
      {schema=schema as GraphSchema {left,right,operands,...},observe} =
    let
      val _ = G.validate_scope graph scope
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      fun guard () =
        (G.validate_scope graph scope;
         if Type.type_epoch ()=epoch andalso Term.term_epoch ()=symbols
         then () else raise ERR "graph_schema_leaf" "retired declaration")
      fun step () = (observe ();guard ())
      fun node current =
        (step ();visible graph scope current;
         ignore (G.type_of graph current))
      fun template (Operand current) = node current
        | template (Literal (current,_)) = node current
        | template (Constructor (current,a,b)) =
            (node current;template a;template b)
      val _ = template left val _ = template right
      fun inputs [] = step ()
        | inputs (current::rest) = (node current;inputs rest)
      val _ = inputs operands
      val source = template_node left val target = template_node right
      val equality = equality_node graph scope step source target
      (* Exact checked schema metadata; no ordinary child normalization.
         The existing assembler still prepares/executes its named INST. *)
      val _ = step ()
      val item = GraphStep
        {source=(step ();source),current=(step ();source),
         result=(step ();target),children=(step ();NONE),
         schema=(step ();SOME schema),closed=(step ();NONE),
         conversion=(step ();NONE),continuation=(step ();NONE)}
      val _ = step () val empty = Redblackmap.mkDict Int.compare
      val _ = step () val key = G.node_id source
      val _ = step () val steps = Redblackmap.insert (empty,key,item)
      val _ = step ()
      val result = GraphConversion
        {source=(step ();source),result=(step ();target),
         equality=(step ();equality),steps=(step ();steps),
         guard_slots=(step ();ref NONE)}
      val _ = guard ()
    in result end

  fun graph_identity graph scope {observe} node =
    graph_conversion_internal graph scope false (fn _ => NONE)
      (fn _ => NONE) (fn _ => NONE) observe (fn _ => NONE) node
  fun graph_leaf graph scope {conversion,template_limit,observe} =
    let val _ = observe ()
        val _ = P.validate_conversion graph scope template_limit conversion
        val source = P.conversion_source conversion
        val target = P.conversion_target conversion
        val equality = equality_node graph scope observe source target
        val step = GraphStep {source = source,current = source,result = target,
          children = NONE,schema = NONE,closed = NONE,
          conversion = SOME conversion,continuation = NONE}
    in GraphConversion {source = source,result = target,equality = equality,
      steps = Redblackmap.insert
        (Redblackmap.mkDict Int.compare,G.node_id source,step),
      guard_slots = ref NONE} end
  fun graph_realized_leaf expected {realization,observe} =
    let val data = P.realization_data_for expected realization
        val _ = observe ()
        val converted = P.conversion_from_realization expected realization
        val legacy = graph_leaf (#graph data) (#scope data)
          {conversion = converted,template_limit = #template_limit data,
           observe = observe}
        val _ = P.validate_realization_for expected realization
    in RealizedGraphConversion
      {legacy = legacy,realization = realization} end
  fun graph_application graph scope {source,left,right,observe} =
    let val _ = observe () val _ = visible graph scope source
        val (f,x) = case G.view graph source of G.Application pair => pair
          | _ => raise ERR "graph_application" "source is not application"
        val _ = if graph_source left = f andalso graph_source right = x
          then () else raise ERR "graph_application" "wrong child recipes"
        val _ = observe ()
        val target = G.application graph scope
          (graph_result left,graph_result right)
        val equality = equality_node graph scope observe source target
    in ApplicationGraphConversion {source = source,result = target,
      equality = equality,left = left,right = right,
      guard_leaves = ref NONE} end
  (* Fuse ONLY private coherent legacy step tables. Equality naming belongs
     to the resulting root; each exact typed leaf retains its original owner
     witness. Conflicting source-node occurrences keep the composed grammar. *)
  fun same_optional equal (NONE,NONE) = true
    | same_optional equal (SOME a,SOME b) = equal (a,b)
    | same_optional _ _ = false
  fun same_graph_step
      (GraphStep {source = a,current = b,result = c,children = d,
                  schema = e,closed = f,conversion = h,continuation = i},
       GraphStep {source = j,current = k,result = l,children = m,
                  schema = n,closed = r,conversion = t,continuation = u}) =
    a = j andalso b = k andalso c = l andalso d = m andalso i = u andalso
    same_optional Portable.pointer_eq (e,n) andalso
    same_optional Portable.pointer_eq (f,r) andalso
    same_optional Portable.pointer_eq (h,t)
  fun graph_application_fused graph scope {source,left,right,observe} =
    let val _ = observe () val _ = visible graph scope source
        val (f,x) = case G.view graph source of G.Application pair => pair
          | _ => raise ERR "graph_application_fused"
            "source is not application"
        val _ = if graph_source left = f andalso graph_source right = x
            then () else raise ERR "graph_application_fused"
              "wrong private child recipes"
        fun union a b = Redblackmap.foldl
          (fn (key,step,answer) =>
            (observe ();case answer of NONE => NONE | SOME table =>
               case Redblackmap.peek (table,key) of NONE =>
                 SOME (Redblackmap.insert (table,key,step))
               | SOME old => if same_graph_step (old,step) then SOME table
                   else NONE)) (SOME a) b
        val coherent = case (left,right) of
            (GraphConversion {steps = a,...},GraphConversion {steps = b,...})
              => union a b
          | _ => NONE
        val fresh = case coherent of SOME steps =>
              if Option.isSome (Redblackmap.peek (steps,G.node_id source))
                then NONE else SOME steps
          | NONE => NONE
    in case fresh of NONE => graph_application graph scope
          {source = source,left = left,right = right,observe = observe}
      | SOME steps =>
          let val _ = observe ()
              val target = G.application graph scope
                (graph_result left,graph_result right)
              val equality = equality_node graph scope observe source target
              val step = GraphStep {source = source,current = target,
                result = target,children = SOME (f,x),schema = NONE,
                closed = NONE,conversion = NONE,continuation = NONE}
              val _ = observe ()
          in GraphConversion {source = source,result = target,
            equality = equality,steps = Redblackmap.insert
              (steps,G.node_id source,step),guard_slots = ref NONE} end
    end

  fun graph_sequence graph scope {first,second,observe} =
    let val _ = observe ()
        val _ = if graph_result first = graph_source second then () else
          raise ERR "graph_sequence" "nonmatching recipe endpoints"
        val source = graph_source first val target = graph_result second
        val equality = equality_node graph scope observe source target
    in SequenceGraphConversion {source = source,result = target,
      equality = equality,first = first,second = second,
      guard_leaves = ref NONE} end

  (* Both leaves must be genuine SAME-Work realized wrappers. No external
     theorem, endpoint pair or phase scalar supplies either executable slot. *)
  fun graph_realized_sequence expected {first,second,observe} =
    let
      fun slot (RealizedGraphConversion {legacy,realization}) =
            (P.validate_realization_for expected realization;
             case inventory_legacy (W.spend_guard_policy expected)
                 legacy_graph_conversions legacy of [converted] => converted
               | _ => raise ERR "graph_realized_sequence"
                   "different private realized leaf grammar")
        | slot _ = raise ERR "graph_realized_sequence"
            "sequence requires two genuine realized leaves"
      val a = slot first val b = slot second
      fun data (RealizedGraphConversion {realization,...}) =
            P.realization_data_for expected realization
        | data _ = raise ERR "graph_realized_sequence" "missing receipt"
      val data = data first
      val other = P.realization_data_for expected
        (case second of RealizedGraphConversion {realization,...} =>
          realization
          | _ => raise ERR "graph_realized_sequence" "missing second receipt")
      val _ = if Portable.pointer_eq (#graph data,#graph other) andalso
          #scope data = #scope other then () else
        raise ERR "graph_realized_sequence" "different actual realized frame"
      val _ = validate_conversion_with_policy expected first
      val _ = validate_conversion_with_policy expected second
      val graph = #graph data and scope = #scope data
      val source = graph_source first and target = graph_result second
      val _ = if graph_result first = graph_source second then () else
        raise ERR "graph_realized_sequence" "nonmatching genuine middle"
      val _ = List.app (visible graph scope)
        [source,graph_result first,target]
      val equality = equality_node graph scope observe source target
      val _ = validate_conversion_with_policy expected first
      val _ = validate_conversion_with_policy expected second
    in DirectRealizedSequence {source = source,result = target,
      equality = equality,first = first,second = second,
      first_slot = a,second_slot = b,guard_leaves = ref NONE} end

  datatype recipe_kind = LegacyStep | ApplicationRecipe | SequenceRecipe
  type recipe_step =
    {id : int,kind : recipe_kind,source : G.node,current : G.node,result :
      G.node,
     children : (int * int) option,prefix : int option,equality : G.node
       option,
     closed : P.closed_fact option,conversion : P.closed_conversion option,
     continuation : int option}
  fun graph_recipe_steps graph scope {observe} conversion =
    let val next = ref 0 val rows = ref ([] : recipe_step list)
        fun fresh () = (observe ();let val id = !next
          in next := id+1;id end)
        fun save (row : recipe_step) =
          (observe ();List.app (visible graph scope)
            [#source row,#current row,#result row];
           Option.app (visible graph scope) (#equality row);
           rows := row :: !rows;
           #id row)
        val objects = ref ([] : (graph_conversion * int) list)
        (* Opening a realized slot and naming its equality are distinct
           executable grammars, even for the same exact recipe object. *)
        val direct_objects = ref ([] : (graph_conversion * int) list)
        fun cached current [] = NONE
          | cached current ((old,id)::rest) =
              (observe ();if Portable.pointer_eq (current,old) then SOME id
               else cached current rest)
        fun collect current =
          (observe ();case cached current (!objects) of SOME id => id | NONE =>
            let val id = collect_fresh current val _ = observe ()
                val _ = objects := (current,id) :: !objects
            in id end)
        and collect_fresh (GraphConversion {source =
          root_source,equality,steps,...}) =
              let val memo = ref (Redblackmap.mkDict Int.compare)
                  val pending = ref (Redblackset.empty Int.compare)
                  fun visit node =
                    (observe ();case Redblackmap.peek (!memo,G.node_id node) of
                      SOME id => id | NONE =>
                      let val _ = if Redblackset.member
                            (!pending,G.node_id node) then
                              raise ERR "recipe" "cyclic conversion recipe"
                            else pending := Redblackset.add
                              (!pending,G.node_id node)
                          val GraphStep {source,current,result,children,
                            schema,closed,conversion,continuation} =
                            Redblackmap.find (steps,G.node_id node)
                          val _ = case schema of NONE => () | SOME _ =>
                            raise ERR "recipe" "schema quote unavailable"
                          val children = Option.map
                            (fn (a,b) => (visit a,visit b)) children
                          val continuation = Option.map visit continuation
                          val id = fresh ()
                          val _ = save {id = id,kind = LegacyStep,source =
                            source,
                            current = current,result = result,
                            children = children,prefix = NONE,equality = if
                              source = root_source then
                              SOME equality else NONE,closed = closed,
                            conversion = conversion,continuation =
                              continuation}
                          val _ = memo := Redblackmap.insert
                            (!memo,G.node_id node,id)
                          val _ = pending := Redblackset.delete
                            (!pending,G.node_id node)
                      in id end)
              in visit root_source end
          | collect_fresh (RealizedGraphConversion {legacy,...}) =
              collect_fresh legacy
          | collect_fresh (saved as PolicyGraphConversion _) =
              (policy_graph_active saved;
               raise ERR "graph_recipe_steps"
                 "policy leaf requires policy assembler")
          | collect_fresh (saved as PolicySequenceGraphConversion _) =
              (policy_graph_active saved;
               raise ERR "graph_recipe_steps"
                 "policy sequence requires policy assembler")
          | collect_fresh (DirectRealizedSequence
              {source,result,equality,first,second,first_slot,second_slot,
               ...}) =
              let
                fun direct converted slot =
                  (observe ();case cached converted (!direct_objects) of
                     SOME id => id
                   | NONE =>
                     let val a = graph_source converted
                         val b = graph_result converted
                         val id = save {id = fresh (),kind = LegacyStep,
                           source = a,current = a,result = b,children = NONE,
                           prefix = NONE,equality = NONE,closed = NONE,
                           conversion = SOME slot,continuation = NONE}
                         val _ = observe ()
                         val _ = direct_objects :=
                           (converted,id) :: !direct_objects
                     in id end)
                val a = direct first first_slot
                val b = direct second second_slot
              in save {id = fresh (),kind = SequenceRecipe,source = source,
                current = graph_result first,result = result,children = NONE,
                prefix = SOME a,equality = SOME equality,closed = NONE,
                conversion = NONE,continuation = SOME b} end
          | collect_fresh (SequenceGraphConversion
              {source,result,equality,first,second,...}) =
              let val a = collect first val b = collect second
              in save {id = fresh (),kind = SequenceRecipe,source = source,
                current = graph_result first,result = result,children = NONE,
                prefix = SOME a,equality = SOME equality,closed =
                  NONE,conversion = NONE,
                continuation = SOME b} end
          | collect_fresh (ApplicationGraphConversion
              {source,result,equality,left,right,...}) =
              let val a = collect left val b = collect right
              in save {id = fresh (),kind = ApplicationRecipe,source =
                source,current = result,
                result = result,children = SOME (a,b),prefix = NONE,
                equality = SOME equality,
                closed = NONE,conversion = NONE,continuation = NONE} end
        val _ = G.validate_scope graph scope
        val root = collect conversion
    in {root = root,steps = List.rev (!rows)} end

  fun graph_assemble graph block conversion =
    let val memo = ref ([] : (graph_conversion * P.edge) list)
        fun cached converted [] = NONE
          | cached converted ((old,edge)::rest) =
              if Portable.pointer_eq (converted,old) then SOME edge
              else cached converted rest
        fun trans a b = P.compose block
              (fn [a,b] => SmtReplayRuleObservation.TRANS a b
                | _ => raise Fail "recipe TRANS premises") [a,b]
        fun named_equality converted proof =
          let val equality = graph_equality converted
              val (partial,right) = case G.view graph equality of
                  G.Application pair => pair
                | _ => raise Fail "recipe equality application"
              val (head,left) = case G.view graph partial of
                  G.Application pair => pair
                | _ => raise Fail "recipe equality head"
              val expansion = P.compose block
                (fn [head,inner,outer] =>
                  let val inner = SmtReplayRuleObservation.TRANS inner
                        (SmtReplayRuleObservation.AP_THM head (P.name block
                          left))
                  in SmtReplayRuleObservation.TRANS outer
                    (SmtReplayRuleObservation.AP_THM inner (P.name block
                      right)) end
                  | _ => raise Fail "recipe equality expansion")
                [P.definition block head,P.definition block partial,
                 P.definition block equality]
          in P.compose block
            (fn [expansion,proof] =>
              SmtReplayRuleObservation.EQ_MP (SmtReplayRuleObservation.SYM
                expansion) proof
              | _ => raise Fail "recipe equality naming") [expansion,proof] end
        fun opened converted =
          P.compose block
            (fn [proof,constructor] => SmtReplayRuleObservation.EQ_MP
              constructor proof
              | _ => raise Fail "recipe named equality")
            [assemble converted,P.constructor block (graph_equality converted)]
        and assemble converted = case cached converted (!memo) of
              SOME edge => edge | NONE =>
                let val edge = assemble_fresh converted
                    val _ = memo := (converted,edge) :: !memo
                in edge end
        and assemble_fresh (converted as GraphConversion _) =
              legacy_assemble graph block converted
          | assemble_fresh (RealizedGraphConversion {legacy,...}) =
              legacy_assemble graph block legacy
          | assemble_fresh (saved as PolicyGraphConversion _) =
              (policy_graph_active saved;
               raise ERR "graph_assemble"
                 "policy leaf requires policy assembler")
          | assemble_fresh
              (saved as PolicySequenceGraphConversion _) =
              (policy_graph_active saved;
               raise ERR "graph_assemble"
                 "policy sequence requires policy assembler")
          | assemble_fresh (converted as DirectRealizedSequence
              {first,second,first_slot,second_slot,...}) =
              let
                fun direct leaf slot = trans
                  (P.checked block (SmtReplayRuleObservation.REFL (P.name block
                    (graph_source leaf))))
                  (P.conversion block slot)
              in named_equality converted (trans
                (direct first first_slot) (direct second second_slot)) end
          | assemble_fresh (converted as SequenceGraphConversion
            {first,second,...}) =
              named_equality converted (trans (opened first) (opened second))
          | assemble_fresh (converted as ApplicationGraphConversion
              {source,result,equality,left,right,...}) =
              let val combined = P.compose block
                    (fn [a,b] => SmtReplayRuleObservation.MK_COMB (a,b)
                      | _ => raise Fail "recipe application premises")
                    [opened left,opened right]
                  val backwards = P.compose block
                    (fn [proof] => SmtReplayRuleObservation.SYM proof
                      | _ => raise Fail "recipe parent symmetry")
                    [P.definition block result]
              in named_equality converted (trans (P.definition block source)
                (trans combined backwards)) end
    in assemble conversion end

  fun graph_assemble_named graph block converted =
    let
      val seen = ref ([] : graph_conversion list)
      fun inspect current =
        if List.exists (fn old => Portable.pointer_eq (old,current)) (!seen)
          then ()
        else
          (seen := current :: !seen;
           case current of GraphConversion _ => ()
           | ApplicationGraphConversion {left,right,...} =>
               (inspect left;inspect right)
           | SequenceGraphConversion {first,second,...} =>
               (inspect first;inspect second)
           | _ => raise ERR "graph_assemble_named"
               "owned/realized conversion requires its policy assembler")
      (* Reject nested policy/realized leaves before even an ordinary sibling
         can execute a native rule. Shared suffixes are inspected once. *)
      val _ = inspect converted
    in case converted of GraphConversion _ =>
        assemble_finite_named graph block converted
      | _ => (ignore (P.checked block boolTheory.TRUTH);
          graph_assemble graph block converted)
    end

  (* A bounded constructor prefix is exposed on large nodes. All repeated
     holes denote the same semantic ID; small nodes may expose their complete
     admitted syntax. Ordinary conversions therefore see neither expanded
     operands nor independently allocated large theorem hypotheses. *)
  fun graph_schema_conversion graph scope
      {conversion,template_limit,prefix_depth} node =
    let
      val _ = G.validate_scope graph scope
      val holes = ref (Redblackmap.mkDict Int.compare)
      val templates = ref (Redblackmap.mkDict Int.compare)
      val observed = ref 0
      fun operand node =
        case Redblackmap.peek (!holes,G.node_id node) of SOME (_,term) => term
        | NONE =>
          let val term = Term.genvar (G.type_of graph node) in
            holes := Redblackmap.insert
              (!holes,G.node_id node,(node,term));term end
      fun template depth node =
        let
          val _ = if !observed < template_limit then () else
            raise ERR "graph_schema_conversion"
              "operator prefix exceeds bounded schema contract"
          val _ = observed := !observed + 1
        in case Redblackmap.peek (!templates,G.node_id node) of
            SOME term => term
          | NONE =>
              let
                (* A shared node can occur at different curried depths.
                   Fix its first bounded view so both occurrences have the
                   same template, and preflight the unfolded result below. *)
                val term = case G.view graph node of
                    G.Constant _ => G.representative graph node
                  | G.Application (operator,argument) =>
                      if depth = 0 then operand node else
                        Term.mk_comb (template (depth-1) operator,
                                      template (depth-1) argument)
                  | _ => operand node
                val _ = templates := Redblackmap.insert
                  (!templates,G.node_id node,term)
              in term end
        end
      val limit = Int.max (0,prefix_depth)
      val term = template limit node
      val _ = case SmtReplayImport.bounded_raw_size template_limit term of
          SOME _ => () | NONE => raise ERR "graph_schema_conversion"
            "operator prefix exceeds bounded schema contract"
      val theorem = conversion term
      val pairs = List.map #2 (Redblackmap.listItems (!holes))
      val schema = checked_graph_schema graph scope
        {theorem = theorem,holes = List.map #2 pairs,
         operands = List.map #1 pairs,template_limit = template_limit}
    in if graph_schema_source schema = graph_schema_result schema then NONE
       else SOME schema end
    handle Conv.UNCHANGED => NONE


  (* The owned entry consumes only the SAME private recipe descriptor. The
     default graph_assemble and schema route above remain unchanged. *)
  fun graph_assemble_for expected graph block conversion =
    let
      val owner = P.primitive_owner_for expected block
      val _ = if Portable.pointer_eq (graph,#graph owner) then () else
        (SmtReplayInvocationWork.close expected;
         raise ERR "graph_assemble_for" "different original graph")
      val _ = validate_conversion_with_policy expected conversion
      val scope = P.scope block
      val {root,steps} = graph_recipe_steps graph scope
        {observe = fn () => SmtReplayInvocationWork.spend expected 1}
          conversion
      val _ = SmtReplayInvocationWork.spend expected 1
      val memo = ref ([] : (int * P.edge) list)
      fun primitive recipe edges = P.execute_primitive expected
        (P.prepare_primitive expected block recipe edges)
      fun reflexive node = primitive (P.ReflexiveName node) []
      fun trans a b = primitive P.Transitivity [a,b]
      fun symmetry edge = primitive P.Symmetry [edge]
      fun equality_mp equation proof = primitive P.EqualityMP [equation,proof]
      fun lookup id [] = NONE
        | lookup id ((old,edge)::rest) =
            (SmtReplayInvocationWork.spend expected 1;
             if old = id then SOME edge else lookup id rest)
      fun step id [] = raise ERR "graph_assemble_for" "missing recipe ID"
        | step id ((row:recipe_step)::rest) =
            (SmtReplayInvocationWork.spend expected 1;
             if #id row = id then row else step id rest)
      fun constructor node = case G.view graph node of
          G.Constant _ => P.definition block node
        | G.Application (operator,operand) =>
            trans (P.definition block node)
              (primitive (P.ApplyNamedArgument operand) [constructor operator])
        | _ => reflexive node
      fun named equality proof =
        let val (partial,right) = case G.view graph equality of
                G.Application pair => pair
              | _ => raise ERR "graph_assemble_for" "equality application"
            val (head,left) = case G.view graph partial of
                G.Application pair => pair
              | _ => raise ERR "graph_assemble_for" "equality head"
            val inner = trans (P.definition block partial)
              (primitive (P.ApplyNamedArgument left) [P.definition block head])
            val outer = trans (P.definition block equality)
              (primitive (P.ApplyNamedArgument right) [inner])
        in equality_mp (symmetry outer) proof end
      fun opened id =
        let val edge = assemble id val row = step id steps
        in case #equality row of NONE => edge
          | SOME equality => equality_mp (constructor equality) edge end
      and assemble id = case lookup id (!memo) of SOME edge => edge
        | NONE =>
          let val row = step id steps
              val source = #source row val current = #current row
              val initial = case #prefix row of SOME prefix => opened prefix
                | NONE => (case #children row of NONE => reflexive source
                  | SOME (left,right) =>
                    if #kind row = LegacyStep andalso current = source then
                      reflexive source else
                    let val a = if #kind row = ApplicationRecipe then
                                opened left else assemble left
                        val b = if #kind row = ApplicationRecipe then
                                opened right else assemble right
                        val combined = primitive P.Congruence [a,b]
                    in trans (P.definition block source)
                      (trans combined (symmetry (P.definition block current)))
                    end)
              val oriented = case (#closed row,#conversion row) of
                  (NONE,NONE) => initial
                | (SOME fact,NONE) =>
                    trans initial (equality_mp
                      (constructor (P.closed_node fact)) (P.closed block fact))
                | (NONE,SOME leaf) =>
                    trans initial (P.conversion block leaf)
                | _ => raise ERR "graph_assemble_for" "two witness slots"
              val equation = case #continuation row of NONE => oriented
                | SOME next => trans oriented
                    (if #kind row = SequenceRecipe then opened next
                     else assemble next)
              val result = case #equality row of NONE => equation
                | SOME equality => named equality equation
              val _ = SmtReplayInvocationWork.spend expected 3
              val _ = memo := (id,result) :: !memo
          in result end
    in assemble root end

  (* Separate authentic legacy-schema grammar. Existing application-only
     descriptors and owned assembler keep their explicit schema refusal. *)
  fun graph_assemble_with_schemas_for expected graph block conversion =
    ((let
      val owner = P.primitive_owner_for expected block
      val _ = if Portable.pointer_eq (graph,#graph owner) then () else
        raise ERR "graph_assemble_with_schemas_for" "different original graph"
      val _ = validate_conversion_with_policy expected conversion
      val scope = #scope owner
      val (source,equality,steps) = case conversion of
          GraphConversion {source,equality,steps,...} =>
            (source,equality,steps)
        | _ => raise ERR "graph_assemble_with_schemas_for"
            "schema producer requires authentic legacy graph recipe"
      val cap = IntInf.fromInt (P.template_limit block)
      val ceiling = IntInf.fromInt
        (SmtReplayInvocationWork.work_limit expected)
      fun spend n = SmtReplayInvocationWork.spend expected n
      fun plus a b = IntInf.min (ceiling+1,a+b)
      fun times a b = IntInf.min (ceiling+1,a*b)
      fun admit amount = if amount > ceiling then
          raise ERR "graph_assemble_with_schemas_for" "schema work ceiling"
        else spend (IntInf.toInt amount)
      fun type_weight ty =
        let val _ = spend 1
        in if Type.is_vartype ty then
            let val name = Type.dest_vartype ty
                val _ = spend (String.size name)
            in plus 1 (IntInf.fromInt (String.size name)) end
           else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                val _ = spend (String.size Thy + String.size Tyop)
            in List.foldl (fn (arg,total) =>
                 (spend 1;plus total (type_weight arg))) 1 Args end
        end
      fun profile term =
        let val _ = spend 1 val own = type_weight (Term.type_of term)
        in if Term.is_comb term then
            let val _ = spend 1 val (a,b) = Term.dest_comb term
                val (ar,ai,aa) = profile a val (br,bi,ba) = profile b
            in (plus 1 (plus ar br),plus 1 (plus ai bi),
                plus own (plus aa ba)) end
           else if Term.is_abs term then
            let val _ = spend 1 val (binder,body) = Term.dest_abs term
                val domain = type_weight (Term.type_of binder)
                val (raw,inc,ann) = profile body
            in (plus 1 raw,plus 2 inc,plus own (plus domain ann)) end
           else (1,1,own)
        end
      fun amount (raw,inc,ann) = plus raw (plus inc ann)
      fun bound (raw,inc,_) = if raw <= cap andalso inc <= cap then ()
        else raise ERR "graph_assemble_with_schemas_for"
          "instantiated compact schema exceeds original template cap"
      fun template (Operand node) =
            (spend 1;visible graph scope node;profile (P.name block node))
        | template (Literal (node,term)) =
            (spend 1;visible graph scope node;profile term)
        | template (Constructor (node,left,right)) =
            let val _ = spend 1 val _ = visible graph scope node
                val own = type_weight (G.type_of graph node)
                val (ar,ai,aa) = template left
                val (br,bi,ba) = template right
            in (plus 1 (plus ar br),plus 1 (plus ai bi),
                plus own (plus aa ba)) end
      val plans = ref ([] :
        (graph_schema * P.closed_named_inst_plan) list)
      fun find schema [] = NONE
        | find schema ((held,data)::rest) =
            (spend 1;if Portable.pointer_eq (schema,held) then SOME data
             else find schema rest)
      fun prepare (schema as GraphSchema
          {left,right,holes,operands,theorem,...}) =
        let val _ = spend 1
            val _ = visible graph scope (template_node left)
            val _ = visible graph scope (template_node right)
        in case find schema (!plans) of SOME _ => () | NONE =>
          let
            val input = profile (Thm.concl theorem)
            val hypotheses = Thm.hyp theorem
            val _ = List.app (fn term =>
              let val value = profile term
              in bound value;admit (amount value) end) hypotheses
            val _ = if null hypotheses andalso clean_schema theorem then ()
              else raise ERR "graph_assemble_with_schemas_for"
                "schema is not a clean closed original law"
            val substitution = ListPair.mapEq
              (fn (hole,node) =>
                (spend 1;visible graph scope node;
                 {redex = hole,residue = P.name block node})) (holes,operands)
            val _ = List.app (fn {redex,residue} =>
              (admit (amount (profile redex));
               admit (amount (profile residue)))) substitution
            val (ar,ai,aa) = template left
            val (br,bi,ba) = template right
            val ty = type_weight (G.type_of graph (template_node left))
            (* Equality constant + two applications; every repeated type
               annotation occurs in this authentic virtual output spine. *)
            val output = (plus 3 (plus ar br),plus 3 (plus ai bi),
              plus (plus 6 (times 3 ty)) (plus aa ba))
            val _ = bound input val _ = bound output
            val _ = admit (plus (amount input) (amount output))
            val plan = P.prepare_closed_named_inst expected block
              {substitution=substitution,theorem=theorem}
            val _ = spend 3
            val _ = plans := (schema,plan) :: !plans
          in () end
        end
      (* Every real INST portfolio is admitted before ANY assembly rule. *)
      val _ = Redblackmap.app (fn (_,GraphStep {schema,...}) =>
        (spend 1;Option.app prepare schema)) steps
      fun primitive recipe edges = P.execute_primitive expected
        (P.prepare_primitive expected block recipe edges)
      fun reflexive node = primitive (P.ReflexiveName node) []
      fun trans a b = primitive P.Transitivity [a,b]
      fun symmetry edge = primitive P.Symmetry [edge]
      fun equality_mp equation proof = primitive P.EqualityMP [equation,proof]
      fun expansion (Operand node) = reflexive node
        | expansion (Literal (node,_)) = P.definition block node
        | expansion (Constructor (node,left,right)) =
            trans (P.definition block node)
              (primitive P.Congruence [expansion left,expansion right])
      val schema_proofs = ref ([] : (graph_schema * P.edge) list)
      fun schema_proof (schema as GraphSchema
          {left,right,theorem,admitted_size,...}) =
        let val _ = visible graph scope (template_node left)
            val _ = visible graph scope (template_node right)
        in case find schema (!schema_proofs) of SOME proof => proof | NONE =>
          let val plan = case find schema (!plans) of
                  SOME actual => actual | NONE =>
                    raise ERR "graph_assemble_with_schemas_for"
                      "unprepared private schema"
              val instantiated = P.execute_closed_named_inst expected plan
              val _ = observe_schema graph 1
                (IntInf.fromInt admitted_size) 1 true
              val proof = trans (expansion left)
                (trans instantiated (symmetry (expansion right)))
              val _ = spend 3
              val _ = schema_proofs := (schema,proof) :: !schema_proofs
          in proof end
        end
      val memo = ref ([] : (G.node * P.edge) list)
      fun lookup node [] = NONE
        | lookup node ((saved,edge)::rest) =
            (spend 1;if node = saved then SOME edge else lookup node rest)
      fun constructor node = case G.view graph node of
          G.Constant _ => P.definition block node
        | G.Application (operator,operand) =>
            trans (P.definition block node)
              (primitive (P.ApplyNamedArgument operand) [constructor operator])
        | _ => reflexive node
      fun assemble node =
        (visible graph scope node;case lookup node (!memo) of
          SOME edge => edge | NONE =>
          let val _ = spend 1
              val GraphStep {current,children,schema,closed,conversion,
                continuation,...} = Redblackmap.find (steps,G.node_id node)
              val initial = case children of NONE => reflexive node
                | SOME (a,b) => if current = node then reflexive node else
                    trans (P.definition block node)
                      (trans (primitive P.Congruence [assemble a,assemble b])
                        (symmetry (P.definition block current)))
              val oriented = case (schema,closed,conversion) of
                  (NONE,NONE,NONE) => initial
                | (SOME actual,NONE,NONE) => trans initial (schema_proof
                  actual)
                | (NONE,SOME fact,NONE) => trans initial
                    (equality_mp (constructor (P.closed_node fact))
                      (P.closed block fact))
                | (NONE,NONE,SOME leaf) =>
                    trans initial (P.conversion block leaf)
                | _ => raise ERR "graph_assemble_with_schemas_for"
                    "multiple semantic witness slots"
              val result = case continuation of NONE => oriented
                | SOME next => trans oriented (assemble next)
              val _ = spend 3 val _ = memo := (node,result) :: !memo
          in result end)
      val proof = assemble source
      val (partial,right) = case G.view graph equality of
          G.Application pair => pair | _ =>
            raise ERR "graph_assemble_with_schemas_for" "equality application"
      val (head,left) = case G.view graph partial of
          G.Application pair => pair | _ =>
            raise ERR "graph_assemble_with_schemas_for" "equality head"
      val inner = trans (P.definition block partial)
        (primitive (P.ApplyNamedArgument left) [P.definition block head])
      val outer = trans (P.definition block equality)
        (primitive (P.ApplyNamedArgument right) [inner])
    in equality_mp (symmetry outer) proof end)
      handle primary =>
        (SmtReplayInvocationWork.close expected;raise primary))

  (* Called inside the caller's SAME Work action. All proof effects use
     fixed policy recipes and the actual contract retained by this block. *)
  structure OrdinaryPolicyAssembly=SmtReplayCanonAssemblyFn
    (struct
       type block=P.block
       type edge=P.edge
       type inst_plan=P.policy_closed_named_inst_plan
       datatype graph_template = datatype graph_template
       datatype graph_schema = datatype graph_schema
       datatype graph_step = datatype graph_step
       datatype graph_conversion = datatype graph_conversion
       val validate_conversion_for=validate_conversion_with_policy
       val policy_graph_guard=policy_graph_guard
       val graph_equality=graph_equality
       val visible=visible
       val observe_schema=observe_schema
       val error=ERR
       val owner_for=P.policy_native_block_owner_for
       fun name _ block node=P.name block node
       fun definition _ block node=P.definition block node
       val constructor=P.constructor_with_policy
       fun closed _ block fact=P.closed block fact
       fun conversion _ block fact=P.conversion block fact
       fun derive expected block recipe edges=
         P.execute_primitive_with_policy expected
           (P.prepare_primitive_with_policy expected block recipe edges)
       val prepare_inst=P.prepare_closed_named_inst_with_policy
       val execute_inst=P.execute_closed_named_inst_with_policy
     end)
  val graph_assemble_with_policy=
    OrdinaryPolicyAssembly.graph_assemble_with_policy

  structure SparsePolicyAssembly=SmtReplayCanonAssemblyFn
    (struct
       type block=P.policy_sparse_block
       type edge=P.policy_sparse_edge
       type inst_plan=P.policy_sparse_named_inst_plan
       datatype graph_template = datatype graph_template
       datatype graph_schema = datatype graph_schema
       datatype graph_step = datatype graph_step
       datatype graph_conversion = datatype graph_conversion
       val validate_conversion_for=validate_conversion_with_policy
       val policy_graph_guard=policy_graph_guard
       val graph_equality=graph_equality
       val visible=visible
       val observe_schema=observe_schema
       val error=ERR
       val owner_for=P.policy_sparse_owner_for
       val name=P.policy_sparse_name_for
       val definition=P.policy_sparse_definition_for
       val constructor=P.policy_sparse_constructor_for
       val closed=P.policy_sparse_closed_for
       val conversion=P.policy_sparse_conversion_for
       val derive=P.policy_sparse_primitive_for
       val prepare_inst=P.prepare_policy_sparse_named_inst
       val execute_inst=P.execute_policy_sparse_named_inst
     end)
  val graph_assemble_sparse_with_policy=
    SparsePolicyAssembly.graph_assemble_with_policy

  (* These constructors run inside the caller's existing Work action.
     No expanded endpoint is traversed or admitted by a leaf wrapper. *)
  fun policy_graph_leaf expected {frame,conversion,observe,realization} =
    ((let
        val data=SmtReplayOwnedScopeReceipt.description_with_policy_for
          expected frame
        val _=P.validate_conversion_for expected conversion
        val maximum= #template_limit(W.semantic_policy expected)
        val graph= #graph data and scope= #scope data
        val _=P.validate_conversion_with_policy graph scope maximum conversion
        val source=P.conversion_source conversion
        val target=P.conversion_target conversion
        val _=observe ()
        val equality=case realization of NONE=>
              equality_node graph scope observe source target
          | SOME receipt=>
              #equality(P.policy_source_realization_data_for expected receipt)
        val step=GraphStep {source=source,current=source,result=target,
          children=NONE,schema=NONE,closed=NONE,
          conversion=SOME conversion,continuation=NONE}
        val legacy=GraphConversion {source=source,result=target,
          equality=equality,steps=Redblackmap.insert
            (Redblackmap.mkDict Int.compare,G.node_id source,step),
          guard_slots=ref NONE}
        val saved=PolicyGraphConversion {work=expected,frame=frame,
          legacy=legacy,slot=conversion,realization=realization,
          canonical_cut=NONE}
        val _=policy_graph_guard expected saved
      in saved end)
     handle primary=>(W.close expected;raise primary))
  fun graph_leaf_with_policy expected {frame,conversion,observe} =
    policy_graph_leaf expected {frame=frame,conversion=conversion,
      observe=observe,realization=NONE}
  fun graph_realized_leaf_with_policy expected {realization,observe} =
    ((let
        val data=P.policy_source_realization_data_for expected realization
        val converted=P.conversion_from_policy_source_realization_for
          expected realization
      in policy_graph_leaf expected {frame= #frame data,
        conversion=converted,observe=observe,realization=SOME realization} end)
     handle primary=>(W.close expected;raise primary))

  fun graph_realized_sequence_with_policy expected {first,second,observe} =
    ((let
        val _=policy_graph_guard expected first
        val _=policy_graph_guard expected second
        val _=if policy_graph_realized first andalso
            policy_graph_realized second then () else
          raise ERR "policy_graph" "sequence requires realized wrappers"
        val a=policy_graph_ports first and b=policy_graph_ports second
        val data=SmtReplayOwnedScopeReceipt.description_with_policy_for
          expected (#frame a)
        val other=SmtReplayOwnedScopeReceipt.description_with_policy_for
          expected (#frame b)
        val _=if Portable.pointer_eq(#graph data,#graph other) andalso
            Portable.pointer_eq(#sources data,#sources other) andalso
            #root data= #root other andalso #scope data= #scope other andalso
            #result a= #source b then () else
          raise ERR "policy_graph" "different actual sequence endpoints"
        val equality=equality_node (#graph data) (#scope data) observe
          (#source a) (#result b)
        val saved=PolicySequenceGraphConversion {work=expected,
          frame= #frame a,source= #source a,result= #result b,
          equality=equality,first=first,second=second}
        val _=policy_graph_guard expected saved
      in saved end)
     handle primary=>(W.close expected;raise primary))

  (* The opaque P token, never a caller cut flag or fake realization,
     supplies exact canonical proof lineage and its original owned frame. *)
  fun graph_closed_fact_cut_with_policy expected {cut,observe}=
    ((let
        val data=P.closed_fact_cut_data_with_policy_for expected cut
        val frame= #frame data val source= #source data
        val target= #target data val equality= #equality data
        val slot= #conversion data
        val _=observe()
        val current=P.closed_fact_cut_data_with_policy_for expected cut
        val _=if Portable.pointer_eq(frame,#frame current)andalso
            Portable.pointer_eq(slot,#conversion current)andalso
            source= #source current andalso target= #target current andalso
            equality= #equality current then ()else
          raise ERR "policy_graph_cut" "actual cut changed during callback"
        val step=GraphStep{source=source,current=source,result=target,
          children=NONE,schema=NONE,closed=NONE,conversion=SOME slot,
          continuation=NONE}
        val legacy=GraphConversion{source=source,result=target,
          equality=equality,steps=Redblackmap.insert
            (Redblackmap.mkDict Int.compare,G.node_id source,step),
          guard_slots=ref NONE}
        val result=PolicyGraphConversion{work=expected,frame=frame,
          legacy=legacy,slot=slot,realization=NONE,canonical_cut=SOME cut}
        val _=policy_graph_guard expected result
      in result end)
     handle primary=>(W.close expected;raise primary))
  (* Both operands must retain genuine canonical-cut/late-realization
     authority; the original private guard checks actual middle/frame. *)
  val graph_cut_sequence_with_policy=graph_realized_sequence_with_policy

  (* The policy assembler's definition operands are distinct from its
     semantic operands. A genuine cut may hide only the latter. This DATA
     inventory mirrors the actual fixed assembler above; it opens no Term
     and grants no native admission. Called inside the existing action. *)
  fun graph_roots_with_policy expected graph scope converted =
    ((let
        val sources=W.original_sources expected
        val actual_graph=SmtReplaySource.owning_graph sources
        val root=SmtReplaySource.owning_scope sources
        val _=if Portable.pointer_eq(graph,actual_graph)then ()else
          raise ERR "policy_definition_roots" "different original graph"
        val limits=W.semantic_policy expected
        val epoch=Type.type_epoch() val symbols=Term.term_epoch()
        fun active()=
          (W.validate_policy expected graph root sources limits;
           G.validate_scope graph scope;
           if G.scope_visible graph scope root then ()else
             raise ERR "policy_definition_roots" "outside original root";
           if Type.type_epoch()=epoch andalso Term.term_epoch()=symbols
             then ()else raise ERR "policy_definition_roots"
               "retired type or term epoch")
        fun tick()=(active();W.spend_policy expected 1)
        fun usable node=
          (tick();visible graph scope node)
        val _=active()
        val _=validate_conversion_with_policy expected converted
        val roots=ref([]:G.node list)
        fun member node []=(tick();false)
          | member node(old::rest)=
              (tick();node=old orelse member node rest)
        fun demand node=
          (usable node;
           if member node(!roots)then ()else
             (tick();roots:=node:: !roots))
        val spine_done=ref([]:(G.scope * G.node)list)
        fun spine_seen [] _=(tick();false)
          | spine_seen((frame,old)::rest)node=
              (tick();(frame=scope andalso old=node)orelse
                spine_seen rest node)
        (* P.constructor_with_policy follows only the operator spine.
           Its named arguments remain operands/cuts, not required roots. *)
        fun constructor node=
          (usable node;
           if spine_seen(!spine_done)node then ()else
             let val _=case G.view graph node of
                     G.Constant _=>demand node
                   | G.Application(operator,_)=>
                       (demand node;constructor operator)
                   | _=>()
             in tick();spine_done:=(scope,node):: !spine_done end)
        val template_done=ref([]:graph_template list)
        fun physical object []=(tick();false)
          | physical object(old::rest)=
              (tick();Portable.pointer_eq(object,old)orelse
                physical object rest)
        fun expansion template=
          (tick();if physical template(!template_done)then ()else
             let val _=case template of
                     Operand node=>usable node
                   | Literal(node,_)=>demand node
                   | Constructor(node,left,right)=>
                       (demand node;expansion left;expansion right)
             in tick();template_done:=template:: !template_done end)
        val schema_done=ref([]:graph_schema list)
        fun schema (held as GraphSchema{left,right,...})=
          (tick();if physical held(!schema_done)then ()else
             (expansion left;expansion right;tick();
              schema_done:=held:: !schema_done))
        val recipe_done=ref([]:graph_conversion list)
        fun visit object=
          (tick();if physical object(!recipe_done)then ()else
             let
               (* named/opened call the real constructor for this equality.
                  Direct sequences do not assemble their child wrappers. *)
               val _=constructor(graph_equality object)
               val _=case object of
                   GraphConversion{steps,...}=>
                     (inventory_step_map (W.spend_guard_policy expected)
                        steps;
                      Redblackmap.app(fn(_,GraphStep
                        {source,current,children,schema=law,closed,...})=>
                        (tick();
                         (case children of SOME _=>
                            if source=current then ()else
                              (demand source;demand current)
                          | NONE=>());
                         Option.app schema law;
                         Option.app(fn fact=>
                           constructor(P.closed_node fact))closed))steps)
                 | RealizedGraphConversion{legacy,...}=>visit legacy
                 | saved as PolicyGraphConversion _=>
                     policy_graph_guard expected saved
                 | saved as PolicySequenceGraphConversion
                     {first,second,...}=>
                     (policy_graph_guard expected saved;
                      visit first;visit second)
                 | SequenceGraphConversion{first,second,...}=>
                     (visit first;visit second)
                 | DirectRealizedSequence _=>()
                 | ApplicationGraphConversion
                     {source,result,left,right,...}=>
                     (demand source;demand result;visit left;visit right)
             in tick();recipe_done:=object:: !recipe_done end)
        val ordinary=graph_roots_for expected converted
        val _=List.app demand ordinary
        val _=visit converted
        fun reverse [] result=(tick();result)
          | reverse(node::rest)result=
              (tick();reverse rest(node::result))
        val result=reverse(!roots)[]
        val _=validate_conversion_with_policy expected converted
        val _=active()
      in result end)
     handle primary=>(W.close expected;raise primary))

end
