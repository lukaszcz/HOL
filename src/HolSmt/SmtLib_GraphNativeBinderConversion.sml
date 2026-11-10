structure SmtLib_GraphNativeBinderConversion
  :> SmtLib_GraphNativeBinderConversion =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayCanonGraph SmtReplayBinder
    SmtReplayImport
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure C = SmtReplayCanonGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNativeBinderConversion"
  datatype local_result = Unhandled | Gap
    | Checked of {target : G.node,theorem : Thm.thm,continuation : bool}
  type options =
    {graph : G.graph,scope : G.scope,admission : SmtReplayBinder.admission,
     template_limit : int,propose : G.scope -> G.node -> C.graph_schema option,
     local_witness : G.scope -> G.node ->
       local_result}
  datatype scalar_conversion = Schema of C.graph_conversion
    | Native of G.node
  datatype step = Step of
    {source : G.node,current : G.node,result : G.node,equality : G.node,
     children : (G.node * G.node) option,
     scalar : scalar_conversion option,witness : G.node option}
  datatype conversion = Conversion of
    {graph : G.graph,scope : G.scope,source : G.node,result : G.node,
     equality : G.node,steps : step list,roots : G.node list,
     witnesses : (G.node * Thm.thm) list,gaps : G.node list}
  fun source (Conversion {source,...}) = source
  fun result (Conversion {result,...}) = result
  fun equality (Conversion {equality,...}) = equality
  fun roots (Conversion {roots,...}) = roots
  fun witnesses (Conversion {witnesses,...}) = witnesses
  fun gaps (Conversion {gaps,...}) = gaps
  fun equation graph scope left right =
    let val operator = G.constant graph scope (Term.inst
          (Type.match_type (Term.type_of boolSyntax.equality)
            (boolSyntax.list_mk_fun
              ([G.type_of graph left,G.type_of graph left],Type.bool)))
          boolSyntax.equality)
    in G.application graph scope
      (G.application graph scope (operator,left),right) end
  fun assemble (Conversion {graph,scope,source,steps,...}) block =
    let
      val _ = G.validate_scope graph scope
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun required node = Redblackmap.find (!memo,G.node_id node)
      fun exposed node edge = P.compose block
        (fn [proof,constructor] => Thm.EQ_MP constructor proof
          | _ => raise Fail "binder conversion expose")
        [edge,P.constructor block node]
      fun named node edge = P.compose block
        (fn [proof,constructor] => Thm.EQ_MP (Thm.SYM constructor) proof
          | _ => raise Fail "binder conversion name")
        [edge,P.constructor block node]
      fun source_edge node =
        let fun find [] _ = raise ERR "assemble" "missing exact witness source"
              | find (owned :: rest) index = if owned = node then index else
                  find rest (index+1)
        in P.source block (find (P.sources block) 0) end
      fun step (Step {source,current,result,equality,children,scalar,witness}) =
        let
          val initial = case witness of SOME node =>
              exposed node (source_edge node)
            | NONE => (case children of NONE =>
                P.checked block (Thm.REFL (P.name block source))
              | SOME (left,right) =>
                  let
                    val (left_eq,left_edge) = required left
                    val (right_eq,right_edge) = required right
                    val combined = P.compose block
                      (fn [left,right] => Thm.MK_COMB (left,right)
                        | _ => raise Fail "binder child congruence")
                      [exposed left_eq left_edge,exposed right_eq right_edge]
                  in P.compose block
                    (fn [old,children,new] =>
                      Thm.TRANS old (Thm.TRANS children (Thm.SYM new))
                      | _ => raise Fail "binder parent congruence")
                    [P.definition block source,combined,
                     P.definition block current] end)
          val edge = case scalar of NONE => initial
            | SOME (Native law) => P.compose block
                (fn [initial,next] => Thm.TRANS initial next
                  | _ => raise Fail "native local transport")
                [initial,exposed law (source_edge law)]
            | SOME (Schema conversion) => P.compose block
                (fn [initial,next] => Thm.TRANS initial next
                  | _ => raise Fail "binder scalar transport")
                [initial,exposed (C.graph_equality conversion)
                   (C.graph_assemble graph block conversion)]
          val edge = named equality edge
        in memo := Redblackmap.insert (!memo,G.node_id source,
             (equality,edge)) end
      val _ = List.app step steps
    in #2 (required source) end
  datatype work = Visit of G.node | Finish of G.node * G.node * G.node
  type state =
    {memo : (int,G.node) Redblackmap.dict ref,steps : step list ref,
     witness_list : (G.node * Thm.thm) list ref,gap_list : G.node list ref,
     all_roots : G.node list ref}
  fun new_state () : state =
    {memo = ref (Redblackmap.mkDict Int.compare),steps = ref [],
     witness_list = ref [],gap_list = ref [],all_roots = ref []}
  fun discover_state
      ({graph,scope,admission,template_limit,propose,local_witness} : options)
      ({memo,steps,witness_list,gap_list,all_roots} : state) root =
    let
      val _ = G.validate_scope graph scope
      val {metric,input_limit,output_limit,check_type,...} = admission
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          template_limit > 0 then () else
        raise ERR "discover" "nonpositive binder conversion contract"
      fun size limit term = case metric of G.RawNodes =>
          SmtReplayImport.bounded_raw_size limit term
        | G.BinderInclusiveNodes =>
            SmtReplayImport.bounded_binder_size limit term
      fun ensure_count label limit count = if count <= limit then () else
        raise ERR "discover" label
      fun node_size label limit node =
        case G.unfolded_nodes graph metric limit node of
          SOME count => (ensure_count label limit count;count)
        | NONE => raise ERR "discover" label
      fun type_terms [] = ()
        | type_terms (term :: pending) =
            (check_type (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term in
                 type_terms (operator :: operand :: pending) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term in
                 type_terms (variable :: body :: pending) end
             else type_terms pending)
      fun bounded_binder node =
        let
          val term = G.representative graph node
        in case size input_limit term of NONE => NONE | SOME old_count =>
          if not (Term.is_abs term) then NONE else
          let
            (* G.admit_binder checks an actual source/admitted ALPHA law.
               Admit its complete equality before FV/type work or frames. *)
            val _ = if output_limit >= 3 andalso
                old_count <= (output_limit-3) div 2 then () else
              raise ERR "binder" "whole source admission law exceeds output"
            val slot = case metric of G.RawNodes => 1
              | G.BinderInclusiveNodes => 2
            val minimum_law_slots = 3+slot+1
            val alpha_budget = (output_limit-3) div 2
            val _ = if alpha_budget >= minimum_law_slots andalso
                old_count <= alpha_budget-minimum_law_slots then () else
              raise ERR "binder"
                "minimum whole proposition ALPHA law exceeds output"
            val _ = type_terms [term]
            (* Existing known ancestor IDs are authoritative. Unknown root
               source free variables are admitted only as exact rigid IDs
               after whole local size/type admission, never SolverFlexible. *)
            val free = Term.free_vars term
            val known = G.free_variable_nodes graph node
            fun owned variable = case known of SOME variables =>
                (case List.find (fn owned => Term.aconv variable
                    (G.representative graph owned)) variables of
                   SOME owned => owned
                 | NONE => raise ERR "binder" "incomplete owned free IDs")
              | NONE => if scope = G.root_scope graph andalso
                    G.origin graph node = G.ImportedSource then
                  G.variable graph scope G.RigidSource variable
                else raise ERR "binder" "unknown scoped source free IDs"
            val bindings = List.map (fn variable => (variable,owned variable))
              free
            val _ = List.app (fn (_,owned) =>
              case G.view graph owned of G.Variable (G.RigidSource,_) => ()
                | G.Variable (G.Bound,_) => ()
                | _ => raise ERR "binder" "unowned source variable kind")
              bindings
            val _ = case known of NONE => () | SOME variables =>
              if Listsort.sort Int.compare (List.map G.node_id variables) =
                  Listsort.sort Int.compare
                    (List.map (G.node_id o #2) bindings) then () else
                raise ERR "binder" "inexact whole source free-ID coverage"
            val temporary = G.new_scope graph scope bindings
            fun close () = G.close_scope graph temporary
            fun work () =
              let
                val admitted = G.admit_binder graph temporary input_limit term
                val (binder,body,frame) = case G.view graph (#node admitted) of
                    G.AdmittedBinder {binder,body,frame} => (binder,body,frame)
                  | _ => raise ERR "binder" "admitted abstraction missing"
                val body_scope = G.node_scope graph body
                val local_scope = if G.scope_visible graph body_scope frame
                  then body_scope else frame
                val converted = discover_state
                  {graph = graph,scope = local_scope,admission = admission,
                   template_limit = template_limit,propose = propose,
                   local_witness = local_witness}
                  (new_state ()) body
                val output = result converted
                val output_count = node_size "unknown or oversized body"
                  output_limit output
                val _ = if output_limit >= 3+slot andalso
                    output_count <= output_limit-(3+slot) andalso
                    old_count <= output_limit-(3+slot)-output_count then ()
                  else raise ERR "binder" "whole closure law exceeds output"
                val target_count = slot+output_count
                val _ = if output_limit >= 3 andalso
                    target_count <= (output_limit-3) div 2 then () else
                  raise ERR "binder"
                    "whole target admission/rehome law exceeds output"
                val law_count = 3+old_count+target_count
                val _ = if output_limit >= 3 andalso
                    law_count <= (output_limit-3) div 2 then () else
                  raise ERR "binder"
                    "whole proposition ALPHA law exceeds output"
                val _ = List.app (check_type o G.type_of graph)
                  (G.reachable graph [output])
                val target = G.abstraction graph temporary output_limit
                  (binder,output)
                val block = P.freeze graph {scope = local_scope,
                  roots = roots converted,
                  sources = List.map #1 (witnesses converted),
                  template_limit = template_limit}
                fun witness (_,node) = Option.map #2 (List.find
                  (fn (owned,_) => owned = node) (witnesses converted))
                val proof = P.realize_with_sources block (equality converted)
                  (assemble converted block) witness
                val lifted = Thm.ABS (G.representative graph binder) proof
                val rehomed = G.rehome graph scope target
                val theorem = Thm.TRANS (#bridge admitted)
                  (Thm.TRANS lifted (#bridge rehomed))
                val actual_equation = equation graph scope node (#node rehomed)
                val actual = G.representative graph actual_equation
                val _ = case size output_limit actual of SOME _ => ()
                  | NONE => raise ERR "binder"
                      "actual closure law exceeds output"
                val theorem = Thm.EQ_MP
                  (Thm.ALPHA (Thm.concl theorem) actual) theorem
              in SOME (#node rehomed,actual_equation,theorem,gaps converted) end
          in work () before close ()
             handle error => (close ();raise error) end end
      fun required node = Redblackmap.find (!memo,G.node_id node)
      fun save node current children witness scalar output =
        let val equality = equation graph scope node output
            val record = Step {source = node,current = current,result = output,
              equality = equality,children = children,witness = witness,
              scalar = scalar}
            val _ = steps := record :: !steps
            val _ = all_roots := equality :: node :: current :: output ::
              (case scalar of NONE => [] | SOME (Native law) => [law]
               | SOME (Schema conversion) => C.graph_roots conversion) @
              !all_roots
        in memo := Redblackmap.insert (!memo,G.node_id node,output) end
      fun native current {target,theorem,continuation} =
        let
          val _ = G.validate_scope graph scope
          val _ = if G.scope_visible graph scope (G.node_scope graph target)
              then () else raise ERR "native" "local target escapes scope"
          val _ = case size input_limit (G.representative graph current) of
              SOME _ => ()
            | NONE => raise ERR "native" "whole local source exceeds input"
          val actual = Thm.concl theorem
          val count = case size output_limit actual of SOME count => count
            | NONE => raise ERR "native" "whole local witness exceeds output"
          val _ = if output_limit >= 3 andalso
              count <= (output_limit-3) div 2 then () else
            raise ERR "native" "whole local witness ALPHA exceeds output"
          val _ = case SmtReplayImport.bounded_raw_size template_limit actual of
              SOME _ => ()
            | NONE => raise ERR "native" "local witness exceeds template"
          val _ = type_terms [actual]
          val (oracles,_) = Tag.dest_tag (Thm.tag theorem)
          val _ = if null (Thm.hyp theorem) andalso
              null (Tag.axioms_of (Thm.tag theorem)) andalso
              List.all (fn oracle => oracle = "DISK_THM") oracles then () else
            raise ERR "native" "local witness is not a checked closed law"
          val (left,right) = boolSyntax.dest_eq actual
          val _ = if Portable.pointer_eq (left,G.representative graph current)
              andalso Portable.pointer_eq
                (right,G.representative graph target) then () else
            raise ERR "native" "local witness lacks exact owned endpoints"
          fun coverage original node =
            let val free = Term.free_vars original
                val known = G.free_variable_nodes graph node
                fun variable term = case known of SOME variables =>
                    (case List.find (fn owned => Term.aconv term
                        (G.representative graph owned)) variables of
                       SOME owned => owned
                     | NONE => raise ERR "native" "missing owned free ID")
                  | NONE => if node = current andalso
                        scope = G.root_scope graph andalso
                        G.origin graph node = G.ImportedSource then
                      G.variable graph scope G.RigidSource term
                    else raise ERR "native" "unknown scoped free IDs"
                val variables = List.map variable free
                val ids = Listsort.sort Int.compare o List.map G.node_id
                val _ = case known of NONE => () | SOME known =>
                  if ids known = ids variables then () else
                    raise ERR "native" "inexact free-ID metadata"
                val _ = List.app (fn owned =>
                  if G.scope_visible graph scope (G.node_scope graph owned)
                    then (case G.view graph owned of
                        G.Variable (G.RigidSource,_) => ()
                      | G.Variable (G.Bound,_) => ()
                      | _ => raise ERR "native" "unowned free variable kind")
                  else raise ERR "native" "free variable escapes scope")
                  variables
            in variables end
          val source_variables = coverage left current
          val target_variables = coverage right target
          val _ = if List.all (fn variable =>
              List.exists (fn owned => owned = variable) source_variables)
              target_variables then () else
            raise ERR "native" "local target introduced a free variable ID"
          val law = equation graph scope current target
          val actual = G.representative graph law
          val theorem = Thm.EQ_MP
            (Thm.ALPHA (Thm.concl theorem) actual) theorem
          val _ = witness_list := (law,theorem) :: !witness_list
          val _ = if continuation then gap_list := target :: !gap_list else ()
        in (target,Native law) end
      fun scalar node current children =
        case propose scope current of NONE =>
          save node current children NONE NONE current
        | SOME schema =>
            let val converted = C.graph_conversion graph scope true
                  (fn next => if next = current then SOME schema else
                    propose scope next) current
            in save node current children NONE (SOME (Schema converted))
              (C.graph_result converted) end
      fun loop [] = ()
        | loop (Visit node :: pending) =
            if Option.isSome (Redblackmap.peek (!memo,G.node_id node)) then
              (ignore (G.type_of graph node);loop pending)
            else (ignore (G.type_of graph node);
              if G.scope_visible graph scope (G.node_scope graph node) then ()
              else raise ERR "discover" "source node escapes scope";
              case local_witness scope node of Gap =>
                  (gap_list := node :: !gap_list;
                   save node node NONE NONE NONE node;loop pending)
                | Checked checked =>
                    let val (target,converted) = native node checked
                    in save node node NONE NONE (SOME converted) target;
                      loop pending end
                | Unhandled =>
                  (case G.view graph node of G.Application (left,right) =>
                  (check_type (G.type_of graph node);
                   loop (Visit left :: Visit right ::
                     Finish (node,left,right) :: pending))
                | G.OpaqueRetained => atom node pending
                | G.AdmittedBinder _ => atom node pending
                | _ => (check_type (G.type_of graph node);
                    scalar node node NONE;loop pending)))
        | loop (Finish (node,left,right) :: pending) =
            let val current = if required left = left andalso
                  required right = right then node else
                G.application graph scope (required left,required right)
            in scalar node current (SOME (left,right));loop pending end
      and atom node pending =
        (case bounded_binder node of NONE =>
           (gap_list := node :: !gap_list;save node node NONE NONE NONE node)
         | SOME (output,law,theorem,gaps) =>
             (witness_list := (law,theorem) :: !witness_list;
              gap_list := gaps @ !gap_list;
              save node output NONE (SOME law) NONE output);
         loop pending)
      val _ = loop [Visit root]
      val output = required root
      val steps = List.rev (!steps)
      val equality = equation graph scope root output
    in Conversion {graph = graph,scope = scope,source = root,result = output,
      equality = equality,steps = steps,roots = !all_roots,
      witnesses = !witness_list,gaps = !gap_list} end
  fun create options = discover_state options (new_state ())
  fun discover options root = create options root
end
