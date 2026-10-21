(* Copyright (c) 2026 The HOL4 contributors. *)
structure Z3_GraphProofReplay =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayRules SmtReplaySource
    SmtReplayClause SmtReplayBinderEquality
    Z3_GraphProofParser
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure Z = Z3_GraphProofParser
  structure R = SmtReplayRules
  structure GD = SmtReplayOwnedZ3GroundDefinition
  structure C = SmtReplayClause
  structure E = SmtReplayDefinitionEnvironment
  structure F = SmtLib_GraphFrontend
  structure S = SmtLib_Parser
  val ERR = Feedback.mk_HOL_ERR "Z3_GraphProofReplay"
  val _ = SmtReplayOwnedZ3GroundDefinition.begin
  datatype action = Source of G.node * int
      | ReconciledSource of G.node
      | PreprocessedSource of G.node
    | Alias of Z.proof_id
    | Compact of {rule : string,target : G.node,premises : Z.proof_id list}
    | LocalLaw of {target : G.node,premises : Z.proof_id list,
                   law : G.node,index : int}
    | RecordedLaw of {target : G.node,premises : Z.proof_id list,
        law : G.node,index : int,definitions : (G.node * int) list}
    | OwnedGroundEquation of {target : G.node,definition : G.node,
        index : int,owner : SmtReplayOwnedZ3GroundDefinition.owner,
        receipt : SmtReplayOwnedZ3GroundDefinition.receipt}
    | OwnedApplyDefinition of {target : G.node,premise : Z.proof_id}
    | BoundNnfLaw of {target : G.node,law : G.node,index : int,
                     hypotheses : (G.node * int) list}
    | Resolution of {target : G.node,premises : Z.proof_id list}
    | Lemma of {target : G.node,body : Z.proof_id,
                assumptions : G.node list,law : G.node,index : int}
  datatype completion = Ordinary of G.node option
    | Pointwise
    | BinderEquality of
        {parent_scope : G.scope, variables : G.node list, target : G.node}
  datatype task = Visit of Z.proof_id | Finish of Z.proof_id
  type local_request =
    {rule : Z3_Proof.proof_rule,
     metadata : Z3_Proof.th_lemma_metadata option,
     target : G.node,premises : G.node list,
     arguments : SmtLib_GraphFrontend.term list,law : G.node}
  type recorded_result = {definitions : G.node list,theorem : Thm.thm}
  type nnf_request =
    {rule : Z3_Proof.proof_rule,target : G.node,
     premises : (G.node list * Thm.thm) list}

  (* Admission precedes public binder operations and ordinary NNF replay.
     An opaque retained operand is counted lazily under the existing quota. *)
  fun admit_nnf_terms terms =
    let
      val limit = SmtResource.max_bv_replay_term_nodes
      val types = SmtWordGraph.new_type_admission ()
      fun admit term =
        (case SmtReplayImport.bounded_raw_size limit term of SOME _ => ()
         | NONE => SmtResource.check_term_size_for
             "BitVector" "binder-opening" (limit+1))
      fun inspect [] = ()
        | inspect (term :: rest) =
            (SmtWordGraph.admit_primitive_type types (Term.type_of term);
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term
               in inspect (operator :: operand :: rest) end
             else if Term.is_abs term then
               let val (variable,body) = Term.dest_abs term
               in inspect (variable :: body :: rest) end
             else inspect rest)
      val _ = List.app admit terms
    in inspect terms end

  local
  datatype equation_mode = PublicGround | PrivateDependent
  fun replay_with_sources_using_packet_mode equation_mode ground_packet
      use_environment use_closed_laws
      use_needed use_variable_witnesses use_ground recorded_law
      use_packed_scc use_fresh_bits reconciliation preprocessing
      canonical_sources
      (owned : {work:SmtReplayInvocationWork.portfolio,
        frame:SmtReplayOwnedScopeReceipt.receipt} option) graph scope
      {proof : Z.proof,template_limit,local_law : local_request ->
        Thm.thm option,nnf : nnf_request -> Thm.thm option} =
    let
      (* SAME original Work. Genuine binding frames retain both lexical
         and construction lifetimes; old selectors use NONE throughout. *)
      fun protected action = action () handle primary =>
        (case owned of NONE => raise primary
         | SOME {work,...} =>
             (SmtReplayInvocationWork.close work;raise primary))
      fun gp validation action = case owned of NONE => action ()
        | SOME {work,...} => protected (fn () =>
            let val _ = SmtLib_GraphPreprocess.validate_with_work
                  work validation
                val result = action ()
                val _ = SmtLib_GraphPreprocess.validate_with_work
                  work validation
            in result end)
      fun gp_originals validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.original_sources validation)
      fun gp_sources validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.source_nodes validation)
      fun gp_roots validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.roots validation)
      fun gp_assumptions validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.processed_assumptions validation)
      fun gp_denied validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.processed_denied_goal validation)
      fun gp_cap validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.template_limit validation)
      fun gp_facts validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.closed_facts validation)
      fun gp_conversions validation = gp validation (fn () =>
        SmtLib_GraphPreprocess.conversions validation)
      fun frame_guard frame expected_scope = case owned of NONE => ()
        | SOME {work,...} => protected (fn () =>
            let val receipt = case frame of SOME held => held
                  | NONE => raise ERR "owned_scope" "missing genuine frame"
                val data = SmtReplayOwnedScopeReceipt.description_for
                  work receipt
            in if Portable.pointer_eq (#graph data,graph) andalso
                #scope data = expected_scope then () else
              raise ERR "owned_scope" "different authentic proof frame" end)
      fun binding_frame parent binding = case owned of NONE => NONE
        | SOME {work,...} => protected (fn () =>
            let val incoming = case parent of SOME held => held
                  | NONE => raise ERR "owned_scope" "missing genuine parent"
            in SOME (SmtReplayOwnedScopeReceipt.binding work incoming
              (SmtLib_GraphFrontend.scoped_session_binding_origin binding)) end)
      fun owned_action frame scope action = case owned of NONE => action ()
        | SOME {work,...} => protected (fn () =>
            (frame_guard frame scope;
             SmtReplayInvocationWork.with_step work (fn () =>
               let val _ = frame_guard frame scope
                   val result = action ()
                   val _ = frame_guard frame scope
               in result end)))
      val original_frame = Option.map (fn {frame,...} => frame) owned
      val _ = frame_guard original_frame scope
      val _ = G.validate_scope graph scope
      val _ = case preprocessing of NONE => ()
        | SOME {sources,validation} =>
            (if Portable.pointer_eq
                (gp_originals validation,sources)
             then () else raise ERR "preprocessing_source"
               "preprocessing has a different original Source owner";
             List.app (fn node =>
               if G.scope_visible graph scope (G.node_scope graph node)
               then () else raise ERR "preprocessing_source"
                 "preprocessing root is outside the original graph scope")
               (gp_sources validation @
                gp_roots validation))
      fun step id = case Redblackmap.peek (#steps proof,id) of
          SOME value => value
        | NONE => raise ERR "discover" "unknown tagged proof reference"
      fun handler (rule : Z3_Proof.proof_rule) = String.translate
        (fn #"_" => "-" | character => String.str character)
        (#replay_handler rule)
      fun all_dependencies id = case step id of
          Z.Rule {premises,...} => premises
        | Z.Alias other => [other]
        | Z.Bind {body,...} => [body]
      (* Check the complete tagged graph before dividing it into blocks.
         Local hypotheses beneath a lemma are not enclosing source facts. *)
      val checked = ref (Redblackmap.mkDict Z.compare_id)
      val canonical = ref ([] : G.node list)
      fun preflight [] = ()
        | preflight (Finish id :: rest) =
            (checked := Redblackmap.insert (!checked,id,2);preflight rest)
        | preflight (Visit id :: rest) =
            (case Redblackmap.peek (!checked,id) of
               SOME 2 => preflight rest
             | SOME _ => raise ERR "discover" "cyclic tagged proof graph"
             | NONE =>
                 (checked := Redblackmap.insert (!checked,id,1);
                  (case step id of Z.Rule {rule,conclusion,...} =>
                     if handler rule = "asserted" then
                       canonical := #node conclusion :: !canonical else ()
                   | _ => ());
                  preflight (List.map Visit (all_dependencies id) @
                    Finish id :: rest)))
      val _ = preflight [Visit (#root proof)]
      val top_seen = ref (Redblackset.empty Z.compare_id)
      fun top_sources [] = ()
        | top_sources (id :: rest) =
            if Redblackset.member (!top_seen,id) then top_sources rest else
              (top_seen := Redblackset.add (!top_seen,id);
               case step id of
                 Z.Rule {rule,conclusion,premises,...} =>
                   (if handler rule = "hypothesis" then
                      canonical := #node conclusion :: !canonical else ();
                    top_sources
                      ((if handler rule = "lemma" then [] else premises) @
                       rest))
               | Z.Alias other => top_sources (other :: rest)
               | Z.Bind _ => top_sources rest)
      val _ = top_sources [#root proof]
      val canonical_ids = Redblackset.addList
        (Redblackset.empty Int.compare,List.map G.node_id (!canonical))
      fun block_sources root local_assumptions local_hypotheses =
        let
          val seen = ref (Redblackset.empty Z.compare_id)
          val allowed = Redblackset.addList
            (canonical_ids,List.map G.node_id local_assumptions)
          fun collect [] sources = List.rev sources
            | collect (id :: rest) sources =
                if Redblackset.member (!seen,id) then collect rest sources
                else
                  (seen := Redblackset.add (!seen,id);
                   case step id of
                     Z.Rule {rule,conclusion,premises,...} =>
                       let
                         val node = #node conclusion
                         val source =
                           (handler rule = "asserted" orelse
                            handler rule = "hypothesis") andalso
                           (Redblackset.member (allowed,G.node_id node) orelse
                            (local_hypotheses andalso
                             handler rule = "hypothesis"))
                       in collect (premises @ rest)
                         (if source then node :: sources else sources) end
                   | Z.Alias other => collect (other :: rest) sources
                   | Z.Bind _ => collect rest sources)
        in collect [root] [] end
      fun complete current_frame scope root local_assumptions completion =
        let
          val _ = frame_guard current_frame scope
          fun callback action = protected (fn () =>
            let val _ = frame_guard current_frame scope
                val result = action ()
                val _ = frame_guard current_frame scope
            in result end)
          val ground_owner = case (ground_packet,owned,current_frame) of
              (SOME packet,SOME {work,...},SOME frame) =>
                SOME (SmtReplayOwnedZ3GroundDefinition.begin work
                  {packet = packet,frame = frame,
                   check_type = SmtWordGraph.admit_primitive_type
                     (SmtWordGraph.new_type_admission ())})
            | (NONE,_,_) => NONE
            | _ => raise ERR "ground_definition" "missing actual owned frame"
          val ground_receipts = ref ([] :
            (SmtReplayOwnedZ3GroundDefinition.owner *
             SmtReplayOwnedZ3GroundDefinition.receipt) list)
          val marks = ref (Redblackmap.mkDict Z.compare_id)
          val plans = ref (Redblackmap.mkDict Z.compare_id)
          val endpoints = ref (Redblackmap.mkDict Z.compare_id)
          val clauses = ref (Redblackmap.mkDict Z.compare_id)
          val order = ref ([] : Z.proof_id list)
          val roots = ref ([] : G.node list)
          val inner = case completion of BinderEquality _ => true
            | Pointwise => true
            | Ordinary _ => false
          val raw_sources = block_sources root local_assumptions inner @
            (if inner then [] else local_assumptions)
          val reconciliation = if root = #root proof andalso
              List.null local_assumptions andalso
              (case completion of Ordinary NONE => true | _ => false)
            then Option.map (fn prepare => prepare scope raw_sources)
              reconciliation else NONE
          val processed = case preprocessing of NONE => []
            | SOME {validation,...} =>
                gp_assumptions validation @
                [gp_denied validation]
          val processed_ids = Redblackset.addList
            (Redblackset.empty Int.compare,List.map G.node_id processed)
          fun derived node =
            Redblackset.member (processed_ids,G.node_id node)
          fun local_source node =
            List.exists (fn saved => saved = node) local_assumptions orelse
            (inner andalso not (Redblackset.member
              (canonical_ids,G.node_id node)))
          val initial_sources = case preprocessing of
              SOME {validation,...} =>
                gp_sources validation @
                List.filter local_source raw_sources
            | NONE => (case reconciliation of NONE => raw_sources
                | SOME plan => Z3_GraphSourceReconcile.sources plan)
          val _ = case reconciliation of NONE => () | SOME plan =>
            roots := Z3_GraphSourceReconcile.roots plan
          val _ = case preprocessing of NONE => ()
            | SOME {validation,...} => roots :=
                gp_roots validation @
                gp_sources validation @ !roots
          val sources = ref (List.rev initial_sources)
          val witnesses = ref (Redblackmap.mkDict Int.compare)
          val _ = case reconciliation of NONE => () | SOME plan =>
            List.app (fn (index,node) =>
              case Z3_GraphSourceReconcile.witness plan (index,node) of
                NONE => () | SOME theorem =>
                  witnesses := Redblackmap.insert
                    (!witnesses,G.node_id node,theorem))
              (ListPair.zip (List.tabulate (length initial_sources,Lib.I),
                initial_sources))
          (* Exact producer ID, within-handler occurrence and Source index. *)
          val recorded_indices = ref
            ([] : (Z.proof_id * int * G.node * int) list)
          val source_count = ref (List.length initial_sources)
          fun source node witness =
            let val index = !source_count in
              source_count := index+1;sources := node :: !sources;
              (case witness of NONE => () | SOME theorem =>
                 witnesses := Redblackmap.insert
                   (!witnesses,G.node_id node,theorem));index end
          val (_,initial_indices) = List.foldl
            (fn (node,(index,table)) =>
              (index+1,if Redblackmap.inDomain (table,G.node_id node) then
                 table else Redblackmap.insert (table,G.node_id node,index)))
            (0,Redblackmap.mkDict Int.compare) initial_sources
          fun assumption node =
            case Redblackmap.peek (initial_indices,G.node_id node) of
              SOME index => index
            | NONE => raise ERR "discover"
                "hypothesis is outside the enclosing source scope"
          fun endpoint id = case Redblackmap.peek (!endpoints,id) of
              SOME node => node
            | NONE => raise ERR "discover" "premise not yet discovered"
          fun clause id = case Redblackmap.peek (!clauses,id) of
              SOME layout => layout
            | NONE => raise ERR "discover" "missing recorded clause boundary"
          fun literal (S.ConstructionOccurrence
              {value,role,token,children,...}) : C.literal =
            case (role,token,children) of
              (S.ConstructionApplication,"not",[child]) =>
                {atom = S.construction_value child,negative = true}
            | (S.ConstructionApplication,"~",[child]) =>
                {atom = S.construction_value child,negative = true}
            | _ =>
                (* A lexical alias keeps its outer semantic negation. Inspect
                   exactly one owned constructor, retaining opaque AND/OR
                   atom boundaries. C.discover/bridge checks the actual NOT
                   constructor; no spelling or raw-term rewrite is used. *)
                (case G.view graph value of
                   G.Application (operator,atom) =>
                     (case G.view graph operator of G.Constant _ =>
                        if Term.same_const (G.representative graph operator)
                            boolSyntax.negation andalso
                            Type.compare (G.type_of graph operator,
                              Term.type_of boolSyntax.negation) = EQUAL andalso
                            Type.compare (G.type_of graph atom,Type.bool)
                              = EQUAL andalso
                            Type.compare (G.type_of graph value,Type.bool)
                              = EQUAL then {atom = atom,negative = true}
                        else {atom = value,negative = false}
                      | _ => {atom = value,negative = false})
                 | _ => {atom = value,negative = false})
          fun layout (term : F.term) =
            let
              val entries = F.clause_occurrences term
              val literals = case entries of
                  [entry] => (case G.view graph (#node term) of
                    G.Constant _ => if Term.same_const
                        (G.representative graph (#node term)) boolSyntax.F
                      then [] else [literal entry]
                  | _ => [literal entry])
                | _ => List.map literal entries
              val result = C.discover graph scope literals
              val _ = if C.root result = #node term then () else
                raise ERR "discover" "recorded clause constructor mismatch"
            in result end
          fun dependencies id = case step id of
              Z.Rule {rule,premises,...} =>
                if handler rule = "lemma" orelse
                    handler rule = "quant-intro" orelse
                    ((handler rule = "nnf-pos" orelse
                      handler rule = "nnf-neg") andalso
                     List.exists (fn id => case step id of
                       Z.Bind _ => true | _ => false) premises)
                then [] else premises
            | Z.Alias other => [other]
            | Z.Bind _ => raise ERR "discover"
                "scoped proof-bind requires its bounded consumer adapter"
          fun clean theorem =
            let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
              List.all (fn tag => tag = "DISK_THM") tags andalso
              List.null (Tag.axioms_of (Thm.tag theorem)) end
          fun compact rule = List.exists (fn name => name = rule)
            ["refl","symm","trans","trans-star","monotonicity",
             "and-elim","iff-false","iff-true","mp","mp-eq",
             "not-or-elim","true-axiom","unit-resolution","def-axiom",
             "commutativity","rewrite"]
          fun finish id =
            let
              val (node,plan) = case step id of
                  Z.Alias other =>
                    (clauses := Redblackmap.insert (!clauses,id,clause other);
                     (endpoint other,Alias other))
                | Z.Bind _ => raise ERR "discover" "unhandled proof-bind"
                | Z.Rule {rule,conclusion,premises,arguments,metadata,...} =>
                    let
                      val node = #node conclusion
                      val name = handler rule
                      val bound_nnf = (name = "nnf-pos" orelse
                        name = "nnf-neg") andalso List.exists
                          (fn id => case step id of Z.Bind _ => true
                            | _ => false) premises
                      val _ = G.validate_scope graph (#scope conclusion)
                      val _ = if G.scope_visible graph scope
                          (G.node_scope graph node) then () else
                        raise ERR "discover" "proof endpoint escapes block scope"
                      val _ = case preprocessing of NONE => ()
                        | SOME _ => if name = "asserted" then
                            if derived node then () else
                              raise ERR "preprocessing_source"
                                "assertion is outside the processed query"
                          else if name = "hypothesis" then
                            if derived node orelse local_source node then ()
                            else raise ERR "preprocessing_source"
                              "hypothesis is outside the original block"
                          else ()
                      val _ = clauses := Redblackmap.insert
                        (!clauses,id,layout conclusion)
                      val premise_nodes =
                        if name = "lemma" orelse name = "quant-intro" orelse
                            bound_nnf then []
                        else List.map endpoint premises
                      fun ground_plan () =
                        case (owned,ground_owner) of
                          (SOME {work,...},SOME owner) =>
                            (case (case equation_mode of PublicGround =>
                                SmtReplayOwnedZ3GroundDefinition.prepare
                              | PrivateDependent =>
                                  GD.prepare_dependent_equation)
                                work owner id of NONE => NONE
                             | SOME pending =>
                               let
                                 val receipt =
                                   SmtReplayOwnedZ3GroundDefinition.execute
                                     work owner pending
                                 val data =
                                   GD.description_for work owner receipt
                                 val _ = if #proof_id data = id andalso
                                     #target data = node then () else
                                   raise ERR "ground_definition"
                                     "actual receipt endpoint differs"
                                 val definition = #definition data
                                 val index = source definition NONE
                                 val _ = recorded_indices :=
                                   (id,0,definition,index) :: !recorded_indices
                                 val _ = ground_receipts :=
                                   (owner,receipt) :: !ground_receipts
                                 val _ = roots := definition :: !roots
                               in SOME (OwnedGroundEquation
                                 {target = node,definition = definition,
                                  index = index,owner = owner,
                                  receipt = receipt}) end)
                        | _ => NONE
                      fun local_plan () =
                        let
                          val law = R.implication graph scope premise_nodes node
                          val request : local_request =
                            {rule = rule,metadata = metadata,target = node,
                             premises = premise_nodes,arguments = arguments,
                             law = law}
                          fun recorded_plan produce =
                            case produce request of NONE => NONE
                            | SOME {definitions,theorem} =>
                              let
                                val law = R.implication graph scope
                                  (definitions @ premise_nodes) node
                                val _ = List.app (fn metric =>
                                  case G.unfolded_nodes graph metric
                                    template_limit law of
                                    SOME count => if count <= template_limit
                                      then () else raise ERR "recorded_definition"
                                        "recorded law exceeds graph quota"
                                  | NONE => raise ERR "recorded_definition"
                                      "recorded law exceeds graph quota")
                                  [G.RawNodes,G.BinderInclusiveNodes]
                                val _ = if List.null (Thm.hyp theorem) andalso
                                    clean theorem andalso Portable.pointer_eq
                                      (Thm.concl theorem,
                                       G.representative graph law)
                                  then () else raise ERR "recorded_definition"
                                    "producer law is not closed, clean and exact"
                                val indices = Lib.mapi
                                  (fn ordinal => fn node =>
                                  let val index = source node NONE in
                                    recorded_indices :=
                                      (id,ordinal,node,index) :: !recorded_indices;
                                    (node,index) end) definitions
                                val index = source law (SOME theorem)
                                val _ = roots := law :: definitions @ !roots
                              in SOME (RecordedLaw
                                {target = node,premises = premises,law = law,
                                 index = index,definitions = indices}) end
                        in case recorded_law of SOME produce =>
                             recorded_plan produce
                           | NONE => (case callback (fn () => local_law request) of
                               NONE => NONE
                          | SOME theorem =>
                              let
                                val _ = if List.null (Thm.hyp theorem) andalso
                                    clean theorem andalso Portable.pointer_eq
                                      (Thm.concl theorem,
                                       G.representative graph law)
                                  then () else raise ERR "discover"
                                    "local rule law is not closed, clean and exact"
                                val index = source law (SOME theorem)
                                val _ = roots := law :: !roots
                              in SOME (LocalLaw
                                {target = node,premises = premises,law = law,
                                 index = index}) end)
                        end
                    in
                      if name = "asserted" orelse name = "hypothesis" then
                        (node,case preprocessing of
                          SOME _ => if name = "hypothesis" andalso
                              local_source node then
                            Source (node,assumption node)
                          else if derived node then PreprocessedSource node
                          else Source (node,assumption node)
                        | NONE => (case reconciliation of NONE =>
                            Source (node,assumption node)
                          | SOME _ => ReconciledSource node))
                      else if bound_nnf then
                        let
                          fun premise id =
                            let
                              val (variables,inner_scope,body) =
                                case step id of
                                  Z.Bind {body,binding,...} =>
                                    let val F.ScopedSession
                                      {variables,scope,...} = binding
                                    in (variables,scope,body) end
                                | _ => ([],scope,id)
                              val next_frame = case step id of
                                  Z.Bind {binding,...} =>
                                    binding_frame current_frame binding
                                | _ => current_frame
                              val completed = complete next_frame inner_scope
                                body local_assumptions Pointwise
                              val ids = Redblackset.addList
                                (Redblackset.empty Int.compare,
                                 List.map G.node_id variables)
                              val _ = if Redblackset.numItems ids =
                                  List.length variables then () else
                                raise ERR "nnf_bound" "duplicate annotation"
                              val _ = List.app (fn variable =>
                                case G.view graph variable of
                                  G.Variable (G.Bound,_) =>
                                    if G.scope_visible graph inner_scope
                                        (G.node_scope graph variable) then ()
                                    else raise ERR "nnf_bound"
                                      "foreign annotation frame"
                                | _ => raise ERR "nnf_bound"
                                    "annotation is not a Bound variable")
                                variables
                            in (variables,completed) end
                          val completed = List.map premise premises
                          val inputs = List.map (fn (variables,result) =>
                            (variables,#theorem result)) completed
                          val _ = admit_nnf_terms
                            (G.representative graph node :: List.concat
                              (List.map (fn (variables,theorem) =>
                                Thm.concl theorem :: Thm.hyp theorem @
                                List.map (G.representative graph) variables)
                                inputs))
                          val theorem = case callback (fn () => nnf
                              {rule = rule,target = node,premises = inputs}) of
                            SOME theorem => theorem
                          | NONE => raise ERR "nnf_bound"
                              "bounded NNF consumer declined"
                          val _ = admit_nnf_terms
                            (Thm.concl theorem :: Thm.hyp theorem)
                          val _ = if clean theorem then () else
                            raise ERR "nnf_bound" "unclean NNF theorem"
                          val theorem = Thm.EQ_MP
                            (Thm.ALPHA (Thm.concl theorem)
                              (G.representative graph node)) theorem
                          val known = canonical_sources @ !sources @
                            List.concat (List.map
                              (fn (_,result) => #hypotheses result) completed)
                          fun retained hypothesis =
                            case List.find (fn owned => Portable.pointer_eq
                              (hypothesis,G.representative graph owned))
                                known of
                              SOME owned => owned
                            | NONE => raise ERR "nnf_bound"
                                "NNF retained a noncanonical hypothesis"
                          fun transport (hypothesis,(theorem,owned)) =
                            let val source = G.rehome graph scope
                                  (retained hypothesis)
                                val instance = Thm.EQ_MP
                                  (Thm.SYM (#bridge source))
                                  (Thm.ASSUME
                                    (G.representative graph (#node source)))
                            in (Drule.PROVE_HYP instance theorem,
                              #node source :: owned) end
                          val (theorem,hypotheses) = List.foldl transport
                            (theorem,[]) (Thm.hyp theorem)
                          val law = R.implication graph scope hypotheses node
                          val limit = SmtResource.max_bitblast_term_nodes
                          fun admit_law term =
                            case SmtReplayImport.bounded_binder_size
                                limit term of
                              SOME _ => ()
                            | NONE => raise ERR "nnf_bound"
                                "conditional NNF law exceeds ordinary quota"
                          val _ = admit_law (G.representative graph law)
                          val conditional = List.foldr
                            (fn (hypothesis,result) => Thm.DISCH
                              (G.representative graph hypothesis) result)
                            theorem hypotheses
                          val _ = admit_law (Thm.concl conditional)
                          val closed = Thm.EQ_MP
                            (Thm.ALPHA (Thm.concl conditional)
                              (G.representative graph law)) conditional
                          val _ = if List.null (Thm.hyp closed) then () else
                            raise ERR "nnf_bound" "NNF law is not closed"
                          val indices = List.map (fn hypothesis =>
                            (hypothesis,source hypothesis NONE)) hypotheses
                          val index = source law (SOME closed)
                          val _ = roots := law :: !roots
                        in (node,BoundNnfLaw
                          {target = node,law = law,index = index,
                           hypotheses = indices}) end
                      else if name = "quant-intro" then
                        let
                          val bound = case premises of [id] => step id
                            | _ => raise ERR "quant_intro"
                                "expected one immediate proof-bind premise"
                          val (body,binding) = case bound of
                              Z.Bind {body,binding,...} => (body,binding)
                            | _ => raise ERR "quant_intro"
                                "premise is not an immediate proof-bind"
                          val F.ScopedSession
                            {variables,scope = inner_scope,...} = binding
                          val _ = if List.null variables then
                            raise ERR "quant_intro" "annotation is empty"
                            else ()
                          val next_frame = binding_frame current_frame binding
                          val completed = complete next_frame inner_scope body
                            local_assumptions
                            (BinderEquality {parent_scope = scope,
                              variables = variables,target = node})
                          val _ = List.app (fn hypothesis =>
                            ignore (source hypothesis NONE))
                            (#hypotheses completed)
                          val theorem = #theorem completed
                          val index = source node (SOME theorem)
                        in (node,Source (node,index)) end
                      else if name = "lemma" then
                        let
                          val body = case premises of [body] => body
                            | _ => raise ERR "lemma" "expected one premise"
                          fun complement ({atom,negative} : C.literal) =
                            if negative then atom else G.application graph scope
                              (G.constant graph scope boolSyntax.negation,atom)
                          val assumptions = List.map complement
                            (C.recorded (clause id))
                          val law = R.implication graph scope local_assumptions node
                          val index = source law NONE
                          val _ = roots := law :: assumptions @ !roots
                        in (node,Lemma {target = node,body = body,
                          assumptions = assumptions,law = law,index = index}) end
                      else if name = "unit-resolution" then
                        if List.null premises then raise ERR "unit_resolution"
                          "empty premise list" else
                          (node,Resolution {target = node,premises = premises})
                      else if name = "intro-def" andalso
                          Option.isSome ground_owner then
                        (node,case ground_plan () of SOME plan => plan
                         | NONE => raise ERR "ground_definition"
                             "fixed ground equation operation is inapplicable")
                      else if name = "apply-def" andalso
                          Option.isSome ground_owner andalso
                          Option.isSome (R.equality graph node) then
                        let val premise = case premises of [actual] => actual
                              | _ => raise ERR "apply_def"
                                  "expected one actual proof premise"
                        in (node,OwnedApplyDefinition
                          {target = node,premise = premise}) end
                      else if compact name then
                        (node,case
                            (if name = "rewrite" orelse name = "commutativity"
                             then local_plan () else NONE) of
                           SOME plan => plan
                         | NONE => Compact
                             {rule = name,target = node,premises = premises})
                      else
                        (node,case local_plan () of SOME plan => plan
                         | NONE => raise ERR "discover"
                             ("no checked graph adapter for Z3 rule " ^ name))
                    end
              val _ = roots := node :: !roots
              val _ = endpoints := Redblackmap.insert (!endpoints,id,node)
              val _ = plans := Redblackmap.insert (!plans,id,plan)
              val _ = order := id :: !order
              val _ = marks := Redblackmap.insert (!marks,id,2)
            in () end
          fun discover [] = ()
            | discover (Finish id :: rest) = (finish id;discover rest)
            | discover (Visit id :: rest) =
                (case Redblackmap.peek (!marks,id) of
                   SOME 2 => discover rest
                 | SOME _ => raise ERR "discover" "cyclic tagged proof graph"
                 | NONE =>
                     (marks := Redblackmap.insert (!marks,id,1);
                      discover (List.map Visit (dependencies id) @
                        Finish id :: rest)))
          val _ = discover [Visit root]
          val target = endpoint root
          val output = case completion of Ordinary output => output
            | Pointwise => NONE
            | BinderEquality _ => NONE
          val desired = case completion of BinderEquality _ => target
            | Pointwise => target
            | Ordinary NONE =>
                R.implication graph scope local_assumptions target
            | Ordinary (SOME node) => node
          val source_nodes = List.rev (!sources)
          (* Old environment routes remain conservative. The opt-in sparse
             route assembles actual compact Hyp before selecting definitions.
             Original Source order/duplicates survive the final handoff. *)
          val closed_laws = if not use_closed_laws then [] else
            List.mapPartial (fn node =>
              case Redblackmap.peek (!witnesses,G.node_id node) of
                SOME theorem => if List.null (Thm.hyp theorem) andalso
                    clean theorem then SOME (node,theorem) else NONE
              | NONE => NONE) source_nodes
          val outer_environment = use_environment andalso
            root = #root proof andalso List.null local_assumptions andalso
            (case completion of Ordinary NONE => true | _ => false)
          val needed_route = use_needed andalso outer_environment
          fun definition_plan needed =
              let
                val (_,private) = List.foldl (fn (node,(seen,nodes)) =>
                  case G.view graph node of G.Variable (G.SolverFlexible,_) =>
                    if Redblackset.member (seen,G.node_id node) then
                      (seen,nodes)
                    else (Redblackset.add (seen,G.node_id node),node :: nodes)
                  | _ => (seen,nodes))
                  (Redblackset.empty Int.compare,[]) (#vars proof)
                val plan = SmtReplayDefinitionEnvironment.prepare graph
                  {scope = scope,allocated = List.rev private,
                   sources = source_nodes,needed = needed,
                   roots = desired :: !roots}
              in plan end
          fun resolved outcome = case outcome of
              SmtReplayDefinitionEnvironment.Resolved resolution => resolution
            | SmtReplayDefinitionEnvironment.RequiresWitness _ =>
                raise ERR "remove_definitions"
                  "compact environment requires a checked cycle witness"
            | SmtReplayDefinitionEnvironment.UnificationRefused _ =>
                raise ERR "remove_definitions"
                  "compact definition unification declined"
            | SmtReplayDefinitionEnvironment.ResolutionRefused _ =>
                raise ERR "remove_definitions"
                  "compact definition resolution declined"
          fun checked_variables plan laws only_needed =
            let
              val types = SmtWordGraph.new_type_admission ()
              val resolve = if only_needed then
                  E.resolve_needed_checked_variables
                else SmtReplayDefinitionEnvironment.resolve_checked_variables
            in resolve plan {preserved = [desired],laws = laws,
              admission = {metric = G.RawNodes,
                limit = SmtResource.max_bv_replay_term_nodes,
                check_type = SmtWordGraph.admit_primitive_type types}} end
          fun retain_reflexive pairs = List.app (fn (node,proof) =>
            witnesses := Redblackmap.insert (!witnesses,G.node_id node,proof))
            pairs
          val (environment,reflexive_sources) =
            if not outer_environment orelse needed_route then (NONE,[])
            else if use_variable_witnesses then
              let val result = checked_variables
                    (definition_plan source_nodes) closed_laws false
              in (SOME (resolved (#outcome result)),
                  #reflexive_sources result) end
            else (SOME (resolved
              (if use_closed_laws then
                 SmtReplayDefinitionEnvironment.resolve_with_closed_sources
                   (definition_plan source_nodes)
                   {preserved = [desired],laws = closed_laws}
               else SmtReplayDefinitionEnvironment.resolve
                 (definition_plan source_nodes) {preserved = [desired]})),[])
          val _ = retain_reflexive reflexive_sources
          val closed_laws = closed_laws @ reflexive_sources
          fun prepare_images resolution laws =
              let
                val table = List.foldl (fn ((node,proof),table) =>
                  Redblackmap.insert (table,G.node_id node,proof))
                  (Redblackmap.mkDict Int.compare) laws
                val indexed = List.mapPartial (fn (index,node) =>
                  Option.map (fn proof => (index,proof))
                    (Redblackmap.peek (table,G.node_id node)))
                  (ListPair.zip (List.tabulate
                    (List.length source_nodes,Lib.I),source_nodes))
                val types = SmtWordGraph.new_type_admission ()
              in SmtReplayClosedSourceImages.prepare graph
                {scope = scope,resolution = resolution,
                 sources = source_nodes,laws = indexed,
                 admission = {metric = G.RawNodes,
                   limit = SmtResource.max_bv_replay_term_nodes,
                   check_type = SmtWordGraph.admit_primitive_type types}}
              end
          val closed_images = if not use_closed_laws then [] else
            case environment of NONE => [] | SOME resolution =>
              prepare_images resolution closed_laws
          val freeze_roots = case environment of NONE => desired :: !roots
            | SOME resolution => desired :: !roots @
                SmtReplayResolve.roots resolution
          val _ = case preprocessing of NONE => ()
            | SOME {validation,...} =>
                (case gp_cap validation of
                   NONE => ()
                 | SOME limit => if limit = template_limit then () else
                     raise ERR "preprocessing_source" "original GP cap differs")
          val block = case owned of NONE => (case preprocessing of NONE =>
              (if needed_route then P.prepare_needed_sources
               else P.freeze) graph
                {scope = scope,roots = freeze_roots,sources = source_nodes,
                 template_limit = template_limit}
            | SOME {validation,...} =>
              (if needed_route then P.prepare_needed_sources_with_conversions
               else P.freeze_with_conversions) graph
                {scope = scope,roots = freeze_roots,sources = source_nodes,
                 closed_facts = gp_facts validation,
                 conversions = gp_conversions validation,
                 template_limit = template_limit})
            | SOME {work,...} =>
              let
                val frame = case current_frame of SOME value => value
                  | NONE => raise ERR "owned_freeze" "missing actual frame"
                val validation = case preprocessing of SOME {validation,...} =>
                    validation
                  | NONE => raise ERR "owned_freeze" "missing original GP"
                val prefix = gp_sources validation
                fun strip [] rest = rest
                  | strip (_ :: _) [] = raise ERR "owned_freeze"
                      "original occurrence prefix is missing"
                  | strip (node :: nodes) (held :: rest) =
                      if node = held then strip nodes rest else
                        raise ERR "owned_freeze" "original Source order differs"
                val extras = strip prefix source_nodes
                val facts = gp_facts validation
                val conversions = gp_conversions validation
                val _ = frame_guard current_frame scope
                (* This genuine producer owns its action. No outer Busy. *)
                fun sparse () = P.prepare_needed_sources_with_work work
                  {frame = frame,roots = freeze_roots,
                   additional_sources = extras,closed_facts = facts,
                   conversions = conversions}
                fun ordinary () = let
                val frontier = P.prepare_scoped_original_realization_frontier
                  work {frame = frame,roots = freeze_roots,
                    additional_sources = extras,closed_facts = facts,
                    conversions = conversions}
                val data = P.realization_frontier_data_for work frontier
                val _ = if #sources data = source_nodes andalso
                    #scope data = scope then () else
                  raise ERR "owned_freeze" "actual Source frame differs"
                val tables = owned_action current_frame scope (fn () =>
                  P.prepare_owned_realization_tables work frontier)
                in owned_action current_frame scope (fn () =>
                  P.freeze_owned_realization_tables_plan work tables) end
                val result = case ground_owner of NONE => ordinary ()
                  | SOME _ => sparse ()
                val _ = case ground_owner of NONE => () | SOME _ =>
                  (P.validate_block_for work result;
                   if P.sources result = source_nodes then () else
                     raise ERR "owned_freeze" "actual occurrence slots differ")
              in result end
          val derived_edge = case preprocessing of NONE => NONE
            | SOME {validation,...} => SOME (case owned of NONE =>
                SmtLib_GraphPreprocess.assembler validation block
              | SOME {work,...} =>
                  SmtLib_GraphPreprocess.assembler_with_work work
                    validation block)
          val edges = ref (Redblackmap.mkDict Z.compare_id)
          fun edge id = case Redblackmap.peek (!edges,id) of
              SOME result => result
            | NONE => raise ERR "assemble" "premise not yet assembled"
          fun premises ids = List.map (fn id => (endpoint id,edge id)) ids
          fun assemble id =
            let
              val plan = Redblackmap.find (!plans,id)
              val completed_lemma = case plan of
                  Lemma {body,assumptions,law,...} =>
                    SOME (#theorem (complete current_frame scope body
                      (local_assumptions @ assumptions) (Ordinary (SOME law))))
                | _ => NONE
              val result = owned_action current_frame scope (fn () =>
                case plan of Source (_,index) => P.source block index
                | ReconciledSource node =>
                    (case reconciliation of SOME original =>
                       Z3_GraphSourceReconcile.assemble original block node
                     | NONE => raise ERR "assemble"
                         "missing original Source reconciliation")
                | PreprocessedSource node =>
                    (case derived_edge of SOME assemble =>
                       (case assemble node of SOME edge => edge
                        | NONE => raise ERR "preprocessing_source"
                            "processed assertion has no checked derivation")
                     | NONE => raise ERR "preprocessing_source"
                         "missing original preprocessing derivation")
                | Alias other => edge other
                | Compact {rule,target,premises = ids} =>
                    R.assemble graph block
                      {rule = rule,target = target,premises = premises ids}
                | LocalLaw {target,premises = ids,law,index} =>
                    R.apply_law graph block
                      {law = (law,P.source block index),target = target,
                       premises = premises ids}
                | RecordedLaw {target,premises = ids,law,index,
                    definitions} =>
                    R.apply_law graph block
                      {law = (law,P.source block index),target = target,
                       premises = List.map (fn (node,index) =>
                         (node,P.source block index)) definitions @ premises ids}
                | OwnedGroundEquation
                    {target,definition,index,owner,receipt} =>
                    let
                      val work = case owned of SOME {work,...} => work
                        | NONE => raise ERR "ground_definition"
                            "missing original Work"
                      val data = GD.description_for work owner receipt
                      val _ = if #proof_id data = id andalso
                          #definition data = definition andalso
                          #target data = target then () else
                        raise ERR "ground_definition"
                          "different retained actual equation occurrence"
                      val incoming = P.source block index
                    in if definition = target then incoming else
                      R.assemble graph block {rule = "symm",target = target,
                        premises = [(definition,incoming)]} end
                | OwnedApplyDefinition {target,premise} =>
                    let
                      val work = case owned of SOME {work,...} => work
                        | NONE => raise ERR "apply_def"
                            "missing original Work"
                      fun guard () =
                        (frame_guard current_frame scope;
                         P.validate_block_for work block)
                      val _ = guard ()
                      (* These are ONLY the actual owned premise edge's
                         ordinary Source dependencies, not parser history,
                         target occurrences or a supplied needed array. *)
                      val dependencies = P.dependencies block (edge premise)
                      val _ = guard ()
                      val retained = P.sources block
                      fun at index =
                        let fun walk [] _ = raise ERR "apply_def"
                                  "actual dependency escapes retained slots"
                              | walk (node::rest) current =
                                  (guard ();
                                   SmtReplayInvocationWork.spend work 1;
                                   if current = index then node else
                                     walk rest (current+1))
                        in walk retained 0 end
                      val endpoints = case R.equality graph target of
                          SOME pair => pair
                        | NONE => raise ERR "apply_def"
                            "target is not an actual HOL equality"
                      fun select [] = raise ERR "apply_def"
                            "definition is absent from actual premise deps"
                        | select (index::rest) =
                            let val _ = guard ()
                                val _ = SmtReplayInvocationWork.spend work 1
                                val definition = at index
                                val _ = if G.scope_visible graph scope
                                    (G.node_scope graph definition) then ()
                                  else raise ERR "apply_def"
                                    "dependency escapes actual proof frame"
                            in if definition = target then
                                 P.source block index
                               else case R.equality graph definition of
                                 SOME (left,right) =>
                                   if (right,left) = endpoints then
                                     R.assemble graph block
                                       {rule = "symm",target = target,
                                        premises = [(definition,
                                          P.source block index)]}
                                   else select rest
                               | NONE => select rest end
                      val result = select dependencies
                      val _ = guard ()
                    in result end
                | BoundNnfLaw {target,law,index,hypotheses} =>
                    R.apply_law graph block
                      {law = (law,P.source block index),target = target,
                       premises = List.map (fn (node,index) =>
                         (node,P.source block index)) hypotheses}
                | Lemma {target,body,assumptions,law,index} =>
                    let
                      val theorem = case completed_lemma of SOME proof => proof
                        | NONE => raise Fail "missing completed local lemma"
                      val _ = if Portable.pointer_eq (Thm.concl theorem,
                          G.representative graph law) then () else
                        raise ERR "lemma" "wrong completed lemma endpoint"
                      val _ = witnesses := Redblackmap.insert
                        (!witnesses,G.node_id law,theorem)
                    in R.apply_law graph block
                      {law = (law,P.source block index),target = target,
                       premises = List.map (fn node =>
                         (node,P.source block (assumption node)))
                         local_assumptions} end
                | Resolution {target,premises = ids} =>
                    let
                      val layouts = List.map clause ids
                      val facts = ListPair.map (fn (layout,id) =>
                        C.from_source block layout (edge id)) (layouts,ids)
                      fun pivot layout = case C.recorded layout of
                          [{atom,negative}] => {atom = atom,negative = not negative}
                        | _ => raise ERR "unit_resolution"
                            "resolving premise is not one recorded literal"
                      val pivots = List.map pivot (List.tl layouts)
                      val result = case C.resolve_chain
                          {pivots = pivots,premises = facts,
                           target = SOME (clause id)} of
                          SOME result => result
                        | NONE => raise ERR "unit_resolution"
                            "recorded literal resolution failed"
                    in C.to_target (clause id) result end)
            in edges := Redblackmap.insert (!edges,id,result) end
          val _ = List.app assemble (List.rev (!order))
          val _ = case output of NONE => () | SOME _ =>
            (case G.view graph target of G.Constant _ =>
               if Term.same_const (G.representative graph target) boolSyntax.F
               then () else raise ERR "lemma" "premise is not a contradiction"
             | _ => raise ERR "lemma" "premise is not a contradiction")
          val discharge = case completion of BinderEquality _ => false
            | Pointwise => false
            | Ordinary _ => not (List.null local_assumptions)
          val (block,closed,edge) = if not discharge then
              (block,target,edge root)
            else
              let val result = case owned of NONE =>
                    P.discharge_sources block
                      {indices = List.map assumption local_assumptions,
                       body = target,edge = edge root}
                  | SOME {work,...} =>
                    let
                      val validation = case preprocessing of
                          SOME {validation,...} => validation
                        | NONE => raise ERR "owned_discharge" "missing GP"
                      val prefix = gp_sources validation
                      val first = List.length prefix
                      val locals = List.drop (initial_sources,first)
                      val rows = ListPair.zip (locals,List.tabulate
                        (List.length locals,fn i => first+i))
                      fun choose [] used = []
                        | choose (node::rest) used =
                          (case List.find (fn (held,index) =>
                              held = node andalso not (List.exists (fn old => old = index) used))
                              rows of
                            SOME (_,index) => index :: choose rest (index::used)
                          | NONE => raise ERR "owned_discharge"
                              "local occurrence is outside retained slots")
                      val indices = choose local_assumptions []
                      val _ = frame_guard current_frame scope
                    in P.discharge_sources_with_work work block
                      {indices = indices,body = target,edge = edge root} end
              in (#block result,#target result,#edge result) end
          val edge = if closed = desired then edge else
            owned_action current_frame scope (fn () =>
              R.boolean_rule graph block desired [(closed,edge)])
          fun supply (_,node) =
            Redblackmap.peek (!witnesses,G.node_id node)
          val (block,edge,environment,closed_images) =
            case (ground_owner,owned) of
              (SOME _,SOME {work,...}) =>
                let
                  val indices = P.needed_source_occurrences_with_work
                    work block edge
                  val slots = P.sources block
                  val actual = List.map (fn index => List.nth (slots,index))
                    indices
                  val original = case preprocessing of
                      SOME {validation,...} => gp_sources validation
                    | NONE => raise ERR "ground_definition" "missing GP"
                  val resolution = owned_action current_frame scope (fn () =>
                    let
                      (* The authentic receipts precede E's scalar metadata.
                         No name/occurrence is inferred from proof spelling. *)
                      val definitions = List.map (fn (owner,receipt) =>
                        SmtReplayOwnedZ3GroundDefinition.description_for
                          work owner receipt) (List.rev (!ground_receipts))
                      val dependencies = case equation_mode of
                          PublicGround => []
                        | PrivateDependent => List.concat
                            (List.map (fn (owner,receipt) =>
                              GD.private_dependencies_for work owner receipt)
                              (List.rev (!ground_receipts)))
                      (* Dependencies are authentic retained paths only;
                         only executed LHS names authorize E assignments. *)
                      val names = List.foldl (fn (data,names) =>
                        if List.exists (fn old => old = #name data) names
                        then names else names @ [#name data]) [] definitions
                      val _ = List.app (fn _ =>
                        SmtReplayInvocationWork.spend work 1)
                        (slots @ actual @ names @ dependencies)
                      val plan = E.prepare graph
                        {scope = scope,allocated = names,
                         sources = slots,needed = actual,
                         roots = desired :: !roots}
                    in resolved (E.resolve_needed_with_closed_sources plan
                      {preserved = desired :: original,laws = []}) end)
                  val final = P.refreeze_needed_sources_with_work work block
                    {roots = SmtReplayResolve.roots resolution,
                     target = desired,edge = edge}
                in (#block final,#edge final,SOME resolution,[]) end
            | _ => if not needed_route then
                (block,edge,environment,closed_images)
            else
              let
                val actual = P.needed_sources_using block edge supply
                val ground_laws = if not use_ground then [] else
                  let
                    val recorded = List.rev (!recorded_indices)
                    val needed_indices = Redblackset.addList
                      (Redblackset.empty Int.compare,
                       P.needed_source_occurrences block edge)
                    val definition_nodes = List.map
                      (fn (_,_,node,_) => node) recorded
                    val definition_needed = List.mapPartial
                      (fn (_,_,node,index) =>
                        if Redblackset.member (needed_indices,index)
                        then SOME node else NONE) recorded
                    val prepare = case recorded_law of NONE =>
                        SmtReplayGroundDefinitions.prepare graph
                      | SOME _ => fn args =>
                          SmtReplayGroundDefinitions.prepare_recorded graph
                            {scope = #scope args,allocated = #allocated args,
                             sources = #sources args,
                             needed = definition_needed,
                             definitions = definition_nodes,limit = #limit args}
                    val ground_plan = prepare
                      {scope = scope,allocated = List.filter (fn node =>
                         case G.view graph node of
                           G.Variable (G.SolverFlexible,_) => true | _ => false)
                         (#vars proof),sources = source_nodes,
                       needed = #needed actual,
                       limit = SmtResource.max_bv_replay_term_nodes}
                    val types = SmtWordGraph.new_type_admission ()
                  in SmtReplayGroundDefinitions.execute ground_plan
                    {check_type = SmtWordGraph.admit_primitive_type types} end
                val _ = retain_reflexive ground_laws
                val actual_laws = #laws actual @ ground_laws
                val needed_indices = Redblackset.addList
                  (Redblackset.empty Int.compare,
                   P.needed_source_occurrences block edge)
                val definition_needed = case recorded_law of NONE =>
                    #needed actual
                  | SOME _ => List.mapPartial (fn (_,_,node,index) =>
                      if Redblackset.member (needed_indices,index)
                      then SOME node else NONE) (List.rev (!recorded_indices))
                val plan = definition_plan definition_needed
                val checked = if use_variable_witnesses then
                    SOME (checked_variables plan actual_laws true)
                  else NONE
                val packed = if not use_packed_scc then NONE else
                  let
                    val (_,allocated) = List.foldl
                      (fn (node,(seen,nodes)) => case G.view graph node of
                        G.Variable (G.SolverFlexible,_) =>
                          if Redblackset.member (seen,G.node_id node) then
                            (seen,nodes)
                          else (Redblackset.add (seen,G.node_id node),
                            node :: nodes)
                      | _ => (seen,nodes))
                      (Redblackset.empty Int.compare,[]) (#vars proof)
                    val allocated = List.rev allocated
                    val types = SmtWordGraph.new_type_admission ()
                    val producer = if use_fresh_bits then
                        SmtReplayPackedSCC.resolve_with_fresh_bits
                      else SmtReplayPackedSCC.resolve
                  in SOME (producer graph
                    {scope = scope,allocated = allocated,
                     sources = source_nodes,needed = #needed actual,
                     roots = desired :: !roots,preserved = [desired],
                     laws = actual_laws,admission = {metric = G.RawNodes,
                       limit = SmtResource.max_bv_replay_term_nodes,
                       check_type = SmtWordGraph.admit_primitive_type types}})
                  end
                val (resolution,packed_images) = case packed of
                    SOME (SmtReplayPackedSCC.Resolved result) =>
                      (#resolution result,#images result)
                  | SOME _ => raise ERR "remove_definitions"
                      "checked anchored packed SCC route declined"
                  | NONE => (resolved (case checked of
                      SOME result => #outcome result
                    | NONE => E.resolve_needed_with_closed_sources plan
                          {preserved = [desired],laws = actual_laws}),[])
                val reflexive_sources = case checked of NONE => []
                  | SOME result => #reflexive_sources result
                val _ = retain_reflexive reflexive_sources
                val images = prepare_images resolution
                  (actual_laws @ reflexive_sources) @ packed_images
                val final = P.refreeze_needed_sources block
                  {roots = SmtReplayResolve.roots resolution,
                   target = desired,edge = edge}
              in (#block final,#edge final,SOME resolution,images) end
        in owned_action current_frame scope (fn () =>
          case completion of Ordinary _ =>
            {theorem = (case environment of NONE =>
                P.realize_with_sources block desired edge supply
              | SOME resolution => if use_closed_laws then
                  P.realize_resolved_with_closed_sources block resolution
                    desired edge closed_images supply
                else P.realize_resolved_with_sources
                  block resolution desired edge supply),
             hypotheses = []}
          | Pointwise =>
              let
                val nodes = P.sources block
                fun canonical hypothesis =
                  case List.find (fn node => Portable.pointer_eq
                      (hypothesis,G.representative graph node)) nodes of
                    SOME node => node
                  | NONE => raise ERR "nnf_bound"
                      "noncanonical pointwise source hypothesis"
                val hypotheses = List.concat (List.map (fn node =>
                  case supply (0,node) of NONE => [node]
                  | SOME theorem => List.map canonical (Thm.hyp theorem)) nodes)
                val _ = admit_nnf_terms (List.map (G.representative graph)
                  (desired :: hypotheses))
                val theorem = P.realize_with_sources block desired edge supply
              in {theorem = theorem,
                  hypotheses = List.map canonical (Thm.hyp theorem)} end
          | BinderEquality {parent_scope,variables,target} =>
              let
                val type_admission = SmtWordGraph.new_type_admission ()
                val limit = SmtResource.max_bv_replay_term_nodes
                val admission : SmtReplayBinder.admission =
                  {metric = G.RawNodes,input_limit = limit,
                   output_limit = limit,
                   check_type = SmtWordGraph.admit_primitive_type type_admission,
                   refuse = fn _ => SmtResource.check_term_size_for
                     "BitVector" "binder-opening" (limit+1)}
              in SmtReplayBinderEquality.close_equality_with_sources graph
                {scope = scope,parent_scope = parent_scope,
                 variables = variables,body = desired,target = target,
                 block = block,edge = edge,witnesses = SOME supply,
                 canonical_sources = canonical_sources,admission = admission,
                 close = fn () => ()} end)
        end
      val theorem = #theorem
        (complete original_frame scope (#root proof) [] (Ordinary NONE))
      val _ = (#close proof) ()
    in theorem end
    handle error => (((#close proof) () handle _ => ());raise error)

  fun replay_with_sources_using_packet ground_packet
      use_environment use_closed_laws use_needed use_variable_witnesses
      use_ground recorded_law use_packed_scc use_fresh_bits reconciliation
      preprocessing canonical_sources owned graph scope args =
    replay_with_sources_using_packet_mode PublicGround ground_packet
      use_environment use_closed_laws use_needed use_variable_witnesses
      use_ground recorded_law use_packed_scc use_fresh_bits reconciliation
      preprocessing canonical_sources owned graph scope args

  fun replay_with_sources_using_environment use_environment use_closed_laws
      use_needed use_variable_witnesses use_ground recorded_law
      use_packed_scc use_fresh_bits reconciliation preprocessing
      canonical_sources owned graph scope args =
    replay_with_sources_using_packet NONE use_environment use_closed_laws
      use_needed use_variable_witnesses use_ground recorded_law
      use_packed_scc use_fresh_bits reconciliation preprocessing
      canonical_sources owned graph scope args

  in
  fun replay_with_sources_using canonical_sources graph scope args =
    replay_with_sources_using_environment false false false false false
      NONE false false NONE NONE
      canonical_sources NONE
      graph scope args

  fun replay_with_definition_environment_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true false false false false
      NONE false false NONE NONE
      canonical_sources NONE
      graph scope args
  fun replay_with_closed_definition_sources_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true false false false
      NONE false false NONE NONE
      canonical_sources NONE
      graph scope args
  fun replay_with_needed_definition_sources_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true true false false
      NONE false false NONE NONE
      canonical_sources NONE
      graph scope args

  fun replay_with_checked_variable_definitions_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true false true false
      NONE false false NONE NONE
      canonical_sources NONE graph scope args
  fun replay_with_needed_checked_variable_definitions_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true true true false
      NONE false false NONE NONE
      canonical_sources NONE graph scope args

  fun replay_with_needed_ground_definition_sources_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true true true true
      NONE false false NONE NONE
      canonical_sources NONE graph scope args

  fun replay_with_recorded_definitions_using recorded_law
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true true true true
      (SOME recorded_law) false false NONE NONE
      canonical_sources NONE graph scope args

  (* Separate opt-in. All six existing selectors keep packed SCC false. *)
  fun replay_with_needed_packed_scc_sources_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true true false false
      NONE true false NONE NONE
      canonical_sources NONE graph scope args

  (* Missing per-bit equations become checked local obligations, not
     canonical Sources. The original packed selector remains conservative. *)
  fun replay_with_needed_fresh_packed_sources_using
      canonical_sources graph scope args =
    replay_with_sources_using_environment true true true false false
      NONE true true NONE NONE
      canonical_sources NONE graph scope args

  fun replay_with_beta_eta_sources_using graph scope
      {sources,proof,template_limit,local_law,nnf,views,admission} =
    replay_with_sources_using_environment false false false false false
      NONE false false
      (SOME (fn current => fn replay =>
        Z3_GraphSourceReconcile.prepare graph current
          {sources = sources,replay = replay,views = views,
           admission = admission})) NONE
      (SmtReplaySource.denied_goal_node sources ::
       SmtReplaySource.assumption_nodes sources) NONE graph scope
      {proof = proof,template_limit = template_limit,local_law = local_law,
       nnf = nnf}
  (* Exact opaque GP derivations, not a caller-provided assertion proof.
     The original occurrence prefix is used in every visible replay block. *)
  fun replay_with_preprocessed_sources_using graph scope
      {sources,preprocessing,proof,template_limit,local_law,nnf} =
    replay_with_sources_using_environment false false false false false
      NONE false false NONE (SOME
        {sources = sources,validation = preprocessing})
      (SmtLib_GraphPreprocess.source_nodes preprocessing) NONE graph scope
      {proof = proof,template_limit = template_limit,local_law = local_law,
       nnf = nnf}
    handle primary => (((#close proof) () handle _ => ());raise primary)
  (* Additive SAME-original-Work path. The parser packet remains checked
     by its owning Consumer; no Source, allowance or caller scope is minted. *)
  fun replay_with_preprocessed_sources_with_work_using work graph scope
      {sources,preprocessing,proof,template_limit,local_law,nnf} =
    let
      val original = SmtReplayInvocationWork.original_sources work
      val expected_graph = SmtReplaySource.owning_graph original
      val expected_scope = SmtReplaySource.owning_scope original
      val limits = SmtReplayInvocationWork.semantic_limits work
      val _ = if Portable.pointer_eq (graph,expected_graph) andalso
          scope = expected_scope andalso
          Portable.pointer_eq (sources,original) andalso
          #template_limit limits = template_limit then () else
        raise ERR "owned_preprocessing" "different original owner or cap"
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
      val _ = SmtLib_GraphPreprocess.validate_with_work work preprocessing
      val frame = SmtReplayOwnedScopeReceipt.root work
      val canonical = SmtLib_GraphPreprocess.source_nodes preprocessing
      val _ = SmtLib_GraphPreprocess.validate_with_work work preprocessing
    in replay_with_sources_using_environment false false false false false
      NONE false false NONE
      (SOME {sources = sources,validation = preprocessing}) canonical
      (SOME {work = work,frame = frame}) graph scope
      {proof = proof,template_limit = template_limit,local_law = local_law,
       nnf = nnf} end
    handle primary => (SmtReplayInvocationWork.close work;raise primary)
  (* Finite opt-in: actual packet/frame equations, no local proof callback.
     Existing general/default selectors continue through the NONE shim. *)
  fun replay_with_ground_definition_packet_with_work work graph scope
      {sources,preprocessing,packet,template_limit} =
    let
      val original = SmtReplayInvocationWork.original_sources work
      val expected_graph = SmtReplaySource.owning_graph original
      val expected_scope = SmtReplaySource.owning_scope original
      val limits = SmtReplayInvocationWork.semantic_limits work
      val _ = if Portable.pointer_eq (graph,expected_graph) andalso
          scope = expected_scope andalso
          Portable.pointer_eq (sources,original) andalso
          #template_limit limits = template_limit then () else
        raise ERR "ground_packet" "different original owner or cap"
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
      val _ = SmtLib_GraphPreprocess.validate_with_work work preprocessing
      val _ = if Portable.pointer_eq
          (SmtLib_GraphProof.graph packet,graph) andalso
          SmtLib_GraphProof.scope packet = scope andalso
          SmtLib_GraphProof.solver packet = "Z3" then () else
        raise ERR "ground_packet" "different actual parser packet"
      val proof = SmtLib_GraphProof.proof packet
      val frame = SmtReplayOwnedScopeReceipt.root work
      val canonical = SmtLib_GraphPreprocess.source_nodes preprocessing
      val _ = SmtLib_GraphPreprocess.validate_with_work work preprocessing
    in replay_with_sources_using_packet (SOME packet)
      false false false false false NONE false false NONE
      (SOME {sources = sources,validation = preprocessing}) canonical
      (SOME {work = work,frame = frame}) graph scope
      {proof = proof,template_limit = template_limit,
       local_law = fn _ => NONE,nnf = fn _ => NONE} end
    handle primary => (SmtReplayInvocationWork.close work;raise primary)
  (* Separate actual dependent equation operation. No legacy/default flag
     or public-ground selector is widened. Assignment needs executed names. *)
  fun replay_with_dependent_equation_packet_with_work work graph scope
      {sources,preprocessing,packet,template_limit} =
    let
      val original = SmtReplayInvocationWork.original_sources work
      val expected_graph = SmtReplaySource.owning_graph original
      val expected_scope = SmtReplaySource.owning_scope original
      val limits = SmtReplayInvocationWork.semantic_limits work
      val _ = if Portable.pointer_eq (graph,expected_graph) andalso
          scope = expected_scope andalso
          Portable.pointer_eq (sources,original) andalso
          #template_limit limits = template_limit then () else
        raise ERR "ground_packet" "different original owner or cap"
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
      val _ = SmtLib_GraphPreprocess.validate_with_work work preprocessing
      val _ = if Portable.pointer_eq
          (SmtLib_GraphProof.graph packet,graph) andalso
          SmtLib_GraphProof.scope packet = scope andalso
          SmtLib_GraphProof.solver packet = "Z3" then () else
        raise ERR "ground_packet" "different actual parser packet"
      val proof = SmtLib_GraphProof.proof packet
      val frame = SmtReplayOwnedScopeReceipt.root work
      val canonical = SmtLib_GraphPreprocess.source_nodes preprocessing
      val _ = SmtLib_GraphPreprocess.validate_with_work work preprocessing
    in replay_with_sources_using_packet_mode PrivateDependent (SOME packet)
      false false false false false NONE false false NONE
      (SOME {sources = sources,validation = preprocessing}) canonical
      (SOME {work = work,frame = frame}) graph scope
      {proof = proof,template_limit = template_limit,
       local_law = fn _ => NONE,nnf = fn _ => NONE} end
    handle primary => (SmtReplayInvocationWork.close work;raise primary)
  end

  fun replay_with_sources canonical_sources graph scope
      {proof,template_limit,local_law} =
    replay_with_sources_using canonical_sources graph scope
      {proof = proof,template_limit = template_limit,local_law = local_law,
       nnf = fn _ => NONE}

  fun replay graph scope args = replay_with_sources [] graph scope args

  fun check_contradiction graph scope
      {sources,proof,template_limit,local_law} =
    let
      val theorem = replay_with_sources
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in theorem end

  fun check_proof graph scope args =
    SmtReplaySource.close_contradiction (#sources args)
      (check_contradiction graph scope args)

  fun check_proof_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_sources_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end
  (* Explicit opt-in; legacy check_proof_using remains the false branch. *)
  fun check_proof_with_definition_environment_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_definition_environment_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end
  fun check_proof_with_closed_definition_sources_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_closed_definition_sources_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end
  fun check_proof_with_needed_definition_sources_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_needed_definition_sources_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_checked_variable_definitions_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_checked_variable_definitions_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_needed_checked_variable_definitions_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_needed_checked_variable_definitions_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_needed_ground_definition_sources_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_needed_ground_definition_sources_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_recorded_definitions_using graph scope
      {sources,proof,template_limit,local_law,recorded_law,nnf} =
    let
      val theorem = replay_with_recorded_definitions_using recorded_law
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_needed_packed_scc_sources_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_needed_packed_scc_sources_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_needed_fresh_packed_sources_using graph scope
      {sources,proof,template_limit,local_law,nnf} =
    let
      val theorem = replay_with_needed_fresh_packed_sources_using
        (SmtReplaySource.denied_goal_node sources ::
         SmtReplaySource.assumption_nodes sources) graph scope
        {proof = proof,template_limit = template_limit,local_law = local_law,
         nnf = nnf}
      val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end

  fun check_proof_with_beta_eta_sources_using graph scope args =
    let val theorem = replay_with_beta_eta_sources_using graph scope args
        val sources = #sources args
        val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end
  fun check_proof_with_preprocessed_sources_using graph scope
      (args as {sources,preprocessing,proof,template_limit,local_law,nnf}) =
    let val theorem = replay_with_preprocessed_sources_using graph scope args
        val _ = SmtReplaySource.check_contradiction sources theorem
    in SmtReplaySource.close_contradiction sources theorem end
  fun check_proof_with_preprocessed_sources_with_work_using work graph scope
      (args as {sources,preprocessing,proof,template_limit,local_law,nnf}) =
    let
      val theorem = replay_with_preprocessed_sources_with_work_using
        work graph scope args
      val limits = SmtReplayInvocationWork.semantic_limits work
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
      val _ = SmtReplaySource.check_contradiction sources theorem
      val result = SmtReplaySource.close_contradiction sources theorem
      val _ = SmtReplaySource.check_goal sources result
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
    in result end
    handle primary => (SmtReplayInvocationWork.close work;raise primary)

  fun check_proof_with_ground_definition_packet_with_work work graph scope
      (args as {sources,preprocessing,packet,template_limit}) =
    let
      val theorem = replay_with_ground_definition_packet_with_work
        work graph scope args
      val limits = SmtReplayInvocationWork.semantic_limits work
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
      val _ = SmtReplaySource.check_contradiction sources theorem
      val result = SmtReplaySource.close_contradiction sources theorem
      val _ = SmtReplaySource.check_goal sources result
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
    in result end
    handle primary => (SmtReplayInvocationWork.close work;raise primary)

  fun check_proof_with_dependent_equation_packet_with_work work graph scope
      (args as {sources,preprocessing,packet,template_limit}) =
    let
      val theorem = replay_with_dependent_equation_packet_with_work
        work graph scope args
      val limits = SmtReplayInvocationWork.semantic_limits work
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
      val _ = SmtReplaySource.check_contradiction sources theorem
      val result = SmtReplaySource.close_contradiction sources theorem
      val _ = SmtReplaySource.check_goal sources result
      val _ = SmtReplayInvocationWork.validate work graph scope sources limits
    in result end
    handle primary => (SmtReplayInvocationWork.close work;raise primary)

end
