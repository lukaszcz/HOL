(* Copyright (c) 2026 The HOL4 contributors. *)
structure CPC_GraphProofReplay :> CPC_GraphProofReplay =
struct
  local open CPC_GraphNativeReservation in end
  local open CPC_GraphOwnedResult SmtReplayResolve in end
  exception OwnedEndpointAdapter = CPC_GraphOwnedResult.Adapter
  open SmtReplayGraph SmtReplayProof SmtReplaySource SmtReplayClause
       SmtReplayRules SmtReplayCanonGraph SmtLib_GraphFrontend
       CPC_ProofParser CPC_Proof SmtRegLanProve SmtReplaySupport
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure C = SmtReplayClause
  structure R = SmtReplayRules
  structure K = SmtReplayCanonGraph
  structure F = SmtLib_GraphFrontend
  structure Q = CPC_ProofParser
  structure GP = SmtLib_GraphPreprocess
  structure W = SmtReplayInvocationWork
  structure SI = SmtReplayImport
  val _ = SmtReplayProof.discharge_sources_with_work
  val _ = SmtLib_GraphPreprocess.assembler_with_work
  structure S = SmtLib_Parser
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphProofReplay"
  type worker = CPC_Proof.step * CPC_Proof.located_term list ->
    Thm.thm * CPC_Proof.located_term
  type clause_worker = CPC_Proof.step * CPC_Proof.located_term list ->
    {theorem:Thm.thm,located:CPC_Proof.located_term,
     clause:SmtClause.owned_witness option}
  datatype producer_origin_gap = OriginTemplateQuota | OriginHypAlignment
  type producer_origin =
    {serial : int,target : SmtReplayGraph.node,
     equation : SmtReplayGraph.node * SmtReplayGraph.node,
     law_node : SmtReplayGraph.node,law : Thm.thm,
     checked_local_law : Thm.thm,
     premises : {index : int,node : SmtReplayGraph.node,
                 command_occurrence : int option} list,
     actual_hypotheses : int list,
     support_indices : (int * int) list,
     support : SmtReplaySupport.certificate,
     deferred : SmtReplayGraph.node option}
  datatype worker_event =
      CommandBegin of {serial : int,command : CPC_ProofParser.graph_command}
    | CommandEnd of {serial : int,node : SmtReplayGraph.node,
                     provenance : CPC_Proof.term_provenance}
    | CheckedLocalLaw of {serial : int,law : Thm.thm}
    | CheckedProducerOrigin of producer_origin
    | ProducerOriginUnavailable of {serial : int,gap : producer_origin_gap}
    | ForcedBegin of {serial : int,step : CPC_Proof.step}
    | ForcedEnd of {serial : int,theorem : Thm.thm,
                    located : CPC_Proof.located_term}
    | ForcedAbort of {serial : int}
    | InvocationEnd
    | InvocationAbort
  type observer = worker_event -> unit
  type observed_statistics =
    {nodes : G.node_statistics,proofs : P.proof_statistics,
     schemas : SmtReplayCanonGraph.schema_statistics,
     assembly_hits : IntInf.int,assembly_misses : IntInf.int}
  datatype assembly_observation = AssemblyObservation of
    {graph : G.graph,hits : IntInf.int ref,misses : IntInf.int ref}
  val assembly_observation = ref (NONE : assembly_observation option)
  fun observe_assembly graph hit = case !assembly_observation of NONE => ()
    | SOME (AssemblyObservation fields) =>
        if Portable.pointer_eq (graph,#graph fields) then
          let val cell = if hit then #hits fields else #misses fields
          in cell := !cell+1 end else ()
  type direct_deferred_request =
    {serial : int,step : CPC_Proof.step,target : G.node,
     theorem : Thm.thm,located : CPC_Proof.located_term,
     hypothesis : Term.term}
  type direct_deferred = direct_deferred_request -> unit option
  type owned_force_request =
    {serial : int,target : SmtReplayGraph.node,step : CPC_Proof.step,
     premises : CPC_Proof.located_term list}
  type owned_force_worker = owned_force_request ->
    Thm.thm * CPC_Proof.located_term
  type completion_request =
    {root : SmtReplayGraph.node,
     mandatory : {serial : int,target : SmtReplayGraph.node} list}
  type completion_result =
    {resolution : SmtReplayResolve.resolution,contradiction : Thm.thm,
     witnesses : {serial : int,original : SmtReplayGraph.node,
       target : SmtReplayGraph.node,witness : Thm.thm} list}
  type completion = completion_request -> completion_result option
  type owned_completion_request =
    {root : SmtReplayGraph.node,
     mandatory : {serial : int,target : SmtReplayGraph.node} list,
     prove : SmtReplayGraph.node -> Thm.thm}
  type owned_completion = owned_completion_request -> completion_result option
  exception ObserverFailure of exn
  exception NativeCompletionAdapter
  exception OriginGap of producer_origin_gap
  type fact =
    {node : G.node, provenance : term_provenance,
     clause : C.occurrences option}
  datatype step = Step of
    {serial : int, fact : fact, premises : step list, recipe : recipe,
     pruned : bool}
  and recipe = Assumption | PreprocessedSource | Equality of string
    | Transitivity | Boolean
    | BooleanSchemas of K.graph_conversion list
    | BooleanAliases of K.graph_conversion list
    | OwnedNegatedSymmetry of K.graph_conversion
    | OwnedAliasTransitivity of
        {premises : K.graph_conversion list,target : K.graph_conversion}
    | Resolution of C.literal list | Alignment
    | ClosedLaw of G.node * Thm.thm *
        (G.node * Thm.thm * step list) option
    | ObligationLaw of
        {obligation : G.node,law : G.node,theorem : Thm.thm,
         selected : (G.node * Thm.thm * step list) option}
    | NativeObligation of CPC_GraphNativeReservation.origin
    | Scope of {hypothesis : G.node, body : step}
  fun fact (Step {fact,...}) = fact
  fun serial (Step {serial,...}) = serial
  fun node step = #node (fact step)
  fun premise_list (Step {recipe=ClosedLaw (_,_,SOME (_,_,selected)),...}) =
        selected
    | premise_list (Step {recipe=ObligationLaw
        {selected=SOME (_,_,selected),...},...}) = selected
    | premise_list (Step {premises,...}) = premises
  fun pruned (Step {pruned,...}) = pruned
  fun recorded_recipe (Step {recipe,...}) = recipe
  fun recipe step = case recorded_recipe step of
      ClosedLaw (_,_,SOME (law,proof,_)) => ClosedLaw (law,proof,NONE)
    | ObligationLaw {obligation,selected=SOME (law,proof,_),...} =>
        ObligationLaw {obligation=obligation,law=law,theorem=proof,
          selected=NONE}
    | original => original
  fun pair_compare ((a,b),(c,d)) = case Int.compare (a,c) of
      EQUAL => if b = d then EQUAL else if b then GREATER else LESS
    | order => order
  fun literal_key ({atom,negative} : C.literal) = (G.node_id atom,negative)
  fun same_literal left right = literal_key left = literal_key right
  fun same_constant graph node constant = case G.view graph node of
      G.Constant _ => Term.same_const (G.representative graph node) constant
    | _ => false
  fun negate graph scope node =
    G.application graph scope (G.constant graph scope boolSyntax.negation,node)
  fun binary graph scope operator (left,right) =
    G.application graph scope
      (G.application graph scope (G.constant graph scope operator,left),right)
  fun equality graph scope (left,right) =
    let val marker = Term.genvar (G.type_of graph left)
        val operator = Term.rator (Term.rator
          (boolSyntax.mk_eq (marker,marker)))
    in binary graph scope operator (left,right) end
  fun conjunction graph scope nodes = CPC_SharedReplayPlan.conjunction
    {visit=fn()=>(),truth=fn()=>G.constant graph scope boolSyntax.T,
     binary=binary graph scope boolSyntax.conjunction} nodes
  fun negated graph node = case R.operands graph boolSyntax.negation 1 node of
      SOME [body] => SOME body | _ => NONE
  fun opposite ({atom,negative} : C.literal) : C.literal =
    {atom = atom,negative = not negative}
  fun operands graph operator count node =
    case R.operands graph operator count node of SOME nodes => nodes
      | NONE => raise ERR "discover" "incorrect rule operand constructor"

  (* Only the recorded immediate occurrence boundary authorizes flattening.
     Compound aliases stay atomic even when their graph values are ORs. *)
  val occurrence_provenance=CPC_SharedReplayPlan.occurrence_provenance
  fun recorded graph = CPC_SharedReplayPlan.recorded (R.operands graph)
  fun clause graph scope root provenance =
    let
      val nodes = case provenance of
          ApplicationProvenance ("or",children) =>
            Option.map (fn nodes => ListPair.zip (nodes,children))
              (recorded graph boolSyntax.disjunction
                (List.length children) root)
        | UnavailableProvenance _ => NONE
        | AmbiguousProvenance _ => NONE
        | _ => SOME [(root,provenance)]
      fun entry (node,ApplicationProvenance ("not",[_])) =
            (case negated graph node of SOME atom =>
               {atom = atom,negative = true}
             | NONE => raise ERR "clause" "recorded NOT constructor differs")
        | entry (node,_) =
          (* A compound alias stays ONE literal. Its outer NOT is an actual
             graph constructor, as in SmtClause.occurrence; C.bridge checks
             that constructor before any resolution uses its signed operand.
             This never supplies erased OR/AND operand boundaries. *)
          (case negated graph node of SOME atom =>
             {atom = atom,negative = true}
           | NONE => {atom = node,negative = false})
      fun discover [(node,AtomicProvenance)] =
          if same_constant graph node boolSyntax.F then
            C.discover graph scope []
          else C.discover graph scope [entry (node,AtomicProvenance)]
        | discover nodes = C.discover graph scope (List.map entry nodes)
    in Option.map discover nodes end
  fun located_fact graph scope ({node,occurrence,...} : F.term) : fact =
    let val provenance = occurrence_provenance occurrence in
      {node = node,provenance = provenance,
       clause = clause graph scope node provenance} end
  fun graph_fact graph scope node provenance : fact =
    {node = node,provenance = provenance,
     clause = clause graph scope node provenance}
  val equality_provenance=CPC_SharedReplayPlan.equality_provenance
  fun child_provenance token count provenance =
    CPC_SharedReplayPlan.child_provenance
      {equal=op =,length=List.length,tabulate=List.tabulate}
      token count provenance
  fun negation_provenance provenance =
    hd (child_provenance "not" 1 provenance)
  fun clause_fact layout : fact =
    {node = C.root layout,provenance = UnavailableProvenance
      "recorded rule clause occurrences",clause = SOME layout}
  fun clause_of step = case #clause (fact step) of SOME layout => layout
    | NONE => raise ERR "discover" "missing recorded clause boundary"
  fun check_contradiction_observing_impl
      {graph,scope,sources,proof : Q.graph_proof,ordinary_limit,
       template_limit,worker : worker,force_worker : worker option,
       observer : observer,history_mode,check_type,
       completion : completion option,
       direct_deferred : direct_deferred option,
       owned_force_worker : owned_force_worker option,
       owned_completion : owned_completion option,
       native_reservation : ({serial : int,step : Q.graph_rule_step} ->
         CPC_GraphNativeReservation.origin option) option,
        preprocessing : GP.validation option,
        owned_work : W.portfolio option,
        clause_worker : clause_worker option} =
    let
      (* Read-only, opt-in diagnostics. Audit does not validate, debit or
         revive Work. Diagnostic failures never replace a replay result or
         its primary exception; the ordinary path does no diagnostic IO. *)
      val trace_work =
        OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS" = SOME "1"
      fun work_checkpoint phase describe =
        if not trace_work then () else
          ((case owned_work of NONE => () | SOME work =>
              let val {charged,retired} = W.audit work
              in TextIO.output (TextIO.stdErr,
                   "CPC_GRAPH_WORK phase=" ^ phase ^ " charged=" ^
                   Int.toString charged ^ " retired=" ^
                   Bool.toString retired ^ describe () ^ "\n");
                 TextIO.flushOut TextIO.stdErr
              end)
           handle _ => ())
      fun work_phase phase = work_checkpoint phase (fn () => "")
      val extended_mode = Option.isSome completion orelse
        Option.isSome direct_deferred orelse
        Option.isSome owned_force_worker orelse
        Option.isSome owned_completion orelse
        Option.isSome native_reservation
      fun notify event = observer event
        handle error => raise ObserverFailure error
      fun validate_owned work =
        let val original = W.original_sources work
            val limits = W.semantic_limits work
            (* Compare expected owner data before held Source/GP activation. *)
            val _ = if Portable.pointer_eq (sources,original) then () else
              raise ERR "owned_replay" "different original Sources"
            val owner = SmtReplaySource.owning_graph original
            val root = SmtReplaySource.owning_scope original
            val _ = if Portable.pointer_eq (graph,owner) andalso scope = root
                andalso #template_limit limits = template_limit then () else
              raise ERR "owned_replay" "different original replay frame"
            val _ = W.validate work owner root original limits
        in case preprocessing of SOME validation =>
             GP.validate_with_work work validation
           | NONE => raise ERR "owned_replay" "missing owned preprocessing" end
      fun action operation = case owned_work of NONE => operation ()
        | SOME work => (validate_owned work;W.with_step work operation)
      fun run () = let
      val _ = Option.app validate_owned owned_work
      val _ = G.validate_scope graph scope
      val _ = if ordinary_limit > 0 andalso template_limit > 0 then () else
        raise ERR "check_contradiction" "nonpositive replay admission limit"
      val canonical_sources = SmtReplaySource.assumption_nodes sources @
        [SmtReplaySource.denied_goal_node sources]
      val _ = List.app (fn node => ignore (G.type_of graph node))
        canonical_sources
      (* A processed assertion is a derived edge, never a new Source. *)
      val preprocessing_roots = case preprocessing of NONE => []
        | SOME validation =>
            let
              val _ = if Portable.pointer_eq
                  (GP.original_sources validation,sources) then () else
                raise ERR "preprocessing" "different original Source owner"
              val _ = case GP.template_limit validation of NONE => ()
                | SOME limit => if limit = template_limit then () else
                    raise ERR "preprocessing" "original GP cap differs"
              val roots = GP.roots validation
              val _ = List.app (fn node =>
                if G.scope_visible graph scope (G.node_scope graph node)
                then () else raise ERR "preprocessing"
                  "conversion root outside replay scope") roots
            in roots end
      val processed_sources = case preprocessing of NONE => []
        | SOME validation => GP.processed_assumptions validation @
            [GP.processed_denied_goal validation]
      val _ = List.app (fn node => ignore (G.type_of graph node))
        processed_sources
      val processed_ids = Redblackset.addList
        (Redblackset.empty Int.compare,List.map G.node_id processed_sources)
      val counter = ref 0
      val forced_counter = ref 0
      val known = ref (Redblackmap.mkDict String.compare)
      val pushes = ref []
      val generalizations = ref (Redblackmap.mkDict Int.compare)
      fun save id current =
        (known := Redblackmap.insert (!known,id,current);current)
      fun make id current premises recipe =
        let val index = !counter
            val _ = counter := index+1
            (* Scheduling metadata only. Propagate through Scope without
               importing its local inventory into the enclosing block. *)
            val selected = action (fn () =>
              let fun tick () = Option.app
                    (fn work => W.spend work 1) owned_work
                  fun any [] = (tick ();false)
                    | any (step::rest) =
                        (tick ();pruned step orelse any rest)
              in tick ();case recipe of
                  ClosedLaw (_,_,SOME _) => true
                | ObligationLaw {selected=SOME _,...} => true
                | Scope {body,...} => pruned body
                | _ => any premises end)
        in save id (Step {serial = index,fact = current,
              premises = premises,recipe = recipe,pruned = selected}) end
      fun find id = case Redblackmap.peek (!known,id) of SOME step => step
        | NONE => raise ERR "discover" ("unknown/scoped-out premise " ^ id)
      fun graph_terms arguments = List.mapPartial
        (fn Q.GraphTerm term => SOME term | _ => NONE) arguments
      fun term_arguments arguments = List.map (#node : F.term -> G.node)
        (graph_terms arguments)
      fun require_one where_ entries = case entries of [entry] => entry
        | _ => raise ERR where_ "expected one operand/premise"
      fun exact_target conclusion inferred = case conclusion of
          NONE => inferred
        | SOME target =>
            if #node target = #node inferred then
              located_fact graph scope target
            else raise ERR "discover" "declared rule endpoint differs"
      fun admission_failure message =
        let
          val metric = if ordinary_limit <
              SmtResource.max_bv_replay_term_nodes then ordinary_limit+1
            else SmtResource.max_bv_replay_term_nodes+1
          val _ = SmtResource.check_term_size_for
            "BitVector" "cpc-local-rule" metric
        in raise ERR "bounded_rule" message end
      fun admit term = case SmtReplayImport.bounded_raw_size
          ordinary_limit term of SOME _ => ()
        | NONE => admission_failure "ordinary input exceeds caller limit"
      fun admit_type_using observe ty =
        let fun visit [] _ = ()
              | visit (ty::rest) count =
                  (observe ();if count >= ordinary_limit then
                    admission_failure "ordinary type exceeds caller limit"
                  else visit ((if Type.is_vartype ty then [] else
                    #2 (Type.dest_type ty)) @ rest) (count+1))
        in visit [ty] 0 end
      val admit_type = admit_type_using (fn () => ())
      fun raw node = let val term = G.representative graph node in
        admit term;admit_type (Term.type_of term);term end
      fun legacy step : located_term =
        {term = raw (node step),provenance = #provenance (fact step)}
      fun argument (Q.GraphTerm value) : located_term =
            {term = raw (#node value),
             provenance = occurrence_provenance (#occurrence value)}
        | argument (Q.GraphIndex index) =
            {term = intSyntax.term_of_int (Arbint.fromInt index),
             provenance = AtomicProvenance}
        | argument _ = raise ERR "bounded_rule"
            "non-term argument needs a specialized bounded rule adapter"
      fun bounded (step : Q.graph_rule_step) premises =
        let
          val _ = work_checkpoint "bounded.enter" (fn () =>
            " step=" ^ #id step ^ " rule=" ^ #name (#rule step))
          val arithmetic_rule = String.isPrefix "arith"
              (#replay_handler (#rule step)) orelse
            String.isPrefix "arith-" (#name (#rule step)) orelse
            String.isPrefix "int_tight_" (#replay_handler (#rule step)) orelse
            (List.exists (fn handler =>
               handler = #replay_handler (#rule step))
               ["eq_resolve","modus_ponens","evaluate"] andalso
             SmtReplayArithmetic.has_numeric_operand graph scope
               {inputs=List.map node premises @ term_arguments (#args step) @
                  (case #conclusion step of NONE => []
                   | SOME value => [#node value]),
                observe=fn () => Option.app
                  (fn work => W.spend_guard_policy work 1) owned_work})
          fun arithmetic_charge amount = Option.app
            (fn work => W.spend_guard_policy work amount) owned_work
          fun arithmetic_observe () = arithmetic_charge 1
          fun selected_raw node = if not arithmetic_rule then raw node else
            let val term = G.representative graph node
                val _ = case
                    SmtReplayImport.bounded_raw_size_with_type_check_observed
                    {check_type=admit_type_using arithmetic_observe,
                     observe=arithmetic_observe,limit=ordinary_limit} term of
                    SOME _ => ()
                  | NONE => admission_failure
                      "ordinary input exceeds caller limit"
                val _ = admit_type_using arithmetic_observe
                  (G.type_of graph node)
            in term end
          val inputs = List.map (fn step =>
            {term=selected_raw (node step),
             provenance= #provenance (fact step)}) premises
          val arguments = List.map (fn value => case value of
              Q.GraphTerm term =>
                {term=selected_raw (#node term),
                 provenance=occurrence_provenance (#occurrence term)}
            | _ => argument value) (#args step)
          val conclusion = Option.map
            (fn value : F.term => {term = selected_raw (#node value),
              provenance = occurrence_provenance (#occurrence value)})
            (#conclusion step)
          val local_step : CPC_Proof.step =
            {id = #id step,rule = #rule step,premises = #premises step,
             conclusion = conclusion,args = arguments}
          fun ordinary local_step inputs =
            case (owned_work,clause_worker) of
              (SOME work,SOME fixed) =>
                let val _ = validate_owned work
                    val {theorem,located,clause} = fixed (local_step,inputs)
                    val _ = validate_owned work
                in (theorem,located,clause) end
            | _ => let val (theorem,located) = worker (local_step,inputs)
                   in (theorem,located,NONE) end
          val arithmetic_node = ref (NONE : G.node option)
          fun arithmetic () =
            let
              val retained = ref (NONE : (int list * term_provenance) option)
              val target_nodes = case #conclusion step of NONE => []
                | SOME value => [#node value]
              val premise_nodes = List.map node premises
              val input_nodes = target_nodes @ premise_nodes @
                term_arguments (#args step)
              fun located old term : located_term =
                {term = term,provenance = #provenance old}
              fun procedure terms =
                let
                  val (targets,rest) =
                    Lib.split_after (length target_nodes) terms
                  val (pts,args) = Lib.split_after (length premises) rest
                  val remaining = ref args
                  fun argument (value,original) = case value of
                      Q.GraphTerm _ =>
                        (case !remaining of term::rest =>
                           (remaining := rest;located original term)
                         | [] => raise ERR "arithmetic" "missing argument")
                    | _ => original
                  val args = ListPair.mapEq argument (#args step,arguments)
                  val local_step : CPC_Proof.step =
                    {id = #id step,rule = #rule step,
                     premises = #premises step,args = args,
                     conclusion = case (targets,conclusion) of
                       ([],NONE) => NONE
                     | ([term],SOME original) => SOME (located original term)
                     | _ => raise ERR "arithmetic" "changed target arity"}
                  val (theorem,result,_) = ordinary local_step
                    (ListPair.mapEq (fn (old,term) => located old term)
                      (inputs,pts))
                  val hypotheses = Thm.hypset theorem
                  val seen = ref Term.empty_tmset
                  val used = List.filter (fn (_,term) =>
                    if HOLset.member (hypotheses,term) andalso
                        not (HOLset.member (!seen,term)) then
                      (seen := HOLset.add (!seen,term);true)
                    else false) (Lib.enumerate 0 pts)
                  val _ = retained := SOME
                    (List.map #1 used,#provenance result)
                in List.foldr (fn ((_,term),proof) => Thm.DISCH term proof)
                     theorem used end
              val result = SmtReplayArithmetic.prove graph scope
                {inputs = input_nodes,template_limit = ordinary_limit,
                 observe = arithmetic_charge,procedure = procedure}
              val (used,provenance) = valOf (!retained)
              val body = List.foldl (fn (_,body) =>
                case R.operands graph boolSyntax.implication 2 body of
                  SOME [_,result] => result
                | _ => raise ERR "arithmetic" "changed conditional schema")
                (#node result) used
              val _ = arithmetic_node := SOME body
              val theorem = List.foldl (fn (index,proof) =>
                Thm.MP proof (Thm.ASSUME (#term (List.nth (inputs,index)))))
                (#theorem result) used
            in (theorem,{term = Thm.concl theorem,provenance = provenance},
                NONE) end
          val (worker_theorem,worker_located,held_clause) =
            if arithmetic_rule then arithmetic () else
              ordinary local_step inputs
          val _ = work_checkpoint "bounded.after-worker" (fn () =>
            " step=" ^ #id step ^ " rule=" ^ #name (#rule step))
          val theorem = worker_theorem
          val located = worker_located
          val _ = Library.check_oracle_tags "CPC_GraphProofReplay"
            "bounded_rule" theorem
          val _ = List.app admit (Thm.concl theorem :: Thm.hyp theorem)
          fun ordinary_import () = case !arithmetic_node of
              SOME node =>
                let val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem)
                      (G.representative graph node)) theorem
                in (exact,graph_fact graph scope node
                    (#provenance located)) end
            | NONE =>
                let val imported = G.import graph scope ordinary_limit
                      (Thm.concl theorem)
                    val theorem = Thm.EQ_MP (#bridge imported) theorem
                in (theorem,graph_fact graph scope (#node imported)
                    (#provenance located)) end
          val retained = case #conclusion step of SOME value => SOME value
            | NONE => if #replay_handler (#rule step) = "trust" then
                (case #args step of [Q.GraphTerm value] => SOME value
                  | _ => NONE) else NONE
          val (theorem,current) = case retained of NONE => ordinary_import ()
            | SOME value =>
                if arithmetic_rule then
                  let val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem)
                        (G.representative graph (#node value))) theorem
                  in (exact,graph_fact graph scope (#node value)
                      (#provenance located)) end
                else if extended_mode andalso Portable.pointer_eq
                    (#term located,G.representative graph (#node value)) then
                  let val (checked,located) = CPC_GraphOwnedResult.align
                        {graph = graph,scope = scope,
                         ordinary_limit = ordinary_limit,target = #node value,
                         theorem = theorem,located = located,premises = inputs}
                  in (checked,graph_fact graph scope (#node value)
                      (#provenance located)) end
                else ordinary_import ()
          val current = exact_target (#conclusion step) current
          val ordinary_hypotheses = List.map
            (G.representative graph o node) premises
          fun premise hypothesis = List.exists
            (Term.aconv hypothesis) ordinary_hypotheses
          val extra = List.filter (not o premise) (Thm.hyp theorem)
          fun private variable = String.isPrefix "@fp."
            (#1 (Term.dest_var variable))
          fun deferred hypothesis =
            let
              val target = G.representative graph (#node current)
              val _ = if #replay_handler (#rule step) = "trust" then () else
                raise ERR "bounded_rule"
                  "local reconstruction retained hypotheses"
              val argument = case #args step of [Q.GraphTerm term] => term
                | _ => raise ERR "trust" "expected one recorded TRUST target"
              val _ = if #node argument = #node current then () else
                raise ERR "trust" "deferred TRUST changed its recorded target"
              val (variables,body) = boolSyntax.strip_forall hypothesis
              val free = Term.free_vars target
              fun same_variables () =
                List.length variables = List.length free andalso
                List.all (fn variable => List.exists
                  (Term.aconv variable) free) variables
              val direct = Term.aconv hypothesis target
              val _ = if direct then
                  if G.dag_nodes graph [#node current] > 256 orelse
                     List.null free orelse List.exists private free then ()
                  else if (case direct_deferred of NONE => false
                      | SOME checked => Option.isSome (checked
                          {serial = !counter,step = local_step,
                           target = #node current,theorem = worker_theorem,
                           located = worker_located,hypothesis = hypothesis}))
                    then ()
                  else raise ERR "trust" "wrong direct deferred hypothesis"
                else if not (List.null variables) andalso same_variables ()
                    andalso Term.aconv body target andalso
                    not (List.exists private free) then ()
                  else raise ERR "trust" "wrong universally closed obligation"
              val (obligation,transported) =
                if extended_mode andalso direct andalso
                    Portable.pointer_eq (hypothesis,target) then
                  (#node current,theorem)
                else
                  let val source =
                        G.import graph scope ordinary_limit hypothesis
                      val supplied = Thm.EQ_MP (Thm.SYM (#bridge source))
                        (Thm.ASSUME (G.representative graph (#node source)))
                  in (#node source,
                    Thm.MP (Thm.DISCH hypothesis theorem) supplied) end
              val _ = if direct then () else
                generalizations := Redblackmap.insert
                  (!generalizations,G.node_id obligation,
                   (variables,#node current))
            in (SOME obligation,transported) end
          val current = case (owned_work,held_clause) of
              (SOME work,SOME held) => action (fn () =>
                let
                  val _ = validate_owned work
                  val data = SmtClause.description_for work held
                  val _ = if Portable.pointer_eq
                      (#theorem data,worker_theorem) then () else
                    raise ERR "worker_clause"
                      "receipt does not describe this actual worker theorem"
                  fun import (entry :
                      {literal:Term.term,negative:bool,atom:Term.term}) =
                    let val raw = case SmtReplayImport.bounded_raw_size
                              ordinary_limit (#atom entry) of SOME n => n
                            | NONE => raise ERR "worker_clause"
                                "actual clause atom exceeds original cap"
                        val inclusive =
                          case SmtReplayImport.bounded_binder_size
                              ordinary_limit (#atom entry) of SOME n => n
                            | NONE => raise ERR "worker_clause"
                                "actual clause binder exceeds original cap"
                        val _ = W.spend work raw
                        val _ = W.spend work inclusive
                        val source = G.import graph scope ordinary_limit
                          (#atom entry)
                    in {atom = #node source,negative = #negative entry} end
                  val literals = List.map import (#occurrences data)
                  val layout = C.discover graph scope literals
                  val _ = if C.root layout = #node current then () else
                    raise ERR "worker_clause"
                      "actual ordered clause differs from canonical target"
                  val _ = validate_owned work
                in {node = #node current,provenance = #provenance current,
                    clause = SOME layout} end)
            | _ =>
                (* Arithmetic schemas no longer retain an expanded native
                   clause witness. The declared occurrence is the SAME
                   checked endpoint and supplies its original ordered clause
                   boundary, just as clause_from_located did in the worker.
                   It does not recover erased conjunction provenance. *)
                if arithmetic_rule then case #conclusion step of
                  SOME value =>
                    let val recorded = located_fact graph scope value
                    in {node = #node current,provenance = #provenance current,
                        clause = #clause recorded} end
                | NONE => current
                else current
          val (obligation,theorem) = case extra of
              [] => (NONE,theorem)
            | [hypothesis] => deferred hypothesis
            | _ => raise ERR "trust" "multiple unexplained deferred hypotheses"
          val nodes = List.map node premises @
            (case obligation of NONE => [] | SOME node => [node])
          val law = R.implication graph scope nodes (#node current)
          fun admit_law term = case SmtReplayImport.bounded_raw_size
              ordinary_limit term of SOME _ => ()
            | NONE => admission_failure "ordinary law exceeds caller limit"
          val _ = case G.unfolded_nodes graph G.RawNodes ordinary_limit law of
              SOME size => if size <= ordinary_limit then () else
                admission_failure "ordinary law exceeds caller limit"
            | NONE => admit_law (G.representative graph law)
          val closed = List.foldr (fn (node,theorem) =>
            Thm.DISCH (G.representative graph node) theorem) theorem nodes
          val _ = admit_law (Thm.concl closed)
          val _ = if List.null (Thm.hyp closed) then () else
            raise ERR "bounded_rule" "local reconstruction retained hypotheses"
          val closed = Thm.EQ_MP
            (Thm.ALPHA (Thm.concl closed) (G.representative graph law)) closed
          val _ = notify (CheckedLocalLaw
            {serial = !counter,law = closed})
          fun origin () =
            case R.equality graph (#node current) of
              NONE => ()
            | SOME equation =>
            let
              (* Exact actual kernel hypotheses select input occurrences.
                 Preserve the full recorded inventory separately. *)
              fun hypothesis term =
                let fun find [] _ = raise OriginGap OriginHypAlignment
                      | find (node :: rest) index =
                          if Portable.pointer_eq
                              (term,G.representative graph node) then index
                          else find rest (index+1)
                in find nodes 0 end
              val used = Listsort.sort Int.compare
                (List.map hypothesis (Thm.hyp theorem))
              val selected_nodes = List.map (fn index => List.nth (nodes,index))
                used
              val minimal = R.implication graph scope selected_nodes
                (#node current)
              val expected = G.representative graph minimal
              fun whole term =
                case
                  (SmtReplayImport.bounded_raw_size ordinary_limit term,
                   SmtReplayImport.bounded_binder_size ordinary_limit term) of
                  (SOME raw,SOME inclusive) => (raw,inclusive)
                | _ => raise OriginGap OriginTemplateQuota
              (* Strict pointer hypotheses and conclusion make this the
                 exact prospective DISCH result, before any new kernel work. *)
              val (right_raw,right_inclusive) = whole expected
              val _ = if 3+2*right_raw <= ordinary_limit andalso
                  3+2*right_inclusive <= ordinary_limit then ()
                else raise OriginGap OriginTemplateQuota
              val reachable = G.block_reachable graph
                (minimal :: #node current :: selected_nodes)
              val costs = List.mapPartial (fn node => case G.view graph node of
                  G.Constant _ => SOME 5 | G.Application _ => SOME 7
                | _ => NONE) reachable
              val context_size = if null costs then 1 else
                List.foldl (op +) 0 costs + 3*(length costs-1)
              val _ = if context_size+4+3*(length selected_nodes+1) <=
                  template_limit then () else
                raise OriginGap OriginTemplateQuota
              val _ = List.app (check_type o G.type_of graph) reachable
              val _ = G.validate_scope graph scope
              val conditional = List.foldr (fn (node,proof) =>
                Thm.DISCH (G.representative graph node) proof)
                theorem selected_nodes
              val (left_raw,left_inclusive) = whole (Thm.concl conditional)
              val _ = if left_raw = right_raw andalso
                  left_inclusive = right_inclusive then () else
                raise ERR "producer_origin" "prospective conditional changed"
              val conditional = Thm.EQ_MP
                (Thm.ALPHA (Thm.concl conditional) expected) conditional
              val _ = if null (Thm.hyp conditional) then () else
                raise ERR "producer_origin" "conditional law is not closed"
              val _ = Library.check_oracle_tags "CPC_GraphProofReplay"
                "producer_origin" conditional
              val certificate = SmtReplaySupport.discover graph scope
                {roots = [minimal],premises = selected_nodes @ [minimal],
                 target = #node current,template_limit = template_limit,
                 check_type = check_type,
                 prove = fn {constructor,premise,...} =>
                   let
                     fun apply [] cursor proof =
                           if cursor = #node current then proof else
                             raise ERR "producer_origin" "wrong conditional end"
                       | apply (index :: rest) cursor proof =
                           (case R.operands graph boolSyntax.implication 2
                               cursor of SOME [left,right] =>
                             if left = List.nth (selected_nodes,index) then
                               apply rest right
                                 (Thm.MP (Thm.EQ_MP (constructor cursor) proof)
                                   (premise index)) else
                                 raise ERR "producer_origin"
                                   "changed antecedent"
                            | _ => raise ERR "producer_origin"
                                "missing antecedent")
                   in apply (List.tabulate (length selected_nodes,fn i => i))
                     minimal (premise (length selected_nodes)) end}
              val recorded = Lib.mapi (fn index => fn step =>
                {index = index,node = node step,
                 command_occurrence = SOME (serial step)}) premises
              val recorded = recorded @ (case obligation of NONE => []
                | SOME node => [{index = length recorded,node = node,
                                 command_occurrence = NONE}])
            in notify (CheckedProducerOrigin
              {serial = !counter,target = #node current,equation = equation,
               law_node = minimal,law = conditional,checked_local_law = closed,
               premises = recorded,actual_hypotheses = used,
               support_indices = Lib.mapi (fn index => fn original =>
                 (index,original)) used,
               support = certificate,deferred = obligation}) end
          val _ = if history_mode then
              (origin () handle OriginGap gap => notify
                (ProducerOriginUnavailable {serial = !counter,gap = gap}))
            else ()
          (* Keep the recorded occurrence inventory and all worker/observer
             callbacks above unchanged. Only the checked bounded theorem's
             Hyp selects the law we will actually replay. A repeated premise
             is discharged once, not expanded into a long vacuous MP spine.
             This is local proof evidence, never caller dependency metadata;
             original Source pruning still uses compact Hyp in P's receipt. *)
          fun selection work =
            let
              fun spend amount = W.spend work amount
              (* Pay the syntax AND type incidences of each new comparison
                 or inference before invoking it. All operands are bounded
                 above already; no new size limit or unfolded graph walk. *)
              fun types ty =
                (spend 3;if Type.is_vartype ty then
                   spend (String.size (Type.dest_vartype ty))
                 else let val {Thy,Tyop,Args}=Type.dest_thy_type ty
                      in spend (String.size Thy+String.size Tyop);
                         List.app types Args end)
              fun quote term =
                (spend 3;types (Term.type_of term);
                 if Term.is_comb term then
                   let val (f,x)=Term.dest_comb term in quote f;quote x end
                 else if Term.is_abs term then
                   let val (v,b)=Term.dest_abs term in quote v;quote b end
                 else if Term.is_var term then
                   spend (String.size (#1 (Term.dest_var term)))
                 else let val {Thy,Name,...}=Term.dest_thy_const term
                      in spend (String.size Thy+String.size Name)end)
              val hypotheses = Thm.hyp theorem
              fun same left right =
                (spend 1;Portable.pointer_eq (left,right) orelse
                 (quote left;quote right;Term.aconv left right))
              fun used term = List.exists (same term) hypotheses
              fun choose [] _ answer =
                    List.foldl (fn (entry,rest) =>
                      (spend 2;entry::rest)) [] answer
                | choose (entry::rest) seen answer =
                    (spend 3;
                     if List.exists (fn held =>
                         (spend 1;node entry=held)) seen orelse
                         not (used (G.representative graph (node entry))) then
                       choose rest seen answer
                     else choose rest (node entry::seen) (entry::answer))
              val selected = choose premises [] []
              val selected_nodes = List.map (fn entry =>
                (spend 2;node entry)) selected
              val selected_nodes = case obligation of NONE => selected_nodes
                | SOME target => List.foldr (fn (entry,rest) =>
                    (spend 2;entry::rest)) [target] selected_nodes
              fun unchanged ([],[]) = (spend 1;true)
                | unchanged (a::more,b::rest) =
                    (spend 1;a=b andalso unchanged (more,rest))
                | unchanged _ = (spend 1;false)
            in if unchanged (selected_nodes,nodes) then
                (selected,law,closed)
              else
                let
                  (* The original bounded law also bounds each operand of
                     the TWO new graph Apps per selected antecedent. mk_comb
                     recomputes operand Types on both kernels: prepay those
                     four syntax/Type walks BEFORE graph construction, apart
                     from the graph's own table/recent-Type/scope fees. *)
                  fun inference () = List.app (fn _ =>
                    quote (Thm.concl closed)) [(),(),(),()]
                  val _ = List.app (fn _ => inference ()) selected_nodes
                  val target = G.implication_with_graph_debit graph scope
                    (W.spend_policy work) selected_nodes (#node current)
                  (* Separately pay DISCH/ALPHA/EQ_MP operands and results,
                     once per inference, not once per cap. *)
                  val _ = List.app (fn _ => inference ()) selected_nodes
                  val _ = inference () val _ = inference ()
                  val proof = List.foldr (fn (entry,proof) =>
                    Thm.DISCH (G.representative graph entry) proof)
                    theorem selected_nodes
                  val _ = if null (Thm.hyp proof) then () else
                    raise ERR "bounded_rule" "selected law retained hypotheses"
                  val proof = Thm.EQ_MP
                    (Thm.ALPHA (Thm.concl proof)
                      (G.representative graph target)) proof
                in (selected,target,proof) end
            end
          val selected = case owned_work of NONE => NONE
            | SOME work => action (fn () =>
                let val (premises,target,proof) = selection work
                in if target=law then NONE else SOME (target,proof,premises)
                end)
          val route = case obligation of NONE =>
                ClosedLaw (law,closed,selected)
            | SOME obligation => ObligationLaw
                {obligation=obligation,law=law,theorem=closed,
                 selected=selected}
        in (current,route) end
      fun pivot_arguments arguments =
        CPC_SharedReplayPlan.pivot_arguments List.length ListPair.mapEq
          same_constant graph Lib.I ERR arguments
      fun erase literal [] = NONE
        | erase literal (head::rest) =
            CPC_SharedReplayPlan.erase_present
              same_literal Option.map erase literal head rest
      fun resolution (step : Q.graph_rule_step) premises =
        let
          val annotations = pivot_arguments (#args step)
          val clauses = List.map (C.recorded o clause_of) premises
          fun join left right pivot =
            CPC_SharedReplayPlan.resolution_join erase opposite (op @)
              ERR "resolution" left right pivot
          fun dynamic left right =
            CPC_SharedReplayPlan.resolution_dynamic List.find List.exists
              same_literal opposite ERR left right
          fun chain current remaining annotations pivots =
            CPC_SharedReplayPlan.resolution_chain join dynamic List.rev
              chain ERR current remaining annotations pivots
          val (literals,pivots) = case clauses of first::rest =>
              chain first rest annotations []
            | [] => raise ERR "resolution" "empty resolution chain"
          val layout = C.discover graph scope literals
          val current = case #conclusion step of
              NONE => clause_fact layout
            | SOME target => located_fact graph scope target
          val _ = case #clause current of SOME _ => ()
            | NONE =>
              raise ERR "resolution" "target lacks exact clause boundary"
        in (current,Resolution pivots) end
      (* chain_m_resolution has an actual destination followed by TWO
         recorded parallel lists. These are not binary polarity/pivot args.
         Every chain pivot is explicit; no complementary-pivot search runs. *)
      fun recorded_chain_resolution (step : Q.graph_rule_step) premises =
        action (fn () =>
        let
          fun observe () = case owned_work of NONE => ()
            | SOME work => W.spend work 1
          val (target,polarities,atoms) = case #args step of
              [Q.GraphTerm target,Q.GraphList polarities,Q.GraphList atoms] =>
                (target,polarities,atoms)
            | _ => raise ERR "chain_m_resolution"
                "expected actual target and two recorded pivot lists"
          val count = List.length premises-1
          val _ = observe ()
          val _ = if count >= 0 andalso List.length polarities = count andalso
              List.length atoms = count then () else
            raise ERR "chain_m_resolution" "recorded pivot count differs"
          fun signed pair = CPC_SharedReplayPlan.recorded_pivot
            observe same_constant G.type_of graph Lib.I negated ERR pair
          val annotations = ListPair.mapEq signed (polarities,atoms)
          val clauses = List.map (fn premise =>
            (observe ();C.recorded (clause_of premise))) premises
          fun join left right pivot = case
              (erase pivot left,erase (opposite pivot) right) of
              (SOME left,SOME right) => left @ right
            | _ => raise ERR "chain_m_resolution"
                "explicit pivot is absent from recorded clauses"
          fun chain current remaining annotations =
            CPC_SharedReplayPlan.recorded_resolution_chain
              observe join chain ERR current remaining annotations
          val literals = case clauses of first::rest =>
                chain first rest annotations
            | [] => raise ERR "chain_m_resolution" "empty actual premise chain"
          val _ = observe ()
          val _ = ignore (C.discover graph scope literals)
          val current = located_fact graph scope target
          val _ = case #conclusion step of NONE => ()
            | SOME declared => if #node declared = #node target then () else
                raise ERR "chain_m_resolution"
                  "declared destination differs from recorded target"
          val _ = case #clause current of SOME _ => ()
            | NONE => raise ERR "chain_m_resolution"
                "destination has no exact recorded clause boundary"
        in (current,Resolution annotations) end)
      fun align (step : Q.graph_rule_step) premises =
        let
          val source = clause_of (require_one "alignment" premises)
          val current = case #conclusion step of
              SOME target => located_fact graph scope target
            | NONE => case graph_terms (#args step) of
                [target] => located_fact graph scope target
              | _ =>
                  if #replay_handler (#rule step) = "factoring" then
                    let
                      fun unique [] _ = []
                        | unique (literal::rest) seen =
                            if Redblackset.member (seen,literal_key literal)
                            then unique rest seen else literal :: unique rest
                              (Redblackset.add (seen,literal_key literal))
                    in clause_fact (C.discover graph scope
                      (unique (C.recorded source)
                        (Redblackset.empty pair_compare))) end
                  else raise ERR "alignment" "missing recorded target"
        in (current,Alignment) end
      fun aggregate_entries operator token node provenance =
        let
          fun children (ConjunctionProvenance (_,entries)) =
                if token = "and" then SOME entries else NONE
            | children (ApplicationProvenance (head,entries)) =
                if head = token then SOME entries else NONE
            | children _ = NONE
        in CPC_SharedReplayPlan.aggregate_entries
          {children=children,recorded=recorded graph operator,
           length=List.length,push=fn {node,provenance}=>fn result=>
             (node,provenance)::result,reverse=List.rev,
           start=fn(nodes,entries,pending)=>
             ListPair.zip(nodes,entries) @ pending,
           initial=fn(node,provenance)=>[(node,provenance)],
           check=fn count=>if count >= template_limit then
             raise ERR "discover" "recorded aggregate exceeds template limit"
             else (),error=ERR "discover"} node provenance end
      fun cnf (step : Q.graph_rule_step) premises =
        let
          val _ = if List.null premises then () else
            raise ERR "cnf" "CNF producer expects no premises"
          val argument = case #args step of Q.GraphTerm term::_ => term
            | _ => raise ERR "cnf" "missing graph operand"
          val root = #node argument
          val _ = if Type.compare (G.type_of graph root,Type.bool) = EQUAL
            then () else raise ERR "cnf" "non-Boolean CNF operand"
          val provenance = occurrence_provenance (#occurrence argument)
          val schemas = ref ([] : K.graph_conversion list)
          val whole = (root,provenance)
          fun positive (node,ApplicationProvenance ("not",[_])) : C.literal =
                (case negated graph node of SOME atom =>
                   {atom = atom,negative = true}
                 | NONE => raise ERR "cnf" "recorded negation differs")
            | positive (atom,_) = {atom = atom,negative = false}
          fun negative (atom,_) : C.literal = {atom = atom,negative = true}
          fun fixed operator count =
            let
              val _ = case #args step of [Q.GraphTerm _] => ()
                | _ => raise ERR "cnf" "incorrect fixed CNF argument count"
              val nodes = operands graph operator count root
              val _ = List.app (fn node =>
                if Type.compare (G.type_of graph node,Type.bool) = EQUAL
                then () else raise ERR "cnf" "non-Boolean CNF child") nodes
              val children = case provenance of
                  EqualityProvenance (left,right) => [left,right]
                | ApplicationProvenance (_,entries) =>
                    if List.length entries = count then entries else
                      List.tabulate (count,fn _ => AtomicProvenance)
                | _ => List.tabulate (count,fn _ => AtomicProvenance)
            in ListPair.zip (nodes,children) end
          fun binary_nodes operator = case fixed operator 2 of
              [left,right] => (left,right)
            | _ => raise Fail "binary CNF operands"
          fun indexed operator token =
            let
              val index = case #args step of
                  [Q.GraphTerm _,Q.GraphIndex index] => index
                | _ => raise ERR "cnf" "expected aggregate and index"
              val entries = aggregate_entries operator token root provenance
            in List.nth (entries,index)
              handle Subscript => raise ERR "cnf" "aggregate index out of range"
            end
          fun aggregate operator token =
            (case #args step of [Q.GraphTerm _] => ()
              | _ => raise ERR "cnf" "incorrect aggregate argument count";
             aggregate_entries operator token root provenance)
          fun xor_nodes () =
            let
              val operator = Term.prim_mk_const {Thy = "HolSmt",Name = "xor"}
              val (left,right) = binary_nodes operator
              val x = Term.genvar Type.bool
              val y = Term.genvar Type.bool
              val theorem = Conv.REWR_CONV HolSmtTheory.xor_def
                (Term.list_mk_comb (operator,[x,y]))
              val schema = K.checked_graph_schema graph scope
                {theorem = theorem,holes = [x,y],operands = [#1 left,#1 right],
                 template_limit = template_limit}
              val conversion = K.graph_conversion graph scope false
                (fn node => if node = root then SOME schema else NONE) root
              val _ = schemas := [conversion]
            in (left,right) end
          fun ite_nodes () = case fixed boolSyntax.conditional 3 of
              [condition,yes,no] => (condition,yes,no)
            | _ => raise Fail "conditional CNF operands"
          val literals = CPC_SharedReplayPlan.cnf_literals
            binary_nodes indexed aggregate xor_nodes ite_nodes
            positive negative List.map ERR (#name (#rule step)) whole
          val current = exact_target (#conclusion step)
            (clause_fact (C.discover graph scope literals))
        in (current,if List.null (!schemas) then Boolean
                    else BooleanSchemas (!schemas)) end
      fun simple (step : Q.graph_rule_step) premises =
        let
          val handler = #replay_handler (#rule step)
          val arguments = term_arguments (#args step)
          val premise_nodes = List.map node premises
          fun current node provenance = graph_fact graph scope node provenance
          fun atom node = current node AtomicProvenance
          fun relation_with_kind kind left right provenance =
            current (case kind of R.HolEquality =>
                equality graph scope (left,right)
              | R.RegLanEquivalence => binary graph scope
                  SmtRegLanProve.equiv_tm (left,right))
              (EqualityProvenance provenance)
          fun inferred_kind left =
            if Type.compare (G.type_of graph left,
                SmtRegLanProve.reglan_ty) = EQUAL then R.RegLanEquivalence
            else R.HolEquality
          fun relation_with left right provenance =
            relation_with_kind (inferred_kind left) left right provenance
          fun relation left right = relation_with left right
            (AtomicProvenance,AtomicProvenance)
          fun proposition node = atom node
          fun one_step () = require_one "discover" premises
          fun one_provenance () = #provenance (fact (one_step ()))
          fun positive node provenance = (node,provenance)
          fun negative node provenance = (negate graph scope node,
            ApplicationProvenance ("not",[provenance]))
          val disjoin = CPC_SharedReplayPlan.disjoin
            {visit=fn()=>(),falsity=fn()=>G.constant graph scope boolSyntax.F,
             atom=atom,current=current,
             binary=binary graph scope boolSyntax.disjunction,
             provenances=List.map #2}
          fun one () = require_one "discover" premise_nodes
          fun relation_kind node = case R.relation graph node of
              SOME (kind,_) => kind
            | NONE => raise ERR "discover" "expected relation premise"
          fun pair node = case R.relation graph node of SOME (_,pair) => pair
            | NONE => raise ERR "discover" "expected relation premise"
          fun provenance_children provenance = case provenance of
              ConjunctionProvenance (_,children) => children
            | ApplicationProvenance (_,children) => children
            | _ => raise ERR "discover" "missing immediate operand boundary"
          val selected = CPC_SharedReplayPlan.selected
            {children = provenance_children,recorded = recorded graph,
             length = List.length,node_at = List.nth,
             provenance_at = List.nth,error = ERR "discover"}
          fun index () = case #args step of [Q.GraphIndex index] => index
            | _ => raise ERR "discover" "expected one recorded index"
          val owned_symmetry = ref (NONE : K.graph_conversion option)
          fun negative_symmetry work = action (fn () =>
            let
              fun observe () = (validate_owned work;W.spend work 1)
              val _ = validate_owned work
              val source = one ()
              fun prepare equation left right =
                let
                  val _ = observe ()
                  val _ = List.app (fn node =>
                    (observe ();
                     if G.scope_visible graph scope
                         (G.node_scope graph node) then () else
                       raise ERR "symm" "operand escapes original frame"))
                    [source,equation,left,right]
                  val ty = G.type_of graph left
                  val _ = if Type.compare (ty,G.type_of graph right) = EQUAL
                    then () else raise ERR "symm" "operand types differ"
                  (* The exact two-hole equality symmetry schema has 13 raw
                     and inclusive nodes. Its type inventory is retained as
                     virtual constructors, before making any schema term or
                     calling the public rewrite rule. Actual hole types are
                     walked independently; no annotation syntax quota. *)
                  val _ = if template_limit >= 13 then () else
                    raise ERR "symm" "fixed symmetry schema exceeds template"
                  datatype planned_type = Actual of Type.hol_type
                    | Arrow of planned_type * planned_type
                  val boolean = Actual Type.bool
                  val operand = Actual ty
                  val bool_partial = Arrow (boolean,boolean)
                  val bool_operator = Arrow (boolean,bool_partial)
                  val typed_partial = Arrow (operand,boolean)
                  val typed_operator = Arrow (operand,typed_partial)
                  val inner = [typed_operator,typed_partial,boolean,
                    operand,operand]
                  val inventory = [bool_operator,bool_partial,boolean] @
                    inner @ inner
                  fun actual ty =
                    (W.spend work 1;
                     if Type.is_vartype ty then
                       W.spend work (String.size (Type.dest_vartype ty))
                     else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                              val _ = W.spend work
                                (String.size Thy+String.size Tyop)
                          in List.app actual Args end)
                  fun visit (Actual ty) = actual ty
                    | visit (Arrow (domain,range)) =
                        (W.spend work 1;
                         W.spend work (String.size "min"+String.size "fun");
                         visit domain;visit range)
                  val _ = W.spend work 13
                  val _ = W.spend work 13
                  val _ = List.app visit inventory
                  val _ = validate_owned work
                  val x = Term.genvar ty
                  val y = Term.genvar ty
                  val theorem = Conv.REWR_CONV boolTheory.EQ_SYM_EQ
                    (boolSyntax.mk_eq (x,y))
                  val _ = validate_owned work
                  val schema = K.checked_graph_schema graph scope
                    {theorem = theorem,holes = [x,y],operands = [left,right],
                     template_limit = template_limit}
                  val _ = if K.graph_schema_source schema = equation then ()
                    else raise ERR "symm" "schema source differs from premise"
                  val conversion = K.graph_conversion graph scope false
                    (fn node => (observe ();
                       if node = equation then SOME schema else NONE)) source
                  val _ = K.validate_conversion_for work conversion
                  val (lp,rp) = equality_provenance
                    (negation_provenance (one_provenance ()))
                  val result = current (K.graph_result conversion)
                    (ApplicationProvenance ("not",
                      [EqualityProvenance (rp,lp)]))
                  val _ = owned_symmetry := SOME conversion
                  val _ = validate_owned work
                in SOME result end
            in case negated graph source of NONE => NONE
              | SOME equation => case R.equality graph equation of
                  SOME (left,right) => prepare equation left right
                | NONE => NONE end)
          val inferred = case CPC_SharedReplayPlan.simple_boolean
              (op =) handler of
              SOME CPC_SharedReplayPlan.SimpleAndIntro =>
                CPC_SharedReplayPlan.and_intro
                  {conjunction=conjunction graph scope,
                   provenances=fn()=>
                     List.map (#provenance o fact) premises,
                   current=current} premise_nodes
            | SOME CPC_SharedReplayPlan.SimpleAndElim =>
                CPC_SharedReplayPlan.and_elim
                  {require_one=require_one,node=node,
                   provenance= #provenance o fact,selected=selected,
                   current=current,error=ERR "discover"}
                  premises (#args step)
            | SOME CPC_SharedReplayPlan.SimpleNotNotElim =>
                CPC_SharedReplayPlan.not_not_elim
                  {negated=negated graph,one=one,
                   one_provenance=one_provenance,
                   negation_provenance=negation_provenance,
                   current=current,error=ERR "not_not_elim"}
            | SOME CPC_SharedReplayPlan.SimpleNotOrElim =>
                CPC_SharedReplayPlan.not_or_elim
                  {require_one=require_one,node=node,negated=negated graph,
                   provenance= #provenance o fact,
                   selected=selected,index=index,
                   negate=negate graph scope,current=current,error=ERR}
                  premises
            | SOME CPC_SharedReplayPlan.SimpleNotImpliesElim1 =>
                CPC_SharedReplayPlan.not_implies_elim1
                  {negated=negated graph,one=one,operands=operands graph,
                   child_provenance=child_provenance,
                   negation_provenance=negation_provenance,
                   one_provenance=one_provenance,current=current,error=ERR}
                  handler
            | SOME CPC_SharedReplayPlan.SimpleNotImpliesElim2 =>
                CPC_SharedReplayPlan.not_implies_elim2
                  {negated=negated graph,one=one,operands=operands graph,
                   child_provenance=child_provenance,
                   negation_provenance=negation_provenance,
                   one_provenance=one_provenance,negative=negative,
                   finish=fn(node,provenance)=>current node provenance,
                   error=ERR} handler
            | SOME CPC_SharedReplayPlan.SimpleImpliesElim =>
                CPC_SharedReplayPlan.implies_elim
                  {operands=operands graph,one=one,
                   child_provenance=child_provenance,
                   one_provenance=one_provenance,negative=negative,
                   positive=positive,disjoin=disjoin}
            | SOME CPC_SharedReplayPlan.SimpleEquivElim1 =>
                CPC_SharedReplayPlan.equiv_elim1
                  {one=one,pair=pair,one_provenance=one_provenance,
                   negative=negative,positive=positive,disjoin=disjoin}
            | SOME CPC_SharedReplayPlan.SimpleEquivElim2 =>
                CPC_SharedReplayPlan.equiv_elim2
                  {one=one,pair=pair,one_provenance=one_provenance,
                   negative=negative,positive=positive,disjoin=disjoin}
            | SOME CPC_SharedReplayPlan.SimpleNotEquivElim1 =>
                CPC_SharedReplayPlan.not_equiv_elim1
                  {one=one,pair=pair,one_provenance=one_provenance,
                   negative=negative,positive=positive,disjoin=disjoin,
                   negated=negated graph,
                   negation_provenance=negation_provenance,error=ERR}
                  handler
            | SOME CPC_SharedReplayPlan.SimpleNotEquivElim2 =>
                CPC_SharedReplayPlan.not_equiv_elim2
                  {one=one,pair=pair,one_provenance=one_provenance,
                   negative=negative,positive=positive,disjoin=disjoin,
                   negated=negated graph,
                   negation_provenance=negation_provenance,error=ERR}
                  handler
            | SOME CPC_SharedReplayPlan.SimpleIteElim1 =>
                CPC_SharedReplayPlan.ite_elim1
                  {same_constant=same_constant graph,one=one,atom=atom,
                   operands=operands graph,child_provenance=child_provenance,
                   one_provenance=one_provenance,negative=negative,
                   positive=positive,disjoin=disjoin}
            | SOME CPC_SharedReplayPlan.SimpleIteElim2 =>
                CPC_SharedReplayPlan.ite_elim2
                  {same_constant=same_constant graph,one=one,atom=atom,
                   operands=operands graph,child_provenance=child_provenance,
                   one_provenance=one_provenance,negative=negative,
                   positive=positive,disjoin=disjoin}
            | SOME CPC_SharedReplayPlan.SimpleNotAnd =>
                let
                  fun produced_entries work body =
                    CPC_SharedReplayPlan.produced_conjunction
                      {run=action,observe=fn()=>W.spend work 1,
                       input=fn()=> #clause(fact(one_step())),
                       recorded=C.recorded,same=op =,
                       children=R.operands graph boolSyntax.conjunction 2,
                       validate=fn current=>
                         if G.scope_visible graph scope
                             (G.node_scope graph current) andalso
                             Type.compare(G.type_of graph current,Type.bool)
                               =EQUAL then () else
                           raise ERR "not_and"
                             "actual AND operand frame or type differs",
                       check=fn count=>if count < template_limit then ()else
                         raise ERR "not_and"
                           "produced AND portfolio exceeds template",
                       pending=fn(left,right,rest)=>left::right::rest,
                       leaf=fn(current,provenance,result)=>
                         (current,provenance)::result,
                       reverse=List.rev,initial=fn body=>[body]} body
                in CPC_SharedReplayPlan.not_and
                  {negated=negated graph,one=one,
                   one_provenance=one_provenance,
                   negation_provenance=negation_provenance,
                   operands=operands graph,
                   is_false=fn node=>same_constant graph node boolSyntax.F,
                   child_provenance=child_provenance,
                   recorded_entries=aggregate_entries
                     boolSyntax.conjunction "and",owned=owned_work,
                   produced_entries=produced_entries,map=List.map,
                   negative=negative,disjoin=disjoin,error=ERR "not_and"}
                end
            | NONE => (case CPC_SharedReplayPlan.simple_equality
                (op =) handler of
              SOME CPC_SharedReplayPlan.SimpleRefl =>
                CPC_SharedReplayPlan.reflexive
                {require_one=require_one,relation=relation} arguments
            | SOME CPC_SharedReplayPlan.SimpleSymm =>
                let fun positive () = CPC_SharedReplayPlan.positive_symmetry
                      {pair=pair,one=one,one_provenance=one_provenance,
                       relation_kind=relation_kind,
                       relation_with_kind=relation_with_kind}
                in case R.relation graph (one ()) of SOME _ => positive ()
                  | NONE => case owned_work of NONE => positive ()
                    | SOME work => case negative_symmetry work of
                        SOME result => result | NONE => positive () end
            | SOME CPC_SharedReplayPlan.SimpleTrans =>
                let
                  fun support step = same_constant graph (node step)
                    boolSyntax.T
                  fun endpoints step =
                    let val (left,right) = pair (node step)
                        val provenance = equality_provenance
                          (#provenance (fact step))
                    in ((left,right),provenance) end
                  fun compose (next,accumulated : fact) =
                    if support next then accumulated
                    else if same_constant graph (#node accumulated)
                        boolSyntax.T then fact next
                    else
                      let
                        val ((left,right),(lp,rp)) =
                          (pair (#node accumulated),equality_provenance
                            (#provenance accumulated))
                        val ((a,b),(ap,bp)) = endpoints next
                        val kind = relation_kind (#node accumulated)
                        val _ = if kind = relation_kind (node next) then ()
                          else raise ERR "trans" "different relation kinds"
                        fun result left right provenance =
                          relation_with_kind kind left right provenance
                      in
                        if left = right then fact next
                        else if a = b then accumulated
                        else if right = a then result left b (lp,bp)
                        else if right = b then result left a (lp,ap)
                        else if left = a then result right b (rp,bp)
                        else if left = b then result right a (rp,ap)
                        else raise ERR "trans"
                          "nonmatching graph transitivity chain"
                      end
                  fun existing_path work (target:F.term) = action (fn () =>
                    let
                      fun observe () =
                        (validate_owned work;W.spend work 1)
                    in CPC_SharedReplayPlan.relation_path
                      {visit=observe,relation=R.relation graph,
                       map_partial=fn action=>fn nodes=>
                         List.mapPartial action nodes,
                       same_kind=op =,same=op =,key=G.node_id,
                       empty=fn()=>Redblackset.empty Int.compare,
                       member=Redblackset.member,add=Redblackset.add,
                       push=fn(node,rest)=>node::rest,
                       fold=List.foldl,error=ERR "trans"}
                      (#node target) premise_nodes end)
                in case #conclusion step of
                    SOME target => (case owned_work of NONE =>
                        located_fact graph scope target
                      | SOME work => if existing_path work target then
                          located_fact graph scope target
                        else raise ERR "trans"
                          "declared target requires a checked alias path")
                  | NONE => case premises of
                      [] => raise ERR "trans" "empty transitivity chain"
                    | first::rest => List.foldl compose (fact first) rest
                end
            | SOME CPC_SharedReplayPlan.SimpleCong =>
                let
                  val source = require_one "cong" arguments
                  val replacements = List.foldl
                    (fn (equation,table) =>
                      let val (left,right) = pair equation in
                        Redblackmap.insert (table,G.node_id left,right) end)
                    (Redblackmap.mkDict Int.compare) premise_nodes
                  val memo = ref (Redblackmap.mkDict Int.compare)
                  val rewrite = CPC_SharedReplayPlan.congruence_rewrite
                    {replacement=fn source=>Redblackmap.peek
                       (replacements,G.node_id source),
                     lookup=fn source=>
                       Redblackmap.peek(!memo,G.node_id source),
                     publish=fn(source,target)=>memo:=Redblackmap.insert
                       (!memo,G.node_id source,target),
                     view=fn source=>case G.view graph source of
                         G.Application pair=>SOME pair
                       | G.OpaqueRetained=>raise ERR "cong"
                           "bounded binder congruence needs admission"
                       | _=>NONE,
                     retained=fn source=>source,same=op =,
                     application=G.application graph scope}
                  val target = rewrite source
                  (* Only the actual parsed OR occurrence supplies this
                     immediate boundary. The same checked congruence must
                     preserve its head and each rewritten operand slot. *)
                  fun owned_or_boundary work = action (fn () =>
                    let
                      val _ = W.spend work 1
                      val original = require_one "cong"
                        (graph_terms (#args step))
                      val provenance = occurrence_provenance
                        (#occurrence original)
                      fun converted old replacement incoming =
                        let val _ = W.spend work 1 in
                          case Redblackmap.peek (replacements,
                              G.node_id old) of
                            SOME changed =>
                              let
                                fun search [] = UnavailableProvenance
                                      "congruence operand witness unavailable"
                                  | search (premise::rest) =
                                      let val _ = W.spend work 1
                                          val (left,right) = pair (node premise)
                                      in if left = old andalso
                                          right = replacement then
                                           #2 (equality_provenance
                                             (#provenance (fact premise)))
                                         else search rest end
                              in
                                if changed = replacement then
                                  search (List.rev premises)
                                else UnavailableProvenance
                                  "congruence operand correspondence differs"
                              end
                          | NONE => if old = replacement then incoming
                              else UnavailableProvenance
                                "changed nested congruence operand"
                        end
                      fun boundary children =
                        let
                          val count = List.length children
                          val _ = W.spend work 1
                          val old = recorded graph boolSyntax.disjunction
                            count source
                          val _ = W.spend work 1
                          val changed = recorded graph boolSyntax.disjunction
                            count target
                        in case (old,changed) of
                            (SOME old,SOME changed) =>
                              let
                                val slots = ListPair.zip (old,changed)
                                val _ = List.app (fn (old,new) =>
                                  (W.spend work 1;
                                   if rewrite old = new then () else
                                     raise ERR "cong"
                                       "recorded OR operand rewrite differs"))
                                  slots
                                val result = ListPair.mapEq
                                  (fn ((old,new),incoming) =>
                                    converted old new incoming)
                                  (slots,children)
                              in relation_with source target
                                (provenance,ApplicationProvenance
                                  ("or",result)) end
                          | _ => relation source target
                        end
                    in case provenance of
                        ApplicationProvenance ("or",children) =>
                          boundary children
                      | _ => relation source target
                    end)
                in case owned_work of NONE => relation source target
                     | SOME work => owned_or_boundary work end
            | SOME CPC_SharedReplayPlan.SimpleHoCong =>
                CPC_SharedReplayPlan.higher_congruence
                  {map=List.map,pair=pair,
                   application=G.application graph scope,
                   relation=relation,error=ERR "ho_cong"} premise_nodes
            | SOME CPC_SharedReplayPlan.SimpleEqResolve =>
                CPC_SharedReplayPlan.equality_resolve
                  {node=node,pair=pair,provenance= #provenance o fact,
                   same=op =,current=current,retry=fn _=>true,
                   error=ERR "eq_resolve"} premises
            | SOME CPC_SharedReplayPlan.SimpleContra =>
                atom (G.constant graph scope boolSyntax.F)
            | NONE => (case handler of
              "false_intro" => CPC_SharedReplayPlan.false_intro
                negated graph one Lib.I G.constant graph scope
                negation_provenance one_provenance relation_with ERR
            | "false_elim" => CPC_SharedReplayPlan.false_elim pair one
                equality_provenance one_provenance same_constant graph
                negative current ERR
            | "true_intro" => CPC_SharedReplayPlan.true_intro one Lib.I
                G.constant graph scope one_provenance relation_with
            | "true_elim" => CPC_SharedReplayPlan.true_elim pair one
                equality_provenance one_provenance same_constant graph
                Lib.I current ERR
            | "process_scope" =>
                let
                  val produced = case (owned_work,#args step,premises) of
                      (SOME work,[Q.GraphTerm body],[incoming]) =>
                        action (fn () =>
                          let
                            val target = #node body
                            fun visible node =
                              (validate_owned work;W.spend work 1;
                               if G.scope_visible graph scope
                                   (G.node_scope graph node) andalso
                                   Type.compare (G.type_of graph node,
                                     Type.bool) = EQUAL then () else
                                 raise ERR "process_scope"
                                   "actual scope operand escapes Bool frame")
                            fun walk node provenance entries =
                              CPC_SharedReplayPlan.process_scope_entries
                                visible (op =) R.operands graph List.rev
                                CPC_SharedReplayPlan.no_metadata_copy target
                                node provenance entries
                            val entries = walk (node incoming)
                              (#provenance (fact incoming)) []
                            fun construct [] = NONE
                              | construct entries =
                                let
                                  val nodes = List.map #1 entries
                                  val children = List.map #2 entries
                                  val antecedent =
                                    conjunction graph scope nodes
                                  val provenance = case children of
                                      [one] => one
                                    | _ => ConjunctionProvenance
                                        (ProcessScopeConjunction,children)
                                  val body_provenance = occurrence_provenance
                                    (#occurrence body)
                                in SOME (if same_constant graph target
                                    boolSyntax.F then
                                    let val (node,provenance) =
                                      negative antecedent provenance
                                    in current node provenance end
                                  else current (binary graph scope
                                      boolSyntax.implication
                                      (antecedent,target))
                                    (ApplicationProvenance ("=>",
                                      [provenance,body_provenance]))) end
                          in case entries of SOME entries => construct entries
                            | NONE => NONE end)
                    | _ => NONE
                in case produced of SOME result => result
                  | NONE => (case #conclusion step of SOME target =>
                      located_fact graph scope target
                    | NONE => raise ERR "discover"
                        "rule needs bounded output inference") end
            | _ => case #conclusion step of SOME target =>
                located_fact graph scope target
              | NONE =>
                raise ERR "discover" "rule needs bounded output inference"))
          val inferred = exact_target (#conclusion step) inferred
          val mode = case handler of "refl" => Equality "refl"
            | "symm" => (case !owned_symmetry of NONE => Equality "symm"
                | SOME conversion => OwnedNegatedSymmetry conversion)
            | "trans" => Transitivity
            | "cong" => Equality "cong" | "ho_cong" => Equality "cong"
            | _ => Boolean
        in (inferred,mode) end
      (* Fixed arithmetic spellings; total heads are never unfolded. *)
      fun fixed_alias_normalizer work =
        let
          val _ = validate_owned work
          fun observe () = (validate_owned work;W.spend work 1)
          fun alias node = case G.view graph node of
              G.Application (partial,right) =>
                (case G.view graph partial of
                   G.Application (head,left) =>
                     (case G.view graph head of G.Constant _ =>
                       let val term = G.representative graph head
                       in if Term.same_const term intSyntax.greater_tm then
                            SOME (integerTheory.INT_GT,0,
                              intSyntax.less_tm,left,right)
                          else if Term.same_const term intSyntax.geq_tm then
                            SOME (integerTheory.INT_GE,0,
                              intSyntax.leq_tm,left,right)
                          else if Term.same_const term intSyntax.minus_tm then
                            SOME (integerTheory.int_sub,2,
                              intSyntax.plus_tm,left,right)
                          else NONE end
                      | _ => NONE)
                 | _ => NONE)
            | _ => NONE
          fun metric limit kind node = case G.unfolded_nodes graph kind
              limit node of SOME size => if size <= limit then size else
                raise ERR "alias_eq_resolve" "original metric cap exhausted"
            | NONE => raise ERR "alias_eq_resolve"
                "fixed redex lacks actual bounded metric provenance"
          fun propose node = case alias node of NONE => NONE
            | SOME (fixed,extra,operator,left,right) =>
                let
                    val _ = observe ()
                    val raw = metric ordinary_limit G.RawNodes node
                    val inclusive = metric ordinary_limit
                      G.BinderInclusiveNodes node
                    fun future size =
                      if size <= (template_limit - 3 - extra) div 2 then
                        3 + size + size + extra
                      else raise ERR "alias_eq_resolve"
                        "prospective fixed equality exceeds original cap"
                    val equality_raw = future raw
                    val equality_inclusive = future inclusive
                    fun constant term =
                      (observe ();G.constant graph scope term)
                    fun application pair =
                      (observe ();G.application graph scope pair)
                    fun binary term (x,y) = application
                      (application (constant term,x),y)
                    val output = if extra = 2 then
                        binary operator (left,application
                          (constant intSyntax.negate_tm,right))
                      else binary operator (right,left)
                    val planned = (observe ();
                      equality graph scope (node,output))
                    val _ = if metric template_limit G.RawNodes planned =
                          equality_raw andalso
                        metric template_limit G.BinderInclusiveNodes planned =
                          equality_inclusive then () else
                      raise ERR "alias_eq_resolve"
                        "actual fixed constructor inventory differs"
                    val types = List.map (G.type_of graph)
                      (G.reachable graph [planned])
                    fun type_portfolio [] used = used
                      | type_portfolio (ty::rest) used =
                          (W.spend work 1;
                            type_portfolio ((if Type.is_vartype ty then []
                              else #2 (Type.dest_type ty)) @ rest) (used+1))
                    val _ = type_portfolio types 0
                    (* Whole raw/inclusive and independent actual type work
                       is debited before matching; private/kernel closure
                       is still not inferred from these exact inventories. *)
                    val _ = W.spend work equality_raw
                    val _ = W.spend work equality_inclusive
                    val _ = validate_owned work
                    val input = G.representative graph node
                    val _ = case SmtReplayImport.bounded_raw_size
                        ordinary_limit input of SOME size =>
                          if size = raw then () else raise ERR
                            "alias_eq_resolve" "actual raw input differs"
                      | NONE => raise ERR "alias_eq_resolve"
                          "fixed alias redex exceeds original ordinary cap"
                    val theorem = Conv.REWR_CONV fixed input
                    val _ = validate_owned work
                    val imported = G.import graph scope template_limit
                      (Thm.concl theorem)
                    (* Actual opening registers the exact whole import/view
                       pair required by record_closed_from_import. *)
                    val opened = G.record_opened_view graph scope
                      template_limit (#node imported)
                    val _ = case R.equality graph (#node opened) of
                        SOME (a,b) =>
                          if a = node andalso b = output then () else
                          raise ERR "alias_eq_resolve"
                            "fixed rewrite differs from prospective endpoints"
                      | NONE => raise ERR "alias_eq_resolve"
                          "fixed rewrite is not typed equality"
                    fun type_check ty =
                      (validate_owned work;check_type ty;validate_owned work)
                    val recorded = P.record_closed_from_import graph scope
                      {node = #node opened,theorem = theorem,
                       template_limit = template_limit,
                       check_type = type_check}
                    val _ = validate_owned work
                in SOME recorded end
          fun normalize node = K.graph_conversion_with_closed graph scope
            {template_limit = template_limit,revisit = false,
             propose = propose,observe = observe} node
          fun viable node = case alias node of NONE => true
            | SOME (_,extra,_,_,_) =>
                let val limit = (template_limit-3-extra) div 2
                    fun bound kind = case G.unfolded_nodes graph kind
                        ordinary_limit node of SOME size => size <= limit
                      | NONE => false
                in bound G.RawNodes andalso bound G.BinderInclusiveNodes end
        in (normalize,viable) end
      fun alias_eq_resolve work (step : Q.graph_rule_step) premises =
        action (fn () =>
          let
            val (normalize,_) = fixed_alias_normalizer work
            fun attempt proposition equation = case R.equality graph
                (node equation) of NONE => NONE
              | SOME (left,right) =>
                  let val (left_prov,right_prov) =
                        equality_provenance (#provenance (fact equation))
                      val source = normalize (node proposition)
                      fun side endpoint result provenance =
                        let val conversion = normalize endpoint
                        in if K.graph_result source =
                            K.graph_result conversion then
                          SOME (exact_target (#conclusion step)
                            (graph_fact graph scope result provenance),
                            BooleanAliases [source,conversion]) else NONE end
                  in case side left right right_prov of SOME selected =>
                       SOME selected
                     | NONE => side right left left_prov end
          in case premises of [first,second] =>
              (case attempt first second of SOME selected => SOME selected
               | NONE => attempt second first)
            | _ => NONE end)
      fun alias_transitivity work (step : Q.graph_rule_step) premises =
        action (fn () =>
          let
            val _ = validate_owned work
            val (normalize,viable) = fixed_alias_normalizer work
            fun observe () = (validate_owned work;W.spend work 1)
            fun allowed node =
              (observe ();
               if G.scope_visible graph scope (G.node_scope graph node) then
                 viable node else raise ERR "alias_transitivity"
                   "actual premise escapes original frame")
            val nodes = List.map node premises @
              (case #conclusion step of NONE => []
               | SOME current => [#node current])
            val ready = List.all allowed (G.reachable graph nodes)
            fun normalized incoming =
              let val _ = observe ()
                  val conversion = normalize (node incoming)
                  val _ = K.validate_conversion_for work conversion
                  val result = K.graph_result conversion
              in ((fact incoming,
                   graph_fact graph scope result AtomicProvenance),
                  conversion) end
            fun compose ((next_raw:fact,next:fact),(raw:fact,current:fact)) =
              (observe ();
               if same_constant graph (#node current) boolSyntax.T then
                 SOME (next_raw,next)
               else if same_constant graph (#node next) boolSyntax.T then
                 SOME (raw,current)
               else case (R.equality graph (#node current),
                          R.equality graph (#node next),
                          R.equality graph (#node raw),
                          R.equality graph (#node next_raw)) of
                 (SOME (left,right),SOME (a,b),
                  SOME (old_left,old_right),SOME (old_a,old_b)) =>
                   let val (lp,rp) = equality_provenance (#provenance raw)
                       val (ap,bp) = equality_provenance
                         (#provenance next_raw)
                       fun result x y old_x old_y provenance = SOME
                         (graph_fact graph scope
                            (equality graph scope (old_x,old_y))
                            (EqualityProvenance provenance),
                          graph_fact graph scope (equality graph scope (x,y))
                            AtomicProvenance)
                   in if old_left = old_right then SOME (next_raw,next)
                     else if old_a = old_b then SOME (raw,current)
                     else if right = a then
                       result left b old_left old_b (lp,bp)
                     else if right = b then
                       result left a old_left old_a (lp,ap)
                     else if left = a then
                       result right b old_right old_b (rp,bp)
                     else if left = b then
                       result right a old_right old_a (rp,ap)
                     else NONE end
               | _ => NONE)
            fun chain [] current = SOME current
              | chain (next::rest) current = case compose (next,current) of
                  SOME result => chain rest result | NONE => NONE
            fun prepare () =
              let val rows = List.map normalized premises
                  val composed = case List.map #1 rows of [] => NONE
                    | first::rest => chain rest first
              in case composed of NONE => NONE
                | SOME (raw,current) =>
                    let
                      val result = case #conclusion step of NONE => raw
                        | SOME target => located_fact graph scope target
                      val conversion = normalize (#node result)
                      val _ = K.validate_conversion_for work conversion
                      val target = K.graph_result conversion
                      val matches = target = #node current orelse
                        (case (R.equality graph target,
                               R.equality graph (#node current)) of
                           (SOME (left,right),SOME (a,b)) =>
                             left = b andalso right = a
                         | _ => false)
                    in if matches then SOME
                      (result,OwnedAliasTransitivity
                        {premises = List.map #2 rows,target = conversion})
                      else NONE end end
          in if ready then prepare () else NONE end)
      fun discover_step (step : Q.graph_rule_step) pop =
        let
          val premises = List.map find (#premises step)
          val handler = #replay_handler (#rule step)
          fun admit_argument_types () = List.app (fn value : F.term =>
            ignore (G.type_of graph (#node value)))
            (graph_terms (#args step))
          val reserved = if pop orelse handler <> "trust" then NONE else
            case native_reservation of NONE => NONE
              | SOME reserve => reserve {serial = !counter,step = step}
          val (current,route) = case reserved of SOME origin =>
              let val target = case #conclusion step of SOME target => target
                    | NONE => raise ERR "native_reservation"
                        "native reservation lacks recorded endpoint"
                  val _ = CPC_GraphNativeReservation.validate_request origin
                    {serial = !counter,target = #node target}
              in (located_fact graph scope target,NativeObligation origin) end
            | NONE => (admit_argument_types ();if pop then
              if handler <> "scope" then raise ERR "scope"
                "step-pop does not use the registered scope rule"
              else case !pushes of
                  [] => raise ERR "scope" "scope pop has no matching push"
                | (hypothesis,outer)::rest =>
                    let
                      val body = require_one "scope" premises
                      val target = R.implication graph scope [hypothesis]
                        (node body)
                      val current = exact_target (#conclusion step)
                        (graph_fact graph scope target
                          (ApplicationProvenance ("=>",
                            [AtomicProvenance,#provenance (fact body)])))
                      val _ = pushes := rest
                      val _ = known := outer
                    in (current,Scope {hypothesis = hypothesis,body = body}) end
            else case CPC_SharedReplayPlan.native_route
                {pop = false,handler = handler} of
              CPC_SharedReplayPlan.Resolved =>
              if #name (#rule step) = "chain_m_resolution" then
                recorded_chain_resolution step premises
              else resolution step premises
            | CPC_SharedReplayPlan.Converted =>
              (cnf step premises handle Feedback.HOL_ERR error =>
                if SmtResource.is_resource_gate error then
                  raise Feedback.HOL_ERR error else bounded step premises)
            | CPC_SharedReplayPlan.Aligned => align step premises
            | CPC_SharedReplayPlan.Simple =>
              (simple step premises handle Feedback.HOL_ERR error =>
                if SmtResource.is_resource_gate error then
                  raise Feedback.HOL_ERR error else
                  (case (owned_work,handler) of (SOME work,"eq_resolve") =>
                     (case alias_eq_resolve work step premises of
                        SOME selected => selected
                      | NONE => bounded step premises)
                   | (SOME work,"trans") =>
                       (case alias_transitivity work step premises of
                          SOME selected => selected
                        | NONE => bounded step premises)
                   | _ => bounded step premises))
            | _ => bounded step premises)
        in make (#id step) current premises route end
      fun discover (Q.GraphAssume (id,term)) =
            let
              val current = located_fact graph scope term
              val route = if Redblackset.member
                  (processed_ids,G.node_id (#node current)) then
                PreprocessedSource else Assumption
              val _ = case preprocessing of NONE => () | SOME _ =>
                if Redblackset.member
                    (processed_ids,G.node_id (#node current)) orelse
                    List.exists (fn node => node = #node current)
                      canonical_sources orelse
                    List.exists (fn (node,_) => node = #node current) (!pushes)
                then () else raise ERR "discover"
                  "assertion outside original or processed Source portfolio"
            in make id current [] route end
        | discover (Q.GraphAssumePush (id,term)) =
            let val _ = pushes := (#node term,!known) :: !pushes
            in make id (located_fact graph scope term) [] Assumption end
        | discover (Q.GraphStep {step,pop}) = discover_step step pop
      fun observed command =
        let
          val occurrence = !counter
          val _ = notify (CommandBegin
            {serial = occurrence,command = command})
          val result = discover command
          val _ = notify (CommandEnd
            {serial = occurrence,node = node result,
             provenance = #provenance (fact result)})
        in result end
      val completed = SmtResource.profile_phase "cvc/graph-rule-admission"
        (List.map observed) (#commands proof)
      val final = case List.rev completed of root::_ => root
        | [] => raise ERR "check_contradiction" "empty CPC proof"
      (* cvc5 can certify an already false input with only ASSUME commands,
         including the trailing denied-goal assumption. Select the actual
         recorded false Source edge, never a freshly solved contradiction.
         Every command above passed the ordinary assertion provenance gate.
         Any STEP/push keeps the exact old final-command requirement. *)
      val root = case owned_work of NONE => final
        | SOME work => action (fn () =>
            let fun assumptions [] = true
                  | assumptions (Q.GraphAssume _ :: rest) =
                      (W.spend work 1;assumptions rest)
                  | assumptions (_ :: _) = (W.spend work 1;false)
                fun recorded [] = final
                  | recorded (candidate::rest) =
                      (W.spend work 1;
                       if same_constant graph (node candidate) boolSyntax.F
                         then candidate else recorded rest)
            in if assumptions (#commands proof) then recorded completed
               else final end)
      val _ = if List.null (!pushes) then () else
        raise ERR "check_contradiction" "unclosed CPC assumption scope"
      val _ = if same_constant graph (node root) boolSyntax.F then () else
        raise ERR "check_contradiction" "final CPC conclusion is not F"

      (* Child scope laws discharge every active local source while compact.
         The parent applies their conditional antecedents to its own local
         edges. Completed witnesses retain only canonical original sources. *)
      fun permitted theorem =
        (Library.check_oracle_tags "CPC_GraphProofReplay" "obligation" theorem;
         if List.all (fn hypothesis => List.exists (fn source =>
              Portable.pointer_eq
                (hypothesis,G.representative graph source)) canonical_sources)
              (Thm.hyp theorem) then () else raise ERR "obligation"
            "deferred proof retains a local or unpermitted hypothesis")
      fun validate_force_target obligation =
        (G.validate_scope graph scope;
         G.validate_scope graph (G.node_scope graph obligation);
         if G.scope_visible graph scope (G.node_scope graph obligation) then ()
         else raise ERR "completion_proof" "escaping completion proof target")
      val obligation_admissions = ref (Redblackmap.mkDict
        (fn (a,b) =>
          (Option.app (fn work => W.spend work 1) owned_work;
           Int.compare (a,b))) :
        (int,Thm.thm * (Term.term * SmtReplayImport.raw_bound) list)
          Redblackmap.dict)
      fun force_obligation_using raw_for admit_for obligation =
        if not (Option.isSome force_worker orelse
                      Option.isSome owned_force_worker) then
                    raise ERR "obligation"
                      "no independently checked fact proves deferred obligation"
                  else let
                        val _ = validate_force_target obligation
                        val target = raw_for obligation
                        val located = {term = target,
                          provenance = AtomicProvenance}
                        val rule = case CPC_Proof.lookup_rule
                            (#cvc_version proof) "trust" of SOME rule => rule
                          | NONE => raise ERR "obligation"
                              "no registered forced TRUST rule"
                        val step : CPC_Proof.step =
                          {id = "graph-forced-obligation",rule = rule,
                           premises = [],args = [located],
                           conclusion = SOME located}
                        val occurrence = !forced_counter
                        val _ = forced_counter := occurrence+1
                        fun execute () = let
                        val _ = notify (ForcedBegin
                          {serial = occurrence,step = step})
                        val (theorem,result) = case owned_force_worker of
                            SOME checked => checked
                              {serial = occurrence,target = obligation,
                               step = step,premises = []}
                          | NONE => valOf force_worker (step,[])
                        val _ = Library.check_oracle_tags
                          "CPC_GraphProofReplay" "force_obligation" theorem
                        val _ = List.app admit_for
                          (Thm.concl theorem :: Thm.hyp theorem)
                        val _ = if Term.aconv (Thm.concl theorem) target andalso
                            Term.aconv (#term result) target andalso
                            not (List.exists (Term.aconv target)
                              (Thm.hyp theorem)) then () else raise ERR
                              "obligation"
                                "forced TRUST deferred or changed target"
                        val theorem = Thm.EQ_MP
                          (Thm.ALPHA (Thm.concl theorem) target) theorem
                        val _ = permitted theorem
                        val _ = notify (ForcedEnd
                          {serial = occurrence,theorem = theorem,
                           located = {term = Thm.concl theorem,
                             provenance = #provenance result}})
                        in theorem end
                        fun abort error =
                          let
                            val _ = notify (ForcedAbort {serial = occurrence})
                              handle abort_error =>
                                (case error of ObserverFailure _ => raise error
                                 | Feedback.HOL_ERR detail =>
                                     (case owned_work of
                                        SOME work =>
                                          if #retired (W.audit work) orelse
                                              SmtResource.is_resource_gate
                                                detail then raise error
                                          else raise abort_error
                                      | NONE =>
                                          if SmtResource.is_resource_gate
                                              detail then raise error
                                          else raise abort_error)
                                 | _ =>
                                     (case owned_work of
                                        SOME work =>
                                          if #retired (W.audit work) then
                                            raise error else raise abort_error
                                      | NONE => raise abort_error))
                          in raise error end
                      in execute () handle error => abort error end
      fun force_obligation obligation = case owned_work of NONE =>
          force_obligation_using raw admit obligation
        | SOME work =>
          let
            val _ = action (fn () => W.spend work 2)
            val held = ref
              ([]:(Term.term * SmtReplayImport.raw_bound) list)
            fun admitted term = action (fn () =>
              (W.spend work 3;
               case SmtReplayImport.bounded_raw_size_with_bound
                   {limit=ordinary_limit,
                    observe=fn () => W.spend work 1} term of
                 NONE => admission_failure
                   "ordinary input exceeds caller limit"
               | SOME bound =>
                   (W.spend work 2;held := (term,bound):: !held)))
            fun native node =
              let val term = G.representative graph node
                  val _ = admitted term
                  val _ = admit_type (Term.type_of term)
              in term end
            val theorem = force_obligation_using native admitted obligation
            val _ = action (fn () =>
              (W.spend work 2;obligation_admissions := Redblackmap.insert
                (!obligation_admissions,G.node_id obligation,
                 (theorem,!held))))
          in theorem end
      fun ordinary_completion () = let
      val _ = if List.exists (fn step => case recipe step of
          NativeObligation _ => true | _ => false) completed then
        raise NativeCompletionAdapter else ()
      val obligation_proofs = ref (Redblackmap.mkDict Int.compare)
      val checked_facts = List.foldl (fn (step,table) =>
        let val key = G.node_id (node step) in
          Redblackmap.insert (table,key,step :: Option.getOpt
            (Redblackmap.peek (table,key),[])) end)
        (Redblackmap.mkDict Int.compare) completed
      fun assemble_recipe block source derived premises clauses scope_law
          local_assumptions apply_law step =
        let val target = node step
        in
        case recipe step of
                      Assumption => source target
                    | PreprocessedSource =>
                        (case derived target of SOME edge => edge
                         | NONE => raise ERR "assemble"
                             "missing processed Source derivation")
                    | Equality rule => R.assemble graph block
                        {rule = rule,target = target,premises = premises ()}
                    | Transitivity =>
                        let
                          val all = premises ()
                          val equalities = List.filter (fn (node,_) =>
                            Option.isSome (R.relation graph node)) all
                          val edge = if same_constant graph target
                              boolSyntax.T then
                              R.boolean_rule graph block target all
                            else R.assemble graph block
                              {rule = "trans-star",target = target,
                               premises = equalities}
                        in P.compose block
                          (fn proof::supports => List.foldl
                            (fn (support,result) =>
                              Thm.CONJUNCT1 (Thm.CONJ result support))
                            proof supports
                            | [] => raise ERR "assemble"
                                "missing transitivity proof")
                          (edge :: List.map #2 all) end
                    | Boolean => R.boolean_rule graph block target (premises ())
                    | BooleanAliases conversions =>
                        R.boolean_rule graph block target
                          (List.map (fn conversion =>
                            (K.graph_equality conversion,
                             K.graph_assemble graph block conversion))
                             conversions @ premises ())
                    | OwnedAliasTransitivity
                        {premises = conversions,target = target_conversion} =>
                        let
                          val work = case owned_work of SOME work => work
                            | NONE => raise ERR "alias_transitivity"
                                "missing original Work"
                          val actual = premises ()
                          fun convert (conversion,(source,incoming)) =
                            let val _ = validate_owned work
                                val _ = K.validate_conversion_for work
                                  conversion
                                val _ = if K.graph_source conversion = source
                                  then () else raise ERR "alias_transitivity"
                                    "different actual premise occurrence"
                                val named = K.graph_assemble_for work
                                  graph block conversion
                                val bridge = P.constructor block
                                  (K.graph_equality conversion)
                                val equation = P.execute_primitive work
                                  (P.prepare_primitive work block P.EqualityMP
                                    [bridge,named])
                                val output = P.execute_primitive work
                                  (P.prepare_primitive work block P.EqualityMP
                                    [equation,incoming])
                            in (K.graph_result conversion,output) end
                          val all = ListPair.mapEq convert
                            (conversions,actual)
                          val equalities = List.filter (fn (node,_) =>
                            Option.isSome (R.equality graph node)) all
                          val _ = K.validate_conversion_for work
                            target_conversion
                          val _ = if K.graph_source target_conversion = target
                            then () else raise ERR "alias_transitivity"
                              "different retained outer target"
                          val normalized_target =
                            K.graph_result target_conversion
                          val normalized_edge = if same_constant graph
                              normalized_target boolSyntax.T then
                              R.boolean_rule graph block normalized_target all
                            else R.assemble graph block
                              {rule = "trans-star",target = normalized_target,
                               premises = equalities}
                          val named = K.graph_assemble_for work graph block
                            target_conversion
                          val bridge = P.constructor block
                            (K.graph_equality target_conversion)
                          val equation = P.execute_primitive work
                            (P.prepare_primitive work block P.EqualityMP
                              [bridge,named])
                          val reverse = P.execute_primitive work
                            (P.prepare_primitive work block P.Symmetry
                              [equation])
                          val edge = P.execute_primitive work
                            (P.prepare_primitive work block P.EqualityMP
                              [reverse,normalized_edge])
                        in P.compose block
                          (fn proof::supports => List.foldl
                            (fn (support,result) =>
                              Thm.CONJUNCT1 (Thm.CONJ result support))
                            proof supports
                            | [] => raise ERR "assemble"
                                "missing alias transitivity proof")
                          (edge :: List.map #2 all) end

                    | OwnedNegatedSymmetry conversion =>
                        (case owned_work of NONE => raise ERR "symm"
                           "owned schema lost original Work"
                         | SOME work =>
                             let val _ = validate_owned work
                                 val _ = K.validate_conversion_for work
                                   conversion
                                 val equation = K.graph_equality conversion
                                 val edge = K.graph_assemble_with_schemas_for
                                   work graph block conversion
                             in R.boolean_rule graph block target
                               ((equation,edge)::premises ()) end)
                    | BooleanSchemas conversions =>
                        R.boolean_rule graph block target
                          (List.map (fn conversion =>
                            (K.graph_equality conversion,
                             K.graph_assemble graph block conversion))
                             conversions @ premises ())
                    | Resolution pivots =>
                        (case C.resolve_chain
                            {pivots = pivots,premises = clauses (),
                             target = SOME (clause_of step)} of
                             SOME clause => C.to_target (clause_of step) clause
                           | NONE => raise ERR "assemble"
                               "recorded resolution did not prove its target")
                    | Alignment =>
                        (case C.align (clause_of step)
                            (require_one "alignment" (clauses ())) of
                             SOME clause => C.to_target (clause_of step) clause
                           | NONE => raise ERR "assemble"
                               "recorded clause alignment failed")
                    | ClosedLaw (law,_,_) =>
                        if law=target andalso null (premise_list step) then
                          source law
                        else apply_law
                          {law = (law,source law),target = target,
                           premises = premises ()}
                    | ObligationLaw {obligation,law,...} => apply_law
                        {law = (law,source law),target = target,
                          premises = premises () @
                            [(obligation,source obligation)]}
                    | NativeObligation _ => raise NativeCompletionAdapter
                    | Scope _ =>
                        let val law = scope_law step
                        in if List.null local_assumptions then source law else
                          apply_law
                            {law = (law,source law),target = target,
                             premises = List.map (fn node => (node,source node))
                               local_assumptions} end
        end
      (* Each successful chunk exports one genuine rooted Source proof.
         The median split below changes only grouping: the rule recipes
         are still assembled by assemble_recipe above. *)
      fun bounded_complete_with_ports work root local_assumptions ancestors
          temporary_ports =
        let
          val _ = validate_owned work
          val frame = SmtReplayOwnedScopeReceipt.root work
          val cap = IntInf.fromInt template_limit
          fun meta operation = W.with_step work operation
          fun tick amount = W.spend work amount
          fun compare (a,b) = (tick 1;Int.compare (a,b))
          fun valid step =
            (tick 2;ignore (G.node_scope graph (node step)))
          val proofs = ref (Redblackmap.mkDict compare :
            (int,P.source_realization) Redblackmap.dict)
          val captured = ref (Redblackmap.mkDict compare :
            (int,P.closed_fact * P.closed_law_spine)
              Redblackmap.dict)
          fun find step =
            let val result = meta (fn () =>
                  (valid step;Redblackmap.peek (!proofs,serial step)))
                val _ = Option.app (fn receipt => ignore
                  (P.source_realization_data_for work receipt)) result
            in result end
          fun save step receipt =
            let val data = P.source_realization_data_for work receipt
                val _ = if #target data=node step then () else
                  raise ERR "bounded_completion" "different chunk endpoint"
            in meta (fn () =>
              (valid step;tick 2;proofs := Redblackmap.insert
                (!proofs,serial step,receipt))) end
          fun list_map function entries =
            List.map (fn entry => (tick 2;function entry)) entries
          fun append left right = meta (fn () =>
            let fun copy [] = (tick 1;right)
                  | copy (first::rest) = (tick 2;first::copy rest)
            in copy left end)
          fun length entries = meta (fn () =>
            let fun count [] total = (tick 1;total)
                  | count (_::rest) total = (tick 1;count rest (total+1))
            in count entries 0 end)
          fun map_external function entries =
            List.map (fn entry => (meta (fn () => tick 2);function entry))
              entries
          fun copy_append [] right = (tick 1;right)
            | copy_append (first::rest) right =
                (tick 2;first::copy_append rest right)
          (* Only an isolated actual-dependency trial supplies these ports.
             Each remains a genuine additional Source occurrence until the
             completed receipt proves it was not used. No caller theorem or
             Hyp list supplies that proof. *)
          val extra_sources = case temporary_ports of
              [] => local_assumptions
            | _ => meta (fn () =>
                copy_append local_assumptions temporary_ports)
          fun recipe_label step = case recipe step of
              Assumption => "assumption"
            | PreprocessedSource => "preprocessed-source"
            | Equality kind => "equality-" ^ kind
            | Transitivity => "transitivity" | Boolean => "boolean"
            | BooleanSchemas _ => "boolean-schemas"
            | BooleanAliases _ => "boolean-aliases"
            | OwnedNegatedSymmetry _ => "owned-negated-symmetry"
            | OwnedAliasTransitivity _ => "owned-alias-transitivity"
            | Resolution _ => "resolution" | Alignment => "alignment"
            | ClosedLaw _ => "closed-law"
            | ObligationLaw _ => "obligation-law"
            | NativeObligation _ => "native-obligation"
            | Scope _ => "scope"
          fun record_exact check_owner law theorem = meta (fn () =>
                  let
                    val _ = check_owner ()
                    fun types [] = tick 1
                      | types ([]::rest) = (tick 1;types rest)
                      | types ((ty::more)::rest) =
                        (tick 2;if Type.is_vartype ty then
                            types (more::rest)
                          else (tick 2;types
                            ((#2 (Type.dest_type ty))::more::rest)))
                    val seen = ref (Redblackset.empty compare)
                    fun inspect [] = tick 1
                      | inspect ((caller,current)::rest) =
                        (tick 3;ignore (G.node_scope graph current);
                         ignore (G.closure_root graph caller current);
                         if Redblackset.member (!seen,G.node_id current)
                           then inspect rest else
                           (tick 2;seen := Redblackset.add
                              (!seen,G.node_id current);
                            types [[G.type_of graph current]];
                            case G.view graph current of
                                G.Application (left,right) =>
                                  (tick 4;inspect
                                    ((caller,left)::(caller,right)::rest))
                              | G.AdmittedBinder _ =>
                                  let
                                    val _ = tick 2
                                    val closure =
                                      G.binder_closure graph caller current
                                    val _ = tick 1
                                    val data = G.binder_closure_data
                                      graph caller closure
                                  in tick 4;inspect
                                    ((#binder_frame data,#binder data)::
                                     (#body_frame data,#body data)::rest)
                                  end
                              | _ => inspect rest))
                    val _ = inspect [(scope,law)]
                    val _ = List.app (fn metric =>
                      case G.unfolded_nodes graph metric template_limit law of
                        SOME count => tick count
                      | NONE => raise ERR "bounded_completion"
                          "closed rule has no admitted metric")
                      [G.RawNodes,G.BinderInclusiveNodes]
                    fun checked ty =
                      (validate_owned work;check_type ty;validate_owned work)
                  in P.record_closed_exact graph scope
                    {node=law,theorem=theorem,
                     template_limit=template_limit,check_type=checked} end)
          fun capture step law theorem arguments =
            case meta (fn () =>
                (valid step;Redblackmap.peek (!captured,serial step))) of
              SOME (fact,spine) =>
                (ignore (P.closed_law_spine_data_for work spine);(fact,spine))
            | NONE =>
              let
                (* This new capture performs no alignment rule. Its
                   actual existing metric/type walks are still paid, and
                   every caller callback remains between owner guards. *)
                val fact = record_exact (fn () => valid step) law theorem
                val spine = P.prepare_closed_law_spine work
                  {frame=frame,fact=fact,premises=arguments,target=node step}
                val all = P.closed_law_spine_prefix_for work spine
                  (length arguments)
                val _ = meta (fn () =>
                  (valid step;tick 2;captured := Redblackmap.insert
                    (!captured,serial step,(fact,all))))
              in (fact,all) end
          fun primitive block instruction arguments =
            let
              fun label () = case instruction of
                  P.ReflexiveName _ => "reflexive"
                | P.Symmetry => "symmetry"
                | P.Transitivity => "transitivity"
                | P.Congruence => "congruence"
                | P.EqualityMP => "equality-mp"
                | P.ApplyNamedArgument _ => "apply-argument"
                | P.ImplicationMP => "implication-mp"
              fun checkpoint phase = work_checkpoint phase
                (fn () => " operation=" ^ label ())
              val _ = checkpoint "bounded.primitive.prepare.before"
              val prepared =
                P.prepare_primitive work block instruction arguments
              val _ = checkpoint "bounded.primitive.prepare.after"
              val result = P.execute_primitive work prepared
              val _ = checkpoint "bounded.primitive.execute.after"
            in result end
          fun constructor block current =
            (tick 2;case G.view graph current of
              G.Constant _ => P.definition block current
            | G.Application (operator,operand) =>
                let val outer = P.definition block current
                    val inner = constructor block operator
                    val applied = primitive block
                      (P.ApplyNamedArgument operand) [inner]
                in primitive block P.Transitivity [outer,applied] end
            | _ => primitive block (P.ReflexiveName current) [])
          fun apply_law block {law=(law,edge),target,premises} =
            let
              fun consume current incoming [] =
                    if current=target then incoming else
                      raise ERR "bounded_completion"
                        "conditional rule has a different final target"
                | consume current incoming ((argument,proof)::rest) =
                  let
                    val _ = tick 4
                    val (partial,tail) = case G.view graph current of
                        G.Application pair => pair
                      | _ => raise ERR "bounded_completion"
                          "conditional rule lost its implication shell"
                    val (head,premise) = case G.view graph partial of
                        G.Application pair => pair
                      | _ => raise ERR "bounded_completion"
                          "conditional rule lost its premise shell"
                    val _ = if premise=argument andalso
                        same_constant graph head boolSyntax.implication
                      then () else raise ERR "bounded_completion"
                        "conditional rule premise order differs"
                    val bridge = constructor block current
                    val named = primitive block P.EqualityMP [bridge,incoming]
                    val result = primitive block P.ImplicationMP [named,proof]
                  in consume tail result rest end
            in consume law edge premises end
          fun prepare roots facts conversions receipts targets boolean
              congruence laws =
            P.prepare_source_cut_rule_law_plan work
              {frame=frame,roots=roots,
               additional_sources=extra_sources,closed_facts=facts,
               conversions=conversions,receipts=receipts,targets=targets,
               boolean=boolean,congruence=congruence,laws=laws}
          fun source block current =
            let
              fun scan [] _ result = result
                | scan (saved::rest) index result =
                    (tick 1;scan rest (index+1)
                      (if saved=current then SOME index else result))
            in case scan (P.sources block) 0 NONE of
                SOME index => P.source block index
              | NONE => raise ERR "bounded_completion"
                  "actual Source occurrence is outside chunk" end
          fun original current =
            let val plan = prepare [] [] [] [] [current] false false []
                val block = P.freeze_source_cut_rule_plan work plan
                val native = P.source_cut_block_for work block
                val edge = meta (fn () =>
                  let fun locate [] _ = raise ERR "bounded_completion"
                            "obligation is not an original Source"
                        | locate (held::rest) index =
                          (tick 1;if held=current then P.source native index
                           else locate rest (index+1))
                  in locate canonical_sources 0 end)
            in P.realize_source_cut_receipt work block current edge end
          fun temporary current =
            let val plan = prepare [] [] [] [] [current] false false []
                val block = P.freeze_source_cut_rule_plan work plan
                val native = P.source_cut_block_for work block
                val edge = meta (fn () => source native current)
            in P.realize_source_cut_receipt work block current edge end
          fun prove selected = case find selected of SOME receipt => receipt
            | NONE =>
              let
                val seen = ref (Redblackset.empty compare)
                val ordered = ref ([]:step list)
                val cuts = ref ([]:(step * P.source_realization) list)
                fun inventory step = case find step of
                    SOME receipt => meta (fn () =>
                      (tick 2;cuts := (step,receipt) :: !cuts))
                  | NONE =>
                    let val fresh = meta (fn () =>
                      (valid step;
                       if Redblackset.member (!seen,serial step) then false
                       else (seen := Redblackset.add (!seen,serial step);
                         true)))
                    in if not fresh then () else
                      case recipe step of
                        Scope {hypothesis,body} =>
                          let val proof = bounded_source body
                                (append local_assumptions [hypothesis])
                              val closed =
                                P.discharge_source_receipt_with_work work
                                  proof hypothesis
                              val _ = save step closed
                          in meta (fn () =>
                            (tick 2;cuts := (step,closed) :: !cuts)) end
                      | _ =>
                          (List.app inventory (premise_list step);
                           meta (fn () =>
                             (tick 2;ordered := step :: !ordered)))
                    end
                val _ = inventory selected
                val steps = meta (fn () =>
                  let fun reverse [] result = (tick 1;result)
                        | reverse (step::rest) result =
                            (tick 2;reverse rest (step::result))
                  in reverse (!ordered) [] end)
                val step_count = length steps
                (* A lower bound can prove a candidate unfit without
                   constructing its larger rule frontier. Each captured
                   law is a real ClosedWitness; its outer actual App
                   shells are mandatory even when operands become holes.
                   Inventory is unique by step serial; capture allocates
                   one distinct fact per such step, even for equal native
                   theorem pointers. The frontier retains those witness
                   occurrences. App IDs are deduplicated independently.
                   Each mandatory App contributes 7 syntax plus 3 join
                   nodes; each Source/witness contributes 1 plus 3.
                   Ignoring constants/conversions and subtracting the
                   final join gives this lower bound, not an exact size. *)
                val minimum = meta (fn () =>
                  let
                    val apps = ref (Redblackset.empty compare)
                    val app_count = ref (0:IntInf.int)
                    val fact_count = ref (0:IntInf.int)
                    fun shell current =
                      (tick 2;ignore (G.node_scope graph current);
                       case G.view graph current of
                         G.Application (operator,_) =>
                           (if Redblackset.member (!apps,G.node_id current)
                              then () else
                              (tick 2;apps := Redblackset.add
                                (!apps,G.node_id current);
                               app_count := !app_count+1);
                            shell operator)
                       | _ => ())
                    fun law current nonempty =
                      (tick 2;fact_count := !fact_count+1;
                       if nonempty then shell current else ())
                    val _ = List.app (fn step =>
                      (valid step;case recipe step of
                         ClosedLaw (current,_,_) => law current
                           (not (null (premise_list step)))
                       | ObligationLaw {law=current,...} => law current true
                       | _ => ())) steps
                    fun count [] total = (tick 1;total)
                      | count (_::rest) total =
                          (tick 1;count rest (total+1))
                    val sources = count canonical_sources
                      (count extra_sources (0:IntInf.int))
                  in IntInf.max (0,10* !app_count+
                       4*(!fact_count+sources)-3) end)
                fun planned () =
                let
                val facts = ref ([]:P.closed_fact list)
                val conversions = ref ([]:P.closed_conversion list)
                val roots = ref ([]:G.node list)
                val targets = ref ([]:G.node list)
                val laws = ref ([]:P.closed_law_spine list)
                val law_facts = ref (Redblackmap.mkDict compare :
                  (int,P.closed_fact) Redblackmap.dict)
                val obligations = ref
                  ([]:(G.node * P.source_realization) list)
                val needs_preprocessing = ref false
                fun conversion value = meta (fn () =>
                  (tick 3;roots := copy_append (K.graph_roots value) (!roots);
                   facts := copy_append (K.graph_closed_facts value) (!facts);
                   conversions := copy_append
                     (K.graph_conversions value) (!conversions)))
                fun rule step =
                  let
                    fun closed law theorem arguments =
                      let val (fact,spine) =
                            capture step law theorem arguments
                      in meta (fn () =>
                        (tick 4;laws := spine :: !laws;
                         law_facts := Redblackmap.insert
                           (!law_facts,G.node_id law,fact))) end
                    val arguments = meta (fn () =>
                      (valid step;list_map node (premise_list step)))
                  in case recipe step of
                      ClosedLaw (law,theorem,_) => closed law theorem arguments
                    | ObligationLaw {law,theorem,obligation,...} =>
                        let val proof = obligation_source obligation
                            val _ = meta (fn () =>
                              (tick 2;obligations :=
                                (obligation,proof) :: !obligations))
                        in closed law theorem
                          (append arguments [obligation]) end
                    | PreprocessedSource => meta (fn () =>
                        (tick 1;case temporary_ports of
                           [] => (tick 1;needs_preprocessing := true)
                         | _ =>
                             let val target=node step val _=tick 3
                             in if List.exists (fn original =>
                                 (tick 3;target=original)) canonical_sources
                               then () else
                                 (tick 1;needs_preprocessing := true) end))
                    | BooleanAliases values => List.app conversion values
                    | BooleanSchemas values => meta (fn () =>
                        List.app (fn value =>
                          (tick 2;roots :=
                            copy_append (K.graph_roots value) (!roots)))
                          values)
                    | OwnedAliasTransitivity {premises,target} =>
                        (meta (fn () => tick 1);
                         List.app conversion (target::premises))
                    | OwnedNegatedSymmetry value => meta (fn () =>
                        (tick 2;roots :=
                          copy_append (K.graph_roots value) (!roots)))
                    | _ => ()
                  end
                val _ = List.app rule steps
                val _ = meta (fn () => List.app (fn step =>
                  (valid step;case recipe step of
                     ClosedLaw _ => () | ObligationLaw _ => ()
                   | Assumption => () | PreprocessedSource => ()
                   | Boolean =>
                       (* The existing Boolean assembler discovers gates
                          in the target AND every actual premise, including
                          an assumption that is not itself a saved cut. *)
                       (tick 2;targets := node step :: copy_append
                         (list_map (fn premise =>
                           (valid premise;node premise)) (premise_list step))
                         (!targets))
                   | _ => (tick 2;targets := node step :: !targets))) steps)
                val validation = case preprocessing of SOME value => value
                  | NONE => raise ERR "bounded_completion"
                      "missing original preprocessing"
                val _ = if not (!needs_preprocessing) then () else
                  meta (fn () =>
                    (tick 3;roots :=
                       copy_append preprocessing_roots (!roots);
                     facts := copy_append
                       (GP.closed_facts validation) (!facts);
                     conversions := copy_append
                       (GP.conversions validation) (!conversions)))
                val receipts = meta (fn () =>
                  copy_append (list_map #2 (!cuts))
                    (list_map #2 (!obligations)))
                val plan = prepare (!roots) (!facts) (!conversions) receipts
                  (!targets) true true (!laws)
                val size = P.source_cut_rule_footprint_for work plan
                val _ = work_checkpoint "bounded.plan" (fn () =>
                  " serial=" ^ Int.toString (serial selected) ^
                  " recipe=" ^ recipe_label selected ^
                  " steps=" ^ Int.toString step_count ^
                  " raw=" ^ IntInf.toString (#raw size) ^
                  " inclusive=" ^ IntInf.toString (#inclusive size))
              in if #raw size+4<=cap andalso #inclusive size+4<=cap then
                let
                  val block = P.freeze_source_cut_rule_plan work plan
                  val native = P.source_cut_block_for work block
                  val _ = work_phase "bounded.import.before"
                  val incoming = map_external (fn (step,receipt) =>
                    (serial step,P.source_cut_edge_for work block receipt))
                    (!cuts)
                  val obligation_edges = map_external (fn (target,receipt) =>
                    (target,P.source_cut_edge_for work block receipt))
                    (!obligations)
                  val _ = work_phase "bounded.import.after"
                  val memo = ref (Redblackmap.mkDict compare)
                  val _ = meta (fn () => List.app (fn (key,edge) =>
                    (tick 2;memo := Redblackmap.insert (!memo,key,edge)))
                    incoming)
                  val derived = if !needs_preprocessing then
                      GP.assembler_with_work work validation native
                    else (fn _ => NONE)
                  fun selected_step (step as Step {serial,fact,...}) =
                    (tick 1;Step {serial=serial,fact=fact,
                      premises=premise_list step,recipe=recipe step,
                      pruned=pruned step})
                  fun law_source target = case List.find
                      (fn (saved,_) => (tick 1;saved=target))
                        obligation_edges of
                      SOME (_,edge) => edge
                    | NONE => case Redblackmap.peek
                        (!law_facts,G.node_id target) of
                        SOME fact => P.closed native fact
                      | NONE => source native target
                  fun assemble recorded =
                    let val step=selected_step recorded
                    in (valid step;case Redblackmap.peek (!memo,serial step) of
                      SOME edge => (observe_assembly graph true;edge)
                    | NONE =>
                      let
                        val _ = observe_assembly graph false
                        fun premises () = list_map
                          (fn premise => (node premise,assemble premise))
                          (premise_list step)
                        fun clauses () = list_map (fn premise =>
                          C.from_source native (clause_of premise)
                            (assemble premise)) (premise_list step)
                        val edge=case temporary_ports of
                            []=>assemble_recipe native law_source derived
                              premises clauses
                              (fn _ => raise ERR "bounded_completion"
                                "scoped recipe was not closed before assembly")
                              local_assumptions (apply_law native) step
                          | _=>
                              (tick 1;case recipe step of Boolean=>
                                let val actual=premises ()
                                    val _=tick 3
                                in case P.prepare_boolean_projection work
                                    native{target=node step,premises=actual}of
                                    SOME plan=>P.execute_boolean_projection
                                      work plan
                                  | NONE=>raise ERR "bounded_completion"
                                      "actual projection eligibility differs"
                                end
                              | PreprocessedSource =>
                                  let val target=node step val _=tick 3
                                  in if List.exists (fn original =>
                                      (tick 3;target=original))
                                        canonical_sources then
                                      source native target
                                    else assemble_recipe native law_source
                                      derived premises clauses
                                      (fn _ => raise ERR "bounded_completion"
                                "scoped recipe was not closed before assembly")
                                      local_assumptions
                                      (apply_law native) step end
                              | _=>assemble_recipe native law_source derived
                                  premises clauses
                                  (fn _ => raise ERR "bounded_completion"
                                "scoped recipe was not closed before assembly")
                                  local_assumptions (apply_law native) step)
                        val _ = tick 2
                        val _ = memo := Redblackmap.insert
                          (!memo,serial step,edge)
                      in edge end) end
                  val _ = work_phase "bounded.assemble.before"
                  val edge = meta (fn () => assemble selected)
                  val _ = work_phase "bounded.assemble.after"
                  val _ = work_phase "bounded.realize.before"
                  val result = P.realize_source_cut_receipt work block
                    (node selected) edge
                  val _ = work_phase "bounded.realize.after"
                  val _ = save selected result
                  val _ = work_phase "bounded.save.after"
                in result end
              else
                (work_checkpoint "bounded.unfit" (fn () =>
                   " serial=" ^ Int.toString (serial selected) ^
                   " recipe=" ^ recipe_label selected ^
                   " steps=" ^ Int.toString step_count ^
                   " raw=" ^ IntInf.toString (#raw size) ^
                   " inclusive=" ^ IntInf.toString (#inclusive size));
                 split selected steps step_count)
              end
              in if minimum+4>cap andalso step_count>1 then
                   (work_checkpoint "bounded.lower-bound" (fn () =>
                      " serial=" ^ Int.toString (serial selected) ^
                      " steps=" ^ Int.toString step_count ^
                      " minimum=" ^ IntInf.toString minimum);
                    split selected steps step_count)
                 else planned ()
              end
          and split selected steps step_count =
            if step_count<=1 then
              single selected
            else
              let
                val ranks = meta (fn () =>
                  let fun add [] _ table = table
                        | add (step::rest) index table =
                          (tick 2;add rest (index+1)
                            (Redblackmap.insert (table,serial step,index)))
                  in add steps 0 (Redblackmap.mkDict compare) end)
                val middle = step_count div 2
                val visited = ref (Redblackset.empty compare)
                fun close step = case find step of SOME _ => () | NONE =>
                  let val state = meta (fn () =>
                    (valid step;
                     if Redblackset.member (!visited,serial step) then NONE
                     else (visited := Redblackset.add (!visited,serial step);
                       Redblackmap.peek (ranks,serial step))))
                  in case state of NONE => ()
                    | SOME index => if index<middle then ignore (prove step)
                      else List.app close (premise_list step) end
                val _ = close selected
              in prove selected end
          and single selected =
            case recipe selected of
              ClosedLaw (law,theorem,_) =>
                sequential selected law theorem
                  (map_external (fn step => (node step,prove step))
                    (premise_list selected))
            | ObligationLaw {law,theorem,obligation,...} =>
                sequential selected law theorem
                  (append (map_external (fn step => (node step,prove step))
                    (premise_list selected))
                   [(obligation,obligation_source obligation)])
            | _ => raise ERR "bounded_completion"
                "one genuine rule still exceeds the original compact cap"
          and sequential selected law theorem arguments =
            let
              val (_,spine) = capture selected law theorem
                (meta (fn () => list_map #1 arguments))
              val first = P.closed_law_spine_prefix_for work spine
                (if null arguments then 0 else 1)
              val (fact,_) = capture selected law theorem
                (meta (fn () => list_map #1 arguments))
              val result = use_closed_law (node selected)
                law fact first arguments
              val _ = save selected result
            in result end
          and use_closed_law destination law fact first arguments =
            let
              fun next current incoming [] =
                    if current=destination then incoming else
                      raise ERR "bounded_completion" "wrong law tail target"
                | next current incoming ((premise,proof)::rest) =
                  let
                    val plan = P.prepare_source_cut_rule_plan work
                      {frame=frame,roots=[],
                       additional_sources=local_assumptions,closed_facts=[],
                       conversions=[],receipts=[incoming,proof],targets=[],
                       boolean=false,congruence=false}
                    val block = P.freeze_source_cut_rule_plan work plan
                    val native = P.source_cut_block_for work block
                    val law_edge = P.source_cut_edge_for work block incoming
                    val arg_edge = P.source_cut_edge_for work block proof
                    val tail = meta (fn () => case G.view graph current of
                        G.Application (_,tail) => tail
                      | _ => raise ERR "bounded_completion"
                          "recorded source law lost its implication")
                    val edge = meta (fn () => apply_law native
                      {law=(current,law_edge),target=tail,
                       premises=[(premise,arg_edge)]})
                    val output = P.realize_source_cut_receipt work block
                      tail edge
                  in next tail output rest end
              val (head_args,remaining) = case arguments of
                  [] => ([],[]) | first::rest => ([first],rest)
              val plan = prepare [] [] []
                (meta (fn () => list_map #2 head_args)) []
                false false [first]
              val block = P.freeze_source_cut_rule_plan work plan
              val native = P.source_cut_block_for work block
              val incoming = map_external (fn (node,receipt) =>
                (node,P.source_cut_edge_for work block receipt)) head_args
              val target = case arguments of [] => law
                | _ => meta (fn () => case G.view graph law of
                    G.Application (_,tail) => tail
                  | _ => raise ERR "bounded_completion" "missing law tail")
              val edge = meta (fn () => apply_law native
                {law=(law,P.closed native fact),target=target,
                 premises=incoming})
              val proof = P.realize_source_cut_receipt work block target edge
              val result = next target proof remaining
            in result end
          and forced_source obligation =
            let
              (* The existing checked worker owns forcing and alignment.
                 This port does not turn its open theorem into a Source.
                 It first closes the actual original Hyp and records that
                 genuine closed law, then uses ordinary named Source MP. *)
              fun retained () = meta (fn () =>
                (tick 2;validate_force_target obligation;
                 Redblackmap.peek (!obligation_admissions,
                   G.node_id obligation)))
              val (theorem,admissions) = case retained () of
                  SOME result => result
                | NONE =>
                    let
                      val prior = meta (fn () =>
                        (tick 1;Redblackmap.peek (!obligation_proofs,
                          G.node_id obligation)))
                      val _ = case prior of NONE => ()
                        | SOME _ => raise ERR "bounded_completion"
                            "checked obligation lacks native admission"
                      val theorem = force_obligation obligation
                      val saved = case retained () of SOME result => result
                        | NONE => raise ERR "bounded_completion"
                            "owned forcing did not retain native admission"
                      val _ = meta (fn () =>
                        (tick 2;obligation_proofs := Redblackmap.insert
                          (!obligation_proofs,G.node_id obligation,theorem)))
                    in saved end
              val (selected,law,closed) = meta (fn () =>
                let
                  val _ = validate_owned work
                  val _ = validate_force_target obligation
                  val limits = W.semantic_limits work
                  val input = IntInf.fromInt (#input_limit limits)
                  val output = IntInf.fromInt (#output_limit limits)
                  val _ = tick 2
                  val hypotheses = Thm.hyp theorem
                  val conclusion = Thm.concl theorem
                  val _ = if Portable.pointer_eq
                      (conclusion,G.representative graph obligation)
                    then () else raise ERR "bounded_completion"
                      "checked forced conclusion lost its exact endpoint"
                  fun pay amount =
                    let val available = IntInf.fromInt
                          (W.work_limit work - #charged (W.audit work))
                    in if amount >= 0 andalso amount <= available then
                         tick (IntInf.toInt amount)
                       else W.abort_work_limit work end
                  fun type_weight ty =
                    let
                      fun visit [] count total = (tick 1;total)
                        | visit (current::rest) count total =
                          (tick 2;
                           if count >= ordinary_limit then
                             admission_failure
                               "forced law Type exceeds caller input"
                           else if Type.is_vartype current then
                             let val bytes = String.size
                                   (Type.dest_vartype current)
                                 val _ = tick bytes
                             in visit rest (count+1)
                                  (total+1+IntInf.fromInt bytes) end
                           else
                             let val children = #2 (Type.dest_type current)
                             in visit (copy_append children rest) (count+1)
                                  (total+1) end)
                      val value = visit [ty] 0 (0:IntInf.int)
                      val _ = validate_owned work
                      val _ = check_type ty
                      val _ = validate_owned work
                    in value end
                  type forced_profile =
                    {raw:IntInf.int,inc:IntInf.int,weight:IntInf.int}
                  fun profile term : forced_profile =
                    let
                      fun walk current count =
                        (tick 2;
                         if count >= ordinary_limit then
                           admission_failure
                             "forced law operand exceeds caller input"
                         else
                           let val own = type_weight (Term.type_of current)
                           in if Term.is_comb current then
                               let val _ = tick 2
                                   val (left,right) = Term.dest_comb current
                                   val (a,n) = walk left (count+1)
                                   val (b,m) = walk right n
                               in ({raw=1+ #raw a+ #raw b,
                                    inc=1+ #inc a+ #inc b,
                                    weight=1+own+ #weight a+ #weight b},m) end
                              else if Term.is_abs current then
                               let val _ = tick 3
                                   val (binder,body) = Term.dest_abs current
                                   val domain = type_weight
                                     (Term.type_of binder)
                                   val (value,n) = walk body (count+1)
                               in ({raw=1+ #raw value,inc=2+ #inc value,
                                    weight=2+own+domain+ #weight value},n) end
                              else
                               let val bytes = if Term.is_var current then
                                     String.size (#1 (Term.dest_var current))
                                   else if Term.is_const current then
                                     let val {Thy,Name,...} =
                                           Term.dest_thy_const current
                                     in String.size Thy+String.size Name end
                                   else 0
                                   val _ = tick bytes
                               in ({raw=1,inc=1,
                                    weight=1+own+IntInf.fromInt bytes},
                                   count+1) end
                           end)
                    in #1 (walk term 0) end
                  fun check limit (value:forced_profile) =
                    if #raw value <= limit andalso #inc value <= limit
                        andalso #raw value <= cap andalso #inc value <= cap
                      then () else raise ERR "bounded_completion"
                        "forced law native input or output exceeds caller"
                  fun root_bound term [] = raise ERR "bounded_completion"
                        "forced native operand has no retained admission"
                    | root_bound term ((native,bound)::rest) =
                        (tick 1;if Portable.pointer_eq (term,native) then
                           SmtReplayImport.raw_bound_data bound term
                         else root_bound term rest)
                  val _ = List.app (fn term =>
                    let val _ = tick 2 val bound = root_bound term admissions
                    in if #raw_upper bound <= input andalso
                        #inc_upper bound <= input andalso
                        #raw_upper bound <= cap andalso #inc_upper bound <= cap
                      then () else raise ERR "bounded_completion"
                        "forced native admission exceeds caller input"
                    end) (conclusion::hypotheses)
                  val actual = profile conclusion
                  val _ = check input actual
                  val held = list_map (fn term =>
                    let val value = profile term
                        val _ = check input value
                    in (term,value) end) hypotheses
                  (* Keep every original occurrence whose exact native
                     pointer is used, including duplicate Source slots. *)
                  fun member term [] = (tick 1;false)
                    | member term ((hypothesis,_)::rest) =
                        (tick 1;Portable.pointer_eq (term,hypothesis) orelse
                          member term rest)
                  fun choose [] _ = (tick 1;[])
                    | choose (source::rest) index =
                        let val _ = tick 2
                            val _ = ignore (G.node_scope graph source)
                            val native = G.representative graph source
                        in if member native held then
                             let val value = profile native
                                 val _ = check input value
                             in (index,source,native,value) ::
                                  choose rest (index+1) end
                           else choose rest (index+1) end
                  val selected = choose canonical_sources 0
                  val _ = List.app (fn (term,_) =>
                    if List.exists (fn (_,_,native,_) =>
                        (tick 1;Portable.pointer_eq (term,native))) selected
                      then () else raise ERR "bounded_completion"
                        "forced Hyp has no actual original Source") held
                  val implication = profile boolSyntax.implication
                  val partial_type = #2 (Type.dom_rng
                    (Term.type_of boolSyntax.implication))
                  val partial_weight = type_weight partial_type
                  val bool_weight = type_weight Type.bool
                  fun name_bytes term =
                    let val _ = tick 2
                        val {Thy,Name,...} = Term.dest_thy_const term
                        val bytes = String.size Thy+String.size Name
                        val _ = tick bytes
                    in IntInf.fromInt bytes end
                  val imp_bytes = name_bytes boolSyntax.implication
                  val eq_bytes = name_bytes boolSyntax.equality
                  (* Both actual typed heads have Bool->Bool->Bool. Their
                     distinct atomic declaration bytes are still counted. *)
                  val imp_shell = 2+ #weight implication+
                    partial_weight+bool_weight
                  val eq_shell = imp_shell-imp_bytes+eq_bytes
                  fun conditional (premise:forced_profile)
                      (tail:forced_profile) : forced_profile =
                    {raw=3+ #raw premise+ #raw tail,
                     inc=3+ #inc premise+ #inc tail,
                     weight=imp_shell+ #weight premise+ #weight tail}
                  fun forecast [] = (tick 1;(actual,held))
                    | forecast ((_,_,native,premise)::rest) =
                        let
                          val (tail,hypotheses) = forecast rest
                          val result = conditional premise tail
                          val _ = check input premise
                          val _ = check input tail
                          val _ = check output result
                          fun retained [] = (tick 1;[])
                            | retained ((term,value)::more) =
                              (tick 1;check input value;
                               if Portable.pointer_eq (native,term) then
                                 retained more
                               else (check output value;
                                 (term,value)::retained more))
                          val remaining = retained hypotheses
                          val hyp_count = List.foldl (fn (_,n) =>
                            (tick 1;n+1)) (0:IntInf.int) hypotheses
                          val hyp_weight = List.foldl
                            (fn ((_,value),total) =>
                              (tick 1;total+ #weight value))
                            (0:IntInf.int) hypotheses
                          (* Actual DISCH input, retained Hyp, result and
                             prospective hypothesis comparisons. Duplicate
                             Source occurrences remain separate arguments,
                             even after the inner DISCH removed their Hyp. *)
                          val _ = pay (3+ #weight premise+ #weight tail+
                            #weight result+hyp_weight+
                            hyp_count*(1+ #weight premise)+hyp_weight)
                        in (result,remaining) end
                  val (result,remaining) = forecast selected
                  val _ = if null remaining then () else
                    raise ERR "bounded_completion"
                      "forced law prospective Hyp is not closed"
                  val equality =
                    {raw=3+2* #raw result,inc=3+2* #inc result,
                     weight=eq_shell+2* #weight result}
                  val _ = if null selected then check output actual else
                    (check input result;check output equality;
                     check input equality;check output result;
                     (* ALPHA and EQ_MP actual operands/results; bounded
                        matching and empty-Hyp/tag validation precede them. *)
                     pay (8+4* #weight result+2* #weight equality))
                  val arguments = list_map (fn (_,node,_,_) => node) selected
                  val argument_count = List.foldl (fn (_,count) =>
                    (tick 1;count+1)) (0:IntInf.int) arguments
                  val _ = pay (4+5*argument_count)
                  val law = if null arguments then obligation else
                    R.implication graph scope arguments obligation
                  (* P.record_closed_exact admits a unique graph Type
                     portfolio. Check that actual future record now, before
                     DISCH, while its graph endpoints remain bounded DATA. *)
                  val record_seen = ref (Redblackset.empty compare)
                  val remaining_types = ref template_limit
                  fun record_types [] = tick 1
                    | record_types ([]::rest) = (tick 1;record_types rest)
                    | record_types ((ty::more)::rest) =
                      (tick 2;
                       if !remaining_types=0 then raise ERR
                         "bounded_completion"
                         "forced closed-record Type portfolio exceeds cap"
                       else remaining_types := !remaining_types-1;
                       if Type.is_vartype ty then record_types (more::rest)
                       else record_types
                         ((#2 (Type.dest_type ty))::more::rest))
                  fun record_nodes [] = tick 1
                    | record_nodes ((caller,current)::rest) =
                      (tick 3;ignore (G.node_scope graph current);
                       ignore (G.closure_root graph caller current);
                       if Redblackset.member
                           (!record_seen,G.node_id current) then
                         record_nodes rest
                       else
                         (tick 2;record_seen := Redblackset.add
                            (!record_seen,G.node_id current);
                          record_types [[G.type_of graph current]];
                          case G.view graph current of
                            G.Application (left,right) =>
                              (tick 4;record_nodes
                                ((caller,left)::(caller,right)::rest))
                          | G.AdmittedBinder _ =>
                              let val _ = tick 2
                                  val closure =
                                    G.binder_closure graph caller current
                                  val _ = tick 1
                                  val data = G.binder_closure_data
                                    graph caller closure
                              in tick 4;record_nodes
                                ((#binder_frame data,#binder data)::
                                 (#body_frame data,#body data)::rest) end
                          | G.OpaqueRetained =>
                              let
                                val _ = tick 2
                                val known =
                                  G.unfolded_nodes graph G.RawNodes
                                    template_limit current
                                val complete =
                                  G.unfolded_nodes graph
                                    G.BinderInclusiveNodes template_limit
                                    current
                                val _ = case (known,complete) of
                                    (SOME _,SOME _) => ()
                                  | _ =>
                                      let
                                        val target =
                                          G.representative graph current
                                        fun derive [] = raise ERR
                                              "bounded_completion"
                                              "opaque operand lacks admission"
                                          | derive ((_,bound)::rest) =
                                              (tick 1;case
                                                SI.raw_bound_subterm
                                                  bound {target=target,
                                                    observe=fn () => tick 1} of
                                                 SOME found => found
                                               | NONE => derive rest)
                                        val bound = derive admissions
                                      in ignore
                                      (G.profile_bounded_native_observed
                                        graph caller
                                        {node=current,bound=bound,
                                         maximum=IntInf.toInt
                                          (IntInf.min (input,
                                            IntInf.min (output,cap))),
                                         observe=fn () => tick 1}) end
                              in record_nodes rest end
                          | _ => record_nodes rest))
                  val _ = record_nodes [(scope,law)]
                  val _ = List.app (fn (metric,predicted) =>
                    case G.unfolded_nodes graph metric template_limit law of
                      SOME count =>
                        (tick count;if IntInf.fromInt count=predicted then ()
                         else raise ERR "bounded_completion"
                           "forced law prospective metric differs")
                    | NONE => raise ERR "bounded_completion"
                        "forced law has no admitted graph metric")
                    [(G.RawNodes,#raw result),
                     (G.BinderInclusiveNodes,#inc result)]
                  val closed = if null selected then theorem else
                    let val proof = List.foldr
                          (fn ((_,_,native,_),proof) =>
                            SmtReplayRuleObservation.DISCH native proof)
                          theorem selected
                        val _ = if null (Thm.hyp proof) then () else
                          raise ERR "bounded_completion"
                            "forced law retained an original Hyp"
                        val expected = G.representative graph law
                        val aligned = SmtReplayRuleObservation.ALPHA
                          (Thm.concl proof) expected
                    in SmtReplayRuleObservation.EQ_MP aligned proof end
                in (selected,law,closed) end)
              val fact = record_exact (fn () =>
                (tick 2;validate_force_target obligation)) law closed
              val arguments = meta (fn () =>
                list_map (fn (_,node,_,_) => node) selected)
              val spine = P.prepare_closed_law_spine work
                {frame=frame,fact=fact,premises=arguments,target=obligation}
              val first = P.closed_law_spine_prefix_for work spine
                (if null arguments then 0 else 1)
              fun occurrence (index,current,_,_) =
                let val plan = prepare [] [] [] [] [current] false false []
                    val block = P.freeze_source_cut_rule_plan work plan
                    val native = P.source_cut_block_for work block
                    val edge = meta (fn () => P.source native index)
                in (current,P.realize_source_cut_receipt work
                  block current edge) end
              val incoming = map_external occurrence selected
            in use_closed_law obligation law fact first incoming end
          and obligation_source obligation =
            if meta (fn () => List.exists
                (fn source => (tick 1;source=obligation)) canonical_sources)
              then original obligation
            else if meta (fn () => List.exists
                (fn port => (tick 1;port=obligation)) temporary_ports)
              then temporary obligation
            else if meta (fn () => List.exists
                (fn ancestor => (tick 1;ancestor=obligation)) ancestors)
              then raise ERR "obligation" "cyclic deferred proof dependency"
            else
              let
                val candidates = meta (fn () =>
                  (tick 1;Option.getOpt (Redblackmap.peek
                    (checked_facts,G.node_id obligation),[])))
                fun independent selected = case recipe selected of
                    Assumption => false | ObligationLaw _ => false
                  | _ =>
                    let
                      val seen = ref (Redblackset.empty compare)
                      fun forbidden target =
                        (tick 1;target=obligation orelse List.exists
                          (fn held => (tick 1;target=held)) ancestors)
                      fun inspect current =
                        (valid current;
                         if Redblackset.member (!seen,serial current) then
                           true
                         else
                           let val _ = tick 2
                               val _ = seen := Redblackset.add
                                 (!seen,serial current)
                               val safe = case recipe current of
                                   ObligationLaw {obligation=target,...} =>
                                     not (forbidden target)
                                 | NativeObligation _ =>
                                     not (forbidden (node current))
                                 | _ => true
                           in safe andalso List.all inspect
                             (premise_list current) end)
                    in inspect selected end
                fun generalized () =
                  let val body = meta (fn () =>
                      (tick 1;Redblackmap.peek
                        (!generalizations,G.node_id obligation)))
                  in case body of NONE => forced_source obligation
                    | SOME (variables,body) =>
                  let
                    val choices = meta (fn () =>
                      (tick 1;Option.getOpt (Redblackmap.peek
                        (checked_facts,G.node_id body),[])))
                    (* GEN candidate selection must inspect the actual
                       surviving Hyp, not reject the first proof and catch
                       a retired Work later. Native free_in sees only this
                       fully bounded, authentically retained portfolio. *)
                    fun admissible proof =
                      let val theorem =
                            P.source_realization_theorem_for work proof
                          val hypotheses = Thm.hyp theorem
                      in meta (fn () =>
                        let
                          fun types [] = tick 1
                            | types ([]::rest) = (tick 1;types rest)
                            | types ((ty::more)::rest) =
                              (tick 2;if Type.is_vartype ty then
                                  types (more::rest)
                                else (tick 2;types
                                  ((#2 (Type.dest_type ty))::more::rest)))
                          fun syntax [] = tick 1
                            | syntax (term::rest) =
                              (tick 1;types [[Term.type_of term]];
                               if Term.is_comb term then
                                 let val (f,x) = Term.dest_comb term
                                 in syntax (f::x::rest) end
                               else if Term.is_abs term then
                                 let val (v,b) = Term.dest_abs term
                                 in syntax (v::b::rest) end
                               else syntax rest)
                          fun quote term =
                            let
                              val raw = case
                                  SmtReplayImport.bounded_raw_size
                                    ordinary_limit term of SOME count => count
                                | NONE => admission_failure
                                    "bounded GEN Hyp exceeds caller input"
                              (* syntax visits each actual binder atom
                                 as well as the body; incidence is paid
                                 without inventing a second input bound. *)
                            in tick raw;syntax [term] end
                          val _ = List.app quote hypotheses
                          val _ = List.app (fn variable =>
                            (tick 1;types [[Term.type_of variable]])) variables
                        in not (List.exists (fn variable =>
                          (tick 1;List.exists (fn hypothesis =>
                            (tick 1;Term.free_in variable hypothesis))
                            hypotheses))
                          variables) end) end
                    fun choose [] = NONE
                      | choose (candidate::rest) =
                          if not (meta (fn () =>
                              (valid candidate;independent candidate)))
                            then choose rest else
                            let val proof = bounded_complete_with_ports work
                                  candidate []
                                    (meta (fn () =>
                                      (tick 1;obligation::ancestors)))
                                    temporary_ports
                            in if admissible proof then SOME proof else
                                 choose rest end
                  in case choose choices of NONE => forced_source obligation
                    | SOME proof =>
                  let
                    fun checked ty =
                      (validate_owned work;check_type ty;validate_owned work)
                    val plan = P.prepare_source_generalization work
                      {source=proof,target=obligation,check_type=checked}
                    val generated = P.execute_source_generalization work plan
                  in SmtReplayOwnedSourceGeneralizationConsumer.execute work
                    {generalized=generated,check_type=checked} end end end
                fun actual_candidates [] = generalized ()
                  | actual_candidates (candidate::rest) =
                      if meta (fn () =>
                          (valid candidate;case recipe candidate of
                             Assumption => true | ObligationLaw _ => true
                           | _ => false)) then actual_candidates rest
                      else
                        (case actual_dependency_candidate work candidate
                            obligation ancestors of
                           NONE => actual_candidates rest
                         | SOME proof => proof)
              in case meta (fn () => List.find
                  (fn step => (valid step;independent step)) candidates) of
                  SOME candidate => bounded_complete_with_ports work candidate
                    [] (meta (fn () => (tick 1;obligation::ancestors)))
                    temporary_ports
                | NONE => actual_candidates candidates
              end
          and bounded_source selected locals =
            if meta (fn () =>
                let fun same ([],[]) = (tick 1;true)
                      | same (a::more,b::rest) =
                          (tick 1;a=b andalso same (more,rest))
                      | same _ = (tick 1;false)
                in same (locals,local_assumptions) end)
              then prove selected else
              bounded_complete_with_ports work selected locals ancestors
                temporary_ports
          val result = prove root
          val _ = validate_owned work
        in result end
      (* A trial has its own local receipt/plan maps. Every provisional
         H/ancestor is a genuine additional Source occurrence. Acceptance
         comes only from the finished receipt's actual absence of ALL such
         occurrences, never from theorem Hyp or syntactic dependency flags. *)
      and actual_dependency_candidate work candidate obligation ancestors =
        let
          val _ = validate_owned work
          val ports = W.with_step work (fn () =>
            (validate_owned work;W.spend work 1;obligation::ancestors))
          val proof = bounded_complete_with_ports work candidate [] ports ports
          val data = P.source_realization_data_for work proof
          val used = W.with_step work (fn () =>
            let
              val _ = validate_owned work
              fun forbidden [] = (W.spend work 1;false)
                | forbidden ((_,node)::more) =
                    (W.spend work 1;List.exists (fn port =>
                      (W.spend work 1;node=port)) ports orelse forbidden more)
            in forbidden (#source_occurrences data) end)
        in if used then NONE else SOME proof end
      (* Optional retry eligibility, never proof permission. Its full
         ordinary forest overestimates every cut forest; unknown recipes
         retain the old force route. Only the resulting genuine receipt's
         actual Source absence can authorize acceptance. *)
      and actual_dependency_eligible work candidate obligation ancestors =
        W.with_step work (fn () =>
          let
            fun tick n = (validate_owned work;W.spend work n)
            fun compare pair = (tick 1;Int.compare pair)
            fun member _ [] = (tick 1;false)
              | member node (saved::rest) =
                  (tick 1;node=saved orelse member node rest)
            val _ = tick 4
            val ports = obligation::ancestors
            val seen = ref (Redblackset.empty compare)
            fun copy [] tail = (tick 1;tail)
              | copy (node::rest) tail =
                  (tick 2;node::copy rest tail)
            val roots = ref (copy canonical_sources ports)
            val laws = ref ([]:G.node list)
            val law_count = ref (0:IntInf.int)
            fun current node =
              (tick 2;ignore (G.closure_root graph scope node))
            fun projected target premises =
              let val _ = current target
                  val visited = ref (Redblackset.empty compare)
                  fun walk node =
                    (current node;tick 1;
                     if node=target then true
                     else if Redblackset.member
                         (!visited,G.node_id node) then false
                     else
                       (tick 2;visited := Redblackset.add
                          (!visited,G.node_id node);
                        case G.view graph node of
                          G.Application (partial,right) =>
                            (current partial;case G.view graph partial of
                              G.Application (head,left) =>
                                (current head;tick 1;
                                 case G.view graph head of
                                   G.Constant _ =>
                                     same_constant graph head
                                       boolSyntax.conjunction andalso
                                     (walk left orelse walk right)
                                 | _ => false)
                            | _ => false)
                        | _ => false))
                  fun any [] = (tick 1;false)
                    | any (premise::rest) =
                        (tick 1;walk (node premise) orelse any rest)
              in tick 1;
                 (case G.view graph target of G.Constant _ =>
                    same_constant graph target boolSyntax.T
                  | _ => false) orelse any premises end
            fun inventory step =
              let val _ = current (node step)
              in if Redblackset.member (!seen,serial step) then true else
                let val _ = tick 3
                    val _ = seen := Redblackset.add (!seen,serial step)
                    val _ = roots := node step :: !roots
                    fun children [] = (tick 1;true)
                      | children (child::rest) =
                          (tick 1;inventory child andalso children rest)
                in case recipe step of
                    Assumption => member (node step) canonical_sources
                      orelse member (node step) ports
                  | PreprocessedSource =>
                      member (node step) canonical_sources
                  | Boolean => children (premise_list step) andalso
                      projected (node step) (premise_list step)
                  | ObligationLaw {obligation,law,...} =>
                      if not (member obligation ports) then false else
                        (current law;tick 3;law_count := !law_count+1;
                         laws := law :: !laws;
                         roots := law :: !roots;
                         children (premise_list step))
                  | _ => false
                end
              end
            fun count [] (n:IntInf.int) = (tick 1;n)
              | count (_::rest) n = (tick 1;count rest (n+1))
            val supported = inventory candidate
            (* Each law adds at most its ClosedWitness, one temporary
               support origin and one receipt target slot. Original prefix
               origins are shared exactly, but equal temporary occurrences
               are deliberately NOT identified by their syntax node. *)
            val upper = ref (4*(count canonical_sources (count ports 0))+
              12* !law_count)
            val visited = ref (Redblackset.empty compare)
            fun forest [] =
                  (tick 1;!upper+4<=IntInf.fromInt template_limit)
              | forest (node::rest) =
                  (current node;
                   if !upper+4>IntInf.fromInt template_limit then false
                   else if Redblackset.member (!visited,G.node_id node) then
                     forest rest
                   else
                     (tick 2;visited := Redblackset.add
                       (!visited,G.node_id node);
                      case G.view graph node of
                        G.Application (left,right) =>
                          (tick 3;upper := !upper+10;
                           forest (left::right::rest))
                      | G.Constant _ =>
                          (tick 1;upper := !upper+8;forest rest)
                      | _ => forest rest))
            fun metric kind law = G.unfolded_nodes_observed
              (fn () => tick 1) graph kind template_limit law
            fun known law = case (metric G.RawNodes law,
                metric G.BinderInclusiveNodes law) of
                (SOME raw,SOME inclusive) =>
                  SOME (raw<=template_limit andalso inclusive<=template_limit)
              | _ => NONE
            fun admit law = case known law of SOME yes => yes | NONE =>
              let
                val _ = current law
                val term = G.representative graph law
                val bound = SI.bounded_raw_size_with_bound_observed
                  {limit=template_limit,observe=fn () => tick 1} term
              in case bound of NONE => false | SOME bound =>
                let
                  val _ = tick 1
                  val data = SI.raw_bound_data bound term
                  val native_cap = IntInf.fromInt template_limit
                  fun profile [] = (tick 1;true)
                    | profile (node::rest) =
                        (current node;case G.view graph node of
                          G.Application (left,right) =>
                            (tick 2;profile (left::right::rest))
                        | G.OpaqueRetained =>
                            (case known node of SOME yes =>
                               yes andalso profile rest
                             | NONE =>
                                let val _ = tick 1
                                    val target = G.representative graph node
                                in case SI.raw_bound_subterm bound
                                    {target=target,observe=fn () => tick 1} of
                                    NONE => false
                                  | SOME child =>
                                      (ignore
                                        (G.profile_bounded_native_observed
                                          graph scope
                                          {node=node,bound=child,
                                           maximum=template_limit,
                                           observe=fn () => tick 1});
                                       profile rest)
                                end)
                        | _ => profile rest)
                in #raw_upper data<=native_cap andalso
                   #inc_upper data<=native_cap andalso profile [law] andalso
                   (case known law of SOME yes => yes | NONE => false)
                end
              end
            fun admitted [] = (tick 1;true)
              | admitted (law::rest) =
                  (tick 1;admit law andalso admitted rest)
            val forest_fits=supported andalso forest (!roots)
            val laws_fit=forest_fits andalso admitted (!laws)
            val _=work_checkpoint "actual-dependency.eligibility" (fn()=>
              " supported=" ^ Bool.toString supported ^
              " forest_fits=" ^ Bool.toString forest_fits ^
              " laws_fit=" ^ Bool.toString laws_fit)
          in laws_fit end)
      and bounded_complete work root locals ancestors =
        bounded_complete_with_ports work root locals ancestors []
      exception BoundedResult of Thm.thm
      fun complete root local_assumptions ancestors =
        let
          fun complete_phase phase = work_checkpoint phase (fn () =>
            " serial=" ^ Int.toString (serial root) ^ " locals=" ^
            Int.toString (List.length local_assumptions))
          val _ = complete_phase "complete.enter"
          fun bounded_result work =
            let
              val receipt = bounded_complete work root
                local_assumptions ancestors
              val receipt = List.foldr (fn (hypothesis,receipt) =>
                P.discharge_source_receipt_with_work work receipt
                  hypothesis) receipt local_assumptions
              val theorem = P.source_realization_theorem_for work receipt
            in raise BoundedResult theorem end
          val pruned_law = pruned root
          val seen = ref (Redblackset.empty Int.compare)
          val witnesses = ref (Redblackmap.mkDict Int.compare)
          val deferred = ref ([] : (step * G.node) list)
          val block_roots = ref []
          val alias_facts = ref ([] : P.closed_fact list)
          val alias_conversions = ref ([] : P.closed_conversion list)
          val obligations = ref ([] : G.node list)
          fun inventory step =
            if Redblackset.member (!seen,serial step) then () else
            (seen := Redblackset.add (!seen,serial step);
             block_roots := node step :: !block_roots;
             case recipe step of
                 Scope _ =>
                   let val law = R.implication graph scope local_assumptions
                         (node step)
                   in deferred := (step,law) :: !deferred;
                      block_roots := law :: !block_roots end
               | ClosedLaw (law,theorem,_) =>
                   (witnesses := Redblackmap.insert
                     (!witnesses,G.node_id law,theorem);
                    block_roots := law :: !block_roots;
                    List.app inventory (premise_list step))
               | ObligationLaw {obligation,law,theorem,...} =>
                   (obligations := obligation :: !obligations;
                    witnesses := Redblackmap.insert
                      (!witnesses,G.node_id law,theorem);
                    block_roots := obligation :: law :: !block_roots;
                    List.app inventory (premise_list step))
               | BooleanAliases conversions =>
                   (List.app (fn conversion =>
                      (block_roots := K.graph_roots conversion @ !block_roots;
                       alias_facts := K.graph_closed_facts conversion @
                         !alias_facts;
                       alias_conversions := K.graph_conversions conversion @
                         !alias_conversions)) conversions;
                    List.app inventory (premise_list step))
               | OwnedAliasTransitivity {premises,target} =>
                   (case owned_work of NONE => raise ERR "alias_transitivity"
                      "missing original Work"
                    | SOME work =>
                        (validate_owned work;
                         List.app (fn conversion =>
                           (K.validate_conversion_for work conversion;
                            block_roots := K.graph_roots conversion @
                              !block_roots;
                            alias_facts := K.graph_closed_facts conversion @
                              !alias_facts;
                            alias_conversions := K.graph_conversions
                              conversion @ !alias_conversions))
                           (target::premises);
                         List.app inventory (premise_list step)))

               | OwnedNegatedSymmetry conversion =>
                   (case owned_work of NONE => raise ERR "symm"
                      "owned schema lost original Work"
                    | SOME work =>
                        (validate_owned work;
                         K.validate_conversion_for work conversion;
                         block_roots := K.graph_roots conversion @
                           !block_roots;
                         List.app inventory (premise_list step)))
               | BooleanSchemas conversions =>
                   (List.app (fn conversion =>
                      block_roots := K.graph_roots conversion @ !block_roots)
                      conversions;
                    List.app inventory (premise_list step))
               | _ => List.app inventory (premise_list step))
          val _ = inventory root
          fun law step = case recipe step of
              ClosedLaw (law,_,_) => [law]
            | ObligationLaw {law,...} => [law] | _ => []
          val law_nodes = ref []
          val seen_laws = ref (Redblackset.empty Int.compare)
          fun laws step =
            if Redblackset.member (!seen_laws,serial step) then () else
            (seen_laws := Redblackset.add (!seen_laws,serial step);
             case recipe step of Scope _ => ()
               | _ => (law_nodes := law step @ !law_nodes;
                       List.app laws (premise_list step)))
          val _ = laws root
          (* Deferred/scope witnesses can retain original Source Hyp. The
             literal sparse finalizer admits only closed supplied laws;
             use genuine Source-cut receipts for these open imports. *)
          val _ = case owned_work of SOME work =>
              if pruned_law andalso
                  (not (null local_assumptions) orelse
                   not (null (!obligations)) orelse not (null (!deferred)))
                then bounded_result work else ()
            | NONE => ()
          val _ = List.app (fn obligation =>
            witnesses := Redblackmap.insert
              (!witnesses,G.node_id obligation,
               close_obligation ancestors obligation)) (!obligations)
          val source_nodes = canonical_sources @ local_assumptions @
            !law_nodes @ !obligations @ List.map #2 (!deferred)
          val closed_target = R.implication graph scope local_assumptions
            (node root)
          val scope_laws = List.foldl (fn ((step,law),table) =>
            Redblackmap.insert (table,serial step,law))
            (Redblackmap.mkDict Int.compare) (!deferred)
          val block = case owned_work of SOME work =>
              let val _ = validate_owned work
                  val validation = case preprocessing of SOME value => value
                    | NONE => raise ERR "owned_replay" "missing preprocessing"
                  val extras = local_assumptions @ !law_nodes @ !obligations @
                    List.map #2 (!deferred)
                  (* The original frontier retains every ordered Source
                     slot, including equal endpoints. source_nodes is
                     exactly its original prefix followed by extras. Each
                     leaf costs 1 plus its 3-node conjunction join, except
                     the last join. No App/constant estimate is used here. *)
                  val source_minimum = W.with_step work (fn () =>
                    let fun count [] total = (W.spend work 1;total)
                          | count (_::rest) total =
                              (W.spend work 2;count rest (total+1))
                        val slots = count source_nodes (0:IntInf.int)
                    in IntInf.max (1,4*slots-3) end)
                  val _ = work_checkpoint "complete.source-bound" (fn () =>
                    " serial=" ^ Int.toString (serial root) ^
                    " minimum=" ^ IntInf.toString source_minimum)
                  val _ = if source_minimum<=
                      IntInf.fromInt template_limit then () else
                    bounded_result work
                  val _ = complete_phase "frontier.before"
                  val frontier =
                    P.prepare_original_realization_frontier_with_extras work
                      {roots = closed_target ::
                         (preprocessing_roots @ !block_roots),
                       additional_sources = extras,
                       closed_facts = !alias_facts @
                         GP.closed_facts validation,
                       conversions = !alias_conversions @
                         GP.conversions validation}
                  val _ = complete_phase "frontier.after"
                  val footprint =
                    P.realization_frontier_footprint_for work frontier
                  val _ = work_checkpoint "complete.footprint" (fn () =>
                    " serial=" ^ Int.toString (serial root) ^
                    " raw=" ^ IntInf.toString (#raw footprint) ^
                    " inclusive=" ^ IntInf.toString (#inclusive footprint))
                  val _ = if #raw footprint<=IntInf.fromInt template_limit
                      andalso #inclusive footprint<=
                        IntInf.fromInt template_limit then () else
                    bounded_result work
              in action (fn () =>
                   let val _ = complete_phase "tables.before"
                       val tables = SmtResource.profile_phase
                         "cvc/graph-table-admission"
                         (P.prepare_owned_realization_tables work) frontier
                       val _ = complete_phase "tables.after"
                       val _ = complete_phase "freeze.before"
                       (* A common context restores discarded Sources.
                          Select sparse realization of the SAME retained
                          frontier, not another discovery or table pass. *)
                       val freeze = if pruned_law then
                           P.freeze_owned_needed_realization_tables_plan
                         else P.freeze_owned_realization_tables_plan
                       val block =
                         SmtResource.profile_phase "cvc/graph-freeze"
                           (freeze work) tables
                       val _ = complete_phase "freeze.after"
                   in block end)
              end
            | NONE => (case preprocessing of NONE => P.freeze graph
              {scope = scope,roots = closed_target :: !block_roots,
               sources = source_nodes,template_limit = template_limit}
            | SOME validation => P.freeze_with_conversions graph
              {scope = scope,roots =
                  closed_target :: (preprocessing_roots @ !block_roots),
               sources = source_nodes,closed_facts = GP.closed_facts validation,
               conversions = GP.conversions validation,
               template_limit = template_limit})
          val (_,indices) = List.foldl (fn (node,(index,table)) =>
            (index+1,Redblackmap.insert (table,G.node_id node,index)))
            (0,Redblackmap.mkDict Int.compare) source_nodes
          fun source node = case Redblackmap.peek (indices,G.node_id node) of
              SOME index => P.source block index
            | NONE => raise ERR "assemble" "assumption is outside source scope"
          val derived = case owned_work of SOME work => action (fn () =>
              case preprocessing of SOME validation =>
                GP.assembler_with_work work validation block
              | NONE => raise ERR "owned_replay" "missing preprocessing")
            | NONE => (case preprocessing of NONE => (fn _ => NONE)
              | SOME validation => GP.assembler validation block)
          val memo = ref (Redblackmap.mkDict Int.compare)
          fun assemble step = case Redblackmap.peek (!memo,serial step) of
              SOME edge => (observe_assembly graph true;edge)
            | NONE =>
                let val _ = observe_assembly graph false
                  val target = node step
                  fun premises () = List.map
                    (fn premise => (node premise,assemble premise))
                    (premise_list step)
                  fun clauses () = List.map (fn premise =>
                    C.from_source block (clause_of premise) (assemble premise))
                    (premise_list step)
                  val edge = assemble_recipe block source derived premises
                    clauses (fn selected => Redblackmap.find
                      (scope_laws,serial selected)) local_assumptions
                    (R.apply_law graph block) step
                  val _ = memo := Redblackmap.insert (!memo,serial step,edge)
                in edge end
          val edge = SmtResource.profile_phase "cvc/graph-construction"
            (fn () => action (fn () => assemble root)) ()
          val dependency_ids = action (fn () => P.dependencies block edge)
          val source_occurrences = ListPair.zip (source_nodes,
            List.tabulate (List.length source_nodes,fn index => index))
          val _ = if List.exists (fn (source,index) =>
              List.exists (fn ancestor => ancestor = source) ancestors andalso
              List.exists (fn dependency => dependency = index) dependency_ids)
              source_occurrences then raise ERR "obligation"
                "checked candidate retains its own deferred source" else ()
          val _ = List.app (fn (step,law) => case recipe step of
              Scope {hypothesis,body} =>
                let
                  (* Close every active local source in the child while it
                     is compact. The parent applies this conditional law to
                     its local edges before its own eventual discharge. *)
                  val theorem = complete body
                    (local_assumptions @ [hypothesis]) ancestors
                  val _ = if Portable.pointer_eq
                      (Thm.concl theorem,G.representative graph law)
                    then () else raise ERR "scope"
                      "wrong completed conditional scope endpoint"
                in witnesses := Redblackmap.insert
                  (!witnesses,G.node_id law,theorem) end
            | _ =>
              raise ERR "scope" "invalid deferred scope recipe") (!deferred)
          val (block,target,edge) =
            if List.null local_assumptions then (block,node root,edge) else
              let val selected = case owned_work of NONE =>
                      List.map (fn hypothesis => Redblackmap.find
                        (indices,G.node_id hypothesis)) local_assumptions
                    | SOME _ => List.tabulate (List.length local_assumptions,
                        fn index => List.length canonical_sources + index)
                  val result = case owned_work of NONE =>
                      P.discharge_sources block
                        {indices = selected,body = node root,edge = edge}
                    | SOME work => P.discharge_sources_with_work work block
                        {indices = selected,body = node root,edge = edge}
              in (#block result,#target result,#edge result) end
        in action (fn () =>
          let
            val _ = complete_phase "realize.before"
            val _ = Option.app
              (fn work => P.validate_block_for work block) owned_work
            val theorem = SmtResource.profile_phase "cvc/graph-realization"
              (P.realize_with_sources block target edge)
              (fn (_,node) => Redblackmap.peek (!witnesses,G.node_id node))
            val _ = complete_phase "realize.after"
          in theorem end) end
        handle BoundedResult theorem => theorem
      and close_obligation ancestors obligation =
        (* An original source is already an independent authorized premise;
           this branch never manufactures authority for a TRUST source. *)
        if List.exists (fn source => source = obligation) canonical_sources then
          Thm.ASSUME (G.representative graph obligation)
        else if List.exists (fn ancestor => ancestor = obligation)
            ancestors then
          raise ERR "obligation" "cyclic deferred proof dependency"
        else case Redblackmap.peek
            (!obligation_proofs,G.node_id obligation) of SOME theorem => theorem
          | NONE =>
              let
                val candidates = Option.getOpt (Redblackmap.peek
                  (checked_facts,G.node_id obligation),[])
                fun independent step = case recipe step of
                    Assumption => false | ObligationLaw _ => false | _ => true
                fun generalized () =
                  case Redblackmap.peek
                      (!generalizations,G.node_id obligation) of
                      NONE => raise ERR "obligation"
                        "obligation has no recorded universal closure"
                    | SOME (variables,body) =>
                        let
                          val bodies = Option.getOpt (Redblackmap.peek
                            (checked_facts,G.node_id body),[])
                          val _ = Option.app (fn work =>
                            action (fn () => W.spend work 1)) owned_work
                          val bounds = ref
                            ([]:(Term.term * SmtReplayImport.raw_bound) list)
                          fun try [] = raise ERR "obligation"
                                "no independent body for universal obligation"
                            | try (candidate::rest) =
                                if not (independent candidate) then
                                  try rest else
                                  (let
                                     val theorem = complete candidate []
                                       (obligation :: ancestors)
                                     val _ = permitted theorem
                                     (* GEN sees only fully bounded terms and
                                        surviving hypotheses on this adapter. *)
                                     fun small term =
                                       case owned_work of NONE =>
                                         (case
                                           SmtReplayImport.bounded_raw_size
                                             ordinary_limit term of
                                            SOME _ => ()
                                          | NONE => raise ERR "generalization"
                                              "bounded GEN adapter declined")
                                       | SOME work =>
                                         let val result = action (fn () =>
                                               (W.spend work 3;
                                                SI.bounded_raw_size_with_bound
                                                  {limit=ordinary_limit,
                                                   observe=fn () =>
                                                     W.spend work 1} term))
                                         in case result of NONE =>
                                              raise ERR "generalization"
                                                "bounded GEN adapter declined"
                                          | SOME bound => action (fn () =>
                                              (W.spend work 2;
                                               bounds :=
                                                 (term,bound):: !bounds))
                                         end
                                     val _ = List.app small
                                       (G.representative graph obligation ::
                                        Thm.concl theorem :: Thm.hyp theorem)
                                     val _ = List.app
                                       (admit_type o Term.type_of) variables
                                     val theorem = List.foldr
                                       (fn (variable,theorem) =>
                                         Thm.GEN variable theorem)
                                       theorem variables
                                     val target =
                                       G.representative graph obligation
                                     val theorem = Thm.EQ_MP
                                       (Thm.ALPHA (Thm.concl theorem) target)
                                       theorem
                                     val _ = permitted theorem
                                     val _ = Option.app (fn work =>
                                       action (fn () =>
                                         (W.spend work 2;
                                          obligation_admissions :=
                                            Redblackmap.insert
                                              (!obligation_admissions,
                                               G.node_id obligation,
                                               (theorem,!bounds))))) owned_work
                                   in theorem end
                                   handle Feedback.HOL_ERR error =>
                                     (case owned_work of
                                        SOME work =>
                                          if #retired (W.audit work) orelse
                                              SmtResource.is_resource_gate
                                                error then
                                            raise Feedback.HOL_ERR error
                                          else try rest
                                      | NONE =>
                                          if SmtResource.is_resource_gate
                                              error then
                                            raise Feedback.HOL_ERR error
                                          else try rest))
                        in try bodies end
                fun forced () =
                  if extended_mode orelse Option.isSome owned_work then
                    force_obligation obligation
                  else (case force_worker of
                    NONE => raise ERR "obligation"
                      "no independently checked fact proves deferred obligation"
                  | SOME force =>
                      let
                        val target = raw obligation
                        val located = {term = target,
                          provenance = AtomicProvenance}
                        val rule = case CPC_Proof.lookup_rule
                            (#cvc_version proof) "trust" of SOME rule => rule
                          | NONE => raise ERR "obligation"
                              "no registered forced TRUST rule"
                        val step : CPC_Proof.step =
                          {id = "graph-forced-obligation",rule = rule,
                           premises = [],args = [located],
                           conclusion = SOME located}
                        val occurrence = !forced_counter
                        val _ = forced_counter := occurrence+1
                        fun execute () = let
                        val _ = notify (ForcedBegin
                          {serial = occurrence,step = step})
                        val (theorem,result) = force (step,[])
                        val _ = Library.check_oracle_tags
                          "CPC_GraphProofReplay" "force_obligation" theorem
                        val _ = List.app admit
                          (Thm.concl theorem :: Thm.hyp theorem)
                        val _ = if Term.aconv (Thm.concl theorem) target andalso
                            Term.aconv (#term result) target andalso
                            not (List.exists (Term.aconv target)
                              (Thm.hyp theorem)) then () else raise ERR
                              "obligation"
                                "forced TRUST deferred or changed target"
                        val theorem = Thm.EQ_MP
                          (Thm.ALPHA (Thm.concl theorem) target) theorem
                        val _ = permitted theorem
                        val _ = notify (ForcedEnd
                          {serial = occurrence,theorem = theorem,
                           located = {term = Thm.concl theorem,
                             provenance = #provenance result}})
                        in theorem end
                        fun abort error =
                          let
                            val _ = notify (ForcedAbort {serial = occurrence})
                              handle abort_error =>
                                (case error of ObserverFailure _ => raise error
                                 | Feedback.HOL_ERR detail =>
                                     if SmtResource.is_resource_gate detail then
                                       raise error else raise abort_error
                                 | _ => raise abort_error)
                          in raise error end
                      in execute () handle error => abort error end)
                fun attempt [] =
                      (generalized () handle Feedback.HOL_ERR error =>
                        case owned_work of
                          SOME work =>
                            if #retired (W.audit work) orelse
                                SmtResource.is_resource_gate error then
                              raise Feedback.HOL_ERR error else forced ()
                        | NONE =>
                            if SmtResource.is_resource_gate error then
                              raise Feedback.HOL_ERR error else forced ())
                  | attempt (candidate::rest) =
                      if not (independent candidate) then attempt rest else
                        (let val theorem = complete candidate []
                                (obligation :: ancestors)
                             val _ = permitted theorem
                         in theorem end
                         handle Feedback.HOL_ERR error =>
                           case owned_work of
                             SOME work =>
                               if #retired (W.audit work) orelse
                                   SmtResource.is_resource_gate error then
                                 raise Feedback.HOL_ERR error
                               else
                                 let
                                   (* Only this exact live cyclic-candidate
                                      decline invokes the genuine trial.
                                      Ordinary successful fitting proofs
                                      retain their original programme. *)
                                   val cyclic = W.with_step work (fn () =>
                                     let
                                       val _ = validate_owned work
                                       fun same a b =
                                         (W.spend work (1+String.size a+
                                            String.size b);a=b)
                                     in same (Feedback.top_structure_of error)
                                          "CPC_GraphProofReplay" andalso
                                        same (Feedback.top_function_of error)
                                          "obligation" andalso
                                        same (Feedback.message_of error)
                                          "cyclic deferred proof dependency"
                                     end)
                                 in if not cyclic orelse not
                                     (actual_dependency_eligible work candidate
                                       obligation ancestors) then attempt rest
                                   else
                                     let
                                       val result =
                                         ((case actual_dependency_candidate
                                             work candidate obligation
                                             ancestors of
                                           NONE => NONE
                                         | SOME receipt =>
                                             let val theorem =
                                               P.source_realization_theorem_for
                                                 work receipt
                                                 val _ = permitted theorem
                                             in SOME theorem end)
                                          handle Feedback.HOL_ERR decline =>
                                            if #retired (W.audit work) orelse
                                                SmtResource.is_resource_gate
                                                  decline then
                                              raise Feedback.HOL_ERR decline
                                            else NONE)
                                     in case result of SOME theorem => theorem
                                       | NONE => attempt rest end
                                 end
                           | NONE =>
                               if SmtResource.is_resource_gate error then
                                 raise Feedback.HOL_ERR error
                               else attempt rest)
                val theorem = attempt candidates
                val _ = if Portable.pointer_eq (Thm.concl theorem,
                    G.representative graph obligation) then () else
                  raise ERR "obligation" "wrong checked obligation endpoint"
                val _ = obligation_proofs := Redblackmap.insert
                  (!obligation_proofs,G.node_id obligation,theorem)
              in theorem end
      val _ = List.app (fn step => case recipe step of
          ObligationLaw {obligation,...} =>
            ignore (close_obligation [] obligation)
        | _ => ()) completed
      in complete root [] [] end
      val mandatory = if not extended_mode then [] else
        List.mapPartial (fn step => case recipe step of
          NativeObligation origin =>
            let val _ = CPC_GraphNativeReservation.validate_committed origin
                val _ = if CPC_GraphNativeReservation.serial origin =
                    serial step
                    andalso CPC_GraphNativeReservation.target origin = node step
                  then () else raise ERR "native_reservation"
                    "committed native occurrence changed"
            in SOME {serial = serial step,target = node step} end
        | ObligationLaw {obligation,...} =>
            SOME {serial = serial step,target = obligation}
        | _ => NONE) completed
      fun completion_permitted theorem =
        (Library.check_oracle_tags "CPC_GraphProofReplay"
           "completion" theorem;
         if null (Tag.axioms_of (Thm.tag theorem)) andalso
             List.all (fn hypothesis => List.exists (fn source =>
               Portable.pointer_eq (hypothesis,
                 G.representative graph source)) canonical_sources)
               (Thm.hyp theorem) then () else
           raise ERR "completion" "unpermitted actual witness Hyp or axiom")
      fun accept ({resolution,contradiction,witnesses} : completion_result) =
        let
          val _ = G.validate_scope graph scope
          val _ = SmtReplayResolve.validate graph scope resolution
          val _ = List.app (fn node =>
            if SmtReplayResolve.node resolution node = node then () else
              raise ERR "completion" "original Source was changed")
            canonical_sources
          val _ = if length witnesses = length mandatory then () else
            raise ERR "completion" "mandatory occurrence inventory changed"
          fun validate {serial = expected,target = original} =
            let val matches = List.filter (fn {serial,...} =>
                    serial = expected) witnesses
                val value = case matches of [value] => value
                  | _ => raise ERR "completion" "missing unique occurrence"
                val {target,witness,original = recorded,...} = value
                val _ = if recorded = original andalso
                    target = SmtReplayResolve.node resolution original then ()
                  else raise ERR "completion" "normalized occurrence changed"
                val _ = if G.scope_visible graph scope
                    (G.node_scope graph target) then () else
                  raise ERR "completion" "normalized occurrence captures scope"
                val _ = completion_permitted witness
                val _ = if Portable.pointer_eq (Thm.concl witness,
                    G.representative graph target) then () else
                  raise ERR "completion" "inexact checked normalized witness"
            in () end
          val _ = List.app validate mandatory
          val _ = completion_permitted contradiction
          val _ = if Portable.pointer_eq (Thm.concl contradiction,
              G.representative graph (node root)) then () else
            raise ERR "completion" "checked contradiction endpoint changed"
          val actual = Thm.hyp contradiction
          val _ = if List.all (fn source => List.exists (fn term =>
                Portable.pointer_eq (term,G.representative graph source))
                actual) canonical_sources then () else
            raise ERR "completion" "mandatory original Source was removed"
          val _ = G.validate_scope graph scope
        in contradiction end
      fun complete_owned close =
        let
          val live = ref true
          val busy = ref false
          fun active () =
            (if !live then () else raise ERR "completion_proof"
               "expired completion proof lease";
             G.validate_scope graph scope)
          fun prove target =
            let val _ = active ()
                val _ = if !busy then raise ERR "completion_proof"
                  "reentrant completion proof lease" else ()
                val _ = busy := true
                val result = (force_obligation target before busy := false)
                  handle error => (busy := false;raise error)
                val _ = active ()
            in result end
          val result = close
            {root = node root,mandatory = mandatory,prove = prove}
            handle error => (live := false;raise error)
          val _ = live := false
        in case result of NONE => ordinary_completion ()
          | SOME result => accept result end
      val _ = work_phase "completion.before"
      val theorem = case owned_completion of SOME close => complete_owned close
        | NONE => case completion of NONE => ordinary_completion ()
          | SOME close => case close {root = node root,mandatory = mandatory} of
              NONE => ordinary_completion () | SOME result => accept result
      val _ = work_phase "completion.after"
      val _ = SmtReplaySource.check_contradiction sources theorem
      val _ = notify InvocationEnd
    in theorem end
    in run () handle error =>
      (work_checkpoint "abort"
         (fn () => " exception=" ^ General.exnName error);
       Option.app W.close owned_work;
       (observer InvocationAbort handle _ => ());
       case error of ObserverFailure original => raise original
       | _ => raise error) end
  fun check_contradiction_observing
      {graph,scope,sources,proof,ordinary_limit,template_limit,
       worker,force_worker,observer} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = observer,
       history_mode = false,check_type = fn _ => (),completion = NONE,
       direct_deferred = NONE,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
        preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  fun check_contradiction_history_observing
      {graph,scope,sources,proof,ordinary_limit,template_limit,
       worker,force_worker,observer,check_type} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = observer,
       history_mode = true,check_type = check_type,completion = NONE,
       direct_deferred = NONE,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
        preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  fun check_contradiction_history_completing
      {graph,scope,sources,proof,ordinary_limit,template_limit,
       worker,force_worker,observer,check_type,completion} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = observer,
       history_mode = true,check_type = check_type,completion = SOME completion,
       direct_deferred = NONE,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
        preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  fun check_contradiction_history_lexical_completing
      {graph,scope,sources,proof,ordinary_limit,template_limit,
       worker,force_worker,observer,check_type,completion,direct_deferred} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = observer,
       history_mode = true,check_type = check_type,completion = SOME completion,
       direct_deferred = SOME direct_deferred,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
        preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  fun check_contradiction_lexical_force_completing
      {graph,scope,sources,proof,ordinary_limit,template_limit,worker,
       observer,check_type,completion,direct_deferred,owned_force_worker} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = NONE,observer = observer,
       history_mode = true,check_type = check_type,completion = SOME completion,
       direct_deferred = SOME direct_deferred,
       owned_force_worker = SOME owned_force_worker,owned_completion = NONE,
       native_reservation = NONE,
        preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  fun check_contradiction_owned_proof_completing
      {graph,scope,sources,proof,ordinary_limit,template_limit,worker,
       observer,check_type,completion,direct_deferred,owned_force_worker} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = NONE,observer = observer,
       history_mode = true,check_type = check_type,completion = NONE,
       direct_deferred = SOME direct_deferred,
       owned_force_worker = SOME owned_force_worker,
       owned_completion = SOME completion,native_reservation = NONE,
        preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  fun check_contradiction_using
      {graph,scope,sources,proof,ordinary_limit,template_limit,
       worker,force_worker} =
    check_contradiction_observing
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = fn _ => ()}
  fun check_contradiction
      {graph,scope,sources,proof,ordinary_limit,template_limit,worker} =
    check_contradiction_using
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = NONE}
  (* Native reservation avoids raw lexical preparation. A missing native
     completion is an explicit adapter gap, never an ordinary assumption. *)
  fun check_contradiction_native_reserving
      {graph,scope,sources,proof,ordinary_limit,template_limit,worker,
       observer,check_type,completion,direct_deferred,owned_force_worker,
       reserve} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = NONE,observer = observer,
       history_mode = true,check_type = check_type,completion = NONE,
       direct_deferred = SOME direct_deferred,
       owned_force_worker = SOME owned_force_worker,
       owned_completion = SOME completion,native_reservation = SOME reserve,
       preprocessing = NONE,owned_work = NONE,clause_worker = NONE}
  (* Ordinary whole-engine opt-in. Native completion/default entry points
     retain their original ownership and Hyp policy. *)
  fun check_contradiction_preprocessed_using
      {graph,scope,sources,preprocessing,proof,ordinary_limit,template_limit,
       worker,force_worker} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = fn _ => (),
       history_mode = false,check_type = fn _ => (),completion = NONE,
       direct_deferred = NONE,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
       preprocessing = SOME preprocessing,owned_work = NONE,
       clause_worker = NONE}
  (* Optional original-Work receiver. All legacy/default entries above
     retain NONE; this receiver fences expected ownership before held GP. *)
  fun check_contradiction_preprocessed_with_work_using work
      {graph,scope,sources,preprocessing,proof,ordinary_limit,template_limit,
       worker,force_worker} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = fn _ => (),
       history_mode = false,check_type = fn _ => (),completion = NONE,
       direct_deferred = NONE,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
       preprocessing = SOME preprocessing,owned_work = SOME work,
       clause_worker = NONE}
  (* Same owner/source checks; only the fixed ordinary worker additionally
     retains its actual opaque clause witness. Old entry above stays NONE. *)
  fun check_contradiction_preprocessed_with_clauses_and_work_using work
      {graph,scope,sources,preprocessing,proof,ordinary_limit,template_limit,
       worker,clause_worker,force_worker} =
    check_contradiction_observing_impl
      {graph = graph,scope = scope,sources = sources,proof = proof,
       ordinary_limit = ordinary_limit,template_limit = template_limit,
       worker = worker,force_worker = force_worker,observer = fn _ => (),
       history_mode = false,check_type = fn _ => (),completion = NONE,
       direct_deferred = NONE,owned_force_worker = NONE,
       owned_completion = NONE,native_reservation = NONE,
       preprocessing = SOME preprocessing,owned_work = SOME work,
       clause_worker = SOME clause_worker}
  fun check_contradiction_preprocessed_observed_with_work_using work
      (input as {graph,scope,sources,preprocessing,template_limit,...}) =
    let
      fun protected action = action ()
        handle primary => (W.close work;raise primary)
      val original = W.original_sources work
      val limits = W.semantic_limits work
      val _ = protected (fn () =>
        (if Portable.pointer_eq (sources,original) then () else
           raise ERR "observed_replay" "different original Sources";
         if Portable.pointer_eq (graph,SmtReplaySource.owning_graph original)
             andalso scope = SmtReplaySource.owning_scope original andalso
             template_limit = #template_limit limits then () else
           raise ERR "observed_replay" "different original graph/root/cap";
         W.validate work graph scope original limits;
         GP.validate_with_work work preprocessing))
      fun run () =
        let
          val _ = case !assembly_observation of NONE => ()
            | SOME _ => raise ERR "observed_replay" "observation reentry"
          val fields = {graph = graph,hits = ref (0 : IntInf.int),
                        misses = ref (0 : IntInf.int)}
          val _ = assembly_observation := SOME (AssemblyObservation fields)
          val outcome = Exn.capture (fn () =>
            check_contradiction_preprocessed_with_work_using work input) ()
          val _ = assembly_observation := NONE
        in (Exn.release outcome,(!(#hits fields),!(#misses fields))) end
      val ((((theorem,(hits,misses)),schemas),proofs),nodes) =
        protected (fn () => G.with_node_statistics graph scope (fn () =>
          P.with_proof_statistics work (fn () =>
            SmtReplayCanonGraph.with_schema_statistics graph scope run)))
      val statistics : observed_statistics =
        {nodes = nodes,proofs = proofs,schemas = schemas,
         assembly_hits = hits,assembly_misses = misses}
    in {theorem = theorem,statistics = statistics} end

  fun prove_preprocessed_with_work_using work (input as {sources,...}) =
    let val contradiction =
          check_contradiction_preprocessed_with_work_using work input
        val original = W.original_sources work
        val _ = if Portable.pointer_eq (sources,original) then () else
          (W.close work;raise ERR "owned_replay" "different final Sources")
    in SmtReplaySource.close_contradiction original contradiction end

  fun prove_preprocessed_with_clauses_and_work_using work
      (input as {sources,...}) =
    let val contradiction =
          check_contradiction_preprocessed_with_clauses_and_work_using
            work input
        val original = W.original_sources work
        val _ = if Portable.pointer_eq (sources,original) then () else
          (W.close work;raise ERR "owned_replay" "different final Sources")
    in SmtResource.profile_phase "cvc/graph-source-finalization"
      (SmtReplaySource.close_contradiction original) contradiction end

  fun prove_preprocessed_using (input as {sources,...}) =
    SmtReplaySource.close_contradiction sources
      (check_contradiction_preprocessed_using input)
  fun prove_using (input as {sources,...}) =
    SmtReplaySource.close_contradiction sources
      (check_contradiction_using input)
  fun prove (input as {sources,...}) =
    SmtReplaySource.close_contradiction sources (check_contradiction input)
end
