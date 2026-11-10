(* Source-only native first pass over the actual persistent factory lease.
   It never creates an ordinary proof from descriptor metadata. *)
structure CPC_GraphNativeFirstPass =
struct
  open CPC_GraphNativeReservation SmtReplayGraph SmtReplayProof
    SmtReplayResolve SmtReplaySource SmtReplaySupport SmtReplayRules
    CPC_GraphProofReplay
    CPC_ProofReplay
    CPC_GraphSelectedProof
    CPC_GraphNativeComponent CPC_GraphResolvedConstructorBridge
    SmtLib_Theories
  structure G = SmtReplayGraph
  structure Q = SmtLib_GraphProof
  structure S = SmtReplaySource
  structure P = SmtReplayProof
  structure R = SmtReplayResolve
  structure C = SmtReplaySupport
  structure Rules = SmtReplayRules
  structure Reservation = CPC_GraphNativeReservation
  structure E = CPC_GraphProofReplay
  structure Worker = CPC_ProofReplay
  structure D = CPC_GraphSelectedProof
  structure A = CPC_GraphNativeAdmission
  structure N = CPC_GraphNativeComponent
  structure B = CPC_GraphResolvedConstructorBridge
  exception NativeGap
  datatype outcome = Checked of
    {theorem : Thm.thm,contradiction : Thm.thm,occurrences : int,
     checked_witnesses : int,native_occurrences : int,
     native_realizations : int,worker_calls : int}
    | Continue
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphNativeFirstPass"
  (* Literal1: NUMERAL(BIT1 ALT_ZERO)=5, n2w1=7; n2w0=3.
     COND spine4 + classifier(source hole)3 + 7 + 3 = 17.
     The schemas contain no binders, so both metrics agree. *)
  val singleton_nodes = 17
  val singleton_alpha_nodes = 3 + 2*singleton_nodes
  val assignment_nodes = 3 + 1 + singleton_nodes
  val assignment_alpha_nodes = 3 + 2*assignment_nodes
  val descriptor_context_nodes = 2*singleton_nodes + 1
  fun compact_budget {nodes,descriptors,commands,originals} =
    let
      val n = IntInf.fromInt nodes
      val m = IntInf.fromInt descriptors
      val k = IntInf.fromInt commands
      val context = 10 * (2*n +
        IntInf.fromInt descriptor_context_nodes*m + 8*k + 1) +
        4 * IntInf.fromInt originals + 4*m
    in 3 + 2*(context+8) end
  fun check_packet {packet,validate,sources,ordinary_limit,template_limit,
                    check_type} =
    let
      val graph = Q.graph packet val scope = Q.scope packet
      fun active () = (validate ();G.validate_scope graph scope)
      val _ = active ()
      val proof : CPC_ProofParser.graph_proof = Q.proof packet
      val originals = S.assumption_nodes sources @ [S.denied_goal_node sources]
      val descriptors = Q.private_bindings packet
      val falsehood = G.constant graph scope boolSyntax.F
      fun arguments (CPC_ProofParser.GraphTerm value) = [#node value]
        | arguments (CPC_ProofParser.GraphList values) =
            List.concat (List.map arguments values)
        | arguments _ = []
      fun nodes (CPC_ProofParser.GraphAssume (_,value)) = [#node value]
        | nodes (CPC_ProofParser.GraphAssumePush (_,value)) = [#node value]
        | nodes (CPC_ProofParser.GraphStep {step,...}) =
            (case #conclusion step of NONE => []
              | SOME value => [#node value]) @
            List.concat (List.map arguments (#args step))
      val reachable = G.block_reachable graph
        (originals @ List.concat (List.map nodes (#commands proof)) @
         List.mapPartial #source descriptors @
         List.map #node (Q.variables packet))
      val whole_budget = compact_budget
        {nodes = length reachable,descriptors = length descriptors,
         commands = length (#commands proof),originals = length originals}
      val _ = if whole_budget <= IntInf.fromInt template_limit then ()
        else raise NativeGap
      val _ = List.app (fn node =>
        (G.validate_scope graph (G.node_scope graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "check_packet" "native input captures scope";
         case G.view graph node of
             G.Constant _ => () | G.Application _ => ()
           | G.Variable (G.Bound,_) => raise NativeGap
           | G.Variable _ => () | _ => raise NativeGap)) reachable
      val original_variables = List.concat (List.map (fn node =>
        case G.free_variable_nodes graph node of SOME variables => variables
          | NONE => raise NativeGap) originals)
      val _ = List.app
        (fn ({node,lexical,...} : SmtLib_GraphFrontend.solver_variable) =>
          List.app (fn original =>
            if node = original orelse
                (G.type_id graph node = G.type_id graph original andalso
                 #1 (Term.dest_var lexical) =
                 #1 (Term.dest_var (G.representative graph original))) then
              raise ERR "check_packet"
                "allocated typed name collides with original Source"
            else ()) original_variables) (Q.variables packet)
      val admission = A.prepare
        {graph = graph,scope = scope,proof = proof,sources = sources,
         template_limit = template_limit,check_type = check_type}
      val primitive = SmtWordGraph.new_type_admission ()
      fun schema_size limit term =
        let fun walk [] n = SOME n
              | walk (term :: rest) n = if n >= limit then NONE else
                  if Term.is_abs term then raise NativeGap
                  else if Term.is_comb term then
                    let val (f,x) = Term.dest_comb term in
                      walk (f :: x :: rest) (n+1) end
                  else walk rest (n+1)
        in if limit < 0 then NONE else walk [term] 0 end
      fun original node = List.exists (fn other => other = node) originals
      fun descriptor marker = case List.find
          (fn {marker = actual,...} => actual = marker) descriptors of
          SOME entry => entry | NONE => raise NativeGap
      val allocated = List.map #node (Q.variables packet)
      val prospective = List.filter (not o original o #2)
        (A.obligations admission)
      fun marker (_,target) =
        case Rules.equality graph target of NONE => raise NativeGap
        | SOME (left,right) =>
            case List.find (fn variable =>
                (variable = left orelse variable = right) andalso
                List.exists (fn {marker,...} => marker = variable) descriptors)
              allocated of SOME variable => variable
            | NONE => raise NativeGap
      val visiting = ref ([] : G.node list)
      val needed = ref ([] : G.node list)
      fun member node = List.exists (fn other => other = node)
      fun need variable = if member variable (!needed) then () else
        if member variable (!visiting) then raise NativeGap else
        let val {kind,source,scope = owner,...} = descriptor variable
            val _ = G.validate_scope graph owner
            val _ = if G.scope_visible graph scope owner andalso
                (kind = "@fp.ZERO" orelse kind = "@fp.INF" orelse
                 kind = "@fp.NAN") then () else raise NativeGap
            val source = case source of SOME node => node
              | NONE => raise NativeGap
            val _ = visiting := variable :: !visiting
            val nodes = G.block_reachable graph [source]
            val _ = List.app (need o #marker) (List.filter
              (fn {marker,...} => member marker nodes) descriptors)
            val _ = visiting := List.tl (!visiting)
        in needed := variable :: !needed end
      val _ = List.app (need o marker) prospective
      val needed = List.filter (fn {marker,...} => member marker (!needed))
        descriptors
      fun build ({marker,kind,source,...} :
          SmtLib_GraphFrontend.private_binding) =
        let
          val source = valOf source
          val _ = List.app
            (SmtWordGraph.admit_primitive_type primitive o G.type_of graph)
            [marker,source]
          val _ = List.app (check_type o G.type_of graph) [marker,source]
          val _ = case G.view graph marker of
              G.Variable (G.SolverFlexible,_) => () | _ => raise NativeGap
          val hole = Term.genvar (G.type_of graph source)
          val name = if kind = "@fp.ZERO" then "smtfp_is_zero"
            else if kind = "@fp.INF" then "smtfp_is_infinite"
            else "smtfp_is_nan"
          val operator = Term.prim_mk_const {Thy = "smtfloat",Name = name}
          val (domain,_) = Type.dom_rng (Term.type_of operator)
          val predicate = Term.mk_comb (Term.inst
            (Type.match_type domain (G.type_of graph source)) operator,hole)
          val template = SmtLib_Theories.mk_bbterm [predicate]
          (* Check the exact fixed operation schemas covered
             by the earlier prospective reserve. *)
          val assignment = boolSyntax.mk_eq
            (G.representative graph marker,template)
          val schemas = [(template,singleton_nodes),
            (boolSyntax.mk_eq (template,template),singleton_alpha_nodes),
            (assignment,assignment_nodes),
            (boolSyntax.mk_eq (assignment,assignment),
             assignment_alpha_nodes)]
          val _ = List.app (fn (term,expected) => List.app
            (fn count => case count expected term of
                SOME actual => if actual = expected then () else
                  raise ERR "build" "singleton schema count changed"
              | NONE => raise ERR "build"
                  "singleton classification template grew")
            [schema_size,schema_size]) schemas
          fun construct term = if Term.is_var term then
              if Portable.pointer_eq (term,hole) then source else
                raise ERR "build" "unexpected component variable"
            else if Term.is_const term then G.constant graph scope term
            else if Term.is_comb term then
              let val (operator,operand) = Term.dest_comb term in
                G.application graph scope
                  (construct operator,construct operand) end
            else raise NativeGap
          val residue = construct template
          val _ = if G.type_id graph marker = G.type_id graph residue
              then () else raise NativeGap
        in {variable = marker,residue = residue} end
      val assignments = List.map build needed
      val prospective_resolution = case R.prepare graph scope
          {flexible = List.map #variable assignments,assignments = assignments,
           roots = A.roots admission,preserved = originals} of
          R.Resolved result => result | R.Refused _ => raise NativeGap
      val prospective_native = List.map (fn (_,target) =>
        let val normalized = R.node prospective_resolution target
            val prepared = case N.prepare
                {graph = graph,scope = scope,target = normalized,
                 template_limit = template_limit,check_type = check_type} of
                SOME value => value | NONE => raise NativeGap
        in (target,normalized,prepared) end) prospective
      (* No lexical transport plan and no ordinary source preparation. *)
      val worker_calls = ref 0
      val factory = Worker.graph_native_reservation_factory
        {graph = graph,scope = scope}
      val plan = Reservation.new
        {packet = packet,sources = sources,validate = active,
         template_limit = template_limit,check_type = check_type,
         lease = #native_lease factory}
      val origins = ref ([] : Reservation.origin list)
      fun reserve request = case Reservation.reserve plan request of
          NONE => raise NativeGap
        | SOME origin => (origins := origin :: !origins;SOME origin)
      val final = ref (NONE :
        {theorem : Thm.thm,contradiction : Thm.thm,occurrences : int,
         checked_witnesses : int,native_occurrences : int,
         native_realizations : int,worker_calls : int} option)
      fun completion ({root,mandatory,...} : E.owned_completion_request) =
        let
          val _ = active ()
          val committed = List.rev (!origins)
          val _ = List.app Reservation.validate_committed committed
          val _ = if length committed = length mandatory andalso
              ListPair.allEq (fn (origin,{serial,target}) =>
                Reservation.serial origin = serial andalso
                Reservation.target origin = target) (committed,mandatory)
            then () else raise NativeGap
          fun descriptor marker = case List.find
              (fn {marker = actual,...} => actual = marker) descriptors of
              SOME entry => entry | NONE => raise NativeGap
          val allocated = List.map #node (Q.variables packet)
          fun equation origin =
            let val (variable,residue) = Reservation.equation origin
                val _ = if List.exists (fn node => node = variable) allocated
                    then () else raise NativeGap
                val _ = descriptor variable
            in {serial = Reservation.serial origin,
              revision = Reservation.revision origin,
              source = Reservation.target origin,variable = variable,
              residue = residue,original_hypothesis = 0,
              original_premises = [{index = 0,
                node = Reservation.target origin,command_occurrence = NONE}]}
              : CPC_GraphDefinitionHistory.occurrence end
          val occurrences = List.map equation committed
          val selected = D.discover_prepared
            {graph = graph,scope = scope,proof = proof,sources = sources,
             admission = admission,equations = occurrences,
             template_limit = template_limit,
             check_type = check_type}
          val certificate = #certificate selected
          val inputs = #inputs selected
          val hypotheses = originals @ List.map #target mandatory
          val _ = if List.map #node inputs = hypotheses then () else
            raise ERR "completion" "native occurrence input map changed"
          val initial_resolution = case R.prepare graph scope
              {flexible = List.map #variable assignments,
               assignments = assignments,
               roots = root :: hypotheses,preserved = originals} of
              R.Resolved result => result | R.Refused _ => raise NativeGap
              val normalized = List.map
                (R.node initial_resolution o #target) mandatory
              fun original node = List.exists
                (fn source => node = source) originals
              val plans = ListPair.mapEq (fn (old,node) =>
                if original node then NONE else
                  case List.find (fn (target,_,_) => target = old)
                      prospective_native of
                    SOME (_,expected,prepared) =>
                      if node = expected then
                        SOME (N.discover_prepared prepared) else
                        raise ERR "completion" "prospective endpoint changed"
                  | NONE => raise NativeGap)
                (List.map #target mandatory,normalized)
              fun equation (entry as {variable,residue}) =
                case List.find (fn node => case Rules.equality graph node of
                    SOME (left,right) =>
                      (left = variable andalso right = residue) orelse
                      (right = variable andalso left = residue)
                  | NONE => false)
                    (R.assignment_sources initial_resolution) of
                    SOME node => {equation = node,variable = variable,
                      residue = residue} : B.assignment
                  | NONE => raise ERR "native_completion"
                      "prepared assignment lacks exact registered equation"
              val authority = List.map equation assignments
              val bridge = B.discover
                {graph = graph,scope = scope,resolution = initial_resolution,
                 originals = originals,targets = List.map #target mandatory,
                 assignments = authority,template_limit = template_limit,
                 check_type = check_type}
              fun joints [node] = [node]
                | joints (node :: rest) =
                    let val targets = joints rest
                        val result = G.application graph scope
                          (G.application graph scope
                            (G.constant graph scope boolSyntax.conjunction,node),
                           List.hd targets)
                    in result :: targets end
                | joints [] = raise ERR "native_completion" "empty joint law"
              val bodies = root :: normalized
              val joint_targets = joints bodies
              val joint_target = List.hd joint_targets
              val native_roots = List.concat (List.mapPartial
                (Option.map N.roots) plans)
              val roots = joint_target :: C.roots certificate @
                B.roots bridge @ native_roots
              val resolution = case R.prepare graph scope
                  {flexible = List.map #variable assignments,
                   assignments = assignments,roots = roots,
                   preserved = originals} of R.Resolved result => result
                | R.Refused _ => raise ERR "native_completion"
                    "joint resolution refused exact prepared assignments"
              val resolution = R.record_assignment_sources resolution
                (List.map #equation authority)
              val _ = R.validate graph scope resolution
              val _ = List.app (fn node =>
                if R.node resolution node = R.node initial_resolution node
                then () else raise ERR "native_completion"
                  "reprepared mandatory endpoint changed")
                (List.map #target mandatory)
              val block = P.freeze graph
                {scope = scope,roots = roots,sources = B.sources bridge,
                 template_limit = template_limit}
              fun source node =
                let fun find [] _ = raise ERR "native_completion"
                          "normalized Source lacks exact original occurrence"
                      | find (current :: rest) index =
                          if node = current then P.source block index
                          else find rest (index+1)
                in find originals 0 end
              val facts = ListPair.mapEq (fn (node,plan) => case plan of
                  NONE => source node | SOME plan => N.assemble block plan)
                (normalized,plans)
              fun occurrence index node =
                if index < length originals then
                  if List.nth (originals,index) = node then
                    P.source block index else raise ERR "native_completion"
                      "mandatory original prefix changed"
                else
                  let val slot = index-length originals
                      val obligation = List.nth (mandatory,slot)
                      val origin = List.nth (committed,slot)
                  in if #target obligation = node then
                      Reservation.assemble block origin (B.original_fact block
                        bridge {target = node,
                          normalized = List.nth (facts,slot)})
                    else raise ERR "native_completion"
                      "selected deferred occurrence map changed" end
              val selected_inputs = List.map (fn index =>
                let val node = #node (List.nth (inputs,index))
                in {index = index,node = node,edge = occurrence index node} end)
                (C.selected certificate)
              val contradiction = C.assemble block certificate selected_inputs
              fun combine [(_,edge)] [_] = edge
                | combine ((node,edge) :: rest) (target :: targets) =
                    let val tail = combine rest targets
                        val tail_target = List.hd targets
                    in Rules.assemble graph block
                      {rule = "and-intro",target = target,
                       premises = [(node,edge),(tail_target,tail)]} end
                | combine _ _ = raise ERR "native_completion"
                    "joint constructor occurrence inventory changed"
              val edge = combine ((root,contradiction) ::
                ListPair.zip (normalized,facts)) joint_targets
              val theorem = P.realize_resolved block resolution joint_target edge
              fun projections [_] theorem = [theorem]
                | projections (_ :: rest) theorem = Thm.CONJUNCT1 theorem ::
                    projections rest (Thm.CONJUNCT2 theorem)
                | projections [] _ = raise ERR "native_completion"
                    "empty projection inventory"
              val checked = projections bodies theorem
              val contradiction = List.hd checked
              val witnesses = ListPair.mapEq
                (fn ({serial,target = old},(target,witness)) =>
                  {serial = serial,original = old,target = target,
                   witness = witness})
                (mandatory,ListPair.zip (normalized,List.tl checked))
              val _ = active ()
              val _ = S.check_contradiction sources contradiction
              val goal = S.close_contradiction sources contradiction
              val _ = S.check_goal sources goal
              val _ = final := SOME {theorem = goal,
                contradiction = contradiction,occurrences = length mandatory,
                checked_witnesses = length hypotheses,
                native_occurrences = length mandatory,native_realizations = 1,
                worker_calls = !worker_calls}
            in SOME {resolution = resolution,contradiction = contradiction,
              witnesses = witnesses} end
      val contradiction = E.check_contradiction_native_reserving
        {graph = graph,scope = scope,sources = sources,proof = proof,
         ordinary_limit = ordinary_limit,template_limit = template_limit,
         worker = fn input =>
           (worker_calls := !worker_calls+1;#worker factory input),
         observer = #observer factory,
         check_type = check_type,completion = completion,reserve = reserve,
         direct_deferred = #direct_deferred factory,
         owned_force_worker = #owned_force_worker factory}
      val _ = active ()
      val _ = A.validate admission
      val _ = S.check_contradiction sources contradiction
    in case !final of SOME result => Checked result
      | NONE => raise ERR "check_packet" "missing checked native completion" end
    handle NativeGap => Continue
      | A.Adapter => Continue
      | E.NativeCompletionAdapter => Continue
end
