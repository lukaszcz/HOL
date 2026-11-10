(* No name prefix selects a graph role or a proof route. All substitutions
   come from actual allocated parser descriptors and retain exact Sources. *)
structure CPC_GraphLexicalTransport :> CPC_GraphLexicalTransport =
struct
  open CPC_GraphClosedPrivateComponent
  open SmtLib_GraphProof SmtLib_GraphFrontend SmtReplaySource
    SmtReplayImport CPC_Proof Library
  structure G = SmtReplayGraph
  structure Q = SmtLib_GraphProof
  structure S = SmtReplaySource
  exception Adapter
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphLexicalTransport"
  fun member term = List.exists (fn other => Term.aconv term other)
  fun same_object left right = Portable.pointer_eq (left,right)
  fun raw limit term = case SmtReplayImport.bounded_raw_size limit term of
      SOME count => count | NONE => raise Adapter
  fun inclusive limit term =
    case SmtReplayImport.bounded_binder_size limit term of
      SOME count => count | NONE => raise Adapter
  fun whole limit term = (ignore (raw limit term);
    ignore (inclusive limit term))
  (* Exact constructor costs: implication/equality adds a constant and two
     applications. Variable-to-variable substitution changes neither metric.
     Count the COMPLETE prospective laws before constructing them or types. *)
  fun conditional limit count conclusion hypotheses =
    let val total = List.foldl (fn (term,total) =>
          total + 3 + IntInf.fromInt (count limit term))
          (IntInf.fromInt (count limit conclusion)) hypotheses
    in if total <= IntInf.fromInt limit then () else raise Adapter end
  fun equality limit count left right =
    if 3 + IntInf.fromInt (count limit left) +
        IntInf.fromInt (count limit right) <= IntInf.fromInt limit then ()
    else raise Adapter
  fun admit_law limit conclusion hypotheses =
    (conditional limit raw conclusion hypotheses;
     conditional limit inclusive conclusion hypotheses)
  fun admit_alpha limit left right =
    (equality limit raw left right;
     equality limit inclusive left right)
  fun bounded_type limit ty =
    let fun visit [] _ = ()
          | visit (ty :: rest) count =
              if count >= limit then raise Adapter else
                visit ((if Type.is_vartype ty then [] else
                  #2 (Type.dest_type ty)) @ rest) (count+1)
    in visit [ty] 0 end
  fun inspect limit check_type terms =
    let fun walk [] = ()
          | walk (term :: rest) =
              let val ty = Term.type_of term
                  val _ = bounded_type limit ty
                  val _ = check_type ty
              in if Term.is_abs term then raise Adapter
                 else if Term.is_comb term then
                   let val (operator,operand) = Term.dest_comb term
                   in walk (operator :: operand :: rest) end
                 else walk rest end
    in walk terms end
  fun law conclusion hypotheses = List.foldr boolSyntax.mk_imp
    conclusion hypotheses
  fun located_term (located : CPC_Proof.located_term) = #term located
  datatype plan = Plan of
    {graph : G.graph, scope : G.scope, validate : unit -> unit,
     limit : int, check_type : Type.hol_type -> unit,
     forward : (Term.term,Term.term) Lib.subst,
     reverse : (Term.term,Term.term) Lib.subst,
     allocated_scopes : G.scope list, owned_variables : Term.term list,
     sources : S.sources, source_roots : G.node list,
     source_goal : Term.term}
  datatype prepared = Prepared of
    {plan : plan, original_target : Term.term, lexical_target : Term.term,
     original_premises : CPC_Proof.located_term list,
     lexical_premises : CPC_Proof.located_term list,
     lexical_step : CPC_Proof.step, input_variables : Term.term list}
  fun visible graph scope node =
    if G.scope_visible graph scope (G.node_scope graph node) then () else
      raise ERR "ownership" "unavailable allocated or source variable"
  fun source_visible graph scope node =
    (G.validate_scope graph (G.node_scope graph node);
     if G.scope_visible graph scope (G.node_scope graph node) then () else
       raise ERR "ownership" "original Source root escapes active scope")
  fun active (Plan {graph,scope,validate,allocated_scopes,sources,
      source_roots,source_goal,...}) =
    (validate ();G.validate_scope graph scope;
     List.app (G.validate_scope graph) allocated_scopes;
     if S.assumption_nodes sources @ [S.denied_goal_node sources] =
         source_roots andalso
         same_object (S.canonical_goal sources) source_goal
       then () else raise ERR "ownership" "original Source inventory changed";
     List.app (source_visible graph scope) source_roots)
  fun new {packet,sources,validate,ordinary_limit,check_type} =
    let val graph = Q.graph packet val scope = Q.scope packet
        val _ = validate () val _ = G.validate_scope graph scope
        val _ = if ordinary_limit > 0 then () else
          raise ERR "new" "nonpositive original caller quota"
        val descriptors = Q.variables packet
        val _ = List.app (fn ({node,scope = declared,...} :
            SmtLib_GraphFrontend.solver_variable) =>
          (G.validate_scope graph declared;visible graph scope node;
           if G.scope_visible graph scope declared then () else
             raise ERR "new" "allocated descriptor scope is unavailable"))
          descriptors
        val source_nodes = S.assumption_nodes sources @
          [S.denied_goal_node sources]
        val source_goal = S.canonical_goal sources
        val _ = List.app (source_visible graph scope) source_nodes
        val source_terms = List.map (G.representative graph) source_nodes
        val owned = List.map (G.representative graph o #node) descriptors
        val lexical = List.map #lexical descriptors
        val _ = List.app (whole ordinary_limit)
          (source_terms @ owned @ lexical)
        val _ = inspect ordinary_limit check_type
          (source_terms @ owned @ lexical)
        fun descriptor ({node,lexical,scope = declared} :
            SmtLib_GraphFrontend.solver_variable) =
          (case G.view graph node of
               G.Variable (G.SolverFlexible,term) =>
                 if Term.is_var lexical andalso
                    Term.type_of lexical = Term.type_of term then () else
                   raise ERR "new" "typed allocated descriptor changed"
             | _ => raise ERR "new" "descriptor is not allocated solver ID")
        val _ = List.app descriptor descriptors
        fun unique terms =
          let fun loop [] = ()
                | loop (term :: rest) =
                    if member term rest then
                      raise ERR "new" "noninjective allocated descriptor map"
                    else loop rest
          in loop terms end
        val _ = unique owned val _ = unique lexical
        fun source_variables node =
          case G.free_variable_nodes graph node of NONE => raise Adapter
            | SOME nodes => List.map (fn variable =>
                (visible graph scope variable;
                 case G.view graph variable of
                     G.Variable (G.RigidSource,term) => term
                   | _ => raise ERR "new"
                       "original Source contains a nonrigid variable")) nodes
        val rigid = List.concat (List.map source_variables source_nodes)
        val _ = if List.exists (fn term => member term rigid) lexical
            orelse List.exists (fn term => member term rigid) owned then
          raise ERR "new" "allocated typed name collides with original Source"
          else ()
        val forward = ListPair.mapEq (fn (owned,lexical) =>
          {redex = owned,residue = lexical}) (owned,lexical)
        val reverse = ListPair.mapEq (fn (owned,lexical) =>
          {redex = lexical,residue = owned}) (owned,lexical)
        val plan = Plan {graph = graph,scope = scope,validate = validate,
          limit = ordinary_limit,check_type = check_type,forward = forward,
          reverse = reverse,allocated_scopes = List.map #scope descriptors,
          owned_variables = owned @ rigid,sources = sources,
          source_roots = source_nodes,source_goal = source_goal}
        val _ = active plan
    in plan end
  fun native_component_contract
      (plan as Plan {graph,scope,check_type,...}) target =
    (active plan;visible graph scope target;{check_type = check_type})
  fun closed_component_contract
      (plan as Plan {graph,scope,limit,check_type,...}) target =
    let val _ = active plan val _ = visible graph scope target
        val actual = G.representative graph target
    in if CPC_GraphClosedPrivateComponent.admit limit actual then
        SOME {limit = limit,check_type = check_type} else NONE end
  fun prepare (plan as Plan {graph,scope,limit,check_type,forward,
      owned_variables,...}) {target,step : CPC_Proof.step,premises} =
    let val _ = active plan val _ = visible graph scope target
        val expected = G.representative graph target
        val conclusion = case #conclusion step of SOME value => value
          | NONE => raise Adapter
        val operands = List.map located_term (#args step)
        val antecedents = List.map located_term premises
        val _ = List.app (whole limit) (expected :: located_term conclusion ::
          operands @ antecedents)
        val _ = admit_law limit expected antecedents
        val _ = if same_object expected (located_term conclusion) then () else
          raise ERR "prepare" "recorded conclusion is not the owned target"
        val _ = inspect limit check_type (expected :: operands @ antecedents)
        val _ = if List.all (fn term => Term.type_of term = Type.bool)
          (expected :: antecedents) then () else
          raise ERR "prepare" "target and immediate Hyp must be propositions"
        val inputs = expected :: operands @ antecedents
        val free = List.concat (List.map Term.free_vars inputs)
        val _ = if List.all (fn term => member term owned_variables) free
          then () else raise ERR "prepare" "input has an unowned free variable"
        val memo = ref ([] : (Term.term * Term.term) list)
        fun translated term =
          case List.find (fn (key,_) => same_object key term) (!memo) of
              SOME (_,result) => result
            | NONE => let val result = Term.subst forward term
                      in memo := (term,result) :: !memo;result end
        fun translate (value : CPC_Proof.located_term) =
          {term = translated (#term value),provenance = #provenance value}
        val lexical_target = translated expected
        val lexical_step = {id = #id step,rule = #rule step,
          premises = #premises step,args = List.map translate (#args step),
          conclusion = SOME (translate conclusion)}
        val lexical_premises = List.map translate premises
        val input_variables = List.concat
          (List.map Term.free_vars (List.map translated inputs))
        val _ = active plan
    in Prepared {plan = plan,original_target = expected,
         lexical_target = lexical_target,original_premises = premises,
         lexical_premises = lexical_premises,lexical_step = lexical_step,
         input_variables = input_variables} end
  fun step (Prepared {plan,lexical_step,...}) = (active plan;lexical_step)
  fun premises (Prepared {plan,lexical_premises,...}) =
    (active plan;lexical_premises)
  fun restore (Prepared {plan = plan as Plan {limit,check_type,reverse,...},
      original_target,lexical_target,original_premises,lexical_premises,
      input_variables,...}) {theorem,located : CPC_Proof.located_term} =
    let val _ = active plan
        val actual = Thm.concl theorem val reported = #term located
        val hypotheses = Thm.hyp theorem
        val candidates = (lexical_target,original_target) ::
          ListPair.mapEq (fn (lexical,owned) =>
            (located_term lexical,located_term owned))
            (lexical_premises,original_premises)
        val _ = List.app (whole limit)
          (actual :: reported :: hypotheses @ List.concat
            (List.map (fn (lexical,owned) => [lexical,owned]) candidates))
        (* Substitution preserves sizes, including complete conditional and
           ALPHA laws. Admit each prospective intermediate before INST. *)
        val _ = admit_law limit actual hypotheses
        val _ = admit_law limit original_target hypotheses
        val _ = admit_alpha limit actual lexical_target
        val _ = admit_alpha limit actual original_target
        (* DISCH removes this exact Hyp and places it in the conclusion, so
           the original complete conditional count already covers its law.
           The MP operand carries one canonical Hyp of the same size. *)
        val _ = List.app (fn hypothesis =>
          (admit_law limit hypothesis [hypothesis];
           List.app (fn (_,owned) => admit_alpha limit hypothesis owned)
             candidates)) hypotheses
        val _ = inspect limit check_type (actual :: reported :: hypotheses @
          List.concat (List.map (fn (lexical,owned) => [lexical,owned])
            candidates))
        val _ = Library.check_oracle_tags "CPC_GraphLexicalTransport"
          "restore" theorem
        val _ = if Term.aconv actual lexical_target andalso
            Term.aconv reported lexical_target then () else
          raise ERR "restore" "actual worker changed the recorded endpoint"
        val _ = if List.all (fn term => member term input_variables)
          (List.concat (List.map Term.free_vars (actual :: hypotheses)))
          then () else raise ERR "restore" "worker invented a free variable"
        fun canonical hypothesis =
          case List.find (fn (lexical,_) => Term.aconv hypothesis lexical)
              candidates of SOME (_,owned) => owned
            | NONE => raise ERR "restore" "worker Hyp lacks original authority"
        val original_hypotheses = List.map canonical hypotheses
        val renamed = Thm.INST reverse theorem
        val renamed_hypotheses = Thm.hyp renamed
        fun canonical_renamed hypothesis =
          case List.find (fn expected => Term.aconv hypothesis expected)
              original_hypotheses of SOME expected => expected
            | NONE => raise ERR "restore" "INST changed original Hyp inventory"
        fun retain (hypothesis,proof) =
          let val expected = canonical_renamed hypothesis
          in if same_object hypothesis expected then proof else
            Thm.MP (Thm.DISCH hypothesis proof)
              (Thm.EQ_MP (Thm.ALPHA expected hypothesis)
                (Thm.ASSUME expected)) end
        val retained = List.foldl retain renamed renamed_hypotheses
        val aligned = Thm.EQ_MP
          (Thm.ALPHA (Thm.concl retained) original_target) retained
        val final_hypotheses = Thm.hyp aligned
        fun pointer_member term terms = List.exists
          (fn other => same_object term other) terms
        val _ = if List.all (fn term => pointer_member term
              original_hypotheses) final_hypotheses andalso
            List.all (fn term => pointer_member term final_hypotheses)
              original_hypotheses then () else
          raise ERR "restore" "canonical original Hyp inventory changed"
        val _ = active plan
    in (aligned,{term = original_target,provenance = #provenance located}) end
end
