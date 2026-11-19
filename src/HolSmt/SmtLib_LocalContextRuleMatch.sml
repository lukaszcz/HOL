(* Separate context matcher: actual Hyp variables/types are rigid.
   Scalar and explicit quantified routes only; HO need is never no-match. *)
(* Pure graph/type preparation for the local-context rule catalogue.
   Matching is not Cond_rewr orientation, a condition proof or an INST plan. *)
structure SmtLib_LocalContextRuleMatch :> SmtLib_LocalContextRuleMatch =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure Ctx = SmtLib_OwnedLocalContextRules
  structure Scope = SmtReplayOwnedScopeReceipt
  val _ = SmtLib_OwnedLocalContextRules.describe_for
  fun catalogue_validate work c = Ctx.validate_for work c
  fun catalogue_rows work c = Ctx.rules_for work c
  fun catalogue_facts work c = List.map
    (fn row => #conditional (Ctx.describe_for work row))
    (catalogue_rows work c)
  fun catalogue_originals work c = List.map P.closed_original
    (catalogue_facts work c)
  val _ = SmtReplayGraph.closure_root
  val _ = SmtReplayInvocationWork.with_step
  val _ = SmtReplayProof.record_closed_from_import
  val ERR = Feedback.mk_HOL_ERR "SmtLib_LocalContextRuleMatch"
  datatype terminal = Equality | Positive | Negative
  datatype phase = New | Compiled | Retired
  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     catalogue : Ctx.catalogue,rulescope:G.scope,
     phase : phase ref,symbol_epoch : int}
  fun retire (Owner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected owner action = action () handle primary =>
    (retire owner;raise primary)
  fun active (owner as Owner
      {work,graph,scope,sources,catalogue,phase,symbol_epoch,...}) =
    protected owner (fn () =>
      (if !phase <> Retired then () else
         raise ERR "active" "matching owner retired";
       W.validate work graph scope sources (W.semantic_limits work);
       catalogue_validate work catalogue;
       if Term.term_epoch () = symbol_epoch then () else
         raise ERR "active" "constant retirement epoch changed"))
  fun tick (owner as Owner {work,...}) =
    (active owner;W.spend work 1;active owner)
  fun begin_internal work catalogue =
    let val _ = catalogue_validate work catalogue
        val sources = W.original_sources work
        val graph = S.owning_graph sources
        val scope = S.owning_scope sources
        val _ = W.validate work graph scope sources (W.semantic_limits work)
        val rows = catalogue_rows work catalogue
        val rulescope = case rows of [] => scope
          | row::_ => #scope (Scope.description_for work
              (#frame (Ctx.describe_for work row)))
        val _ = List.app (fn row =>
          if #scope (Scope.description_for work
              (#frame (Ctx.describe_for work row)))=rulescope then () else
            raise ERR "begin" "context clauses have different actual frames")
          rows
    in Owner {work = work,graph = graph,scope = scope,sources = sources,
      catalogue = catalogue,rulescope=rulescope,phase = ref New,
      symbol_epoch = Term.term_epoch ()}
    end handle primary => (W.close work;raise primary)
  fun begin work catalogue = begin_internal work catalogue
  structure Shared = SmtLib_RuleMatchSharedFn (struct
    type owner = owner
    datatype terminal = datatype terminal
    fun graph (Owner {graph,...}) = graph
    fun scope (Owner {scope,...}) = scope
    val active = active
    val tick = tick
    fun spend (Owner {work,...}) n = W.spend work n
    val err = ERR
  end)
  structure Walk = Shared.Walk
  open Walk
  datatype operation = datatype Shared.operation
  datatype schema = Schema of
    {owner : owner,index : int,rule : Thm.thm,whole : tree,
     binders : G.node list,free : G.node list,
     rigid_types:Type.hol_type list,conditions : tree list,
     left : tree,
     right : tree option,terminal : terminal,operations : operation list}
  datatype matched = Match of
    {owner : owner,schema : schema,caller : G.scope,traversal : G.scope,
     target : tree,types : (Type.hol_type * Type.hol_type) list,
     arguments : (G.node * tree) list,output : profile option,used : bool ref}
  datatype instance = Instance of
    {matched : matched,theorem : Thm.thm,proof : P.closed_fact}
  datatype result = NoMatch | NeedsHigherOrder | Matched of matched
  fun compile (owner as Owner {work,graph,rulescope,catalogue,phase,...}) =
    protected owner (fn () => W.with_step work (fn () =>
      let val _ = active owner
          val _ = if !phase = New then phase := Compiled else
            raise ERR "compile" "catalogue compilation already consumed"
          val originals = catalogue_originals work catalogue
          val facts = catalogue_facts work catalogue
          val rows = catalogue_rows work catalogue
          val _ = if length originals = length facts then () else
            raise ERR "compile" "fixed catalogue incidence mismatch"
          fun schemas index rule whole =
            let val metadata = Ctx.describe_for work (List.nth (rows,index))
                val fixed = #fixed_variables metadata
                val free = List.filter (fn node =>
                  not (List.exists (fn variable => guarded owner (fn () =>
                    Term.term_eq variable (G.representative graph node)))
                    fixed)) (free_nodes owner whole)
                (* Hyp types, including types of bound-only variables in
                   the antecedent, are rigid just as in PART_MATCH. *)
                val assumption = G.representative graph
                  (#assumption metadata)
                val rigid = guarded owner (fn () =>
                  Term.type_vars_in_term assumption)
            in List.map (fn {binders,conditions,left,right,terminal,
                  operations} =>
                Schema {owner = owner,index = index,rule = rule,
                  whole = whole,binders = binders,free = free,
                  rigid_types = rigid,conditions = conditions,left = left,
                  right = right,terminal = terminal,operations = operations})
              (Shared.leaves owner "compile" whole) end
      in Shared.compile_rules owner {caller = "compile",scope = rulescope,
        original_changed = "fixed original theorem changed",
        length_mismatch = "fixed catalogue length",originals = originals,
        facts = facts,per_rule = schemas,
        validate_fact = fn fact => P.validate_closed_fact graph rulescope
          (#template_limit (W.semantic_limits work)) fact} end))
  fun original (Schema {owner,rule,...}) = (active owner;rule)
  fun context_for expected (Schema {owner=owner as Owner
      {work,catalogue,...},index,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "context_for" "foreign expected Work";
      active owner;
      Ctx.describe_for work (List.nth (catalogue_rows work catalogue,index)))
     handle primary => (W.close expected;raise primary))

  fun prepare (owner as Owner {work,...})
      {schema = schema as Schema
        {owner = held,binders,free,rigid_types,left,right,...},
       caller,traversal,target} =
    protected owner (fn () =>
      (Shared.same_owner "foreign matching owner" owner held;
       W.with_step work (fn () =>
         case Shared.search owner {binders = binders,free = free,
             rigid_types = rigid_types,left = left,right = right,
             caller = caller,traversal = traversal,target = target,
             admit_target = fn _ => ()} of
           Shared.Missed => NoMatch
         | Shared.HigherOrder => NeedsHigherOrder
         | Shared.Found {target = actual,types,arguments,output} =>
             Matched (Match {owner = owner,schema = schema,
               caller = caller,traversal = traversal,target = actual,
               types = types,arguments = arguments,output = output,
               used = ref false}))))
  fun validate_for expected (Match {owner = owner as Owner
      {work,rulescope,...},schema = Schema {whole,...},caller,traversal,
       target,...}) =
    (Shared.validate_match owner "validate_for"
       {known = Portable.pointer_eq (expected,work),rulescope = rulescope,
        whole = whole,caller = caller,traversal = traversal,target = target}
     handle primary => (W.close expected;raise primary))
  fun describe_for expected (value as Match
      {schema = Schema {index,rule,binders,free,conditions,terminal,...},
       types,arguments,target,output,...}) =
    let val _ = validate_for expected value
    in Shared.describe {rule = rule,index = index,binders = binders,
      free = free,conditions = conditions,terminal = terminal,types = types,
      arguments = arguments,target = target,output = output} end
  (* This derives a closed CONDITIONAL instance. The literal first-order
     route does not claim Cond_rewr's orientation/condition solver policy. *)
  fun instantiate (value as Match {owner = owner as Owner
      {work,graph,rulescope,catalogue,...},schema = Schema
        {index,whole,rule,free,operations,terminal,left,right,...},
      types,arguments,traversal,target,used,...}) {check_type} =
    protected owner (fn () => W.with_step work (fn () =>
      let val provenance = Shared.Provenance (fn () =>
            let val fact = List.nth (catalogue_facts work catalogue,index)
                val _ = P.validate_closed_fact graph rulescope
                  (#template_limit (W.semantic_limits work)) fact
            in if Portable.pointer_eq (rule,P.closed_original fact)
                  andalso P.closed_node fact=node whole then () else
                raise ERR "instantiate" "context rule provenance changed"
            end)
          val {theorem,proof} = Shared.instantiate owner (Shared.Plain work)
            {validate = fn () => validate_for work value,used = used,
             check_type = check_type,whole = whole,rule = rule,free = free,
             operations = operations,terminal = terminal,left = left,
             right = right,target = target,traversal = traversal,
             types = types,arguments = arguments,canonical = provenance}
      in Instance {matched = value,theorem = theorem,proof = proof} end))
  fun instance_context_for expected
      (Instance {matched=Match {schema,...},...}) =
    context_for expected schema
  fun instance_condition_for expected
      (Instance {matched = value as Match
        {owner,traversal,...},proof,...}) index =
    Shared.condition_of owner (Shared.Plain expected) "instance_condition_for"
      {validate_match = fn () => validate_for expected value,
       traversal = traversal,proof = proof,index = index}
  fun instance_target_for expected
      (Instance {matched = value as Match
        {target,caller,traversal,...},...}) =
    (validate_for expected value;Shared.target_of target caller traversal)
  fun instance_fact_for expected
      (Instance {matched = value as Match {owner,traversal,...},proof,...}) =
    Shared.fact_of owner (Shared.Plain expected)
      {validate_match = fn () => validate_for expected value,
       traversal = traversal,proof = proof}
  fun pattern_for expected (Schema
      {owner=owner as Owner {work,rulescope,...},whole,left,right,...}) =
    (Shared.pattern owner "pattern_for"
       {known = Portable.pointer_eq (expected,work),rulescope = rulescope,
        whole = whole,left = left,right = right}
     handle primary => (W.close expected;raise primary))

end
