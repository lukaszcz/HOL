(* Pure graph/type preparation for the exact fixed numeric law catalogue.
   Matching is not Cond_rewr orientation, a condition proof or an INST plan. *)
structure SmtLib_GraphNumericRuleMatch :> SmtLib_GraphNumericRuleMatch =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure C = SmtLib_GraphNumericRewriteCatalogue
  structure K = SmtLib_GraphNumericCanonical
  val _ = SmtLib_GraphNumericCanonical.validate_for
  datatype catalogue = Raw of C.catalogue | Canonical of K.catalogue
  fun catalogue_validate work (Raw c) = C.validate_for work c
    | catalogue_validate work (Canonical c) = K.validate_for work c
  fun catalogue_originals (Raw c) = C.originals c
    | catalogue_originals (Canonical c) = K.originals c
  fun catalogue_facts (Raw c) = C.checked_rules c
    | catalogue_facts (Canonical c) = K.checked_rules c
  val _ = SmtLib_GraphNumericRewriteCatalogue.validate_for
  val _ = SmtReplayGraph.closure_root
  val _ = SmtReplayInvocationWork.with_step
  val _ = SmtReplayProof.record_closed_from_import
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumericRuleMatch"
  datatype terminal = Equality | Positive | Negative
  datatype phase = New | Compiled | Retired
  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     catalogue : catalogue,phase : phase ref,symbol_epoch : int}
  fun retire (Owner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected owner action = action () handle primary =>
    (retire owner;raise primary)
  fun active (owner as Owner
      {work,graph,scope,sources,catalogue,phase,symbol_epoch}) =
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
    in Owner {work = work,graph = graph,scope = scope,sources = sources,
      catalogue = catalogue,phase = ref New,symbol_epoch = Term.term_epoch ()}
    end handle primary => (W.close work;raise primary)
  fun begin work catalogue = begin_internal work (Raw catalogue)
  fun begin_canonical work catalogue =
    begin_internal work (Canonical catalogue)
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
     binders : G.node list,free : G.node list,conditions : tree list,
     left : tree,
     right : tree option,terminal : terminal,operations : operation list}
  datatype matched = Match of
    {owner : owner,schema : schema,caller : G.scope,traversal : G.scope,
     target : tree,types : (Type.hol_type * Type.hol_type) list,
     arguments : (G.node * tree) list,output : profile option,used : bool ref}
  datatype instance = Instance of
    {matched : matched,theorem : Thm.thm,proof : P.closed_fact}
  datatype result = NoMatch | NeedsHigherOrder | Matched of matched
  fun compile (owner as Owner {work,graph,scope,catalogue,phase,...}) =
    protected owner (fn () => W.with_step work (fn () =>
      let val _ = active owner
          val _ = if !phase = New then phase := Compiled else
            raise ERR "compile" "catalogue compilation already consumed"
          val originals = catalogue_originals catalogue
          val facts = catalogue_facts catalogue
          val _ = if length originals = length facts then () else
            raise ERR "compile" "fixed catalogue incidence mismatch"
          fun schemas index rule whole =
            let val free = free_nodes owner whole
            in List.map (fn {binders,conditions,left,right,terminal,
                  operations} =>
                Schema {owner = owner,index = index,rule = rule,
                  whole = whole,binders = binders,free = free,
                  conditions = conditions,left = left,right = right,
                  terminal = terminal,operations = operations})
              (Shared.leaves owner "compile" whole) end
      in Shared.compile_rules owner {caller = "compile",scope = scope,
        original_changed = "fixed original theorem changed",
        length_mismatch = "fixed catalogue length",originals = originals,
        facts = facts,per_rule = schemas,
        validate_fact = fn fact => P.validate_closed_fact graph scope
          (#template_limit (W.semantic_limits work)) fact} end))
  fun original (Schema {owner,rule,...}) = (active owner;rule)
  fun stock_origin (Schema {owner = owner as Owner {catalogue,...},
      index,...}) =
    (active owner;case catalogue of
       Raw c => (index,List.nth (C.originals c,index))
     | Canonical c => List.nth (K.origins c,index))

  fun prepare (owner as Owner {work,...})
      {schema = schema as Schema {owner = held,binders,free,left,right,...},
       caller,traversal,target} =
    protected owner (fn () =>
      (Shared.same_owner "foreign matching owner" owner held;
       W.with_step work (fn () =>
         case Shared.search owner {binders = binders,free = free,
             rigid_types = [],left = left,right = right,caller = caller,
             traversal = traversal,target = target,
             admit_target = fn _ => ()} of
           Shared.Missed => NoMatch
         | Shared.HigherOrder => NeedsHigherOrder
         | Shared.Found {target = actual,types,arguments,output} =>
             Matched (Match {owner = owner,schema = schema,
               caller = caller,traversal = traversal,target = actual,
               types = types,arguments = arguments,output = output,
               used = ref false}))))
  fun validate_for expected (Match {owner = owner as Owner {work,scope,...},
      schema = Schema {whole,...},caller,traversal,target,...}) =
    (Shared.validate_match owner "validate_for"
       {known = Portable.pointer_eq (expected,work),rulescope = scope,
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
  fun instantiate (value as Match {owner = owner as Owner {work,...},
      schema = Schema {whole,rule,free,operations,terminal,left,right,...},
      types,arguments,traversal,target,used,...}) {check_type} =
    protected owner (fn () => W.with_step work (fn () =>
      let val {theorem,proof} = Shared.instantiate owner (Shared.Plain work)
            {words = Shared.plain_words,
             validate = fn () => validate_for work value,used = used,
             check_type = check_type,whole = whole,rule = rule,free = free,
             operations = operations,terminal = terminal,left = left,
             right = right,target = target,traversal = traversal,
             types = types,arguments = arguments,canonical = Shared.Bridge}
      in Instance {matched = value,theorem = theorem,proof = proof} end))
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
      {owner=owner as Owner {work,scope,...},whole,left,right,...}) =
    (Shared.pattern owner "pattern_for"
       {known = Portable.pointer_eq (expected,work),rulescope = scope,
        whole = whole,left = left,right = right}
     handle primary => (W.close expected;raise primary))

  structure RP=SmtReplayResourcePolicy
  structure NC=SmtReplayNativeContract
  datatype policy_catalogue = Raw of C.policy_catalogue | Canonical of
    K.policy_catalogue
  fun catalogue_validate work (Raw c) = C.validate_with_policy_for work c
    | catalogue_validate work (Canonical c) = K.validate_with_policy_for work c
  fun catalogue_originals (Raw c) = C.originals_with_policy c
    | catalogue_originals (Canonical c) = K.originals_with_policy c
  fun catalogue_facts (Raw c) = C.checked_rules_with_policy c
    | catalogue_facts (Canonical c) = K.checked_rules_with_policy c
  val _ = SmtLib_GraphNumericRewriteCatalogue.validate_for
  val _ = SmtReplayGraph.closure_root
  val _ = SmtReplayInvocationWork.with_step
  val _ = SmtReplayProof.record_closed_from_import
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumericRuleMatch"
  datatype phase = New | Compiled | Retired
  datatype policy_owner = PolicyOwner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     policy_catalogue : policy_catalogue,phase : phase ref,symbol_epoch : int,
     native_contract:NC.contract,native_events:IntInf.int ref}
  fun retire (PolicyOwner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected policy_owner action = action () handle primary =>
    (retire policy_owner;raise primary)
  fun active (policy_owner as PolicyOwner
      {work,graph,scope,sources,policy_catalogue,phase,symbol_epoch,
       native_contract,native_events}) =
    protected policy_owner (fn () =>
      (if !phase <> Retired then () else
         raise ERR "active" "matching policy_owner retired";
       W.validate_policy work graph scope sources (W.semantic_policy work);
       NC.validate_for work native_contract;
       catalogue_validate work policy_catalogue;
       if Term.term_epoch () = symbol_epoch then () else
         raise ERR "active" "constant retirement epoch changed"))
  fun tick (policy_owner as PolicyOwner
      {work,native_contract,native_events,...}) =
    (active policy_owner;
     if !native_events<IntInf.fromInt
         (#type_work_limit (NC.for_work work native_contract)) then () else
       raise ERR "tick" "native matching allowance exhausted";
     native_events:= !native_events+1;
     W.spend_policy work 1;active policy_owner)
  fun begin_internal work policy_catalogue =
    let val _ = catalogue_validate work policy_catalogue
        val native_contract=case policy_catalogue of
            Raw c=>C.native_contract_for work c
          | Canonical c=>K.native_contract_for work c
        val sources = W.original_sources work
        val graph = S.owning_graph sources
        val scope = S.owning_scope sources
        val _ = W.validate_policy work graph scope sources (W.semantic_policy
          work)
    in PolicyOwner {work = work,graph = graph,scope = scope,sources = sources,
      policy_catalogue = policy_catalogue,phase = ref New,
      symbol_epoch = Term.term_epoch (),native_contract=native_contract,
      native_events=ref 0}
    end handle primary => (W.close work;raise primary)
  fun begin_with_policy work policy_catalogue = begin_internal work (Raw
    policy_catalogue)
  fun begin_canonical_with_policy work policy_catalogue =
    begin_internal work (Canonical policy_catalogue)
  structure Shared = SmtLib_RuleMatchSharedFn (struct
    type owner = policy_owner
    datatype terminal = datatype terminal
    fun graph (PolicyOwner {graph,...}) = graph
    fun scope (PolicyOwner {scope,...}) = scope
    val active = active
    val tick = tick
    fun spend (PolicyOwner {work,...}) n =
      W.spend_policy work (IntInf.fromInt n)
    val err = ERR
  end)
  structure Walk = Shared.Walk
  open Walk
  datatype operation = datatype Shared.operation
  datatype policy_schema = PolicySchema of
    {policy_owner : policy_owner,index : int,rule : Thm.thm,whole : tree,
     binders : G.node list,free : G.node list,conditions : tree list,
     left : tree,
     right : tree option,terminal : terminal,operations : operation list}
  datatype policy_matched = PolicyMatch of
    {policy_owner : policy_owner,policy_schema : policy_schema,caller :
      G.scope,traversal : G.scope,
     target : tree,types : (Type.hol_type * Type.hol_type) list,
     arguments : (G.node * tree) list,output : profile option,used : bool ref}
  datatype policy_instance = PolicyInstance of
    {policy_matched : policy_matched,theorem : Thm.thm,proof : P.closed_fact}
  datatype policy_result = PolicyNoMatch | PolicyNeedsHigherOrder |
    PolicyMatched of policy_matched
  fun compile_with_policy (policy_owner as PolicyOwner
    {work,graph,scope,policy_catalogue,phase,...}) =
    protected policy_owner (fn () => W.with_step work (fn () =>
      let val _ = active policy_owner
          val _ = if !phase = New then phase := Compiled else
            raise ERR "compile_with_policy"
              "policy_catalogue compilation already consumed"
          val originals = catalogue_originals policy_catalogue
          val facts = catalogue_facts policy_catalogue
          val _ = if length originals = length facts then () else
            raise ERR "compile_with_policy"
              "fixed policy_catalogue incidence mismatch"
          fun schemas index rule whole =
            let val free = free_nodes policy_owner whole
            in List.map (fn {binders,conditions,left,right,terminal,
                  operations} =>
                PolicySchema {policy_owner = policy_owner,index = index,
                  rule = rule,whole = whole,binders = binders,free = free,
                  conditions = conditions,left = left,right = right,
                  terminal = terminal,operations = operations})
              (Shared.leaves policy_owner "compile_with_policy" whole) end
      in Shared.compile_rules policy_owner
        {caller = "compile_with_policy",scope = scope,
         original_changed = "fixed original_with_policy theorem changed",
         length_mismatch = "fixed policy_catalogue length",
         originals = originals,facts = facts,per_rule = schemas,
         validate_fact = fn fact => P.validate_closed_fact_with_policy graph
           scope (#template_limit (W.semantic_policy work)) fact} end))
  fun original_with_policy (PolicySchema {policy_owner,rule,...}) = (active
    policy_owner;rule)
  fun stock_origin_with_policy (PolicySchema {policy_owner = policy_owner as
    PolicyOwner {policy_catalogue,...},
      index,...}) =
    (active policy_owner;case policy_catalogue of
       Raw c => (index,List.nth (C.originals_with_policy c,index))
     | Canonical c => List.nth (K.origins_with_policy c,index))

  fun prepare_with_policy (policy_owner as PolicyOwner {work,...})
      {policy_schema = policy_schema as PolicySchema {policy_owner =
        held,binders,free,left,right,...},
       caller,traversal,target} =
    protected policy_owner (fn () =>
      (Shared.same_owner "foreign matching policy_owner" policy_owner
         held;
       W.with_step work (fn () =>
         case Shared.search policy_owner {binders = binders,free = free,
             rigid_types = [],left = left,right = right,caller = caller,
             traversal = traversal,target = target,
             admit_target = fn actual =>
               let val native=NC.for_work work
                     (case policy_owner of PolicyOwner {native_contract,...}=>
                       native_contract)
                   val input_cap=IntInf.fromInt
                     (#input_limit (#semantic_limits native))
                   val footprint= #profile (data actual)
               in if #raw footprint<=input_cap andalso
                    #inc footprint<=input_cap then () else
                  raise ERR "prepare_with_policy"
                    "native input exceeds limit" end} of
           Shared.Missed => PolicyNoMatch
         | Shared.HigherOrder => PolicyNeedsHigherOrder
         | Shared.Found {target = actual,types,arguments,output} =>
             PolicyMatched (PolicyMatch {policy_owner = policy_owner,
               policy_schema = policy_schema,caller = caller,
               traversal = traversal,target = actual,types = types,
               arguments = arguments,output = output,used = ref false}))))
  fun validate_with_policy_for expected (PolicyMatch {policy_owner =
    policy_owner as PolicyOwner {work,scope,...},
      policy_schema = PolicySchema {whole,...},
       caller,traversal,target,...}) =
    (Shared.validate_match policy_owner "validate_with_policy_for"
       {known = Portable.pointer_eq (expected,work),rulescope = scope,
        whole = whole,caller = caller,traversal = traversal,target = target}
     handle primary => (W.close expected;raise primary))
  fun describe_with_policy_for expected (value as PolicyMatch
      {policy_schema = PolicySchema
        {index,rule,binders,free,conditions,terminal,...},
       types,arguments,target,output,...}) =
    let val _ = validate_with_policy_for expected value
    in Shared.describe {rule = rule,index = index,binders = binders,
      free = free,conditions = conditions,terminal = terminal,types = types,
      arguments = arguments,target = target,output = output} end
  (* This derives a closed CONDITIONAL instance. The literal first-order
     route does not claim Cond_rewr's orientation/condition solver policy. *)
  val policy_words =
    {fname = "instantiate_with_policy",
     quota = "prospective policy_instance exceeds quota",
     template = "policy_instance exceeds closed-recording template",
     portfolio = "policy_instance portfolio exceeds original_with_policy Work",
     collapsed = "type policy_instance collapses free domains",
     operand = "proved policy_instance differs from policy_matched operand"}
  fun instantiate_with_policy (value as PolicyMatch {policy_owner =
    policy_owner as PolicyOwner {work,native_contract,...},
      policy_schema = PolicySchema
        {whole,rule,free,operations,terminal,left,right,...},types,
      arguments,traversal,target,used,...}) {check_type} =
    protected policy_owner (fn () => W.with_step work (fn () =>
      let val {theorem,proof} = Shared.instantiate policy_owner
            (Shared.Policied {work = work,contract = native_contract})
            {words = policy_words,
             validate = fn () => validate_with_policy_for work value,
             used = used,check_type = check_type,whole = whole,rule = rule,
             free = free,operations = operations,terminal = terminal,
             left = left,right = right,target = target,
             traversal = traversal,types = types,arguments = arguments,
             canonical = Shared.Bridge}
      in PolicyInstance {policy_matched = value,theorem = theorem,
        proof = proof} end))
  fun policy_regime expected (PolicyOwner {native_contract,...}) =
    Shared.Policied {work = expected,contract = native_contract}
  fun instance_condition_with_policy_for expected
      (PolicyInstance {policy_matched = value as PolicyMatch
        {policy_owner,traversal,...},proof,...}) index =
    Shared.condition_of policy_owner (policy_regime expected policy_owner)
      "instance_condition_with_policy_for"
      {validate_match = fn () => validate_with_policy_for expected value,
       traversal = traversal,proof = proof,index = index}
  fun instance_target_with_policy_for expected
      (PolicyInstance {policy_matched = value as PolicyMatch
        {target,caller,traversal,...},...}) =
    (validate_with_policy_for expected value;
     Shared.target_of target caller traversal)
  fun instance_fact_with_policy_for expected
      (PolicyInstance {policy_matched = value as PolicyMatch
        {policy_owner,traversal,...},proof,...}) =
    Shared.fact_of policy_owner (policy_regime expected policy_owner)
      {validate_match = fn () => validate_with_policy_for expected value,
       traversal = traversal,proof = proof}
  fun pattern_with_policy_for expected (PolicySchema
      {policy_owner=policy_owner as PolicyOwner {work,scope,...},whole,left,
       right,...}) =
    (Shared.pattern policy_owner "pattern_with_policy_for"
       {known = Portable.pointer_eq (expected,work),rulescope = scope,
        whole = whole,left = left,right = right}
     handle primary => (W.close expected;raise primary))

  fun instance_native_contract_for expected
      (held as PolicyInstance {policy_matched=value as PolicyMatch
        {policy_owner=PolicyOwner {native_contract,...},...},...}) =
    (validate_with_policy_for expected value;native_contract)

end
