structure SmtLib_GraphSemanticPacketPreprocess
  :> SmtLib_GraphSemanticPacketPreprocess =
struct
  open SmtReplayGraph SmtReplayProof SmtReplaySource SmtReplayCanonGraph
    SmtLib_GraphBinderPacketConversion SmtLib_GraphNumComparison
    SmtLib_GraphNumArithmetic SmtLib_GraphNumGuardedArithmetic
    SmtLib_GraphNativeFloatSurface SmtLib_GraphStringTransfer
    SmtLib_GraphScopedMap SmtLib_GraphPreprocessDerived SmtLib_GraphFrontend
    SmtLib_GraphBackend SmtLib_GraphScopedInventory
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure D = SmtLib_GraphPreprocessDerived
  structure C = SmtReplayCanonGraph
  structure B = SmtLib_GraphBinderPacketConversion
  structure NC = SmtLib_GraphNumComparison
  structure NA = SmtLib_GraphNumArithmetic
  structure NG = SmtLib_GraphNumGuardedArithmetic
  structure NF = SmtLib_GraphNativeFloatSurface
  structure ST = SmtLib_GraphStringTransfer
  structure F = SmtLib_GraphFrontend
  structure K = SmtLib_GraphBackend
  structure I = SmtLib_GraphScopedInventory
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphSemanticPacketPreprocess"
  type options =
    {graph : G.graph,scope : G.scope,import_limit : int,template_limit : int,
     prefix_depth : int,natural_enabled : bool,
     admission : SmtReplayBinder.admission}
  type producers =
    {propose : G.node -> C.graph_schema option,
     float : unit -> SmtLib_GraphNativeFloatTransfer.producer option,
     string : unit -> ST.producer option}
  datatype coordinator = Coordinator of
    {options : options,producer : G.scope -> producers,
     inventory : I.inventory}
  datatype validation = Validation of
    {coordinator : coordinator,base : D.validation,
     assumptions : B.conversion list,denied : B.conversion,
     aliases : G.node list,dependency_gaps : G.node list,
     outbound_gaps : G.node list,
     outbound : (I.entry * I.classification) list,closed : bool ref}
  fun remaining_stages () =
    ["free-natural ordinary forall/guard tactic equivalence",
     "exact global num-word entanglement and native-bag policy",
     "natural/float quantifier carrier-changing bridges",
     "guarded native float source facts and full nested coverage",
     "guarded integer cancellation via checked source premise",
     "scoped image rehome and authoritative outbound alias mapping",
     "let, real-pow, polymorphic, real-div and refl simplification",
     "fun-equality, word, set, sequence, bag and collection stages",
     "integer divides, beta, theorem discovery and assumption cleanup",
     "datatype transfer and parser branch source alignment",
     "automatic authoritative outbound token/type packet mapping",
     "actual SolverSpec/Z3/CVC invocation and replay selection"]
  fun create (options as {graph,scope,template_limit,prefix_depth,
                         natural_enabled,admission,...} : options) =
    let
      val _ = G.validate_scope graph scope
      val check_type = #check_type admission
      val cache = ref (Redblackmap.mkDict Int.compare)
      val inventory = I.create graph scope admission
      fun producer scope =
        (G.validate_scope graph scope;
         case Redblackmap.peek (!cache,G.scope_id scope) of SOME created =>
           created
         | NONE =>
             let
               val floats = ref NONE
               val strings = ref NONE
               val numbers = ref NONE
               fun float () = case !floats of SOME created => created
                 | NONE => let val created = NF.create graph scope
                     {template_limit = template_limit,
                      prefix_depth = prefix_depth,check_type = check_type}
                   in floats := SOME created;created end
               fun string () = case !strings of SOME created => created
                 | NONE => let val created = ST.create graph scope
                     {template_limit = template_limit,
                      prefix_depth = prefix_depth,check_type = check_type}
                   in strings := SOME created;created end
               fun numeric () = if not natural_enabled then [] else
                 case !numbers of SOME created => created
                 | NONE =>
                   let
                     val comparisons = NC.propose graph scope
                       {template_limit = template_limit,
                        check_type = check_type}
                     val arithmetic = NA.propose graph scope
                       {template_limit = template_limit,
                        check_type = check_type}
                     val guarded = NG.create graph scope
                       {template_limit = template_limit,
                        check_type = check_type}
                     val created = [comparisons,arithmetic,#propose guarded]
                   in numbers := SOME created;created end
               fun choose [] _ = NONE
                 | choose (propose :: rest) node = case propose node of
                     SOME schema => SOME schema | NONE => choose rest node
               val string_heads = [
                 Term.prim_mk_const {Thy = "smtstring",Name = "str_inj"},
                 Term.prim_mk_const {Thy = "list",Name = "isPREFIX"},
                 Term.prim_mk_const {Thy = "string",Name = "string_lt"},
                 Term.prim_mk_const {Thy = "string",Name = "string_le"}]
               fun head node = case G.view graph node of
                   G.Application (operator,_) => head operator
                 | G.Constant _ => SOME (G.representative graph node)
                 | _ => NONE
               fun same candidate terms =
                 List.exists (Term.same_const candidate) terms
               fun float_head candidate =
                 let
                   val {Thy,Name,...} = Term.dest_thy_const candidate
                   val equality = Term.same_const candidate boolSyntax.equality
                   val domain = if equality then SOME
                     (#1 (Type.dom_rng (Term.type_of candidate))) else NONE
                   val native = case domain of NONE => false | SOME ty =>
                     if Type.is_vartype ty then false else
                       let val {Thy,Tyop,...} = Type.dest_thy_type ty in
                         Thy = "binary_ieee" andalso Tyop = "float"
                       end
                 in Thy = "binary_ieee" orelse Thy = "smtfloat" orelse native
                   orelse (Thy = "bool" andalso Name = "/\\" andalso
                     Option.isSome (!floats))
                 end
               (* Dispatch observes owned constructor IDs, not whole raw
                  terms. Typed producers remain the semantic authority. *)
               fun proposal node =
                 (G.validate_scope graph scope;
                  ignore (G.type_of graph node);
                  case head node of NONE => NONE | SOME candidate =>
                    choose
                      ((if same candidate string_heads orelse
                           (Term.same_const candidate boolSyntax.equality
                            andalso
                            Type.compare (#1 (Type.dom_rng
                              (Term.type_of candidate)),
                              stringSyntax.string_ty) = EQUAL) then
                          [#propose (string ())] else []) @
                       (if float_head candidate then
                          [#propose (float ())] else []) @
                       (if natural_enabled andalso
                           (same candidate [numSyntax.less_tm,numSyntax.leq_tm,
                              intSyntax.int_injection] orelse
                            (Term.same_const candidate boolSyntax.equality
                             andalso Type.compare (#1 (Type.dom_rng
                               (Term.type_of candidate)),numSyntax.num)
                               = EQUAL))
                          then numeric () else []))
                      node)
               fun propose node =
                 let
                   val result = proposal node
                   fun numeric image = case G.view graph image of
                       G.Application (_,operand) => I.capture inventory scope
                         I.Natural {image = image,operands = [operand]}
                     | _ => raise ERR "propose" "invalid injection image"
                   val _ = Option.app (fn schema => List.app numeric
                     (NC.injections graph [C.graph_schema_result schema]))
                     result
                   val _ = case !floats of NONE => () | SOME created =>
                     List.app (fn {image,operands,...} =>
                       I.capture inventory scope I.NativeFloat
                         {image = image,operands = operands})
                       ((#aliases created) ())
                   val _ = case !strings of NONE => () | SOME created =>
                     List.app (fn {image,operand,...} =>
                       I.capture inventory scope I.String
                         {image = image,operands = [operand]})
                       ((#aliases created) ())
                 in result end
               val created = {propose = propose,
                 float = fn () => !floats,string = fn () => !strings}
               val _ = cache := Redblackmap.insert
                 (!cache,G.scope_id scope,created)
             in created end)
    in Coordinator {options = options,producer = producer,
      inventory = inventory} end
  fun active
      (Validation {coordinator = Coordinator {options,...},closed,...}) =
    (if !closed then raise ERR "active" "validation is closed" else ();
     G.validate_scope (#graph options) (#scope options))
  fun original_sources (validation as Validation {base,...}) =
    (active validation;D.original_sources base)
  fun processed_assumptions
      (validation as Validation {assumptions,...}) =
    (active validation;List.map B.result assumptions)
  fun processed_denied_goal (validation as Validation {denied,...}) =
    (active validation;B.result denied)
  fun processed_goal
      (validation as Validation {coordinator = Coordinator {options,...},...}) =
    let
      val graph = #graph options
      val denied = processed_denied_goal validation
      val goal = case G.view graph denied of G.Application (operator,goal) =>
          if Term.same_const (G.representative graph operator)
              boolSyntax.negation then goal else
            raise ERR "processed_goal" "denied goal lost negation"
        | _ => raise ERR "processed_goal" "denied goal lost application"
    in (List.map (G.representative graph)
      (processed_assumptions validation),G.representative graph goal) end
  fun conversions (Validation {assumptions,denied,...}) = denied :: assumptions
  fun roots (validation as Validation {base,...}) =
    (active validation;D.roots base @
     List.concat (List.map B.roots (conversions validation)))
  fun witnesses validation =
    (active validation;
     List.concat (List.map B.witnesses (conversions validation)))
  fun source_nodes (validation as Validation {base,...}) =
    (active validation;D.source_nodes base @ List.map #1 (witnesses validation))
  fun binder_gaps validation =
    (active validation;List.concat (List.map B.gaps (conversions validation)))
  fun dependency_gaps
      (validation as Validation {dependency_gaps,...}) =
    (active validation;dependency_gaps)
  fun outbound_gaps (validation as Validation {outbound_gaps,...}) =
    (active validation;outbound_gaps)
  fun alias_nodes (validation as Validation {aliases,...}) =
    (active validation;aliases)
  fun discover_unchecked
      (coordinator as Coordinator {options,producer,inventory})
      {goal,facts,rules} =
    let
      val {graph,scope,import_limit,template_limit,natural_enabled,
           admission,...} = options
      val _ = G.validate_scope graph scope
      val created = producer scope
      val check_type = #check_type admission
      fun base facts = D.discover graph scope
        {goal = goal,import_limit = import_limit,revisit = true,
         check_type = check_type,conversion = #propose created,
         facts = facts,rules = rules}
      val preliminary = base facts
      val conversion = B.create
        {graph = graph,scope = scope,admission = admission,
         template_limit = template_limit,
         propose = fn scope => #propose (producer scope),
         completed = I.completed inventory}
      val converted = List.map conversion
        (D.processed_denied_goal preliminary ::
          D.processed_assumptions preliminary)
      val output = List.map B.result converted
      val unknown = ref (Redblackmap.mkDict Int.compare)
      val free = List.concat (List.map (fn node =>
        case G.free_variable_nodes graph node of SOME variables => variables
        | NONE => (unknown := Redblackmap.insert
            (!unknown,G.node_id node,node);[])) output)
      val naturals = ref (Redblackmap.mkDict Int.compare)
      val _ = if natural_enabled then List.app (fn node =>
        if Type.compare (G.type_of graph node,numSyntax.num) = EQUAL then
          (case G.view graph node of G.Variable (G.RigidSource,_) =>
              naturals := Redblackmap.insert (!naturals,G.node_id node,node)
            | _ => ()) else ()) free else ()
      val _ = if natural_enabled then List.app (fn image =>
        case G.view graph image of G.Application (_,operand) =>
            if G.scope_visible graph scope (G.node_scope graph operand) then
              naturals := Redblackmap.insert
                (!naturals,G.node_id operand,operand)
            else ()
          | _ => raise ERR "discover" "malformed integer source image")
        (NC.injections graph output) else ()
      val positive = List.map (NA.nonnegative graph scope
        {template_limit = template_limit,check_type = check_type})
        (List.map #2 (Redblackmap.listItems (!naturals)))
      (* Rediscovery keeps the same original Source representative map.
         The checked positivity facts never become ordinary Sources. *)
      val final = base (facts @ positive)
      val denied = conversion (D.processed_denied_goal final)
      val assumptions = List.map conversion (D.processed_assumptions final)
      val outputs = B.result denied :: List.map B.result assumptions
      val _ = List.app (fn node =>
        case G.free_variable_nodes graph node of SOME _ => () | NONE =>
          unknown := Redblackmap.insert (!unknown,G.node_id node,node)) outputs
      val natural_images = if natural_enabled then
        let val injection = G.constant graph scope intSyntax.int_injection in
          List.map (fn (_,operand) =>
            G.application graph scope (injection,operand))
            (Redblackmap.listItems (!naturals)) @ NC.injections graph outputs
        end else []
      val float_aliases = case (#float created) () of NONE => []
        | SOME producer => List.map #image ((#aliases producer) ())
      val string_aliases = case (#string created) () of NONE => []
        | SOME producer => List.map #image ((#aliases producer) ())
      val outbound = I.classify inventory outputs
      val packet_roots = List.mapPartial (fn (_,classification) =>
        case classification of I.RootAlias {image,...} => SOME image
          | _ => NONE) outbound
      val unresolved = List.mapPartial (fn (entry,classification) =>
        case classification of I.Unresolved _ => SOME (I.image entry)
          | _ => NONE) outbound
      val aliases = natural_images @ float_aliases @ string_aliases @
        packet_roots
    in Validation {coordinator = coordinator,base = final,
      assumptions = assumptions,denied = denied,aliases = aliases,
      dependency_gaps = List.map #2 (Redblackmap.listItems (!unknown)),
      outbound_gaps = unresolved,outbound = outbound,closed = ref false} end
  fun discover (coordinator as Coordinator {inventory,...}) request =
    discover_unchecked coordinator request
    handle error => (I.close inventory;raise error)
  fun outbound_inventory (validation as Validation {outbound,...}) =
    (active validation;outbound)
  fun close
      (Validation {coordinator = Coordinator {inventory,...},closed,...}) =
    if !closed then () else (closed := true;I.close inventory)
  fun install_packet
      (validation as Validation {coordinator = Coordinator {inventory,...},
                                outbound,...}) packet session declarations =
    (active validation;
     if List.exists (fn (_,classification) => case classification of
         I.TargetPacket owned => I.packet_target owned = I.packet_target packet
       | _ => false) outbound then () else
       raise ERR "install_packet" "unrecorded final target packet";
     I.install_packet inventory packet session declarations)
  fun assembler (validation as Validation {base,...}) block =
    let
      val _ = active validation
      val original = D.assembler base block
      val compiled = List.map (fn conversion =>
        (B.result conversion,B.source conversion,B.assemble conversion block))
        (conversions validation)
      fun assemble node =
        (active validation;
         case List.find (fn (target,_,_) => target = node) compiled of
           SOME (_,source,equality) =>
             (case original source of NONE => NONE | SOME edge =>
                let val conversion = valOf (List.find
                      (fn conversion => B.result conversion = node)
                      (conversions validation))
                in SOME (P.compose block
                  (fn [source,equality,constructor] =>
                    Thm.EQ_MP (Thm.EQ_MP constructor equality) source
                    | _ => raise Fail "semantic source transport")
                  [edge,equality,P.constructor block (B.equality conversion)])
                end)
         | NONE => original node)
    in assemble end
  fun realize_contradiction validation block false_node edge =
    let
      val registered = witnesses validation
      fun witness (_,node) = Option.map #2
        (List.find (fn (owned,_) => owned = node) registered)
      val theorem = P.realize_with_sources block false_node edge witness
    in S.close_contradiction (original_sources validation) theorem end
  fun install_frontend
      (validation as Validation {coordinator = Coordinator {options,...},...})
      (session : F.session) {aliases,scope_opened,record_map} =
    let
      val _ = active validation
      val {graph,scope,admission,template_limit,...} = options
      val reader = #reader session
      val _ = G.validate_scope graph (#scope reader)
      val inventory = alias_nodes validation
      val backend = #backend reader
      fun install (token,node) =
        let
          val ty = G.type_of graph node
          val _ = if List.exists (fn owned => owned = node) inventory then ()
            else raise ERR "install_frontend" "unrecorded outbound alias"
          val _ = case G.free_variable_nodes graph node of NONE =>
              raise ERR "install_frontend" "unknown outbound source free IDs"
            | SOME variables => List.app (fn variable =>
                if G.scope_visible graph scope (G.node_scope graph variable)
                then () else raise ERR "install_frontend"
                  "outbound source free ID escapes") variables
          fun parse frame _ indices arguments =
            if not (null indices andalso null arguments) then
              raise ERR "alias" "outbound alias requires nullary occurrence"
            else let val active = valOf (K.frame_scope backend frame) in
              if G.scope_visible graph active (G.node_scope graph node)
              then node else raise ERR "alias" "outbound alias escapes reader"
            end
        in (#add_source_parser session) (token,ty,parse) end
      val _ = List.app install aliases
    in SmtLib_GraphScopedMap.install
      {graph = graph,admission = admission,template_limit = template_limit,
       scope_opened = scope_opened,record = record_map} session end
end
