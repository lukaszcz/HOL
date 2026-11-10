(* Native private closure keeps actual residues as owned graph references. *)
structure CPC_NativePrivateClosure :> CPC_NativePrivateClosure =
struct
  open CPC_ProofParser SmtLib_GraphProof SmtLib_GraphFrontend SmtReplayGraph
    SmtReplaySource SmtReplayResolve SmtReplayRules SmtReplayProof
    SmtReplaySupport SmtReplaySupportedEquality SmtReplayUnify
    SmtReplayUnifyPlan SmtReplayImport SmtLib_Theories
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure R = SmtReplayResolve
  structure Rules = SmtReplayRules
  structure P = SmtReplayProof
  structure C = SmtReplaySupport
  structure E = SmtReplaySupportedEquality
  structure U = SmtReplayUnify
  structure N = SmtReplayUnifyPlan
  structure Q = SmtLib_GraphProof
  structure Parser = CPC_ProofParser
  structure F = SmtLib_GraphFrontend
  val ERR = Feedback.mk_HOL_ERR "CPC_NativePrivateClosure"
  datatype continuation = MissingAssignment | MissingNativeWitness
    | BinderAdapter | ScopedCommandAdapter | UnsupportedCommand
    | UnresolvedCycle | TemplateAdapter
  exception Defer of continuation
  type statistics =
    {occurrences : int,assignments : int,native_witnesses : int,
     selected : int list,graph_nodes : int,captured_occurrences : int,
     proof_counts : (int * int) list}
  datatype outcome = Checked of
    {theorem : Thm.thm,contradiction : Thm.thm,statistics : statistics}
    | Continue of continuation
  type choice = {variable : G.node,residue : G.node,stored : G.node}
  type authority =
    {variable : G.node,residue : G.node,original_index : int,target : G.node,
     relation : G.node,premises : G.node list,conversion : E.certificate,
     trans : E.certificate}
  type bridge =
    {original : G.node,target : G.node,witness : Thm.thm,plan : N.plan}
  datatype fact = Fact of
    {node : G.node,recipe : recipe,occurrence : int}
  and recipe = Original of int | Pending of int | Reflexive of G.node
    | Contradiction of fact * fact | Conjunction of fact * fact
    | Selection of int * fact
  fun node (Fact {node,...}) = node
  fun recipe (Fact {recipe,...}) = recipe
  fun occurrence (Fact {occurrence,...}) = occurrence
  fun pointer left right = Portable.pointer_eq (left,right)
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      null (Thm.hyp theorem) andalso null (Tag.axioms_of (Thm.tag theorem))
      andalso List.all (fn tag => tag = "DISK_THM") tags end

  (* The fixed ordinary explicit-component grammar is bounded independently
     of its source. Instantiation sees one small typed hole; only the graph
     constructor substitutes the actual operand reference. *)
  fun grammar kind marker hole =
    let
      fun unary theory name argument =
        let val operator = Term.prim_mk_const {Thy = theory,Name = name}
            val (domain,_) = Type.dom_rng (Term.type_of operator)
        in Term.mk_comb (Term.inst
          (Type.match_type domain (Term.type_of argument)) operator,
          argument) end
      fun application theory name arguments = List.foldl
        (fn (argument,operator) =>
          let val (domain,_) = Type.dom_rng (Term.type_of operator) in
            Term.mk_comb (Term.inst
              (Type.match_type domain (Term.type_of argument)) operator,
              argument) end)
        (Term.prim_mk_const {Thy = theory,Name = name}) arguments
      fun predicate name = unary "smtfloat" name hole
      fun selector name = unary "binary_ieee"
        ("recordtype.float.seldef." ^ name)
        (unary "smtfloat" "smtfp_rep" hole)
      fun unpack name = application "smtfloatReplayWord" name
        [boolSyntax.mk_disj (predicate "smtfp_is_zero",
           boolSyntax.mk_disj (predicate "smtfp_is_nan",
             predicate "smtfp_is_infinite")),
         selector "Exponent",selector "Significand",
         wordsSyntax.mk_word_L (wordsSyntax.dim_of marker)]
    in if kind = "@fp.SIGN" then selector "Sign"
      else if kind = "@fp.EXPONENT" then
        unpack "smtfp_cvc_unpacked_exponent"
      else if kind = "@fp.SIGNIFICAND" then
        unpack "smtfp_cvc_unpacked_significand"
      else if kind = "@fp.ZERO" then
        SmtLib_Theories.mk_bbterm [predicate "smtfp_is_zero"]
      else if kind = "@fp.NAN" then
        SmtLib_Theories.mk_bbterm [predicate "smtfp_is_nan"]
      else if kind = "@fp.INF" then
        SmtLib_Theories.mk_bbterm [predicate "smtfp_is_infinite"]
      else raise Defer MissingAssignment end

  fun check_packet {packet,validate,sources,template_limit,dag_limit,
                    check_type} =
    let
      val graph = Q.graph packet
      val scope = Q.scope packet
      val proof : Parser.graph_proof = Q.proof packet
      fun active () = (validate ();G.validate_scope graph scope)
      val _ = active ()
      val _ = if template_limit > 0 andalso dag_limit > 0 andalso
          Q.solver packet = "cvc5" then () else
        raise ERR "check_packet" "invalid native private contract"
      val canonical = S.assumption_nodes sources @ [S.denied_goal_node sources]
      val bindings = Q.private_bindings packet
      fun visible node =
        if G.scope_visible graph scope (G.node_scope graph node) then () else
          raise ERR "check_packet" "native private node captures scope"
      val _ = List.app visible canonical
      val _ = List.app (fn {marker,scope = declared,source,...} =>
        (G.validate_scope graph declared;visible marker;
         if G.node_scope graph marker = declared then () else
           raise ERR "check_packet" "private declaration scope changed";
         (case G.view graph marker of G.Variable (G.SolverFlexible,_) => ()
           | _ => raise ERR "check_packet" "private marker is not allocated");
         Option.app visible source)) bindings
      val original_ids = List.concat (List.map (fn root =>
        case G.free_variable_nodes graph root of SOME nodes => nodes
          | NONE => raise Defer BinderAdapter) canonical)
      fun collides marker original = marker = original orelse
        (G.type_id graph marker = G.type_id graph original andalso
         #1 (Term.dest_var (G.representative graph marker)) =
           #1 (Term.dest_var (G.representative graph original)))
      val _ = if List.exists (fn {marker,...} =>
          List.exists (collides marker) original_ids) bindings then
        raise ERR "check_packet" "private marker occurs in original Source"
        else ()
      fun inspect roots =
        let val nodes = G.block_reachable graph roots
            val _ = if length nodes <= dag_limit then () else
              raise Defer TemplateAdapter
            val _ = List.app (fn node =>
              (visible node;case G.view graph node of
                  G.OpaqueRetained => raise Defer BinderAdapter
                | G.AdmittedBinder _ => raise Defer BinderAdapter
                | G.Variable (G.Bound,_) => raise Defer BinderAdapter
                | _ => ())) nodes
        in List.app (check_type o G.type_of graph) nodes end
      fun equality (left,right) =
        let val hole = Term.genvar (G.type_of graph left)
            val operator = G.constant graph scope (Term.rator (Term.rator
              (boolSyntax.mk_eq (hole,hole))))
        in G.application graph scope
          (G.application graph scope (operator,left),right) end
      (* Exact P.freeze constructor/source cost; no actual residue expansion.
         The prospective conditional retains every supplied premise. *)
      fun admit roots sources premises =
        let val reachable = G.block_reachable graph (roots @ sources)
            val _ = if length reachable <= dag_limit then () else
              raise Defer TemplateAdapter
            val definitions = List.mapPartial (fn node =>
              case G.view graph node of G.Constant _ => SOME 5
                | G.Application _ => SOME 7 | _ => NONE) reachable
            val leaves = length sources + length definitions
            val cost = if leaves = 0 then 1 else
              length sources + List.foldl (op +) 0 definitions + 3*(leaves-1)
        in if cost+4+3*premises <= template_limit then () else
          raise Defer TemplateAdapter end
      val falsehood = G.constant graph scope boolSyntax.F
      val known = ref (Redblackmap.mkDict String.compare)
      val obligations = ref ([] : G.node list)
      val independent = ref ([] : G.node list)
      val last = ref (NONE : fact option)
      val captured = ref 0
      val fact_nodes = ref ([] : G.node list)
      fun new_fact {node,recipe} =
        let val serial = !captured
            val _ = captured := serial+1
            val _ = fact_nodes := node :: !fact_nodes
        in Fact {node = node,recipe = recipe,occurrence = serial} end
      fun add id fact =
        if Redblackmap.inDomain (!known,id) then
          raise Defer ScopedCommandAdapter
        else (known := Redblackmap.insert (!known,id,fact);last := SOME fact)
      fun find id = case Redblackmap.peek (!known,id) of SOME fact => fact
        | NONE => raise ERR "command" "unknown or expired premise ID"
      fun declared step target = case #conclusion
          (step : Parser.graph_rule_step) of NONE => () | SOME value =>
            if #node value = target then () else
              raise ERR "command" "declared native endpoint differs"
      fun private target =
        let val nodes = G.block_reachable graph [target] in
          List.exists (fn {marker,...} =>
            List.exists (fn node => node = marker) nodes) bindings end
      fun source_index target =
        let fun loop [] _ = raise ERR "command"
                  "assumption is not a canonical original Source"
              | loop (source :: rest) index = if source = target then index
                  else loop rest (index+1)
        in loop canonical 0 end
      fun command (Parser.GraphAssume (id,value)) =
            add id (new_fact {node = #node value,
                         recipe = Original (source_index (#node value))})
        | command (Parser.GraphAssumePush _) = raise Defer ScopedCommandAdapter
        | command (Parser.GraphStep {step,pop}) =
            if pop then raise Defer ScopedCommandAdapter else
            let
              val name = #replay_handler (#rule step)
              val _ = if (name = "trust" orelse name = "refl") andalso
                  not (null (#premises step)) then
                raise Defer UnsupportedCommand else ()
              val fact = if name = "trust" then
                  (case #args step of [Parser.GraphTerm value] =>
                    let val target = #node value
                        val _ = declared step target
                        val _ = if private target then () else
                          raise Defer UnsupportedCommand
                        val index = length (!obligations)
                        val _ = obligations := target :: !obligations
                    in new_fact {node = target,recipe = Pending index} end
                   | _ => raise Defer UnsupportedCommand)
                else if name = "refl" then
                  (case #args step of [Parser.GraphTerm value] =>
                    let val operand = #node value
                        val target = equality (operand,operand)
                        val _ = declared step target
                        val _ = independent := target :: !independent
                    in new_fact {node = target,recipe = Reflexive operand} end
                   | _ => raise Defer UnsupportedCommand)
                else if name = "and_intro" then
                  (case (List.map find (#premises step),#args step) of
                     ([left,right],[]) =>
                       let val operator = G.constant graph scope
                             boolSyntax.conjunction
                           val target = G.application graph scope
                             (G.application graph scope
                               (operator,node left),node right)
                           val _ = declared step target
                       in new_fact {node = target,
                         recipe = Conjunction (left,right)} end
                   | _ => raise Defer UnsupportedCommand)
                else if name = "and_elim" then
                  (case (List.map find (#premises step),#args step) of
                     ([premise],[Parser.GraphIndex index]) =>
                       if index = 0 orelse index = 1 then
                         (case Rules.operands graph boolSyntax.conjunction 2
                             (node premise) of SOME operands =>
                           let val target = List.nth (operands,index)
                               val _ = declared step target
                           in new_fact {node = target,
                             recipe = Selection (index,premise)} end
                          | _ => raise ERR "command" "nonbinary conjunction")
                       else raise Defer UnsupportedCommand
                   | _ => raise Defer UnsupportedCommand)
                else if name = "contra" then
                  let val premises = List.map find (#premises step)
                      fun choose [] = raise ERR "command"
                            "native contra lacks exact opposite facts"
                        | choose (positive :: rest) =
                            case List.find (fn negative =>
                              case Rules.operands graph boolSyntax.negation 1
                                  (node negative) of
                                SOME [body] => body = node positive
                              | _ => false) premises of
                                SOME negative => (positive,negative)
                              | NONE => choose rest
                      val pair = choose premises
                      val _ = declared step falsehood
                  in new_fact {node = falsehood,
                    recipe = Contradiction pair} end
                else raise Defer UnsupportedCommand
            in add (#id step) fact end
      val _ = List.app command (#commands proof)
      val root = case !last of SOME root =>
          if node root = falsehood then root else
            raise ERR "command" "native packet does not end in contradiction"
        | NONE => raise ERR "command" "empty native packet"
      val obligations = List.rev (!obligations)
      val all = falsehood :: canonical @ obligations @ !independent @
        List.rev (!fact_nodes)
      val count = length canonical
      val proof_counts = ref
        (Redblackmap.mkDict Int.compare : (int,int) Redblackmap.dict)
      fun prove ({name,constructor,premise} : C.discovery) =
        let
          (* One memo per discovery and one key per captured command
             occurrence. Equal targets never identify distinct commands. *)
          val memo = ref
            (Redblackmap.mkDict Int.compare : (int,Thm.thm) Redblackmap.dict)
          fun visit fact =
            let val serial = occurrence fact in
              case Redblackmap.peek (!memo,serial) of SOME proof => proof
              | NONE =>
                let
                  val _ = proof_counts := Redblackmap.insert
                    (!proof_counts,serial,1 + Option.getOpt
                      (Redblackmap.peek (!proof_counts,serial),0))
                  val proof = case recipe fact of
                      Original index => premise index
                    | Pending index => premise (count+index)
                    | Reflexive operand => Thm.EQ_MP
                        (Thm.SYM (constructor (node fact)))
                        (Thm.REFL (name operand))
                    | Conjunction (left,right) =>
                        Thm.EQ_MP (Thm.SYM (constructor (node fact)))
                          (Thm.CONJ (visit left) (visit right))
                    | Selection (index,source) =>
                        let val conjunction = Thm.EQ_MP
                              (constructor (node source)) (visit source)
                        in if index = 0 then Thm.CONJUNCT1 conjunction
                          else Thm.CONJUNCT2 conjunction end
                    | Contradiction (positive,negative) =>
                        let val positive_proof = visit positive
                            val negative_proof = Thm.EQ_MP
                              (constructor (node negative)) (visit negative)
                            val contradiction = Thm.MP
                              (Thm.NOT_ELIM negative_proof) positive_proof
                        in Thm.EQ_MP (Thm.SYM (constructor falsehood))
                          contradiction end
                  val _ = memo := Redblackmap.insert (!memo,serial,proof)
                in proof end
            end
        in visit root end
      (* Include explicit-source dependencies transitively. Chronological
         packet descriptors do not themselves authorize any equality. *)
      fun closure used =
        let val needed = List.filter (fn {marker,...} =>
              List.exists (fn node => node = marker) used) bindings
            val expanded = G.block_reachable graph
              (obligations @ List.mapPartial #source needed)
        in if List.all (fn node => List.exists (fn old => old = node) used)
            expanded then needed else closure expanded end
      val needed = closure (G.block_reachable graph obligations)
      val _ = if null needed andalso not (null obligations) then
        raise ERR "discover" "private obligation lost descriptor" else ()
      fun grammar_size kind = if kind = "@fp.SIGN" then 5 else
        if kind = "@fp.EXPONENT" orelse kind = "@fp.SIGNIFICAND" then 31
        else if List.exists (fn name => name = kind)
            ["@fp.ZERO","@fp.NAN","@fp.INF"] then 17
        else raise Defer MissingAssignment
      val _ = List.app (fn {kind,source,...} : F.private_binding =>
        (if Option.isSome source then () else raise Defer MissingAssignment;
         if 3+2*grammar_size kind <= template_limit then () else
           raise Defer TemplateAdapter)) needed
      val _ = admit all [] (length canonical+length obligations)
      val _ = inspect (all @ List.mapPartial #source needed)
      val root_certificate = C.discover graph scope
        {roots = all,premises = canonical @ obligations,target = falsehood,
         template_limit = template_limit,check_type = check_type,
         prove = prove}
      fun build ({marker,kind,source,...} : F.private_binding) =
        case source of NONE => raise Defer MissingAssignment
          | SOME source =>
              let
                (* Fixed grammar counts are 5,31,31,17,17,17 including hole.
                   Full fixed ALPHA and conditional schema costs fit first. *)
                val size = grammar_size kind
                val _ = if 3+2*size <= template_limit then () else
                  raise Defer TemplateAdapter
                val hole = Term.genvar (G.type_of graph source)
                val template = grammar kind
                  (G.representative graph marker) hole
                val _ = if Option.isSome (SmtReplayImport.bounded_raw_size
                    template_limit template) andalso Option.isSome
                    (SmtReplayImport.bounded_binder_size
                      template_limit template) then () else
                  raise Defer TemplateAdapter
                fun construct term = if Term.is_var term then
                    if pointer term hole then source else
                      raise ERR "grammar" "unowned template free variable"
                  else if Term.is_comb term then
                    let val (operator,operand) = Term.dest_comb term in
                      G.application graph scope
                        (construct operator,construct operand) end
                  else if Term.is_const term then
                    (check_type (Term.type_of term);
                     G.constant graph scope term)
                  else raise Defer BinderAdapter
                val residue = construct template
                val _ = if G.type_id graph marker =
                    G.type_id graph residue
                    then () else raise ERR "grammar"
                      "private field type changed"
                val stored = equality (marker,residue)
              in {variable = marker,residue = residue,stored = stored} end
      val choices = List.map build needed
      val assignments = List.map (fn {variable,residue,...} =>
        {variable = variable,residue = residue}) choices
      val stored = List.map #stored choices
      fun prepare roots = case R.prepare graph scope
          {flexible = List.map #variable choices,assignments = assignments,
           roots = roots @ stored,preserved = falsehood :: canonical} of
            R.Resolved resolution =>
              R.record_assignment_sources resolution stored
          | R.Refused R.CyclicAssignments => raise Defer UnresolvedCycle
          | R.Refused R.NeedsBinderAdmission => raise Defer BinderAdapter
          | R.Refused _ => raise ERR "resolve" "invalid private assignments"
      val resolution = prepare (all @ C.roots root_certificate)
      val normalized = List.map (fn {variable,residue,stored} =>
        {variable = variable,residue = R.node resolution residue,
         stored = stored}) choices
      fun equality_certificate rule target premises =
        (admit (target :: premises) [] (length premises);
         E.discover graph scope
           {rule = rule,target = target,premises = premises,
            template_limit = template_limit,check_type = check_type})
      (* Ordinary leaf-before-cycle scheduling, retaining each original
         equation occurrence. A dependent residue needs already checked
         normalized dependency edges, never an unwitnessed rewritten Source. *)
      fun schedule ([] : (int * choice) list) (done : authority list) =
            List.rev done
        | schedule pending done =
            let
              fun eligible (_,original : choice) =
                List.all (fn dependency =>
                  not (List.exists (fn {variable,...} =>
                    variable = dependency) choices) orelse
                  List.exists (fn {variable,...} =>
                    variable = dependency) done)
                  (case G.free_variable_nodes graph (#residue original) of
                     SOME nodes => nodes | NONE => raise Defer BinderAdapter)
              val selected = case List.find eligible pending of
                  SOME value => value | NONE => raise Defer UnresolvedCycle
              val (index,original) = selected
              val choice = List.nth (normalized,index)
              val variable = #variable choice
              val residue = #residue choice
              val target = equality (variable,residue)
              val relation = equality (#residue original,residue)
              val premises = List.map #target (List.rev done)
              val conversion = if #residue original = residue then
                  equality_certificate "refl" relation [] else
                    equality_certificate "cong" relation premises
              val trans = equality_certificate "trans" target
                [#stored original,relation]
              val value = {variable = variable,residue = residue,
                original_index = index,target = target,relation = relation,
                premises = premises,conversion = conversion,trans = trans}
            in schedule (List.filter (fn (i,_) => i <> index) pending)
              (value :: done) end
      val authorities = schedule (Lib.enumerate 0 choices) []
      fun bridge original =
        let
          val target = R.node resolution original
          val _ = if List.exists (fn fact => R.node resolution fact = target)
              (!independent) then () else raise Defer MissingNativeWitness
          val certificate = equality_certificate "refl" target []
          val _ = admit (E.roots certificate) [] 0
          val witness_block = P.freeze graph
            {scope = scope,roots = E.roots certificate,sources = [],
             template_limit = template_limit}
          val witness = P.realize witness_block target
            (E.assemble witness_block certificate [])
          val _ = if clean witness andalso pointer (Thm.concl witness)
              (G.representative graph target) then () else
            raise ERR "witness" "native witness is not closed clean and exact"
          val unified = case U.unify graph
              {scope = scope,flexible = List.map #variable normalized,
               equations = List.map (fn {variable,residue,...} =>
                 (variable,residue)) normalized @ [(original,target)]} of
                U.Unified result => result
              | U.NoMatch _ => raise Defer BinderAdapter
          val _ = List.app (fn {variable,residue} =>
            if List.exists (fn {variable = name,residue = value,...} =>
                name = variable andalso value = residue) normalized then ()
            else raise ERR "bridge" "unwitnessed native assignment")
            (U.assignments unified)
          val plan = N.discover graph scope unified
          val _ = if null (N.binder_relations plan) then () else
            raise Defer BinderAdapter
        in {original = original,target = target,witness = witness,plan = plan}
        end
      val bridges = List.map bridge obligations
      val roots = all @ C.roots root_certificate @
        List.concat (List.map (fn {target,relation,conversion,trans,...} =>
          target :: relation :: E.roots conversion @ E.roots trans)
          authorities)
        @ List.concat (List.map (fn {target,plan,...} =>
          target :: N.roots plan) bridges)
      val resolution = prepare roots
      val inventory = canonical @ stored @ List.map #target bridges
      val _ = admit roots inventory 0
      val block = P.freeze graph
        {scope = scope,roots = roots,sources = inventory,
         template_limit = template_limit}
      fun entries certificate nodes edges = List.map (fn index =>
        {index = index,node = List.nth (nodes,index),
         edge = List.nth (edges,index)}) (E.selected certificate)
      val stored_edges = List.tabulate (length stored,fn index =>
        P.source block (count+index))
      fun assemble_authorities ([] : authority list) done = List.rev done
        | assemble_authorities
            ({conversion,trans,relation,premises,original_index,...} :: rest)
            done =
            let val previous = List.rev done
                val relation_edge = E.assemble block conversion
                  (entries conversion premises previous)
                val source = List.nth (stored,original_index)
                val edge = E.assemble block trans
                  (entries trans [source,relation]
                    [List.nth (stored_edges,original_index),relation_edge])
            in assemble_authorities rest (edge :: done) end
      val authority_edges = assemble_authorities authorities []
      fun old_edge index ({original,target,plan,...} : bridge) =
        let
          fun assignment ({assignment = {variable,residue},equation} :
              N.obligation) =
            let val i = case List.find (fn (_,authority) =>
                    #variable authority = variable andalso
                    #residue authority = residue andalso
                    #target authority = equation)
                    (Lib.enumerate 0 authorities) of SOME (i,_) => i
                  | NONE => raise ERR "assemble"
                      "missing exact assignment edge"
            in List.nth (authority_edges,i) end
          val equations = N.assemble block plan assignment
          val relation = #target (List.last (N.equations plan))
          val equality_edge = P.compose block
            (fn [constructor,proof] => Thm.EQ_MP constructor proof
              | _ => raise ERR "assemble" "missing law equality")
            [P.constructor block relation,List.last equations]
        in P.compose block
          (fn [relation,proof] => Thm.EQ_MP (Thm.SYM relation) proof
            | _ => raise ERR "assemble" "missing native resolved law")
          [equality_edge,P.source block (count+length stored+index)] end
      val obligation_edges = Lib.mapi old_edge bridges
      val chosen = C.selected root_certificate
      val goal_edge = C.assemble block root_certificate
        (List.map (fn index =>
          {index = index,node = List.nth (canonical @ obligations,index),
           edge = if index < count then P.source block index else
             List.nth (obligation_edges,index-count)}) chosen)
      val edge = P.compose block
        (fn proof :: _ => proof | _ => raise ERR "assemble" "empty final DAG")
        (goal_edge :: obligation_edges)
      fun witness (index,node) =
        if index < count+length stored then NONE else
          let val value = List.nth (bridges,index-count-length stored)
          in if #target value = node then SOME (#witness value) else
            raise ERR "witness" "native occurrence index changed" end
      val _ = active ()
      val contradiction = P.realize_resolved_with_sources block resolution
        falsehood edge witness
      val _ = S.check_contradiction sources contradiction
      val theorem = S.close_contradiction sources contradiction
      val _ = S.check_goal sources theorem
      val _ = active ()
    in Checked {theorem = theorem,contradiction = contradiction,
      statistics = {occurrences = length obligations,
        assignments = length choices,native_witnesses = length bridges,
        selected = chosen,graph_nodes = G.dag_nodes graph roots,
        captured_occurrences = !captured,
        proof_counts = Redblackmap.listItems (!proof_counts)}} end
    handle Defer reason => Continue reason
end
