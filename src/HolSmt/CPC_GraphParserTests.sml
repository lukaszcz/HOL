(* Focused Task35 CPC parser regressions. Parser packets certify syntax,
   not inference. Only bounded semantic observations below are reconstructed
   and kernel-compared; the shared70/80 controls NEVER reconstruct a Term. *)
val _ = load "CPC_GraphValueProofParser"
structure CPC_GraphParserTests =
struct
  open HolKernel Parse boolLib bossLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure V = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure T = SmtLib_GraphTranslation
  structure F = SmtLib_GraphFrontend
  structure B = SmtLib_GraphBackend
  structure PV = SmtLib_GraphParserValue
  structure MD = SmtLib_GraphDeclarationMetadata
  structure M = SmtLib_GraphParserMapping
  structure D = SmtLib_GraphDatatypeParser
  structure RP = SmtReplayResourcePolicy
  structure P = SmtLib_Parser
  structure CS = SmtLib_ConstructorSyntax
  structure C = CPC_ProofParser
  structure Old = CPC_Proof
  structure CV = CPC_GraphValueProofParser
  structure VP = SmtLib_GraphValueProof
  structure Packet = SmtLib_GraphProof

  val cap = RP.AtMost 1000000000
  val index_override = ref (NONE:int option)
  val maximum = 4096
  val version = "1.3.4"
  val goal = ``(task35_option:bool option) = SOME T``
  val compound = ``task35_p \/ task35_q``
  (* Native signatures from cpc_parameterized_skolem_registry_success in
     Unittest.sml. Source imports preserve these exact HOL types rather
     than relying on a solver's Set/Bag encoding to manufacture fixtures. *)
  val sources =
    [("task35_compound",compound),
     ("task35_string", ``SmtStr []``),
     ("task35_regex", ``reglan_none``),
     ("task35_sequence", ``([]:num list)``),
     ("task35_bool_sequence", ``([]:bool list)``),
     ("task35_array", ``(\x:num. 0:num)``),
     ("task35_bool_array", ``(\x:num. T)``),
     ("task35_set", ``(\x:num. T)``),
     ("task35_bag", ``(\x:num. 0:num)``),
     ("task35_table", ``(\b:num->num. 0:num)``),
     ("task35_map", ``(\x:num. &x:int)``),
     ("task35_bad_map", ``(\x:bool. 0:int)``),
     ("task35_num", ``0:num``),
     ("task35_re_alpha_x", ``reglan_concat
       (reglan_to_re ((\x:smtstr. x) (SmtStr [97]))) reglan_allchar``),
     ("task35_re_alpha_y", ``reglan_concat
       (reglan_to_re ((\y:smtstr. y) (SmtStr [97]))) reglan_allchar``),
     ("task35_re_alpha_z", ``reglan_concat
       (reglan_to_re ((\z:smtstr. z) (SmtStr [97]))) reglan_allchar``)]
  val policy = {template_limit=cap,index_limit=cap,
    operand_limit=cap,token_limit=cap}
  type env = {graph:G.graph,scope:G.scope,sources:S.sources,
    work:W.portfolio,query:GP.graph_query,metadata:MD.metadata,
    private_atoms:(Term.term * string) list ref}
  type value_contents = PV.value C.constructed_graph_proof VP.contents
  datatype route = Finite | Policy | Value
  val routes = [Finite,Policy,Value]
  fun route_name Finite = "finite"
    | route_name Policy = "policy"
    | route_name Value = "production Value"
  fun require text yes = if yes then () else raise Fail text
  val failures = ref ([]:string list)
  val bridges = ref 0
  fun test label action =
    (testutils.tprint ("Task35 " ^ label);
     ((action ();testutils.OK ()) handle primary =>
       (failures := label :: !failures;
        print ("FAILED: " ^ General.exnMessage primary ^ "\n"))))
  fun finally action close =
    let val result = Exn.capture action ()
        val cleanup = Exn.capture close ()
    in case result of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end
  fun stream text action =
    let val input = TextIO.openString text
    in finally (fn () => action input) (fn () => TextIO.closeIn input) end
  fun input text =
    let val next = ref 0 in fn () =>
      if !next=String.size text then NONE else
        let val char = String.sub (text,!next)
        in next := !next+1;SOME char end end

  (* The genuine group390 factory, including actual emitted datatype
     metadata. No forged Mapping/session or arbitrary PV validation guard. *)
  fun owned action =
    let
      val graph = G.new () val scope = G.root_scope graph
      val originals = S.new graph scope 10000 {assumptions=[],goal=goal}
      val work = W.begin_with_policy graph scope originals
        {limits={input_limit=cap,output_limit=cap,template_limit=cap},
         work_limit=cap}
      fun run () =
        let
          val {assumptions,denied} = V.originals_with_policy work
          val validation = V.validate_portfolio_with_policy work
            {assumptions=assumptions,goal= #node (S.goal_source originals),
             denied=denied}
          val query = GP.prepare_query_with_policy work
            (GP.from_portfolio_with_policy work validation)
          fun open_view caller node = ignore
            (G.record_opened_view_with_policy graph caller
              (RP.AtMost 10000) node)
          val metadata = T.with_outbound_query_analysis_with_policy work
            query open_view (fn context =>
              SmtLib.outbound_with_backend_context
                {sequence_emission=false,set_backend=SmtLib.Z3Set,
                 bag_backend=SmtLib.Z3ArrayBag,
                 has_set_terms=false,has_bag_terms=false}
                (fn backend =>
                  let
                    val operations =
                      SmtLib_GraphCarrierOperations.make_with_datatypes
                        context {sequence_emission=false}
                        {term_to_string=fn _ =>
                          raise Fail "unexpected Task35 formatter"}
                    val emission = SmtLib_GraphDispatcher.emit context
                      {operations=operations,regime=SmtLib.FirstOrder,
                       apply_operator=SmtLib.ApplyUnderscore,
                       prefix="task35_emitted_",roots=[(0,#goal context)]}
                  in MD.freeze context
                    {graph=graph,scope=scope,regime=SmtLib.FirstOrder,
                     backend=backend,operations=operations,emission=emission}
                  end))
        in action ({graph=graph,scope=scope,sources=originals,
          work=work,query=query,metadata=metadata,
          private_atoms=ref []}:env) end
    in finally run (fn () => (W.close work;G.close_scope graph scope)) end
  fun types (e:env) = M.types (MD.mapping (#metadata e))
  fun dictionaries e =
    let val (sorts,terms) = SmtLib_Logics.parsedicts_of_logic "ALL"
        val terms = SmtLib.parser_datatype_term_dictionary_from_types
          (types e) terms
        val terms = List.foldl (fn ((name,term),dict) =>
          Library.extend_dict
            ((name,SmtLib_Theories.K_zero_zero term),dict)) terms sources
    in (Library.union_dict (D.sort_dictionary_from_types (types e)) sorts,
        terms) end
  fun finite_options (e:env) : F.options =
    {graph= #graph e,scope= #scope e,logic="ALL",sources=sources,
     sorts=D.sort_dictionary_from_types (types e),binder_lists=[],
     import_limit=10000,literal_limit=10000,binder_limit=10000,
     recipe_limits={template_limit=10000,
       index_limit=case !index_override of NONE => 10000 | SOME n => n,
       operand_limit=10000,token_limit=10000},
     special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  fun policy_options (e:env) : 'a F.constructed_policy_options =
    {graph= #graph e,scope= #scope e,logic="ALL",sources=sources,
     sorts=D.sort_dictionary_from_types (types e),binder_lists=[],
     import_limit=cap,literal_limit=cap,binder_limit=cap,
     recipe_limits={template_limit=cap,operand_limit=cap,token_limit=cap,
       index_limit=case !index_override of NONE => cap
         | SOME n => RP.AtMost (IntInf.fromInt n)},
     special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  fun install e session =
    let val backend = #backend (#reader (session:F.session))
    in D.install_with_policy
      {limits=policy,error=Feedback.mk_HOL_ERR "CPC_ProofParser"}
      (types e) (fn () => SmtLib.parser_datatype_declarations_from_types
        (types e))
      (fn () => ignore (B.frame_scope backend (B.root backend)))
      session (fn _ => ());session end
  fun native_packet route e text = stream text (fn stream =>
    C.packet version (case route of
        Finite => C.graph_command_reader_with_factory
          (fn options => fn description => fn tokens =>
            install e (F.create_session options description tokens))
          (finite_options e) (dictionaries e) version stream
      | Policy => C.graph_command_reader_with_factory_with_policy
          (fn options => fn description => fn tokens => install e
            (F.create_session_with_policy options description tokens))
          (policy_options e) (dictionaries e) version stream
      | Value => raise Fail "Value is not a native packet"))
  fun value_packet (e:env) text =
    CV.create_packet_with_policy_from_input (#work e) (#query e)
      (policy_options e) (#metadata e) version (input text)
  (* Only authentic packet inventories enter the oracle. Printed generated
     names are not inspected, guessed, alpha-matched or used as keys. *)
  fun native_inventory (e:env) held =
    let
      val _ = require "private inventory has a foreign packet owner"
        (Portable.pointer_eq (Packet.graph held,#graph e) andalso
         Packet.scope held= #scope e)
      val bindings = Packet.private_bindings held
      val variables = Packet.variables held
      val _ = require "private inventory exceeds4096"
        (length bindings<=maximum andalso length variables<=maximum)
      fun atom (binding:F.private_binding) =
        let val node = #marker binding
            val term = case G.view (#graph e) node of
                G.Variable (G.SolverFlexible,term) => term
              | _ => raise Fail "private inventory is not a fresh variable"
            val _ = require "private marker missing from solver inventory"
              (List.exists (fn variable => #node variable=node andalso
                #scope variable= #scope binding andalso
                Type.compare (Term.type_of (#lexical variable),
                  Term.type_of term)=EQUAL) variables)
        in (term,#kind binding) end
    in #private_atoms e := List.map atom bindings end
  fun value_inventory (e:env) (current:value_contents) =
    let
      val context = #context current
      val _ = require "private Value inventory has a foreign packet owner"
        (Portable.pointer_eq (#graph current,#graph e) andalso
         #scope current= #scope e)
      val bindings = #private_bindings current
      val variables = #variables current
      val _ = require "private Value inventory exceeds4096"
        (length bindings<=maximum andalso length variables<=maximum)
      fun atom (binding:VP.private_binding) =
        let val marker = #marker binding
            val term = case PV.proof_view context
                (PV.proof_term context marker) of
                PV.ProofVariable (G.SolverFlexible,term) => term
              | _ => raise Fail "private Value is not a fresh variable"
            val _ = require "private Value missing from solver inventory"
              (PV.scope_of context marker= #scope binding andalso
               List.exists (fn variable =>
                 PV.key context (#node variable)=PV.key context marker
                 andalso #scope variable= #scope binding andalso
                 Type.compare (Term.type_of (#lexical variable),
                   Term.type_of term)=EQUAL) variables)
        in (term,#kind binding) end
    in #private_atoms e := List.map atom bindings end
  fun with_native route text action = owned (fn e =>
    let val held = native_packet route e text
    in finally (fn () =>
      (native_inventory e held;action e (Packet.proof held)))
      (fn () => Packet.close held) end)
  fun with_value text action = owned (fn e =>
    let val held = value_packet e text
    in finally (fn () => W.with_step (#work e) (fn () =>
      let val current = VP.contents_with_policy_for (#work e) (#query e) held
      in value_inventory e current;action e current end))
      (fn () => VP.close held) end)
  fun legacy e text = stream text
    (C.parse_stream_with_version (dictionaries e) version)

  fun bounded term = require "Task35 semantic oracle exceeds4096"
    (Option.isSome (SmtReplayImport.bounded_raw_size maximum term))
  (* Closed, independently enumerated native opaque-head vocabulary. The
     three semantic choice constructors and @purify are NOT renamings.
     @const's native callback names its result by the admitted index. *)
  val native_private_kinds =
    ["@strings_deq_diff", "@strings_stoi_result",
     "@strings_stoi_non_digit", "@strings_itos_result",
     "@strings_num_occur", "@strings_num_occur_re",
     "@strings_occur_index", "@strings_occur_index_re",
     "@strings_replace_all_result", "@witness_string_length",
     "@tables_group_part", "@tables_group_part_element", "@bags_map_sum",
     "@bags_distinct_elements", "@bags_distinct_elements_size",
     "@bags_map_preimage_injective",
     "@cpc.const.0", "@cpc.const.3", "@cpc.const.4"]
  fun rename_private (e:env) term =
    let
      val _ = bounded term
      val atoms = !(#private_atoms e)
      val free = Term.free_vars term
      fun mapping (atom,kind) =
        if not (List.exists (fn variable => Term.compare
            (atom,variable)=EQUAL) free) then NONE else
        let
          val _ = require ("unadmitted private oracle kind: " ^ kind)
            (List.exists (fn admitted => admitted=kind) native_private_kinds)
          val _ = require "ambiguous private oracle inventory"
            (List.all (fn (other,other_kind) =>
              Term.compare (atom,other)<>EQUAL orelse kind=other_kind) atoms)
          val target = Term.mk_var (kind,Term.type_of atom)
          val _ = require "private renaming changed type or atom role"
            (Term.is_var atom andalso Term.is_var target andalso
             Type.compare (Term.type_of atom,Term.type_of target)=EQUAL)
          (* Never hide an existing ordinary free variable by collapsing it
             with a private one. Bound names are handled capture-avoidably. *)
          val _ = require "private renaming collides with ordinary variable"
            (not (List.exists (fn variable =>
              Term.compare (target,variable)=EQUAL andalso
              not (List.exists (fn (saved,_) =>
                Term.compare (saved,variable)=EQUAL) atoms)) free))
        in SOME {redex=atom,residue=target} end
      val result = Term.subst (List.mapPartial mapping atoms) term
    in bounded result;result end

  (* The source importer stops at abstractions. Record only those exact
     retained native atoms from the fixed, independently bounded fixtures;
     regex fixtures also contain an opaque lambda below an application. *)
  val retained_fixture_atoms =
    let fun atoms term =
          if Term.is_abs term then [term]
          else if Term.is_comb term then
            let val (f,x) = Term.dest_comb term in atoms f @ atoms x end
          else []
        fun fixture (_,term) = (bounded term;atoms term)
        val result = List.concat (List.map fixture sources)
        val _ = require "retained fixture inventory exceeds4096"
          (length result<=maximum)
    in result end

  (* TEST ONLY: retained source fixtures may be imported as opaque leaves.
     Demand an authentic same-graph reference and exact retained source,
     then admit its original native size BEFORE inspecting native syntax.
     This does not open a production graph view or grant Source authority. *)
  fun retained_original (e:env) graph scope node remaining =
    let
      val _ = require "opaque oracle has a foreign graph/reference"
        (Portable.pointer_eq (graph,#graph e) andalso
         G.scope_visible graph scope (G.node_scope graph node))
      val _ = require "opaque oracle expected an opaque leaf"
        (case G.view graph node of G.OpaqueRetained => true | _ => false)
      val source = case G.source_anchor graph node of
          SOME source => source
        | NONE => raise Fail "opaque oracle has no retained source"
      val _ = require "opaque oracle source node changed" (#node source=node)
      val original = #original source
      val size = case SmtReplayImport.bounded_raw_size
          (!remaining+1) original of
          SOME size => size
        | NONE => raise Fail "opaque oracle exceeds remaining4096 budget"
      val _ = remaining := !remaining-(size-1)
      val _ = require "opaque oracle is not an original test fixture"
        (List.exists (fn fixture => Portable.pointer_eq (original,fixture))
          retained_fixture_atoms)
      val _ = require "opaque oracle retained source changed"
        (Portable.pointer_eq (original,G.representative graph node))
    in original end
  fun small_graph (e:env) root =
    let
      val graph = #graph e
      val remaining = ref maximum
      fun walk environment node =
        let val _ = require "Task35 graph oracle exceeds4096" (!remaining>0)
            val _ = remaining := !remaining-1
        in case List.find (fn (saved,_) => saved=node) environment of
            SOME (_,term) => term
          | NONE => case G.view graph node of
              G.Variable (_,atom) => atom
            | G.Constant _ => G.representative graph node
            | G.Application (f,x) =>
                Term.mk_comb (walk environment f,walk environment x)
            | G.AdmittedBinder {binder,body,...} =>
                let val variable = Term.genvar (G.type_of graph binder)
                in Term.mk_abs (variable,
                  walk ((binder,variable)::environment) body) end
            | G.OpaqueRetained =>
                retained_original e graph (G.node_scope graph node) node
                  remaining
        end
    in rename_private e (walk [] root) end
  (* The visit counter precedes each reconstruction, including retained
     Source syntax. Binder environments use proof identity, never spelling. *)
  fun small_value (e:env) context value =
    let
      val remaining = ref maximum
      fun walk environment node =
        let val _ = require "Task35 Value oracle exceeds4096" (!remaining>0)
            val _ = remaining := !remaining-1
            val key = PV.proof_key context node
        in case List.find (fn (saved,_) => saved=key) environment of
            SOME (_,term) => term
          | NONE => case PV.proof_view context node of
              PV.ProofVariable (_,atom) => atom
            | PV.ProofConstant atom => atom
            | PV.ProofApplication (f,x) =>
                Term.mk_comb (walk environment f,walk environment x)
            | PV.ProofAbstraction {binder,body,...} =>
                let val variable = Term.genvar
                      (PV.proof_type_of context binder)
                in Term.mk_abs (variable,walk
                  ((PV.proof_key context binder,variable)::environment)
                  body) end
            | PV.ProofOpaque =>
                (case PV.proof_graph_reference context node of
                   SOME {graph,scope,node,...} =>
                     retained_original e graph scope node remaining
                 | NONE => raise Fail
                     "opaque Value has no authentic reference")
        end
      val result = walk [] (PV.proof_term context value)
    in rename_private e result end
  fun normalize term = Conv.QCONV
    (DEPTH_CONV BETA_CONV THENC
     simpLib.SIMP_CONV pureSimps.pure_ss [boolTheory.LET_THM] THENC
     DEPTH_CONV BETA_CONV) term
  fun bridge left right =
    let
      val _ = bounded left val _ = bounded right
      val lhs = normalize left val rhs = normalize right
      val a = boolSyntax.rhs (Thm.concl lhs)
      val b = boolSyntax.rhs (Thm.concl rhs)
      val _ = bounded a val _ = bounded b
      val proof = Thm.TRANS lhs
        (Thm.TRANS (Thm.ALPHA a b) (Thm.SYM rhs))
      val _ = Library.check_oracle_tags "CPC_GraphParserTests" "bridge" proof
      val _ = require "bridge endpoints, types, Hyp or tags changed"
        (null (Thm.hyp proof) andalso
         null (Tag.axioms_of (Thm.tag proof)) andalso
         Type.compare (Term.type_of left,Term.type_of right)=EQUAL andalso
         Term.aconv (Thm.concl proof) (boolSyntax.mk_eq (left,right)))
    in bridges := !bridges+1 end
  fun same_option compare (NONE,NONE) = ()
    | same_option compare (SOME a,SOME b) = compare (a,b)
    | same_option _ _ = raise Fail "optional conclusion changed"
  fun compare_commands raw (old:Old.proof)
      (current:'a C.constructed_graph_proof) =
    let
      fun term (a:Old.located_term,b:'a F.constructed_term) =
        bridge (#term a) (raw (#node b))
      fun argument (a,C.GraphTerm b) = term (a,b)
        | argument _ = raise Fail "ordinary argument changed role"
      fun command (Old.ASSUME (a,x),C.GraphAssume (b,y)) =
            (require "assume ID changed" (a=b);term (x,y))
        | command (Old.ASSUME_PUSH (a,x),C.GraphAssumePush (b,y)) =
            (require "assume-push ID changed" (a=b);term (x,y))
        | command (Old.STEP a,C.GraphStep {step=b,...}) =
            (require "step ID/rule/premise order or multiplicity changed"
               (#id a= #id b andalso #rule a= #rule b andalso
                #premises a= #premises b);
             same_option term (#conclusion a,#conclusion b);
             ListPair.appEq argument (#args a,#args b))
        | command _ = raise Fail "command kind/order changed"
    in require "resolved version changed"
         (#cvc_version old= #cvc_version current);
       ListPair.appEq command (#commands old,#commands current) end
  fun positive label text = List.app (fn route =>
    test (label ^ " / " ^ route_name route) (fn () => case route of
      Value => with_value text (fn e => fn current =>
        compare_commands (small_value e (#context current))
          (legacy e text) (#proof current))
    | _ => with_native route text (fn e => fn proof =>
        compare_commands (small_graph e) (legacy e text) proof))) routes
  fun failure action =
    (action ();NONE) handle Feedback.HOL_ERR detail => SOME
      (Feedback.top_structure_of detail,Feedback.top_function_of detail,
       Feedback.message_of detail)
      | Fail message => SOME ("Fail","",message)
  fun negative_using equivalent label text = List.app (fn route =>
    test (label ^ " / exact " ^ route_name route) (fn () => owned (fn e =>
      let val expected = failure (fn () => ignore (legacy e text))
          val actual = failure (fn () => case route of
              Value => VP.close (value_packet e text)
            | _ => Packet.close (native_packet route e text))
          val _ = G.validate_scope (#graph e) (#scope e)
          fun describe NONE = "ACCEPTED"
            | describe (SOME (origin,where_,message)) =
                origin ^ "." ^ where_ ^ ": " ^ message
      in require ("first exception changed: legacy=" ^ describe expected ^
           "; graph=" ^ describe actual)
           (Option.isSome expected andalso equivalent (expected,actual))
      end))) routes
  fun negative label text = negative_using (op =) label text
  fun classified label text =
    let fun class NONE = NONE
          | class (SOME (origin,where_,_)) = SOME (origin,where_)
    in negative_using (fn (a,b) => class a=class b) label text end

  (* Ordinary annotation parsing historically ignores attribute payloads.
     Let the legacy outcome decide acceptance: malformed-looking metadata
     is not permission to add a new graph-only refusal. *)
  fun differential label text = List.app (fn route =>
    test (label ^ " / differential " ^ route_name route) (fn () =>
      owned (fn e =>
        let
          val previous = Exn.capture (fn () => legacy e text) ()
          fun compare raw proof =
            compare_commands raw (Exn.release previous) proof
          fun parse () = case route of
              Value =>
                let val held = value_packet e text
                in finally (fn () => W.with_step (#work e) (fn () =>
                  let val current = VP.contents_with_policy_for
                        (#work e) (#query e) held
                  in value_inventory e current;
                    compare (small_value e (#context current))
                      (#proof current) end)) (fn () => VP.close held) end
            | _ =>
                let val held = native_packet route e text
                in finally (fn () =>
                  (native_inventory e held;compare (small_graph e)
                    (Packet.proof held))) (fn () => Packet.close held) end
        in case previous of Exn.Res _ => parse ()
          | Exn.Exn primary =>
              let
                val expected = failure (fn () => raise primary)
                val actual = failure (fn () => case route of
                    Value => VP.close (value_packet e text)
                  | _ => Packet.close (native_packet route e text))
              in require "annotation first exception changed"
                (Option.isSome expected andalso actual=expected) end
        end))) routes

  (* Aggregate occurrence shape is intentionally distinct from its semantic
     value. This checks both paths to repeated operands, not a set of IDs. *)
  datatype shape = Atom | App of string * shape list
  fun occurrence_shape (P.ConstructionOccurrence
      {role=P.ConstructionReference _,children=[child],...}) =
        occurrence_shape child
    | occurrence_shape (P.ConstructionOccurrence
      {role=P.ConstructionAnnotation,children=[child],...}) =
        occurrence_shape child
    | occurrence_shape (P.ConstructionOccurrence
        {role=P.ConstructionAtom,...}) = Atom
    | occurrence_shape (P.ConstructionOccurrence {token,children,...}) =
        App (token,List.map occurrence_shape children)
  fun provenance_shape provenance = case provenance of
      Old.AtomicProvenance => Atom
    | Old.ApplicationProvenance (name,children) =>
        App (name,List.map provenance_shape children)
    | Old.ConjunctionProvenance (_,children) =>
        App ("and",List.map provenance_shape children)
    | Old.EqualityProvenance (a,b) =>
        App ("=",[provenance_shape a,provenance_shape b])
    | _ => raise Fail "unexpected aggregate provenance"
  fun assumptions (proof:'a C.constructed_graph_proof) =
    List.map (fn C.GraphAssume (_,term) => term
      | _ => raise Fail "expected assumption") (#commands proof)
  fun located label text expected = List.app (fn route =>
    test (label ^ " / " ^ route_name route) (fn () =>
      let
        fun check e raw (proof:'a C.constructed_graph_proof) =
          let val old = legacy e text
              val _ = compare_commands raw old proof
              val terms = assumptions proof
              val prior = List.map (fn Old.ASSUME (_,term) =>
                    provenance_shape (#provenance term)
                  | _ => raise Fail "expected legacy assumption")
                (#commands old)
          in require "legacy aggregate provenance changed" (prior=expected);
             require "located alias erased operand order/multiplicity"
               (List.map (occurrence_shape o #occurrence) terms=expected);
             require "replay lost the located aggregate boundaries"
               (List.map (provenance_shape o
                  CPC_SharedReplayPlan.occurrence_provenance o #occurrence)
                  terms=expected);
             List.app (fn term => G.validate_scope (#graph e) (#scope term))
               terms end
      in case route of Value => with_value text (fn e => fn current =>
           check e (small_value e (#context current)) (#proof current))
       | _ => with_native route text (fn e => check e (small_graph e))
      end)) routes
  fun annotations () = List.app (fn route => test
    ("annotation wrappers preserve defined OR / " ^ route_name route)
    (fn () =>
      let
        val text = "((define a () (! (or true false) :qid inner)) " ^
          "(assume @a (! a :pattern ((a)) :qid a)))"
        fun check (proof:'a C.constructed_graph_proof) =
          let val term = hd (assumptions proof)
              fun strip (P.ConstructionOccurrence
                  {role=P.ConstructionReference _,children=[child],...}) =
                    strip child
                | strip (P.ConstructionOccurrence
                  {role=P.ConstructionAnnotation,token="!",
                   children=[child],...}) = child
                | strip _ = raise Fail "annotation occurrence lost"
              val inner = strip (strip (#occurrence term))
          in require "annotated definition lost OR boundary"
            (occurrence_shape inner=App ("or",[Atom,Atom])) end
      in case route of Value => with_value text
           (fn _ => fn current => check (#proof current))
       | _ => with_native route text (fn _ => check) end)) routes

  fun source_occurrences () = List.app (fn route => test
    ("Source leaf identity survives definition/LET / " ^ route_name route)
    (fn () =>
      let
        val text = "((define a () task35_compound) " ^
          "(assume @a (let ((copy a)) (or copy (not copy) copy))))"
        fun check source (proof:''a C.constructed_graph_proof) =
          let val term = hd (assumptions proof)
              val children = case #occurrence term of
                  P.ConstructionOccurrence
                    {token="or",children=[a,b,c],...} => (a,b,c)
                | _ => raise Fail "source alias lost OR occurrence"
              val (left,negative,right) = children
              val node = P.construction_value left
              fun atomic (P.ConstructionOccurrence
                  {role=P.ConstructionReference _,children=[child],...}) =
                    atomic child
                | atomic (P.ConstructionOccurrence
                  {role=P.ConstructionAtom,value,children=[],...}) =
                    value=node
                | atomic _ = false
          in require "Source compound was flattened or replaced"
               (source node andalso atomic left andalso atomic right);
             require "negated Source changed identity or occurrence"
               (case negative of P.ConstructionOccurrence
                  {token="not",children=[child],...} => atomic child
                | _ => false) end
        fun native_source (e:env) node =
          case G.source_anchor (#graph e) node of
              SOME {original,...} => Portable.pointer_eq (original,compound)
            | NONE => false
      in case route of Value => with_value text (fn e => fn current =>
          let val context = #context current
          in check (fn value => case PV.proof_graph_reference context
              (PV.proof_term context value) of
                SOME {graph,node,...} =>
                  Portable.pointer_eq (graph,#graph e) andalso
                  native_source e node
              | NONE => false) (#proof current) end)
       | _ => with_native route text (fn e => check (native_source e)) end))
    routes

  (* Native Packet.proof is intentionally a plain syntax getter, not a
     lifetime guard. Only the production Value packet promises this check. *)
  fun packet_lifetime () =
    test "production packet close expires context, not caller root"
      (fn () => owned (fn e =>
        let
          val held = value_packet e
            "((assume @a (forall ((x Bool)) x)))"
          val _ = W.with_step (#work e) (fn () => ignore
            (VP.contents_with_policy_for (#work e) (#query e) held))
          val _ = VP.close held
          val stale = failure (fn () => W.with_step (#work e) (fn () =>
            ignore (VP.contents_with_policy_for
              (#work e) (#query e) held)))
          val _ = G.validate_scope (#graph e) (#scope e)
        in require "closed Value packet remained readable"
          (Option.isSome stale) end))

  fun unique_value context root =
    let val seen = ref (Redblackset.empty Int.compare)
        fun loop [] result = result
          | loop (node::rest) result =
              let val key = PV.key context node in
                if Redblackset.member (!seen,key) then loop rest result
                else
                  let val _ = seen := Redblackset.add (!seen,key)
                      val children = case PV.view context node of
                          PV.Application (a,b) => [a,b]
                        | PV.Abstraction {binder,body,...} => [binder,body]
                        | _ => []
                  in loop (children @ rest) (node::result) end
              end
    in loop [root] [] end
  fun shared_text bound depth =
    let fun name n = "shared_" ^ Int.toString n
        fun definitions n = if n>depth then "" else
          "(define " ^ name n ^ " () " ^
          (if n=0 then "true" else
            "(and " ^ name (n-1) ^ " " ^ name (n-1) ^ ")") ^ ") " ^
          definitions (n+1)
        fun lets n = if n>depth then
            (if bound then "(forall ((x Bool)) (or x local_" ^
               Int.toString depth ^ "))"
             else "(or true local_" ^ Int.toString depth ^ ")")
          else "(let ((local_" ^ Int.toString n ^ " " ^
            (if n=0 then name depth else
              "(or local_" ^ Int.toString (n-1) ^ " local_" ^
                Int.toString (n-1) ^ ")") ^ ")) " ^ lets (n+1) ^ ")"
    in "(" ^ definitions 0 ^ "(assume @a " ^ lets 0 ^ "))" end
  fun shared_dag depth = List.app (fn route => test
    ("unexpanded definitions/LET depth" ^ Int.toString depth ^ " / " ^
      route_name route) (fn () =>
      let
        fun provenance (proof:'a C.constructed_graph_proof) =
          let val visits = ref 0
              val result = CPC_SharedReplayPlan.occurrence_provenance_observed
                (fn _ => visits := !visits+1)
                (#occurrence (hd (assumptions proof)))
              val _ = print ("TASK35_PROVENANCE " ^ Int.toString depth ^
                " visits=" ^ Int.toString (!visits) ^ "\n")
          in require "provenance expanded a shared proof LET"
               (!visits<80*depth+100);ignore result end
        fun native (e:env) proof =
          let val _ = provenance proof
              val root = #node (hd (assumptions proof))
              val nodes = G.reachable (#graph e) [root]
              fun diamond node = case G.view (#graph e) node of
                  G.Application (f,x) => (case G.view (#graph e) f of
                    G.Application (_,y) => x=y | _ => false)
                | _ => false
              val diamonds = length (List.filter diamond nodes)
              val _ = print ("TASK35_NATIVE_SHARED " ^
                Int.toString depth ^ " nodes=" ^ Int.toString (length nodes) ^
                " diamonds=" ^ Int.toString diamonds ^
                " FV=" ^ (case G.free_variable_nodes (#graph e) root of
                  NONE => "unknown" | SOME xs => Int.toString (length xs)) ^
                " raw=" ^ (case G.unfolded_nodes (#graph e)
                  G.BinderInclusiveNodes 4096 root of NONE => "large"
                  | SOME n => Int.toString n) ^ "\n")
          in require "native sharing expanded, erased, or lost closure"
            (length nodes<12*depth+40 andalso
             length (List.filter diamond nodes)>=2*depth andalso
             G.unfolded_nodes (#graph e) G.BinderInclusiveNodes 4096 root
               =SOME 4097 andalso
             G.free_variable_nodes (#graph e) root=SOME []) end
        fun value _ (current:value_contents) =
          let val _ = provenance (#proof current)
              val context = #context current
              val root = #node (hd (assumptions (#proof current)))
              val nodes = unique_value context root
              fun diamond node = case PV.view context node of
                  PV.Application (f,x) => (case PV.view context f of
                    PV.Application (_,y) =>
                      PV.key context x=PV.key context y | _ => false)
                | _ => false
          in require "Value sharing expanded, erased, or lost closure"
            (length nodes<12*depth+40 andalso
             length (List.filter diamond nodes)>=2*depth andalso
             null (PV.free_variables context root)) end
      in case route of Value => with_value (shared_text true depth) value
       | _ => with_native route (shared_text false depth) native end)) routes

  fun branching_text depth =
    let fun name n = "branch_" ^ Int.toString n
        fun defs n = if n>depth then "" else
          "(define " ^ name n ^ " () " ^
          (if n=0 then "(or @x false)" else
            "(and (forall ((y Bool)) (or y " ^ name (n-1) ^ ")) " ^
            "(forall ((z Bool)) (or z " ^ name (n-1) ^ ")))") ^
          ") " ^ defs (n+1)
    in "((define @x () (@var \"x\" Bool)) " ^ defs 0 ^
      "(assume @a (forall (@list @x) " ^ name depth ^ ")))" end
  fun branching_dag depth = test
    ("branching shared lexical capture depth" ^ Int.toString depth)
    (fn () => with_value (branching_text depth) (fn _ => fn current =>
      let val context = #context current
          val term = hd (assumptions (#proof current))
          val root = #node term
          val nodes = unique_value context root
          val blocks = #binder_blocks term
          val _ = print ("TASK35_BRANCH " ^ Int.toString depth ^
            " nodes=" ^ Int.toString (length nodes) ^ " blocks=" ^
            Int.toString (length blocks) ^ "\n")
          fun actual (_,count,node) = count=1 andalso
            List.exists (fn value => PV.key context value=
              PV.key context node) nodes
      in require "irrelevant binders expanded capture or block metadata"
        (length nodes<14*depth+40 andalso length blocks=2*depth+1 andalso
         List.all actual blocks andalso
         null (PV.free_variables context root)) end))

  fun captured_text depth =
    let fun name n = "captured_" ^ Int.toString n
        fun defs n = if n>depth then "" else
          "(define " ^ name n ^ " () " ^
          (if n=0 then "(or @x false)" else "(and " ^ name (n-1) ^
            " " ^ name (n-1) ^ ")") ^ ") " ^ defs (n+1)
    in "((define @x () (@var \"x\" Bool)) " ^ defs 0 ^
      "(assume @a (forall (@list @x) " ^ name depth ^ ")))" end
  fun captured_dag depth = test
    ("shared lexical capture depth" ^ Int.toString depth) (fn () =>
      with_value (captured_text depth) (fn _ => fn current =>
        let val context = #context current
            val root = #node (hd (assumptions (#proof current)))
            val nodes = unique_value context root
            val binders = List.mapPartial (fn node =>
              case PV.view context node of PV.Abstraction {binder,...} =>
                SOME binder | _ => NONE) nodes
        in require "capture expanded, missed Bound identity, or leaked x"
          (length nodes<6*depth+30 andalso length binders=1 andalso
           null (PV.free_variables context root)) end))

  fun binder_scopes () = List.app (fn route => test
    ("quoted lexical shadow/fresh Bound IDs / " ^ route_name route)
    (fn () =>
      let
        val text = "((define x () (or true false)) " ^
          "(assume @a (forall ((x Bool)) x)) " ^
          "(assume @b (forall ((|x| Bool)) x)) (assume @c x))"
        fun check e raw nodes abstraction free
            (proof:''a C.constructed_graph_proof) =
          let val terms = assumptions proof
              val _ = compare_commands raw (legacy e text) proof
              fun binder (term:''a F.constructed_term) =
                case List.mapPartial abstraction
                    (nodes (#node term)) of
                  [(variable,body)] =>
                    (require "body lost its exact Bound identity"
                       (variable=body);variable)
                | _ => raise Fail "expected one admitted binder"
              val first = binder (List.nth (terms,0))
              val second = binder (List.nth (terms,1))
          in require "separate binders reused a Bound identity"
               (first<>second);
             List.app (fn term => require "closed term became open"
               (null (free (#node term)))) terms end
      in case route of Value => with_value text (fn e => fn current =>
          let val context = #context current
          in check e (small_value e context) (unique_value context)
            (fn node => case PV.view context node of
                PV.Abstraction {binder,body,...} => SOME (binder,body)
              | _ => NONE) (PV.free_variables context) (#proof current) end)
       | _ => with_native route text (fn e => check e (small_graph e)
           (fn root => G.reachable (#graph e) [root])
           (fn node => case G.view (#graph e) node of
               G.AdmittedBinder {binder,body,...} => SOME (binder,body)
             | _ => NONE)
           (fn root => case G.free_variable_nodes (#graph e) root of
               SOME variables => variables
             | NONE => raise Fail "unknown binder dependencies")) end)) routes
  fun private_scopes () =
    test "private scalar/FP markers are not lexical definition identities"
      (fn () => with_value
        "((define @t1 () (@fp.NAN (_ BitVec 1))) \
        \(define @t2 () (@fp.NAN (_ BitVec 1))) \
        \(assume @a (= @t1 @t2)) \
        \(assume @b (let ((|@fp.NAN| true)) |@fp.NAN|)) \
        \(assume @c (let ((i 3)) (and (= (@const 3 true) true) \
        \(let ((i 4)) (= (@const 4 true) false))))))"
        (fn e => fn current =>
          let val context = #context current
              val terms = assumptions (#proof current)
              val equality = #node (hd terms)
              val (left,right) = case PV.view context equality of
                  PV.Application (f,right) => (case PV.view context f of
                    PV.Application (_,left) => (left,right)
                  | _ => raise Fail "missing private equality operator")
                | _ => raise Fail "missing private equality"
              val bindings = #private_bindings current
              val kinds = List.map #kind bindings
              val locals = List.filter (fn binding =>
                #kind binding="@cpc.const.3" orelse
                #kind binding="@cpc.const.4") bindings
          in require "private FP occurrences were conflated"
               (PV.key context left<>PV.key context right);
             bridge boolSyntax.T
               (small_value e context (#node (List.nth (terms,1))));
             require ("private LET indexes lost scoped inventory: " ^
                 String.concatWith "," kinds)
               (List.exists (fn kind => kind="@cpc.const.3") kinds andalso
                List.exists (fn kind => kind="@cpc.const.4") kinds);
             List.app (fn binding => require
               "private marker owner was replaced by lexical scope"
               (#lexical_scope binding<> #scope binding andalso
                PV.scope_of context (#marker binding)= #scope binding))
               locals;
             require "proof markers became original assumptions"
               (null (S.assumption_nodes (#sources e))) end))

  (* Exercise the lexical/private distinction directly, independently of
     the parser's generated spelling. Explicit private variables are atoms;
     original variables are lexical even when name AND type coincide. *)
  fun private_source_syntax () =
    test "private source atoms resist lexical capture/substitution" (fn () =>
      let
        val spent = ref (0:IntInf.int)
        fun spend amount =
          (spent := !spent+amount;
           require "private syntax observation exceeds fixed budget"
             (!spent<=1000000))
        val x = Term.mk_var ("task35_private_source",Type.bool)
        val y = Term.mk_var ("task35_other_source",Type.bool)
        val private = CS.private_atom
        val atom = private x
        val lexical = CS.variable x
        fun is_atom source = case CS.view spend source of
            CS.Atom saved => Term.compare (saved,x)=EQUAL
          | _ => false
        fun is_true source = case CS.view spend source of
            CS.Atom saved => Term.aconv saved boolSyntax.T
          | _ => false
        val _ = require "private atom entered lexical free variables"
          (null (CS.free_variables spend atom) andalso
           List.exists (fn variable => Term.compare (variable,x)=EQUAL)
             (CS.all_variables spend [atom]))
        val _ = require "private atom alpha-matched its lexical namesake"
          (not (CS.aconv spend (atom,lexical)))
        val _ = require "lexical substitution replaced a private atom"
          (is_atom (CS.substitute spend [(x,CS.native boolSyntax.T)] atom)
           andalso is_true
             (CS.substitute spend [(x,CS.native boolSyntax.T)] lexical))
        val captured = CS.abstraction (x,atom)
        val _ = require "private atom was bound or alpha-renamed"
          (case CS.dest_abs spend captured of
             SOME (_,body) => is_atom body
           | NONE => false)
        val _ = require "source alpha ignored private atom identity"
          (CS.aconv spend (captured,CS.abstraction (y,private x)) andalso
           not (CS.aconv spend (captured,CS.abstraction (y,private y))))
        val _ = require "LET normalization captured a private atom"
          (is_atom (CS.normalize_lets spend
            (CS.let_expression ([(x,CS.native boolSyntax.T)],atom)))
           andalso is_true (CS.normalize_lets spend
            (CS.let_expression ([(x,CS.native boolSyntax.T)],lexical))))
      in () end)

  fun private_capture () =
    test "generated private identity is not a lexical alias domain"
      (fn () =>
        let
          val prefix = "((define @nan () (@fp.NAN (_ BitVec 1))) " ^
            "(define @expr () (= @nan @nan)) "
          val name = with_value (prefix ^ "(assume @a @expr))")
            (fn _ => fn current =>
              let val context = #context current
                  val marker = #marker (valOf (List.find (fn binding =>
                    #kind binding="@fp.NAN") (#private_bindings current)))
                  val variable = valOf (List.find (fn variable =>
                    PV.key context (#node variable)=PV.key context marker)
                    (#variables current))
              in #1 (Term.dest_var (#lexical variable)) end)
          val text = prefix ^ "(assume @a (forall ((|" ^ name ^
            "| (_ BitVec 1))) @expr)))"
        in with_value text (fn _ => fn current =>
          let val context = #context current
              val marker = #marker (valOf (List.find (fn binding =>
                #kind binding="@fp.NAN") (#private_bindings current)))
              val term = hd (assumptions (#proof current))
              val variables = PV.free_variables context (#node term)
          in require "lexical capture replaced a generated private marker"
            (length variables=1 andalso PV.key context (hd variables)=
              PV.key context marker) end) end)

  fun private_quantifier_capture () =
    let
      val prefix = "((define @nan () (@fp.NAN (_ BitVec 1))) "
      val name = with_value (prefix ^ "(assume @a (= @nan @nan)))")
        (fn _ => fn current =>
          let val context = #context current
              val marker = #marker (valOf (List.find (fn binding =>
                #kind binding="@fp.NAN") (#private_bindings current)))
              val variable = valOf (List.find (fn variable =>
                PV.key context (#node variable)=PV.key context marker)
                (#variables current))
          in #1 (Term.dest_var (#lexical variable)) end)
      (* The private atom and lexical binder print identically, but only
         the lexical operand occurrence belongs to the FORALL's domain. *)
      val quantified = "(forall ((|" ^ name ^ "| (_ BitVec 1))) " ^
        "(= @nan |" ^ name ^ "|))"
      val text = prefix ^ "(step @p :rule refl :args " ^
        "((@quantifiers_skolemize " ^ quantified ^ " 0))))"
    in test "quantifier witness retains colliding private atom" (fn () =>
      with_value text (fn _ => fn current =>
        let val context = #context current
            val marker = #marker (valOf (List.find (fn binding =>
              #kind binding="@fp.NAN") (#private_bindings current)))
            val witness = case #commands (#proof current) of
                [C.GraphStep {step={args=[C.GraphTerm term],...},...}] =>
                  #node term
              | _ => raise Fail "missing colliding quantifier witness"
            val free = PV.free_variables context witness
        in require "quantifier capture replaced a private atom"
          (length free=1 andalso PV.key context (hd free)=
            PV.key context marker) end)) end

  fun testers () = owned (fn e =>
    let
      val declarations = SmtLib.parser_datatype_declarations_from_types
        (types e)
      val constructors = case List.find
          (fn {hol_type,...}:SmtLib.parser_datatype_declaration =>
            Type.compare (hol_type,``:bool option``)=EQUAL) declarations of
          SOME {constructors,...} => constructors
        | NONE => raise Fail "actual emitted option schema missing"
      val none = case List.find
          (fn {selectors,...}:SmtLib.parser_datatype_constructor =>
            null selectors) constructors of SOME {token,...} => token
        | NONE => raise Fail "actual NONE constructor missing"
      val some = case List.find
          (fn {selectors,...}:SmtLib.parser_datatype_constructor =>
            length selectors=1) constructors of SOME {token,...} => token
        | NONE => raise Fail "actual SOME constructor missing"
      fun fixture constructor term =
        "((define @t () (is " ^ constructor ^ " " ^ term ^ ")) " ^
        "(assume @a (= @t ((_ is " ^ constructor ^ ") " ^ term ^ "))) " ^
        "(step @b :rule refl :args ((= (is " ^ constructor ^ " " ^ term ^
        ") (is " ^ constructor ^ " " ^ term ^ ")))))"
      (* Reuse exact emitted tokens in fresh factories; deterministic
         emission is part of this closed, fixed fixture. *)
    in positive "nested CPC NONE tester normalization" (fixture none none);
       positive "nested CPC SOME tester normalization"
         (fixture some ("(" ^ some ^ " true)")) end)

  (* Native signatures from cpc_parameterized_skolem_registry_success.
     Each result is an observable refl argument, including function-valued
     private skolems. Keep this inventory independent of the registry. *)
  val parameterized_fixtures =
    [("@purify", "0"),
     ("@array_deq_diff", "task35_array task35_array"),
     ("@const", "0 task35_string"),
     ("@quantifiers_skolemize", "(forall ((x Bool)) x) 0"),
     ("@re_unfold_pos_component", "task35_string task35_regex 0"),
     ("@strings_deq_diff", "task35_string task35_string"),
     ("@strings_stoi_result", "task35_string"),
     ("@strings_stoi_non_digit", "task35_string"),
     ("@strings_itos_result", "0"),
     ("@strings_num_occur", "task35_string task35_string"),
     ("@strings_num_occur_re", "task35_string task35_regex"),
     ("@strings_occur_index", "task35_string task35_string"),
     ("@strings_occur_index_re", "task35_string task35_regex"),
     ("@strings_replace_all_result", "task35_sequence"),
     ("@witness_string_length", "task35_sequence"),
     ("@sets_deq_diff", "task35_set task35_set"),
     ("@bags_deq_diff", "task35_bag task35_bag"),
     ("@tables_group_part", "task35_table"),
     ("@tables_group_part_element", "task35_table task35_bag"),
     ("@bags_map_sum", "task35_map task35_bag 0"),
     ("@bags_distinct_elements", "task35_bag"),
     ("@bags_distinct_elements_size", "task35_bag"),
     ("@bags_map_preimage_injective", "task35_map task35_bag 0")]
  fun parameterized_registry () =
    let
      val names = List.map #1 parameterized_fixtures
      val _ = test "complete native parameterized registry inventory"
        (fn () => require "parameterized registry fixture drift"
          (length names=23 andalso
           Listsort.sort String.compare names=
           Listsort.sort String.compare C.cpc_parameterized_skolem_names))
      fun fixture (name,args) =
        let val text = "((step @p :rule refl :args ((" ^ name ^ " " ^
              args ^ "))))"
            fun check raw old proof =
              let val prior_bridges = !bridges
                  val _ = compare_commands raw old proof
              in require "registry fixture did not prove exactly one bridge"
                (!bridges=prior_bridges+1) end
        in List.app (fn route => test
          ("native parameterized registry " ^ name ^ " / " ^ route_name route)
          (fn () => case route of
             Value => with_value text (fn e => fn current =>
               check (small_value e (#context current))
                 (legacy e text) (#proof current))
           | _ => with_native route text (fn e => fn proof =>
               check (small_graph e) (legacy e text) proof))) routes end
    in List.app fixture parameterized_fixtures end

  (* Private identity oracle: inventories and dependencies are exact sets
     of allocated IDs, never generated-name patterns or alpha matches.
     Sort metadata allocations are inventoried even when the constructor
     deliberately discards them from its semantic result. *)
  fun private_dependencies () =
    let
      fun sorted names = Listsort.sort String.compare names
      fun same_ids actual expected =
        length actual=length expected andalso
        List.all (fn node => List.exists (fn saved => node=saved)
          expected) actual andalso
        List.all (fn node => List.exists (fn saved => node=saved)
          actual) expected
      fun fixture (label,definitions,inventory,dependencies,
          witness_sort,body) =
        let
          val prefix = "(" ^ definitions ^
            "(define @q () (forall ((x " ^ witness_sort ^ ")) " ^
            body ^ ")) " ^
            "(define @qa () @q) " ^
            "(define @w () (@quantifiers_skolemize @qa 0)) " ^
            "(define @wa () @w) "
          val text = prefix ^
            "(assume @a (forall ((outer Bool)) " ^
            "(forall ((inner Bool)) (= @wa " ^
            "(@quantifiers_skolemize @qa 0))))) " ^
            "(step @p :rule refl :args (@w @wa " ^
            "(@quantifiers_skolemize @qa 0))))"
          fun check (e:env) bindings variables free
              (proof:''a C.constructed_graph_proof) =
            let
              val _ = require "private family allocation inventory changed"
                (sorted (List.map #1 bindings)=sorted inventory andalso
                 sorted (List.map #2 (!(#private_atoms e)))=sorted inventory)
              fun marker kind = case List.filter (fn (saved,_) =>
                    saved=kind) bindings of
                  [(_,node)] => node
                | _ => raise Fail ("non-unique private kind: " ^ kind)
              val expected = List.map marker dependencies
              val _ = require "private allocations reused an identity"
                (length (Lib.op_mk_set (fn a => fn b => a=b)
                   (List.map #2 bindings))=
                 length bindings)
              (* Source annotations retain the allocated lexical descriptor,
                 not the graph's kernel representative. Match only authentic
                 packet variables by the exact private marker identity. *)
              val atoms = List.map (fn kind =>
                case List.filter (fn (node,_) => node=marker kind)
                    variables of
                  [(_,lexical)] => lexical
                | _ => raise Fail
                    ("non-unique private descriptor: " ^ kind)) dependencies
              fun source (term:''a F.constructed_term) =
                let
                  (* Bound expanded nodes, not observation Work: source
                     queries also charge names and repeated expansion.
                     This test-only oracle uses a non-debit callback. *)
                  val remaining = ref maximum
                  fun observe (_:IntInf.int) = ()
                  val syntax = case #source_syntax term of
                      SOME syntax => syntax
                    | NONE => raise Fail "private witness lost source syntax"
                  fun walk syntax =
                    (require "private source oracle exceeds4096 nodes"
                       (!remaining>0);
                     remaining := !remaining-1;
                     case CS.view observe syntax of
                       CS.Atom atom => if Term.is_var atom then [atom]
                         else []
                     | CS.Variable _ => []
                     | CS.Apply (f,x) => walk f @ walk x
                     | CS.Abstract (_,body) => walk body)
                  val actual = Lib.op_mk_set
                    (fn a => fn b => Term.compare (a,b)=EQUAL) (walk syntax)
                  fun names atoms = "[" ^ String.concatWith ", "
                    (sorted (List.map (#1 o Term.dest_var) atoms)) ^ "]"
                in require
                  ("private source annotation changed allocated atoms: " ^
                   "actual=" ^ names actual ^ "; expected=" ^ names atoms)
                  (length actual=length atoms andalso
                   List.all (fn atom => List.exists (fn saved =>
                     Term.compare (atom,saved)=EQUAL) atoms) actual);
                   require "private source atom became a lexical dependency"
                     (null (CS.free_variables observe syntax)) end
              fun term (term:''a F.constructed_term) =
                (require "alias/binder/witness changed private dependencies"
                   (same_ids (free (#node term)) expected);
                 source term)
              val terms = case #commands proof of
                  [C.GraphAssume (_,assumption),
                   C.GraphStep {step={args=[C.GraphTerm a,C.GraphTerm b,
                     C.GraphTerm c],...},...}] => [assumption,a,b,c]
                | _ => raise Fail "private witness fixture changed shape"
            in List.app term terms end
        in List.app (fn route => test
          ("private dependency " ^ label ^ " / " ^ route_name route)
          (fn () => case route of
              Value => with_value text (fn e => fn current =>
                let val context = #context current
                in check e (List.map (fn binding =>
                    (#kind binding,PV.key context (#marker binding)))
                    (#private_bindings current))
                  (List.map (fn variable =>
                    (PV.key context (#node variable),#lexical variable))
                    (#variables current))
                  (List.map (PV.key context) o PV.free_variables context)
                  (#proof current) end)
            | _ => owned (fn e =>
                let val held = native_packet route e text
                in finally (fn () =>
                  (native_inventory e held;
                   check e (List.map (fn binding =>
                     (#kind binding,#marker binding))
                     (Packet.private_bindings held))
                     (List.map (fn variable =>
                       (#node variable,#lexical variable))
                       (Packet.variables held))
                     (fn node => case G.free_variable_nodes (#graph e) node of
                         SOME nodes => nodes
                       | NONE => raise Fail "unknown private dependencies")
                     (Packet.proof held))) (fn () => Packet.close held) end)))
          routes end
      fun single (name,expression,inventory,dependencies) =
        fixture (name,"(define @m () " ^ expression ^ ") ",
          inventory,dependencies,"Bool","(and (= @m @m) (= x x))")
      val opaque_kinds = List.filter (fn name =>
        name<>"@cpc.const.0" andalso name<>"@cpc.const.3" andalso
        name<>"@cpc.const.4") native_private_kinds
      val opaque = List.filter (fn (name,_) => List.exists
        (fn kind => name=kind) opaque_kinds) parameterized_fixtures
      val _ = test "exact opaque private dependency fixture inventory"
        (fn () => require "opaque private fixture inventory drift"
          (length opaque=16 andalso
           sorted (List.map #1 opaque)=sorted opaque_kinds))
      val _ = List.app (fn (name,args) => single
        (name,"(" ^ name ^ " " ^ args ^ ")",[name],[name])) opaque
      val _ = List.app (fn name => single (name,name,[name],[name]))
        ["@int_div_by_zero","@mod_by_zero","@div_by_zero"]
      val _ = List.app single
        [("BitVec sort","(_ BitVec 1)",["@cpc.BitVec"],["@cpc.BitVec"]),
         ("FloatingPoint sort","(_ FloatingPoint 3 5)",
          ["@cpc.FloatingPoint"],["@cpc.FloatingPoint"]),
         ("function sort","(-> (_ BitVec 1) (_ BitVec 1))",
          ["@cpc.BitVec","@cpc.->"],["@cpc.->"]),
         ("const discards sort operand","(@const 0 (_ BitVec 1))",
          ["@cpc.BitVec","@cpc.const.0"],["@cpc.const.0"])]
      val _ = List.app (fn name => List.app (fn source => single
        (name ^ (if source="" then " fresh" else " source-indexed"),
         "(" ^ name ^ " (_ BitVec 1)" ^ source ^ ")",
         ["@cpc.BitVec",name],[name])) [""," (fp #b0 #b000 #b0000)"])
        ["@fp.SIGN","@fp.EXPONENT","@fp.SIGNIFICAND","@fp.ZERO",
         "@fp.NAN","@fp.INF"]
      val _ = List.app (fn name => single
        (name,"(" ^ name ^ " (_ FloatingPoint 3 5) " ^
          "(_ FloatingPoint 3 5))",["@cpc.FloatingPoint",name],
          ["@cpc.FloatingPoint",name])) ["fp.max_total","fp.min_total"]
      (* Root definitions are referenced inside TWO enclosing binders,
         including a newly constructed witness, not just its root alias. *)
      val _ = fixture ("root @k const Bool witness",
        "(define @k () (@const 0 true)) (define @m () @k) ",
        ["@cpc.const.0"],["@cpc.const.0"],"Bool","(= @k x)")
      val _ = fixture ("root @z nullary Int witness",
        "(define @z () @int_div_by_zero) (define @m () @z) ",
        ["@int_div_by_zero"],["@int_div_by_zero"],"Int","(= @z x)")
    in () end

  (* A boundary unit test, not an artificial parser resource policy: keep
     the SAME original Work/context/caps and make one bounded debit that
     exceeds its actual remaining allowance. The :args wrapper must not
     replace the terminal primary with its ordinary parse_step diagnostic. *)
  fun argument_resource_failure () = test
    "terminal Work failure survives graph_step_argument :args" (fn () =>
      let
        fun run wrapped =
          let
            val terminal = ref false
            val retired = ref false
            val actual = failure (fn () => with_value
              "((step @p :rule refl :args (true)))"
              (fn e => fn current =>
                let
                  val context = #context current
                  val factory = B.values_with_policy
                    {context=context,graph= #graph e,scope= #scope e,
                     import_limit=cap,literal_limit=cap,binder_limit=cap}
                  val backend = #backend factory
                  fun parse _ =
                    (PV.spend context 1000000000
                     handle primary =>
                       (terminal := B.failure_requires_propagation backend;
                        retired := #retired (W.audit_policy (#work e));
                        raise primary))
                in finally (fn () => if wrapped then
                    C.graph_step_argument backend "@p" "refl" parse
                      (C.RawAtom "true")
                  else parse (C.RawAtom "true")) (#close factory) end))
          in require "resource fixture did not retire the original owner"
               (!terminal andalso !retired andalso Option.isSome actual);
             actual end
        val expected = run false
        val _ = require "resource fixture failed before its bounded debit"
          (expected=SOME ("SmtReplayInvocationWork","admit",
            "original cumulative work allowance exhausted"))
        val actual = run true
      in require "terminal :args exception was rewritten"
        (actual=expected) end)

  (* Check immediate source blocks, not the flattened HOL binder spine. *)
  fun quantifier_metadata () = List.app (fn (label,formula,expected) =>
    let
      val text = "((define @q () " ^ formula ^ ") (assume @a @q))"
      fun sizes (Old.BinderBlockProvenance ("forall",count,body)) =
            count::sizes body
        | sizes _ = []
      fun check e raw (proof:'a C.constructed_graph_proof) =
        let
          val _ = compare_commands raw (legacy e text) proof
          val term = hd (assumptions proof)
          val actual = List.map (fn (kind,count,_) =>
            (require "non-FORALL source block" (kind="forall");count))
            (#binder_blocks term)
          val provenance = CPC_SharedReplayPlan.occurrence_provenance
            (#occurrence term)
        in require "immediate source block metadata was flattened"
          (actual=expected andalso sizes provenance=expected) end
    in List.app (fn route => test
      (label ^ " immediate metadata / " ^ route_name route) (fn () =>
        case route of Value => with_value text (fn e => fn current =>
          check e (small_value e (#context current)) (#proof current))
        | _ => with_native route text (fn e => check e (small_graph e))))
      routes end)
    [("flat", "(forall ((x Bool) (y Bool)) (or x y))", [2]),
     ("nested", "(forall ((x Bool)) (forall ((y Bool)) (or x y)))", [1,1])]

  fun quantifier_boundaries () =
    let
      val flat = "(forall ((x Bool) (y Bool)) (or x y))"
      val nested = "(forall ((x Bool)) (forall ((y Bool)) (or x y)))"
      fun witnesses label quantified alias indices =
        let val operand = if alias then "@q" else quantified
            val text = "(" ^
              (if alias then "(define @q () " ^ quantified ^ ") " else "") ^
              "(step @p :rule refl :args (" ^ String.concatWith " "
                (List.map (fn index => "(@quantifiers_skolemize " ^
                  operand ^ " " ^ index ^ ")") indices) ^ ")))"
        in positive label text end
      val _ = List.app (fn alias =>
        (witnesses "flat FORALL witnesses retain both immediate binders"
           flat alias ["0","1"];
         witnesses "nested FORALL witness stops at immediate block"
           nested alias ["0"];
         witnesses "nested EXISTS boundary is preserved"
           "(forall ((x Bool)) (exists ((y Bool)) (= x y)))"
           alias ["0"])) [false,true]
      val alpha =
        "((define @first () (forall ((x Bool) (y Bool)) (or x y))) " ^
        "(define @second () (forall ((u Bool) (v Bool)) (or u v))) " ^
        "(step @p :rule refl :args " ^
        "((@quantifiers_skolemize @second 0) " ^
        "(@quantifiers_skolemize @first 0) " ^
        "(@quantifiers_skolemize @second 1))))"
      val _ = positive "alpha-equivalent blocks reuse canonical source" alpha
      (* The semantic bridge alone permits either alpha-renamed candidate.
         Inspect only the outer source SELECT binder to pin first-candidate
         canonicalization independently of Value's fresh oracle binders. *)
      fun canonical (proof:'a C.constructed_graph_proof) =
        let
          val remaining = ref 4096
          fun spend n =
            (remaining := !remaining-IntInf.toInt n;
             require "canonical source observation exceeds4096"
               (!remaining>=0))
          fun name (C.GraphTerm term) =
                let val source = valOf (#source_syntax term)
                    val (_,abstraction) = valOf (CS.dest_comb spend source)
                    val (variable,_) = valOf (CS.dest_abs spend abstraction)
                in #1 (Term.dest_var variable) end
            | name _ = raise Fail "canonical witness changed argument role"
          val names = case #commands proof of
              [C.GraphStep {step={args,...},...}] => List.map name args
            | _ => raise Fail "missing canonical witness step"
        in require "FORALL lookup replaced the first canonical source"
          (names=["x","x","y"]) end
      val _ = List.app (fn route => test
        ("first alpha-canonical source / " ^ route_name route) (fn () =>
          case route of Value => with_value alpha
            (fn _ => fn current => canonical (#proof current))
          | _ => with_native route alpha (fn _ => canonical))) routes
      (* Conflicts are legal until a witness requests a source boundary.
         Neither insertion order nor alias selection may erase ambiguity. *)
      val _ = List.app (fn (a,b) =>
        let val prefix = "((define @first () " ^ a ^ ") " ^
              "(define @second () " ^ b ^ ") "
        in positive "unused conflicting FORALL metadata remains legal"
             (prefix ^ "(assume @a (= @first @second)))");
           List.app (fn name => negative
             "alpha-equal conflicting FORALL metadata fails closed"
             (prefix ^ "(step @p :rule refl :args " ^
               "((@quantifiers_skolemize " ^ name ^ " 0))))"))
             ["@first","@second"] end) [(flat,nested),(nested,flat)]
    in quantifier_metadata () end

  fun regex_components () =
    let
      val a = "(str.to_re \"a\")"
      val b = "(str.to_re \"b\")"
      val c = "(str.to_re \"c\")"
      fun concat a b = "(re.++ " ^ a ^ " " ^ b ^ ")"
      val body = concat a b
      val star = "(re.* " ^ body ^ ")"
      val patterns =
        [("left associated concat", concat (concat a b) c),
         ("right associated concat", concat a (concat b c)),
         ("left direct-star expansion", concat (concat body star) body),
         ("right direct-star expansion", concat body (concat star body)),
         ("right alpha direct-star expansion",
          concat "task35_re_alpha_x"
            (concat "(re.* task35_re_alpha_y)" "task35_re_alpha_z")),
         ("left alpha direct-star expansion",
          concat (concat "task35_re_alpha_x" "(re.* task35_re_alpha_y)")
            "task35_re_alpha_z")]
      fun fixture regex = "((step @p :rule refl :args (" ^
        String.concatWith " " (List.tabulate (3,fn i =>
          "(@re_unfold_pos_component \"abc\" " ^ regex ^ " " ^
          Int.toString i ^ ")")) ^ ")))"
      fun coherent raw (proof:'a C.constructed_graph_proof) =
        let
          val args = case #commands proof of
              [C.GraphStep {step={args,...},...}] => args
            | _ => raise Fail "missing regex component step"
          fun choice (C.GraphTerm term) =
                let val normalized = boolSyntax.rhs
                      (Thm.concl (normalize (raw (#node term))))
                in case HolKernel.find_terms boolSyntax.is_select
                    normalized of
                    [selected] => selected
                  | _ => raise Fail "component lost its single choice" end
            | choice _ = raise Fail "component changed argument role"
          val choices = List.map choice args
        in require "missing regex projections" (length choices=3);
           List.app (fn selected => bridge (hd choices) selected)
             (tl choices) end
    in List.app (fn (label,regex) =>
      let val text = fixture regex
      in positive ("regex " ^ label) text;
         List.app (fn route => test
           ("coherent regex choices " ^ label ^ " / " ^ route_name route)
           (fn () => case route of Value => with_value text
             (fn e => fn current => coherent
               (small_value e (#context current)) (#proof current))
           | _ => with_native route text
               (fn e => coherent (small_graph e)))) routes;
         negative ("regex " ^ label ^ " exact upper bound")
           ("((step @p :rule refl :args ((@re_unfold_pos_component " ^
            "\"abc\" " ^ regex ^ " 3))))") end) patterns end

  (* Sort arguments are packet metadata, not counterfeit HOL variables.
     Matching controls compare their types and kernel-check object terms;
     negatives compare the complete native first-exception triple. *)
  fun set_sort_metadata () =
    let
      fun matching label text = List.app (fn route =>
        test (label ^ " / " ^ route_name route) (fn () =>
          let
            fun check e raw (proof:'a C.constructed_graph_proof) =
              let
                val old = case #commands (legacy e text) of
                    [Old.STEP step] => #args step
                  | _ => raise Fail "expected one native step"
                val args = case #commands proof of
                    [C.GraphStep {step,...}] => #args step
                  | _ => raise Fail "expected one graph step"
                fun flatten (C.GraphList entries) =
                      List.concat (List.map flatten entries)
                  | flatten argument = [argument]
                fun compare (located:Old.located_term,argument) =
                  case (#provenance located,argument) of
                    (Old.UnavailableProvenance "CPC Set sort metadata",
                     C.GraphSort ty) => require "Set metadata type changed"
                      (Type.compare (Term.type_of (#term located),ty)=EQUAL)
                  | (Old.UnavailableProvenance "CPC Set sort metadata",_) =>
                      raise Fail "Set metadata lost its packet role"
                  | (_,C.GraphTerm term) => bridge (#term located)
                      (raw (#node term))
                  | _ => raise Fail "object argument changed packet role"
              in ListPair.appEq compare
                (old,List.concat (List.map flatten args)) end
          in case route of
              Value => with_value text (fn e => fn current =>
                check e (small_value e (#context current)) (#proof current))
            | _ => with_native route text (fn e => check e (small_graph e))
          end)) routes
      fun fixtures rule =
        let
          val prefix = if rule="sets-member-emp" then "0 " else ""
          fun text args = "((step @p :rule " ^ rule ^ " :args (" ^
            prefix ^ args ^ ")))"
          val set = "(as set.empty (Set Int)) "
          val bad = set ^ "(Set Bool)"
        in
          matching (rule ^ " matching sort") (text (set ^ "(Set Int)"));
          matching (rule ^ " matching term marker") (text (set ^ set));
          matching (rule ^ " list-expanded matching sort")
            (text ("(@list " ^ set ^ ") (Set Int)"));
          matching (rule ^ " empty list preserves sort position")
            (text (set ^ "(@list) (Set Int)"));
          matching (rule ^ " list alias preserves sort position")
            ("((define @sets () (@list " ^ set ^ ")) " ^
             "(step @p :rule " ^ rule ^ " :args (" ^ prefix ^
             "@sets (Set Int))))");
          negative (rule ^ " sort in object position")
            (text ("(Set Int) " ^ set));
          negative (rule ^ " sort after metadata position")
            (text (set ^ set ^ "(Set Int)"));
          negative (rule ^ " sort inside object list")
            (text ("(@list (Set Int)) " ^ set));
          negative (rule ^ " sort inside metadata-position list")
            (text (set ^ "(@list (Set Int))"));
          negative (rule ^ " invalid sort metadata wrapper")
            (text (set ^ "(Set task35_missing_sort)"));
          negative (rule ^ " malformed sort metadata wrapper")
            (text (set ^ "(Set)"));
          negative (rule ^ " invalid sort follows flattened list")
            (text ("(@list " ^ set ^ ") (Set task35_missing_sort)"));
          negative (rule ^ " invalid sort precedes later object failure")
            (text (set ^ "(Set task35_missing_sort) task35_missing_arg"));
          negative (rule ^ " invalid sort precedes later syntax failure")
            ("((step @p :rule " ^ rule ^ " :args (" ^ prefix ^ set ^
             "(Set task35_missing_sort) (");
          negative (rule ^ " mismatched sort") (text bad);
          negative (rule ^ " mismatched term marker")
            (text (set ^ "(as set.empty (Set Bool))"));
          negative (rule ^ " list-expanded mismatched sort")
            (text ("(@list " ^ set ^ ") (Set Bool)"));
          negative (rule ^ " parse failure precedes metadata validation")
            (text (bad ^ " task35_missing_argument"));
          negative (rule ^ " metadata precedes later premise validation")
            ("((step @p :rule " ^ rule ^ " :args (" ^ prefix ^ bad ^
             ") :premises (@missing)))");
          negative (rule ^ " earlier premise validation precedes metadata")
            ("((step @p :rule " ^ rule ^ " :premises (@missing) :args (" ^
             prefix ^ bad ^ ")))");
          negative (rule ^ " conclusion precedes metadata validation")
            ("((step @p task35_missing_conclusion :rule " ^ rule ^
             " :args (" ^ prefix ^ bad ^ ")))")
        end
    in
      List.app fixtures
        ["sets-minus-self","sets-card-emp","sets-is-empty-elim",
         "sets-member-emp"];
      negative "sort in ordinary rule argument"
        "((step @p :rule refl :args ((Set Int))))";
      negative "nested argument lists are object syntax"
        "((step @p :rule refl :args ((@list (@list true)))))";
      negative "object-list type diagnostic remains native"
        "((step @p :rule refl :args ((@list (@var x (-> Int))))))";
      negative "ordinary argument precedes later premise failure"
        "((step @p :rule refl :args (task35_missing_arg) \
        \:premises (@missing)))";
      negative "ordinary conclusion precedes earlier premise failure"
        "((step @p task35_missing_conclusion :rule refl \
        \:premises (@missing) :args (task35_missing_arg)))";
      List.app (fn rule =>
        let val tail = if rule="resolution" then " false" else " 0"
        in
          negative (rule ^ " list is not an object operand")
            ("((step @p :rule " ^ rule ^ " :args ((@list true)" ^
             tail ^ "))) ");
          negative (rule ^ " list alias is not an object operand")
            ("((define @xs () (@list true)) (step @p :rule " ^ rule ^
             " :args (@xs" ^ tail ^ "))) ")
        end) ["cnf_and_pos","cnf_or_neg","resolution"];
      (* Native unparenthesized @list bookkeeping skips to the end of the
         definition and does not define an object/list alias. *)
      positive "opaque list bookkeeping is syntax-only"
        "((define @xs () @list (task35_missing_term)) \
        \(step @p true :rule refl :args (true)))";
      negative "opaque list bookkeeping is not an argument alias"
        "((define @xs () @list (true)) \
        \(step @p :rule refl :args (@xs)))";
      negative "opaque list bookkeeping is not a binder alias"
        "((define @xs () @list (true)) \
        \(step @p :rule refl :args ((forall (@list @xs) true)))))"
    end

  (* review-9f6e78c99: packet roles, proof-local freshness and variable
     aliases are independent invariants. Do not send GraphList through the
     ordinary positive helper: native structured lists are HOL wrappers,
     whereas ordinary lists flatten into separate native arguments. *)
  fun missing_invariants () =
    let
      fun packet label structured widths text = List.app (fn route =>
        test (label ^ " / " ^ route_name route) (fn () =>
          let
            fun check e raw (proof:'a C.constructed_graph_proof) =
              let
                val old = legacy e text
                val (a,b) = case (#commands old,#commands proof) of
                    ([Old.STEP a],[C.GraphStep {step=b,...}]) => (a,b)
                  | _ => raise Fail "expected one list-bearing step"
                val _ = require "list packet step header changed"
                  (#cvc_version old= #cvc_version proof andalso
                   #id a= #id b andalso #rule a= #rule b andalso
                   #premises a= #premises b)
                fun term (located:Old.located_term,argument) =
                  case argument of
                    C.GraphTerm value => bridge (#term located)
                      (raw (#node value))
                  | _ => raise Fail "expected an object argument"
                val _ = same_option (fn (x,y) =>
                  term (x,C.GraphTerm y)) (#conclusion a,#conclusion b)
                fun boundary (NONE,C.GraphTerm _) = ()
                  | boundary (SOME count,C.GraphList entries) =
                      require "list boundary/length changed"
                        (length entries=count)
                  | boundary _ = raise Fail "list argument role changed"
                val _ = ListPair.appEq boundary (widths,#args b)
                fun structured_arg (located:Old.located_term,argument) =
                  case argument of
                    C.GraphList entries =>
                      let val (elements,_) = listSyntax.dest_list
                            (#term located)
                          fun element (native,C.GraphTerm value) =
                                bridge native (raw (#node value))
                            | element _ = raise Fail "nested list element"
                      in ListPair.appEq element (elements,entries) end
                  | _ => term (located,argument)
                fun flatten (C.GraphList entries) = entries
                  | flatten argument = [argument]
              in if structured then
                   ListPair.appEq structured_arg (#args a,#args b)
                 else ListPair.appEq term
                   (#args a,List.concat (List.map flatten (#args b))) end
          in case route of
              Value => with_value text (fn e => fn current =>
                check e (small_value e (#context current)) (#proof current))
            | _ => with_native route text (fn e => check e (small_graph e))
          end)) routes
      val structured_rules =
        ["arith-mod-over-mod","arith-mod-over-mod-mult",
         "str-contains-refl"]
      val _ = List.app (fn rule =>
        let
          fun step args = "(step @p :rule " ^ rule ^ " :args (" ^
            args ^ "))"
        in
          negative (rule ^ " mixed inline structured list")
            ("(" ^ step "(@list 0 true)" ^ ")");
          negative (rule ^ " mixed structured list alias")
            ("((define @mixed () (@list true 0)) " ^ step "@mixed" ^ ")");
          negative (rule ^ " mixed list precedes later object failure")
            ("(" ^ step "(@list true 0) task35_missing_arg" ^ ")");
          negative (rule ^ " mixed list precedes later syntax failure")
            ("((step @p :rule " ^ rule ^ " :args ((@list true 0) (");
          negative (rule ^ " list element precedes later syntax failure")
            ("((step @p :rule " ^ rule ^
             " :args ((@list task35_missing_arg (");
          negative (rule ^ " list element precedes later object failure")
            ("(" ^ step "(@list task35_missing_arg task35_missing_arg2)" ^
             ")");
          negative (rule ^ " mixed alias precedes later syntax failure")
            ("((define @mixed () (@list true 0)) (step @p :rule " ^
             rule ^ " :args (@mixed (");
          packet (rule ^ " separate homogeneous/empty inline lists") true
            [SOME 2,NONE,SOME 0,SOME 1]
            ("(" ^ step "(@list 0 1) 2 (@list) (@list true)" ^ ")");
          packet (rule ^ " separate homogeneous/empty list aliases") true
            [SOME 2,NONE,SOME 0,SOME 1]
            ("((define @ints () (@list 0 1)) " ^
             "(define @empty () (@list)) " ^
             "(define @bools () (@list true)) " ^
             step "@ints 2 @empty @bools" ^ ")")
        end) structured_rules
      val _ = packet "ordinary heterogeneous inline lists still flatten"
        false [SOME 3,NONE,SOME 0,SOME 2]
        "((step @p :rule refl :args \
        \((@list true 0 #b1) false (@list) (@list 1 true))))"
      val _ = packet "ordinary heterogeneous list aliases still flatten"
        false [SOME 3,NONE,SOME 0,SOME 2]
        ("((define @mixed () (@list true 0 #b1)) " ^
         "(define @empty () (@list)) (define @tail () (@list 1 true)) " ^
         "(step @p :rule refl :args (@mixed false @empty @tail)))")

      val _ = positive "unused heterogeneous list definition is legal"
        "((define @mixed () (@list true 0)) (assume @a true))"
      val opaque = "(define @fresh () @list (true))"
      val definitions =
        [("term","(define @fresh () true)"),
         ("list","(define @fresh () (@list true))"),
         ("opaque",opaque),
         ("variable","(define @fresh () (@var \"x\" Bool))"),
         ("const","(declare-const @fresh Bool)"),
         ("fun","(declare-fun @fresh (Bool) Bool)")]
      val _ = List.app (fn (kind,command) =>
        (negative ("opaque name cannot become " ^ kind)
           ("(" ^ opaque ^ " " ^ command ^ ")");
         negative (kind ^ " name cannot become opaque")
           ("(" ^ command ^ " " ^ opaque ^ ")");
         (* Pin the native duplicate diagnostic independently of the broken
            body; otherwise equal body errors could conceal late checking. *)
         test (kind ^ " duplicate precedes malformed body / native")
           (fn () => owned (fn e =>
             let val expected = failure (fn () => ignore (legacy e
                       ("(" ^ command ^ " " ^ opaque ^ ")")))
                 val actual = failure (fn () => ignore (legacy e
                       ("(" ^ command ^ " (define @fresh (")))
             in require "native duplicate did not win first-error order"
               (Option.isSome expected andalso expected=actual) end));
         negative (kind ^ " duplicate precedes malformed body")
           ("(" ^ command ^ " (define @fresh ("))) definitions

      (* Freshness must win before even reading a malformed binder/body,
         including builtins and supplied source-dictionary entries. *)
      val _ = List.app (fn (name,message) =>
        let val text = "((define " ^ name ^ " ("
        in
          test (name ^ " freshness precedes malformed body / native")
            (fn () => owned (fn e => require
              "native freshness diagnostic changed"
              (failure (fn () => ignore (legacy e text))=
               SOME ("CPC_ProofParser","parse_define",message))));
          negative (name ^ " freshness precedes malformed body") text
        end)
        [("true","CPC definition may not shadow builtin symbol true"),
         ("task35_num","CPC definition may not redefine source symbol " ^
           "task35_num")]
      val list_failure =
        "((define @xs () (@list task35_missing_arg ("
      val _ = test "definition list element precedes later syntax / native"
        (fn () => owned (fn e =>
          let val expected = failure (fn () => ignore (legacy e
                "((define @xs () (@list task35_missing_arg)))"))
              val actual = failure (fn () => ignore (legacy e list_failure))
          in require "native list element did not win first-error order"
            (Option.isSome expected andalso expected=actual) end))
      val _ = negative "definition list element precedes later syntax"
        list_failure
      val _ = negative "nested definition-list operand precedes later syntax"
        "((define @xs () (@list (or task35_missing_arg ("
      val _ = positive "definition-list inline variable retains binder identity"
        ("((define @x () (@var \"x\" Bool)) " ^
         "(define @vars () (@list (@var \"x\" Bool))) " ^
         "(assume @a (forall @vars @x)))")
      val _ = List.app (fn (label,term) => positive
        ("streaming definition-list " ^ label)
        ("((define @xs () (@list " ^ term ^ ")) " ^
         "(assume @a true))"))
        [("higher-order application","(_ task35_array task35_num)"),
         ("indexed sort marker","(_ BitVec 3)"),
         ("qualified empty","(as seq.empty (Seq Bool))"),
         ("annotation","(! true :named list_tag)"),
         ("LET","(let ((p true)) p)"),
         ("sorted binder","(forall ((p Bool)) p)"),
         ("CPC binder","(forall (@list (@var \"p\" Bool)) true)")]
      val _ = negative "ordinary list subterm does not admit CPC @var"
        "((define @xs () (@list (or (@var \"x\" Bool) false))))"
      val _ = negative "CPC binder does not declare a new dictionary entry"
        "((define @xs () (@list (forall (@list (@var \"x\" Bool)) x))))"
      val _ = positive "CPC binder preserves a same-named proof constant"
        ("((define x () true) (define @xs () (@list " ^
         "(forall (@list (@var \"x\" Bool)) x))) (assume @a true))")
      val _ = positive "CPC binder preserves proof constant semantics"
        ("((define x () true) (assume @a " ^
         "(forall (@list (@var \"x\" Bool)) x)))")

      (* review-30352f126: recursive CPC operands and ordinary subterms
         have different binder grammars; quotation selects semantic heads. *)
      val _ = positive "recursive CPC binder elaborates annotated variable"
        ("((define @x () (@var \"x\" Bool)) " ^
         "(define @xs () (@list " ^
         "(forall (@list (! @x :named bound_x)) @x))) " ^
         "(assume @a true))")
      val _ = negative "ordinary nested binder does not admit CPC @var"
        ("((define @xs () (@list " ^
         "(or (forall (@list (@var \"x\" Bool)) true) false))) " ^
         "(assume @a true))")
      val _ = negative "empty ordinary binder keeps ordinary body grammar"
        ("((define @xs () (@list " ^
         "(or (forall () (@var \"x\" Bool)) false))) (assume @a true))")
      val _ = positive "annotated lexical LET binder retains source variable"
        ("((define @xs () (@list (let ((q true)) " ^
         "(forall (@list (! q :named b)) q)))) (assume @a true))")
      val _ = negative "inline LET is not a native variable binder operand"
        ("((define @x () (@var \"x\" Bool)) " ^
         "(define @xs () (@list (or " ^
         "(forall (@list (let ((z @x)) z)) @x) false))) " ^
         "(assume @a true))")
      val recursive_failure =
        "((define @xs () (@list (forall (@list (or task35_missing_arg ("
      val _ = test "recursive binder operand precedes later syntax / native"
        (fn () => owned (fn e => require
          "native recursive operand first-error diagnostic changed"
          (failure (fn () => ignore (legacy e recursive_failure))=
           SOME ("SmtLib_Parser","t_with_args_unknown_symbol",
             "failed to parse 'task35_missing_arg' (with indices [] and " ^
             "0 argument(s)): unknown symbol (no dictionary entry)"))))
      val _ = negative "recursive binder operand precedes later syntax"
        recursive_failure
      val _ = List.app (fn kind =>
        let fun text binders body = "((define @xs () (@list (" ^ kind ^
              " (@list " ^ binders ^ ") " ^ body ^ "))) (assume @a true))"
        in
          negative (kind ^ " recursive invalid binder native diagnostic")
            (text "(! true :named bad)" "true");
          negative (kind ^ " recursive invalid binder follows body error")
            (text "(! true :named bad)" "task35_missing_arg");
          negative (kind ^ " recursive invalid binder follows later operand")
            (text "(! true :named bad) task35_missing_arg" "true");
          negative (kind ^ " recursive invalid binder follows later syntax")
            ("((define @xs () (@list (" ^ kind ^
             " (@list (! true :named bad) (");
          negative (kind ^ " recursive valid suffix preserves body type error")
            (text "true (@var \"x\" Bool)" "0");
          negative (kind ^ " recursive invalid suffix precedes body type error")
            (text "(@var \"x\" Bool) true" "0")
        end) ["forall","exists","lambda"]
      val _ = positive "quoted CPC @var in a definition list"
        "((define @xs () (@list (|@var| \"x\" Bool))) (assume @a true))"

      val variable = "(define @x () (@var \"x\" Bool)) "
      val _ = List.app (fn (label,definitions,body) => positive label
        ("(" ^ variable ^ definitions ^ "(assume @a " ^ body ^ "))"))
        [("variable binder alias chain",
          "(define @y () @x) (define @z () @y) ",
          "(forall (@list @z) (or @x @y @z))"),
         ("quoted variable binder alias",
          "(define |binder alias| () @x) ",
          "(forall (@list |binder alias|) @x)"),
         ("annotated variable binder alias",
          "(define @y () (! @x :named alias_tag)) ",
          "(forall (@list @y) @x)"),
         ("LET-normalized variable binder alias",
          "(define @y () (let ((copy @x)) copy)) ",
          "(forall (@list @y) @x)"),
         ("variable aliases in a recorded binder list",
          "(define @y () @x) (define @z () (@var \"z\" Bool)) " ^
          "(define @vars () (@list @y @z)) ",
          "(forall @vars (or @x @y @z))"),
         ("variable binder alias captures a compound definition",
          "(define @y () @x) (define @body () (or @x false)) ",
          "(forall (@list @y) @body)")]
      val _ = differential "variable alias under an enclosing lexical LET"
        ("(" ^ variable ^ "(define @y () @x) " ^
         "(assume @a (let ((x true)) " ^
         "(forall (@list @y) (or @x @y)))))")
      val _ = positive "sorted lexical binder shadows variable alias type"
        ("(" ^ variable ^ "(define @y () @x) " ^
         "(assume @a (forall ((@y Int)) " ^
         "(forall (@list @y) (= @y 0)))))")
      val _ = positive "sorted lexical binder is an inline binder reference"
        "((assume @a (forall ((q Bool)) (forall (@list q) q))))"
      val _ = positive "CPC binder keeps a differently typed lexical namesake"
        ("((define @i () (@var \"x\" Int)) " ^
         "(define @vars () (@list @i)) " ^
         "(assume @a (forall ((x Bool)) (forall @vars x))))")
      val _ = positive "lexical LET name shadows retained binder alias"
        ("(" ^ variable ^ "(define @y () @x) " ^
         "(assume @a (let ((@y true)) (forall (@list @y) true))))")
      (* Nested binders use the shared native binder parser, including its
         exact non-variable diagnostic, rather than top-level term builders. *)
      val _ = List.app (fn (label,definitions,binder) => negative label
        ("(" ^ variable ^ definitions ^
         "(assume @a (= (forall " ^ binder ^ " true) true)))"))
        [("non-variable term alias is not a binder",
          "(define @bad () (not @x)) ","(@list @bad)"),
         ("non-variable annotated alias is not a binder",
          "(define @bad () (! true :named bad_tag)) ","(@list @bad)")]

      (* Exercise the copied frontend tables without inventing a packet or
         a Value factory. Both public native frontend constructors suffice
         to catch a child mutating its parent's opaque-name set/list table. *)
      val _ = List.app (fn route => test
        ("opaque child-context isolation / " ^ route_name route) (fn () =>
          owned (fn e =>
            let
              val description = {solver="cvc5",version=version,
                policy=F.CPC,reserved_names=[]}
              fun tokens text = P.make_cpc_proof_tokenizer_from_input
                (input text)
              val parent = case route of
                  Finite => F.create_session (finite_options e)
                    description (tokens "")
                | _ => F.create_session_with_policy (policy_options e)
                    description (tokens "")
              val _ = (#define_opaque parent) "@parent"
              fun child opened =
                let val F.ScopedSession {session,close,...} = opened
                in finally (fn () =>
                  let
                    val inherited = failure (fn () =>
                      (#define_opaque session) "@parent")
                    val expected = SOME ("CPC_ProofParser","parse_define",
                      "duplicate CPC declaration or definition of symbol " ^
                      "@parent")
                    val _ = require "child lost inherited opaque name"
                      (inherited=expected)
                    val _ = (#define_opaque session) "@child"
                    val value = (#parse_from session) (tokens "true")
                    val _ = (#define_list session) ("@child_list",[value])
                    val namespace = (#namespace parent) ()
                  in require "child declarations leaked into parent"
                    (not (HOLset.member (#proof_terms namespace,
                       (#symbol_key parent) "@child")) andalso
                     not (Option.isSome
                       ((#lookup_list parent) "@child_list"))) end) close end
              val _ = child ((#open_bindings parent) [])
              (* A sibling must also be able to introduce the same names. *)
              val _ = child ((#open_binders parent)
                [("local","local",Type.bool)])
              val _ = (#define_opaque parent) "@child"
              val _ = (#define_list parent) ("@child_list",[])
            in () end))) [Finite,Policy]
    in () end

  (* review-dab9ea1bf: an explicit private-marker binder captures its
     allocation identity, including retained aliases, not its spelling. *)
  fun private_binder_aliases () =
    let
      val prefix = "((define @k () (@const 3 true)) "
      fun fixture definitions body = prefix ^ definitions ^
        "(assume @a " ^ body ^ "))"
      val compound = fixture
        "(define @alias () @k) (define @body () (or @k false)) "
        "(forall (@list @alias) @body)"
      val _ = List.app (fn (label,definitions,body) => positive label
        (fixture definitions body))
        [("private marker is an explicit FORALL binder","",
          "(forall (@list @k) @k)"),
         ("private binder alias chain",
          "(define @alias () @k) (define @copy () @alias) ",
          "(forall (@list @copy) (or @k @alias @copy))"),
         ("private binder named list alias",
          "(define @alias () @k) (define @vars () (@list @alias)) ",
          "(forall @vars @k)"),
         ("nested distinct private binders",
          "(define @j () (@const 4 true)) ",
          "(forall (@list @k) (exists (@list @j) (or @k @j)))"),
         ("nested repeated private binder shadows by identity","",
          "(forall (@list @k) (and @k (exists (@list @k) @k)))"),
         ("private marker is an explicit EXISTS binder","",
          "(exists (@list @k) @k)"),
         ("private marker is an explicit LAMBDA binder","",
          "(= (lambda (@list @k) @k) (lambda ((x Bool)) x))")]
      val _ = positive "private binder captures compound aliased body"
        compound
      val child_first =
        "((assume @a (forall ((x Bool)) (@const 3 true))) " ^
        "(assume @b (exists ((y Bool)) (@const 3 true))) " ^
        "(assume @c (let ((z true)) (@const 3 true))) " ^
        "(assume @d (@const 3 true)))"
      val _ = positive "stable private allocation first appears in child"
        child_first
      val _ = List.app (fn route => test
        ("child-first private identity across sibling/LET/root / " ^
          route_name route) (fn () =>
          let
            fun check free (proof:''a C.constructed_graph_proof) =
              let val terms = assumptions proof
                  val dependencies = List.map (free o #node) terms
              in require "stable private allocation split across scopes"
                (length terms=4 andalso case dependencies of
                   [a as [_],b,c,d] => a=b andalso b=c andalso c=d
                 | _ => false) end
          in case route of
              Value => with_value child_first (fn _ => fn current =>
                let val context = #context current
                in require "stable private allocation inventory grew"
                     (length (#private_bindings current)=1);
                   check (List.map (PV.key context) o
                     PV.free_variables context) (#proof current) end)
            | _ => with_native route child_first (fn e => check
                (fn node => case G.free_variable_nodes (#graph e) node of
                   SOME nodes => nodes
                 | NONE => raise Fail "unknown child-first dependencies"))
          end)) routes
      (* Test-only source reconstruction, charged by expanded node count
         BEFORE visiting children. No source observation grants authority. *)
      fun source_term syntax =
        let val remaining = ref maximum
            fun observe (_:IntInf.int) = ()
            fun walk source =
              (require "private binder source oracle exceeds4096"
                 (!remaining>0);
               remaining := !remaining-1;
               case CS.view observe source of
                   CS.Variable variable => variable
                 | CS.Atom atom => (bounded atom;atom)
                 | CS.Apply (f,x) => Term.mk_comb (walk f,walk x)
                 | CS.Abstract (binder,body) =>
                     Term.mk_abs (binder,walk body))
        in walk syntax end
      (* review-30352f126: a repeated private constructor must resolve to
         the explicit binder, not allocate a free marker in its child scope.
         The small shape oracle checks operand identity before any bridge. *)
      datatype private_shape = BoundEquality
        | Quantified of private_shape
        | Paired of private_shape * private_shape
      fun identities same application abstraction shape root =
        let
          fun operands node =
            let val (operator,right) = application node
                val (_,left) = application operator
            in (left,right) end
          fun walk environment BoundEquality node =
                let val binder = hd environment
                    val (left,right) = operands node
                in require "private equality operands lost bound identity"
                  (same (left,binder) andalso same (right,binder) andalso
                   same (left,right)) end
            | walk environment (Quantified body_shape) node =
                let val (_,closure) = application node
                    val (binder,body) = abstraction closure
                in walk (binder::environment) body_shape body end
            | walk environment (Paired (a,b)) node =
                let val (left,right) = operands node
                in walk environment a left;walk environment b right end
        in walk [] shape root end
      val equality = "(= @k (@const 3 true))"
      val repeated =
        [("direct", "(forall (@list @k) " ^ equality ^ ")",
          Quantified BoundEquality),
         ("nested", "(forall (@list @k) (and " ^ equality ^
          " (exists (@list @k) " ^ equality ^ ")))",
          Quantified (Paired (BoundEquality,Quantified BoundEquality))),
         ("nested constructor binder",
          "(forall (@list @k) (exists (@list (@const 3 true)) " ^
          equality ^ "))",Quantified (Quantified BoundEquality)),
         ("nested annotated binder",
          "(forall (@list @k) (exists (@list (! @k :named inner)) " ^
          equality ^ "))",Quantified (Quantified BoundEquality)),
         ("sibling", "(and (forall (@list @k) " ^ equality ^
          ") (exists (@list @k) " ^ equality ^ "))",
          Paired (Quantified BoundEquality,Quantified BoundEquality))]
      val _ = List.app (fn (label,body,shape) => List.app (fn route => test
        (label ^ " private reoccurrence identity/FV/bridges / " ^
          route_name route) (fn () =>
          let
            val text = fixture "" body
            fun native_identity term =
              (bounded term;
               identities (fn (a,b) => Term.compare (a,b)=EQUAL)
                 Term.dest_comb Term.dest_abs shape term;
               require "private reoccurrence has native/source free variables"
                 (null (Term.free_vars term)))
            fun check e raw (proof:'a C.constructed_graph_proof) =
              let
                val old = legacy e text
                val native = case #commands old of
                    [Old.ASSUME ("@a",term)] => #term term
                  | _ => raise Fail "expected one native private assumption"
                val term = hd (assumptions proof)
                val source = source_term (valOf (#source_syntax term))
                val actual = raw (#node term)
              in native_identity native;native_identity source;
                 native_identity actual;
                 bridge native actual;bridge source actual end
          in case route of
              Value => with_value text (fn e => fn current =>
                let
                  val context = #context current
                  val root = #node (hd (assumptions (#proof current)))
                  fun application node = case PV.view context node of
                      PV.Application pair => pair
                    | _ => raise Fail "expected private Value application"
                  fun abstraction node = case PV.view context node of
                      PV.Abstraction {binder,body,...} => (binder,body)
                    | _ => raise Fail "expected private Value binder"
                  val _ = identities (fn (a,b) =>
                    PV.key context a=PV.key context b)
                    application abstraction shape root
                  val _ = require "private Value FV is not exactly empty"
                    (null (PV.free_variables context root))
                in check e (small_value e context) (#proof current) end)
            | _ => with_native route text (fn e => fn proof =>
                let
                  val graph = #graph e
                  val root = #node (hd (assumptions proof))
                  fun application node = case G.view graph node of
                      G.Application pair => pair
                    | _ => raise Fail "expected private graph application"
                  fun abstraction node = case G.view graph node of
                      G.AdmittedBinder {binder,body,...} => (binder,body)
                    | _ => raise Fail "expected private graph binder"
                  val _ = identities (op =) application abstraction
                    shape root
                  val _ = require "private graph FV is not exactly empty"
                    (case G.free_variable_nodes graph root of
                       SOME [] => true | _ => false)
                in check e (small_graph e) proof end)
          end)) routes) repeated
      val _ = List.app (fn route => test
        ("explicit private binder source/semantic bridge / " ^
          route_name route) (fn () =>
          let
            fun check raw (proof:'a C.constructed_graph_proof) =
              let val term = hd (assumptions proof)
                  val syntax = valOf (#source_syntax term)
                  val source = source_term syntax
              in require "bound private marker remained free in source"
                   (null (Term.free_vars source));
                 bridge ``!x:bool. x \/ F`` source;
                 bridge source (raw (#node term)) end
          in case route of
              Value => with_value compound (fn e => fn current =>
                check (small_value e (#context current)) (#proof current))
            | _ => with_native route compound
                (fn e => check (small_graph e)) end)) routes
      val _ = test "explicit private source binder preserves lexical namesake"
        (fn () =>
          let
            val spent = ref (0:IntInf.int)
            fun observe amount =
              (spent := !spent+amount;
               require "private namesake source observation exceeds budget"
                 (!spent<=1000000))
            val x = Term.mk_var ("task35_private_binder",Type.bool)
            val y = Term.mk_var ("task35_private_bound",Type.bool)
            val disjunction = CS.native (#1 (Term.dest_comb
              (#1 (Term.dest_comb (boolSyntax.mk_disj (x,x))))))
            val body = CS.application
              (CS.application (disjunction,CS.private_atom x),CS.variable x)
            val syntax = CS.private_abstraction observe (x,body)
            val (binder,bound_body) = valOf (CS.dest_abs observe syntax)
            val (operator,right) = valOf (CS.dest_comb observe bound_body)
            val (_,left) = valOf (CS.dest_comb observe operator)
            fun lexical expected source = case CS.view observe source of
                CS.Variable actual => Term.compare (expected,actual)=EQUAL
              | _ => false
          in require "explicit binding captured its lexical namesake"
               (Term.compare (binder,x)<>EQUAL andalso
                lexical binder left andalso lexical x right andalso
                (case CS.free_variables observe syntax of
                   [free] => Term.compare (free,x)=EQUAL | _ => false));
             bridge (Term.mk_abs (y,boolSyntax.mk_disj (y,x)))
               (source_term syntax) end)
    in () end

  fun private_source_sharing () =
    test "private source binder construction stays local/shared" (fn () =>
      let
        val spent = ref (0:IntInf.int)
        fun observe n = spent := !spent+n
        val variables = List.tabulate (80,fn i =>
          Term.mk_var ("task35_vacuous_" ^ Int.toString i,Type.bool))
        val body = List.foldl (fn (variable,body) =>
          CS.private_abstraction observe (variable,body))
          (CS.native boolSyntax.T) variables
        val _ = require "private source construction scanned binder bodies"
          (!spent<=80)
        val ordinary = List.foldl CS.abstraction
          (CS.native boolSyntax.T) variables
        val baseline = ref (0:IntInf.int)
        fun ordinary_observe n = baseline := !baseline+n
        val _ = CS.strip_abs ordinary_observe ordinary
        val _ = CS.free_variables ordinary_observe ordinary
        val (binders,tail) = CS.strip_abs observe body
        val free = CS.free_variables observe body
      in require "lazy private source lost a binder or vacuous body"
           (length binders=80 andalso
            CS.is_constant observe boolSyntax.T tail andalso null free);
         require ("private lowering exceeds ordinary source-query work: " ^
             IntInf.toString (!spent) ^ " vs " ^ IntInf.toString (!baseline))
           (!spent<=2 * !baseline+10000)
      end)

  fun run () =
    let
      val _ = failures := [] val _ = bridges := 0
      val _ = missing_invariants ()
      val _ = private_binder_aliases ()
      val _ = private_source_sharing ()
      val _ = set_sort_metadata ()
      (* Verbatim flattened-index fixtures from Unittest, made observable
         by using each definition as a refl argument, not merely parsing it. *)
      val indexed =
        [("regex power","(re.^ 2 (str.to_re \"a\"))"),
         ("regex loop","(re.loop 1 2 (str.to_re \"a\"))"),
         ("character","(char 97)"),("divisible","(divisible 3 6)"),
         ("repeat","(repeat 2 #b10)"),
         ("rotate left","(rotate_left 1 #b01)"),
         ("rotate right","(rotate_right 1 #b01)"),
         ("CPC word literal","(@bv 3 4)"),
         ("CPC bit selection","(@bit 1 #b11)"),
         ("CPC Boolean vector","(@from_bools true false true)"),
         ("integer to word","(int_to_bv 4 3)"),
         ("private bit selection","(@bit_of 0 #b1)"),
         ("signed extension","(sign_extend 1 #b1)"),
         ("unsigned extension","(zero_extend 1 #b1)"),
         ("to_fp","(to_fp 3 5 roundNearestTiesToEven 1/1)"),
         ("to_fp_bv","(to_fp_bv 3 5 #b00110000)"),
         ("to_fp_unsigned",
          "(to_fp_unsigned 3 5 roundNearestTiesToEven #b0011)"),
         ("fp.to_sbv","(fp.to_sbv 4 roundTowardZero (fp #b1 #b100 #b1000))"),
         ("fp.to_ubv","(fp.to_ubv 4 roundTowardZero (fp #b0 #b100 #b1000))")]
      val _ = List.app (fn (label,term) => positive
        ("deindexed " ^ label)
        ("((define @t () " ^ term ^ ") (step @p (= @t @t) " ^
         ":rule refl :args (@t)))")) indexed
      val parameterized =
        [("parameterized purify uses the graph operand ID",
          "((assume @a (@purify true)))"),
         ("parameterized quantifier witness uses the immediate FORALL block",
          "((assume @a (@quantifiers_skolemize " ^
          "(forall ((x Bool)) x) 0)))"),
         ("parameterized regex components share a concrete choice",
          "((assume @a (= (@re_unfold_pos_component \"ab\" " ^
          "(re.++ (str.to_re \"a\") (str.to_re \"b\")) 0) \"a\")))")]
      val _ = parameterized_registry ()
      val _ = quantifier_boundaries ()
      val _ = regex_components ()
      val _ = List.app (fn (label,text) =>
        (test (label ^ " / legacy control") (fn () =>
           owned (fn e => ignore (legacy e text)));
         positive label text)) parameterized
      val _ = List.app (fn (label,text) => positive label text)
        [("optional conclusion and definition",
          "((define @t () false) (assume @a @t) " ^
          "(step @b :rule refl :args (@t)))"),
         ("definition normalizes LET before later literal-index use",
          "((define n () (let ((i 2)) i)) " ^
          "(assume @a (= (repeat n #b1) #b11)))"),
         ("definition normalizes simultaneous LET index aliases",
          "((define n () (let ((i 2) (j 3)) i)) " ^
          "(assume @a (= (repeat n #b1) #b11)))"),
         ("CPC empty/unary Boolean aggregates remain supported",
          "((assume @a (= (and) true)) (assume @b (= (or) false)) " ^
          "(assume @c (= (and true) (or true))))"),
         ("CPC lambda binder-list alias",
          "((define @x () (@var \"x\" Bool)) " ^
          "(assume @a (= (lambda (@list @x) @x) " ^
          "(lambda ((x Bool)) x))))"),
         ("ascribed sequence empty",
          "((define @t () (= (seq.len (as seq.empty (Seq Int))) 0)) " ^
          "(assume @a @t))"),
         ("compound alias beneath its lexical binder",
          "((define @x () (@var \"x\" Bool)) " ^
          "(define @t () (or @x false)) " ^
          "(assume @a (forall (@list @x) @t)))"),
         ("compound definition follows lexical LET bindings",
          "((define @x () (@var \"x\" Bool)) " ^
          "(define @t () (or @x false)) " ^
          "(assume @a (let ((x true)) @t)))"),
         ("capture relocates unchanged closed subtrees",
          "((define @x () (@var \"x\" Bool)) " ^
          "(define @t () (forall ((y Bool)) (or @x (not false)))) " ^
          "(assume @a (forall (@list @x) @t)))"),
         ("capture relocates unchanged literal operands",
          "((define @x () (@var \"x\" Bool)) " ^
          "(define @t () (forall ((y Bool)) (or @x (= 3 4)))) " ^
          "(assume @a (forall (@list @x) @t)))"),
         ("compound definition captures below a nested alias binder",
          "((define @x () (@var \"x\" Bool)) " ^
          "(define @t () (forall ((y Bool)) (or @x y))) " ^
          "(assume @a (forall (@list @x) @t)))"),
         ("quoted definition and simultaneous LET shadow",
          "((define |alias name| () true) (assume @a " ^
          "(let ((x |alias name|)) (let ((x 7) (copy x)) copy))))"),
         ("source disjunction stays one leaf",
          "((define a () task35_compound) (assume @a (or a (not a) a)))"),
         ("semantic flattened divisible LET index",
          "((assume @a (let ((n 2)) (divisible n 6))))"),
         ("singleton bare premise",
          "((assume @a false) " ^
          "(step @b :rule true_elim :premises @a))"),
         ("ordered repeated premises and step-pop",
          "((assume-push @a true) " ^
          "(step-pop @b true :rule refl :premises (@a @a) :args (true)))")]
      val pair = App ("or",[Atom,Atom])
      val triple = App ("or",[pair,Atom,pair])
      val _ = located "definition plus LET aggregate boundaries"
        "((define a () (or true false)) (define b () (or a false a)) \
        \(assume @a b) (assume @b (let ((a true) (copy a)) \
        \(or copy a copy))))"
        [triple,App ("or",[pair,Atom,pair])]
      val _ = located "nested conjunction order/multiplicity"
        "((define a () (and true false)) \
        \(assume @a (and a false a)))"
        [App ("and",[App ("and",[Atom,Atom]),Atom,
                     App ("and",[Atom,Atom])])]
      val _ = located "compound Source is not flattened by aliases"
        "((define a () task35_compound) (assume @a (or a a false)))"
        [App ("or",[Atom,Atom,Atom])]
      val _ = annotations ()
      val _ = source_occurrences ()
      val _ = binder_scopes ()
      val _ = positive "bounded shared lexical capture" (captured_text 3)
      val _ = List.app captured_dag [40,80]
      val _ = positive "bounded branching shared capture" (branching_text 2)
      val _ = List.app branching_dag [20,40,80]
      val _ = packet_lifetime ()
      val _ = private_scopes ()
      val _ = private_source_syntax ()
      val _ = private_capture ()
      val _ = private_quantifier_capture ()
      val _ = private_dependencies ()
      val _ = argument_resource_failure ()
      val _ = test "actual emitted datatype tester fixtures" testers
      (* All registry entries must reject missing/extra arguments through
         the native authoritative callback, not a graph-only catch-all. *)
      val _ = List.app (fn (name,args) =>
        (negative ("native parameterized missing arguments " ^ name)
           ("((step @p :rule refl :args ((" ^ name ^ "))))");
         negative ("native parameterized extra argument " ^ name)
           ("((step @p :rule refl :args ((" ^ name ^ " " ^ args ^
            " true))))"))) parameterized_fixtures
      (* Preserve the actual legacy first HOL_ERR triple, rather than
         merely checking that malformed input failed somewhere. *)
      val _ = List.app (fn (label,term) => negative label
        ("((assume @a " ^ term ^ "))"))
        [("lexical flattened repeat index",
          "(let ((n 2)) (= (repeat n #b1) #b11))"),
         ("lexical CPC word index","(let ((n 2)) (@bv n 4))"),
         ("lexical private constant index",
          "(let ((i 3)) (= (@const i true) true))"),
         ("private constant index type","(@const true true)"),
         ("private constant Num index","(@const task35_num true)"),
         ("String parameterized sort","(@strings_stoi_result 0)"),
         ("RegLan parameterized sort",
          "(@strings_num_occur_re task35_string task35_string)"),
         ("Int parameterized sort","(@strings_itos_result task35_string)"),
         ("mixed Seq parameterized sort",
          "(@strings_deq_diff task35_sequence task35_bool_sequence)"),
         ("Array coherence parameterized sort",
          "(@array_deq_diff task35_array task35_bool_array)"),
         ("Set range parameterized sort",
          "(@sets_deq_diff task35_array task35_array)"),
         ("nested Bag parameterized sort","(@tables_group_part task35_bag)"),
         ("Bag-map domain parameterized sort",
          "(@bags_map_sum task35_bad_map task35_bag 0)"),
         ("Bag-map image parameterized sort",
          "(@bags_map_sum task35_map task35_bag task35_num)"),
         ("function-range parameterized sort",
          "(@bags_map_preimage_injective task35_map task35_bag task35_num)"),
         ("quantifier negative index",
          "(@quantifiers_skolemize (forall ((x Bool)) x) (- 1))"),
         ("quantifier upper bound",
          "(@quantifiers_skolemize (forall ((x Bool)) x) 1)"),
         ("quantifier huge index",
          "(@quantifiers_skolemize (forall ((x Bool)) x) " ^
          "999999999999999999999999999999999999999999999999999999)"),
         ("quantifier flat upper bound",
          "(@quantifiers_skolemize " ^
          "(forall ((x Bool) (y Bool)) (or x y)) 2)"),
         ("quantifier nested alias immediate bound",
          "(let ((q (forall ((x Bool)) (forall ((y Bool)) (or x y))))) " ^
          "(@quantifiers_skolemize q 1))"),
         ("quantifier nested immediate bound",
          "(@quantifiers_skolemize " ^
          "(forall ((x Bool)) (forall ((y Bool)) (or x y))) 1)"),
         ("quantifier index type",
          "(@quantifiers_skolemize (forall ((x Bool)) x) true)"),
         ("quantifier non-concrete Int index",
          "(forall ((i Int)) " ^
          "(@quantifiers_skolemize (forall ((x Bool)) x) i))"),
         ("quantifier rejects EXISTS operand",
          "(@quantifiers_skolemize (exists ((x Bool)) x) 0)"),
         ("quantifier rejects non-FORALL operand",
          "(@quantifiers_skolemize true 0)"),
         ("regex negative component",
          "(@re_unfold_pos_component \"\" re.none (- 1))"),
         ("regex huge component",
          "(@re_unfold_pos_component \"\" re.none " ^
          "999999999999999999999999999999999999999999999999999999)"),
         ("regex component index type",
          "(@re_unfold_pos_component \"\" re.none true)"),
         ("regex component source type",
          "(@re_unfold_pos_component 0 re.none 0)"),
         ("regex component regex type",
          "(@re_unfold_pos_component \"\" \"\" 0)"),
         ("negative flattened repeat index","(repeat (- 1) #b1)"),
         ("non-numeral flattened repeat index","(repeat true #b1)"),
         ("missing flattened repeat argument","(repeat 2)"),
         ("flattened FP index count","(to_fp_bv 3)"),
         ("Boolean argument type","(not 0)"),
         ("equality endpoint types","(= true 0)"),
         ("array index type",
          "(select ((as const (Array Int Bool)) true) false)"),
         ("unknown binder sort","(forall ((x task35_missing_sort)) x)"),
         ("malformed ascribed sort","(as seq.empty (Seq Int Bool))")]
      val _ = List.app (fn (label,term) => classified label
        ("((assume @a " ^ term ^ "))"))
        [("compound flattened index retains native failure class",
          "(repeat (+ 1 1) #b1)"),
         ("LET index is source syntax, not its evaluated semantic ID",
          "(= (repeat (let ((n 2)) n) #b1) #b11)"),
         ("LET private index retains its native failure class",
          "(= (@bv (let ((n 2)) n) 4) #b0010)"),
         ("private constant index also preserves original source syntax",
          "(= (@const (let ((n 2)) n) true) true)")]
      val _ = negative "normalized negative alias keeps native exception"
        ("((define n () (let ((i 2)) (- i))) " ^
         "(assume @a (= (repeat n #b1) #b11)))")
      val _ = classified "normalized nonliteral alias remains malformed"
        ("((define n () (let ((i 2)) (+ i 1))) " ^
         "(assume @a (= (repeat n #b1) #b11)))")
      val _ = finally (fn () =>
        (index_override := SOME 8;
         positive "bounded normalized index alias"
           ("((define n () (let ((i 2)) i)) " ^
            "(assume @a (= (repeat n #b1) #b11)))");
         classified "finite index cap does not replace native syntax failure"
           "((assume @a (= (repeat (+ 1 1) #b1) #b11)))"))
        (fn () => index_override := NONE)
      val _ = List.app (fn (label,term) => differential label
        ("((assume @a " ^ term ^ "))"))
        [("supported annotation missing attribute value","(! true :named)"),
         ("supported annotation numeric keyword","(! true :1 bad)"),
         ("supported annotation non-keyword tail","(! true bad)")]
      (* Unsupported-rule scanning does validate raw certificate syntax;
         these are pinned malformed controls, not new ordinary refusals. *)
      val _ = List.app (fn (label,term) => negative label
        ("((step @p " ^ term ^ " :rule str-to-lower-concat))"))
        [("raw annotation invalid keyword","(! x :1 bad)"),
         ("raw annotation non-keyword tail","(! x bad)"),
         ("raw equality arity","(=)"),
         ("raw numeral binder","(forall ((1 Int)) x)")]
      val _ = List.app shared_dag [70,80]
      val _ = require "no checked CPC semantic comparisons ran" (!bridges>60)
      val _ = print ("TASK35_KERNEL_BRIDGES " ^ Int.toString (!bridges) ^
        "\n")
      val _ = require ("Task35 failures: " ^
        String.concatWith ", " (List.rev (!failures))) (null (!failures))
    in () end
end
