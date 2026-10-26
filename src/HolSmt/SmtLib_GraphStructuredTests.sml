(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphStructuredTests =
struct
  open HolKernel boolLib testutils
  structure B = SmtLib_GraphBackend
  structure C = B.C
  structure G = SmtReplayGraph
  structure P = SmtLib_Parser
  structure R = SmtLib_GraphTheories
  structure PV = SmtLib_GraphParserValue
  structure RP = SmtReplayResourcePolicy
  structure F = SmtLib_GraphFrontend

  val maximum : int = 4096
  val policy_maximum = RP.AtMost (IntInf.fromInt maximum)
  val limits = {template_limit=4096,index_limit=256,
                operand_limit=256,token_limit=256}
  val policy = {template_limit=RP.AtMost 4096,index_limit=RP.AtMost 256,
                operand_limit=RP.AtMost 256,token_limit=RP.AtMost 256}
  fun ensure text yes = if yes then () else raise Fail text
  fun tokens text =
    let val position = ref 0 in
      P.make_cpc_proof_tokenizer_from_input (fn () =>
        if !position = String.size text then NONE
        else let val c = String.sub (text,!position)
             in position := !position+1; SOME c end)
    end
  val cfg : P.parser_cfg =
    {mk_let_bindings=P.smtlib_mk_let_bindings,mk_let=P.smtlib_mk_let,
     mk_bound_var=Term.mk_var,lookup_binder_list=fn _ => NONE,
     record_binder_block=fn _ => (),symbol_key=P.proof_symbol_text,
     type_symbol_key=Lib.I,parse_choice=false,parse_lambda=true}
  fun required NONE = raise Fail "unhandled test ascription"
    | required (SOME value) = value
  fun options backend frame : 'a P.construction_cfg =
    {backend=backend,frame=frame,symbol_key=P.proof_symbol_text,
     type_symbol_key=Lib.I,index_limit=256,parse_choice=false,
     parse_lambda=true,lookup_binder_list=fn _ => NONE,
     binder_reference=fn _ => fn _ => raise Fail "binder alias",
     record_binder_block=fn _ => (),
     ascribed_symbol=fn frame => fn description =>
       required (R.ascribed backend frame limits description),
     coerce_arguments=R.coerce_arguments backend}
  fun policy_options backend frame : 'a P.policy_construction_cfg =
    {backend=backend,frame=frame,symbol_key=P.proof_symbol_text,
     type_symbol_key=Lib.I,index_limit=RP.AtMost 256,parse_choice=false,
     parse_lambda=true,lookup_binder_list=fn _ => NONE,
     binder_reference=fn _ => fn _ => raise Fail "binder alias",
     record_binder_block=fn _ => (),
     ascribed_symbol=fn frame => fn description =>
       required (R.ascribed_with_policy backend frame policy description),
     coerce_arguments=R.coerce_arguments backend}
  fun string_literal token = case P.proof_string_token token of
      SOME text => SmtLib_String_Literal.mk_string_term text
    | NONE => SmtLib_Theories.decline token "not a string literal"
  fun native_literal token = SmtLib_Theories.K_zero_zero
    (string_literal token) token
  fun literals backend (sorts,dictionary) = (sorts,
    Library.extend_dict (("_",fn frame => fn token => fn indices =>
      fn arguments => B.literal backend frame
        (native_literal token indices arguments)),dictionary))
  fun logic solver = if solver="cvc5" then "HO_ALL" else "ALL"
  fun ordinary solver text =
    let val (sorts,dictionary) =
          SmtLib_Logics.parsedicts_of_solver_logic solver (logic solver)
    in P.parse_term_with_cfg cfg (tokens text)
      (sorts,Library.extend_dict (("_",native_literal),dictionary)) end
  fun parsed backend exact solver text =
    if exact then P.parse_term_with_policy
      (policy_options backend (B.root backend)) (tokens text)
      (literals backend (#dictionaries
        (R.select_with_policy_no_override backend policy
          {logic=logic solver,solver=SOME solver})))
    else P.parse_term_with_backend
      (options backend (B.root backend)) (tokens text)
      (literals backend (#dictionaries (R.select backend limits
        {logic=logic solver,solver=SOME solver})))

  fun with_graph exact action =
    let val graph=G.new () val scope=G.root_scope graph
        val backend=if exact then B.graphs_with_policy
          {graph=graph,scope=scope,import_limit=policy_maximum,
           literal_limit=policy_maximum,binder_limit=policy_maximum}
          else B.graphs {graph=graph,scope=scope,import_limit=maximum,
                        literal_limit=maximum,binder_limit=maximum}
        val result=Exn.capture (fn () => action graph backend) ()
        val _=G.close_scope graph scope
    in Exn.release result end
  fun with_values action =
    let val graph=G.new () val scope=G.root_scope graph
        val context=PV.create {graph=graph,scope=scope,
          validate=fn () => (),spend=fn _ => (),retire=fn () => ()}
        val held=B.values_with_policy {context=context,graph=graph,
          scope=scope,import_limit=policy_maximum,
          literal_limit=policy_maximum,binder_limit=policy_maximum}
        val result=Exn.capture (fn () =>
          action graph context (#backend held)) ()
        val _=(#close held) () val _=G.close_scope graph scope
    in Exn.release result end

  (* Test-only interpretation, AFTER an unfolded binder-inclusive bound.
     Never use this helper on the shared-DAG resource controls. *)
  fun small_graph graph node =
    (ensure "expanded graph test fixture"
       (Option.isSome
         (G.unfolded_nodes graph G.BinderInclusiveNodes maximum node));
     G.representative graph node)

  (* proof_view also handles authentic retained graph syntax. In particular
     Abstraction is not B.Opaque, nor a reason to skip a value comparison.
     Count first, then reconstruct with an identity-keyed binder environment;
     printed names must never identify distinct bound occurrences. *)
  fun small_value context value =
    let
      val root=PV.proof_term context value
      val left=ref maximum
      fun bound term =
        (left := !left-1; ensure "expanded value test fixture" (!left>=0);
         case PV.proof_view context term of
           PV.ProofVariable _ => ()
         | PV.ProofConstant _ => ()
         | PV.ProofApplication (f,x) => (bound f;bound x)
         | PV.ProofAbstraction {binder,body,...} =>
             (bound binder;bound body)
         | PV.ProofOpaque => raise Fail "opaque value test fixture")
      val _=bound root
      fun lookup key [] = NONE
        | lookup key ((held,term)::rest) =
            if key=held then SOME term else lookup key rest
      fun walk environment term =
        case PV.proof_view context term of
          PV.ProofVariable (_,lexical) =>
            (case lookup (PV.proof_key context term) environment of
               SOME bound => bound | NONE => lexical)
        | PV.ProofConstant atom => atom
        | PV.ProofApplication (f,x) =>
            Term.mk_comb (walk environment f,walk environment x)
        | PV.ProofAbstraction {binder,body,...} =>
            let val variable=Term.genvar (PV.proof_type_of context binder)
            in Term.mk_abs (variable,walk
              ((PV.proof_key context binder,variable)::environment) body)
            end
        | PV.ProofOpaque => raise Fail "opaque value test fixture"
    in walk [] root end

  (* Normalize BOTH sides using beta/LET plumbing and the two closed set
     literal definitions (native Bool constant arrays may use EMPTY/UNIV).
     No EVAL, blast, extensionality or semantic search hides a mismatch. *)
  fun normalize term = Conv.QCONV
    (DEPTH_CONV BETA_CONV THENC
     simpLib.SIMP_CONV pureSimps.pure_ss [boolTheory.LET_THM] THENC
     DEPTH_CONV BETA_CONV THENC
     REWRITE_CONV [pred_setTheory.UNIV_DEF,pred_setTheory.EMPTY_DEF]) term
  fun bridge original constructed =
    let
      val _=ensure "comparison fixture bound"
        (Option.isSome (SmtReplayImport.bounded_raw_size maximum original)
         andalso Option.isSome
           (SmtReplayImport.bounded_raw_size maximum constructed))
      val lhs=normalize original val rhs=normalize constructed
      val equality=Thm.ALPHA (boolSyntax.rhs (Thm.concl lhs))
        (boolSyntax.rhs (Thm.concl rhs)) handle error =>
          (print ("STRUCTURED_BRIDGE_LEFT "^
             Hol_pp.term_to_string (boolSyntax.rhs (Thm.concl lhs))^"\n"^
             "STRUCTURED_BRIDGE_RIGHT "^
             Hol_pp.term_to_string (boolSyntax.rhs (Thm.concl rhs))^"\n");
           raise error)
      val theorem=Thm.TRANS lhs (Thm.TRANS equality (Thm.SYM rhs))
      val _=ensure "structured builder changed types/Hyp"
        (null (Thm.hyp theorem) andalso
         Type.compare (Term.type_of original,Term.type_of constructed)=EQUAL)
      val _=ensure "comparison endpoints changed"
        (Term.aconv (Thm.concl theorem)
          (boolSyntax.mk_eq (original,constructed)))
    in Library.check_oracle_tags "GraphStructuredTests" "bridge" theorem end

  (* Public frontend sessions supplement the direct parser tests below.
     All fixtures are closed: no serializer Mapping/source declarations or
     external solver process is needed. *)
  fun description solver =
    {solver=solver,version=if solver="Z3" then "4.12.2" else "1.3.4",
     policy=if solver="Z3" then F.Z3 else F.CPC,reserved_names=[]}
  fun frontend_options graph solver : F.options =
    {graph=graph,scope=G.root_scope graph,logic=logic solver,sources=[],
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=maximum,literal_limit=maximum,binder_limit=maximum,
     recipe_limits=limits,special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  fun frontend_policy_options graph solver : 'a F.constructed_policy_options =
    {graph=graph,scope=G.root_scope graph,logic=logic solver,sources=[],
     sorts=Redblackmap.mkDict String.compare,binder_lists=[],
     import_limit=policy_maximum,literal_limit=policy_maximum,
     binder_limit=policy_maximum,recipe_limits=policy,
     special=fn _ => fn _ => NONE,
     ascribed=fn _ => fn _ => fn _ => NONE}
  fun graph_session graph exact solver =
    let val session=if exact then F.create_session_with_policy
          (frontend_policy_options graph solver)
            (description solver) (tokens "")
          else F.create_session (frontend_options graph solver)
            (description solver) (tokens "")
        val _ = (#add_literal_parser session) string_literal
    in session end
  fun frontend_graph graph exact solver text =
    #node ((#parse_from (graph_session graph exact solver)) (tokens text))
  fun value_session graph context backend solver =
    let
      (* Public backend-parametric session API, with the genuine factory's
         backend/context. No forged Mapping factory or declaration table. *)
      val session=F.create_policy_session_for_backend
        (frontend_policy_options graph solver) backend
        {identity=PV.key context,same_identity=op =,
         guard_private=PV.usable context,
         guard_observation=fn check => PV.protect context check,
         private_scope=fn frame => valOf
           (B.frame_lexical_scope backend frame)} []
        (fn {root,dictionary,variables,source_types,retain_descriptor,
             declaration_key} => (dictionary,variables))
        (description solver) (tokens "")
      val _ = (#add_literal_parser session) string_literal
    in session end
  fun frontend_value graph context backend solver text =
    #node ((#parse_from (value_session graph context backend solver))
      (tokens text))

  fun positive solver text =
    let val original=ordinary solver text in
      List.app (fn exact =>
        (with_graph exact (fn graph => fn backend => bridge original
           (small_graph graph (parsed backend exact solver text)));
         with_values (fn _ => fn context => fn backend => bridge original
           (small_value context (parsed backend exact solver text)))))
        [false,true]
    end
  fun session_positive solver text =
    let val original=ordinary solver text in
      List.app (fn exact => with_graph exact (fn graph => fn _ =>
        bridge original
          (small_graph graph (frontend_graph graph exact solver text))))
        [false,true];
      with_values (fn graph => fn context => fn backend => bridge original
        (small_value context
          (frontend_value graph context backend solver text)))
    end
  fun alias_positive solver source text =
    let
      val definition=ordinary solver source
      val (sorts,dictionary)=
        SmtLib_Logics.parsedicts_of_solver_logic solver (logic solver)
      fun alias token indices arguments =
        if null indices then Term.list_mk_comb (definition,arguments)
        else SmtLib_Theories.decline token "source value takes no indices"
      val dictionary=List.foldl Library.extend_dict dictionary
        [("structured_alias",alias),("structured_alias2",alias),
         ("_",native_literal)]
      val original=P.parse_term_with_cfg cfg (tokens text) (sorts,dictionary)
      fun parse session =
        let
          val value=(#parse_from session) (tokens source)
          val _=(#define session) ("structured_alias",value)
          val alias=(#parse_from session) (tokens "structured_alias")
          val _=(#define session) ("structured_alias2",alias)
        in #node ((#parse_from session) (tokens text)) end
      val _=List.app (fn exact => with_graph exact (fn graph => fn _ =>
        bridge original (small_graph graph
          (parse (graph_session graph exact solver))))) [false,true]
    in with_values (fn graph => fn context => fn backend =>
      bridge original (small_value context
        (parse (value_session graph context backend solver)))) end

  fun failure action = (ignore (action ());NONE)
    handle Feedback.HOL_ERR e => SOME
      (Feedback.top_structure_of e,Feedback.top_function_of e,
       Feedback.message_of e)
    | exn => SOME (General.exnName exn,"",General.exnMessage exn)
  fun negative solver text =
    let val expected=failure (fn () => ordinary solver text)
        (* Isolate each refusal: a value failure may retire its context. *)
        val outcomes=List.map (fn exact => with_graph exact
          (fn _ => fn backend => failure (fn () =>
            parsed backend exact solver text))) [false,true] @
          List.map (fn exact => with_values
            (fn _ => fn _ => fn backend => failure (fn () =>
              parsed backend exact solver text))) [false,true]
        fun describe NONE = "ACCEPTED"
          | describe (SOME (origin,where_,message)) =
              origin^"."^where_^": "^message
        val _=if List.all (fn actual => actual=expected) outcomes then ()
          else print ("\nordinary="^describe expected^"\n"^
            String.concat (List.map
              (fn actual => "constructed="^describe actual^"\n") outcomes))
    in ensure ("malformed classification: "^solver^" "^text)
      (Option.isSome expected andalso
       List.all (fn actual => actual=expected) outcomes) end

  (* Let the native strip_abs/name convention decide acceptance. In
     particular, duplicate lexical names are not an a priori refusal. *)
  fun differential solver text =
    case failure (fn () => ordinary solver text) of
        NONE => positive solver text
      | SOME _ => negative solver text

  (* The same admitted lexical body, including intentional binder capture,
     represented without relying on a kernel's printed lambda names. *)
  fun binder_representations binders body =
    let
      val raw=Term.list_mk_abs (binders,body)
      val hole=Term.genvar (Term.type_of body)
    in
      [("native",C.native raw),
       ("abstraction",List.foldr C.abstraction (C.native body) binders),
       ("template/native",C.from_template
         {template=raw,holes=[],operands=[]}),
       ("template/body",C.from_template
         {template=Term.list_mk_abs (binders,hole),holes=[hole],
          operands=[C.native body]})]
    end

  (* Term.strip_abs uses simultaneous naming on some kernels. The contract
     here is REPEATED public dest_abs, just like native comprehension. *)
  fun opened_native term =
    if Term.is_abs term then
      let val (binder,body)=Term.dest_abs term
          val (binders,body)=opened_native body
      in (binder::binders,body) end
    else ([],term)

  fun binder_invariants () =
    let
      val x=Term.mk_var ("task33_x",Type.bool)
      val xi=Term.mk_var ("task33_x",intSyntax.int_ty)
      val y=Term.mk_var ("task33_y",Type.bool)
      val prime=Term.mk_var ("task33_x'",Type.bool)
      val same=boolSyntax.mk_eq (xi,xi)
      val cases=[([x],same),([x],xi),([x],boolSyntax.T),([x],x),
        ([x,y],same),([x,x],x),([x,xi],same),([x,x],same),
        ([x,prime],boolSyntax.mk_conj (x,prime)),
        ([x,prime],boolSyntax.mk_conj (x,same)),
        ([x,prime],same),
        ([x,y],boolSyntax.mk_conj (x,y)),
        ([x],boolSyntax.mk_eq
          (Term.mk_abs (prime,x),Term.mk_abs (prime,prime)))]
      fun check (binders,body) =
        let
          val raw=Term.list_mk_abs (binders,body)
          val (expected,tail)=opened_native raw
          fun representation (label,source) =
            let
              val spent=ref (0:IntInf.int)
              fun observe n=(ensure "negative syntax debit" (n>=0);
                             spent := !spent+n)
              val (actual,rest)=C.strip_abs observe source
              val _=ensure (label^": public binder opening convention")
                (length actual=length expected andalso
                 ListPair.allEq (Lib.uncurry Term.aconv) (actual,expected))
              val _=ensure (label^": stored source variable names/order")
                (ListPair.allEq (Lib.uncurry Term.aconv)
                  (C.all_variables observe [source],Term.all_varsl [raw]))
              val _=ensure (label^": opened body variable names/order")
                (ListPair.allEq (Lib.uncurry Term.aconv)
                  (C.all_variables observe [rest],Term.all_varsl [tail]))
              val _=ensure (label^": abstraction/body types")
                (Type.compare (C.type_of source,Term.type_of raw)=EQUAL
                 andalso Type.compare
                   (C.type_of rest,Term.type_of tail)=EQUAL)
              val _=List.app (fn constant => ensure
                (label^": opened constant body")
                (C.is_constant observe constant rest =
                 (Term.is_const tail andalso Term.same_const tail constant)))
                [boolSyntax.T,boolSyntax.F]
            in ensure (label^": uncharged binder observation") (!spent>0)
            end
        in List.app representation (binder_representations binders body) end

      (* Qualified-head replay substitutes fresh, distinct typed holes, not
         lexical bodies (whose intentional capture is tested above). Keep
         the native oracle tiny BEFORE calling subst: even its conservative
         template-size times operand-size expansion bound is at most 512. *)
      val h=Term.genvar Type.bool
      val k=Term.genvar Type.bool
      val hi=Term.genvar intSyntax.int_ty
      val hf=Term.genvar (Type.--> (Type.bool,Type.bool))
      val yi=Term.mk_var ("task33_y",intSyntax.int_ty)
      fun abs bs body=Term.list_mk_abs (bs,body)
      fun plain term=([],term)
      val substitutions=
        [("same-type capture",abs [x] h,[(h,plain x)]),
         ("different-type namesake",abs [x] h,[(h,plain same)]),
         ("occupied fresh name",abs [x] h,
           [(h,plain (boolSyntax.mk_conj (x,prime)))]),
         ("retained template free name",abs [x]
           (boolSyntax.mk_conj (prime,h)),[(h,plain x)]),
         ("nested collisions",abs [x,prime] h,
           [(h,plain (boolSyntax.mk_conj (x,prime)))]),
         ("duplicate binders",abs [x,x] h,[(h,plain x)]),
         ("mixed-type binders",abs [x,xi] h,
           [(h,plain (boolSyntax.mk_conj (x,same)))]),
         ("bound and introduced occurrence",abs [x]
           (boolSyntax.mk_conj (x,h)),[(h,plain x)]),
         ("outer rename collides with inner binder",abs [x,prime]
           (boolSyntax.mk_conj (x,h)),[(h,plain x)]),
         ("unchanged nested binders",abs [x,prime]
           (boolSyntax.mk_conj (x,h)),[(h,plain y)]),
         ("operand bound names only",abs [x] hf,[(hf,([x],x))]),
         ("operand bound name does not block freshening",abs [x] hf,
           [(hf,([prime],x))]),
         ("operand free and bound occurrences",abs [x] hf,
           [(hf,([prime],boolSyntax.mk_conj (x,prime)))]),
         ("unused colliding hole",abs [x] y,[(h,plain x)]),
         ("used and unused holes",abs [x] h,
           [(h,plain y),(k,plain x)]),
         ("unused operand bound names",abs [x] h,
           [(h,plain x),(hf,([prime],prime))]),
         ("non-Boolean hole",abs [x]
           (boolSyntax.mk_eq (hi,hi)),[(hi,plain xi)]),
         ("different-type noncollision",abs [x]
           (boolSyntax.mk_eq (hi,xi)),[(hi,plain yi)]),
         ("repeated occurrences",boolSyntax.mk_conj (y,
           boolSyntax.mk_conj (h,y)),
           [(h,plain (boolSyntax.mk_conj (x,prime)))]),
         ("simultaneous occurrence order",boolSyntax.mk_conj (k,
           boolSyntax.mk_conj (h,k)),[(h,plain x),(k,plain y)]),
         ("true hole",h,[(h,plain boolSyntax.T)]),
         ("false hole",h,[(h,plain boolSyntax.F)]),
         ("unused hole constant",boolSyntax.T,[(h,plain boolSyntax.F)]),
         ("constant opened body",abs [x] h,[(h,plain boolSyntax.T)]),
         ("constant application is not constant",boolSyntax.mk_neg h,
           [(h,plain boolSyntax.T)]),
         ("constant abstraction is not constant",abs [x] h,
           [(h,plain boolSyntax.F)])]
      fun bounded term =
        case SmtReplayImport.bounded_raw_size 64 term of
            SOME size => size
          | NONE => raise Fail "substitution invariant fixture bound"
      fun variables_equal (left,right) =
        length left=length right andalso
        ListPair.allEq (Lib.uncurry Term.aconv) (left,right)
      fun binder_free term =
        if Term.is_abs term then false
        else if Term.is_comb term then
          let val (f,a)=Term.dest_comb term
          in binder_free f andalso binder_free a end
        else true
      fun substitution (name,template,bindings) =
        let
          val holes=List.map #1 bindings
          val bodies=List.map #2 bindings
          val operands=List.map (fn (bs,b) => abs bs b) bodies
          val template_size=bounded template
          val operand_size=List.foldl
            (fn (term,n) => bounded term+n) 0 operands
          val _=ensure (name^": native substitution expansion bound")
            (template_size*(1+operand_size)<=512)
          val _=ensure (name^": qualified holes are fresh and distinct")
            (List.all Term.is_var holes andalso
             length (Lib.op_mk_set Term.aconv holes)=length holes andalso
             not (List.exists (fn hole => List.exists
               (fn variable => Term.aconv hole variable)
               (Term.all_varsl operands)) holes))
          val raw=Term.subst (ListPair.mapEq
            (fn (hole,operand) => {redex=hole,residue=operand})
            (holes,operands)) template
          val _=ensure (name^": substituted fixture bound")
            (Option.isSome (SmtReplayImport.bounded_raw_size 512 raw))
          fun representation index =
            let
              val sources=List.map (fn (bs,b) => #2 (List.nth
                (binder_representations bs b,index))) bodies
              val label=name^"/"^Int.toString index
              val spent=ref (0:IntInf.int)
              fun observe n=(ensure (label^": negative syntax debit")
                (n>=0);spent := !spent+n)
              val source=C.from_substitution observe
                {template=template,holes=holes,operands=sources}
              fun compare suffix native syntax =
                let
                  val label=label^suffix
                  val (expected,tail)=opened_native native
                  val (actual,rest)=C.strip_abs observe syntax
                  val _=ensure (label^": stored binder names/all-vars order")
                    (variables_equal (C.all_variables observe [syntax],
                      Term.all_varsl [native]))
                  val _=ensure (label^": repeated public binder opening")
                    (variables_equal (actual,expected))
                  val _=ensure (label^": opened all-vars occurrence order")
                    (variables_equal (C.all_variables observe [rest],
                      Term.all_varsl [tail]))
                  val _=ensure (label^": multi-root occurrence order")
                    (variables_equal
                      (C.all_variables observe [rest,syntax,rest],
                       Term.all_varsl [tail,native,tail]))
                  (* There is no public free-vars query. On binder-free
                     opened tails all-vars IS free-vars, including order;
                     the wrappers below also exercise private free/bound
                     tagging when the operands retain inner binders. *)
                  val _=if binder_free tail then
                    ensure (label^": opened free-vars occurrence order")
                      (variables_equal (C.all_variables observe [rest],
                        Term.free_varsl [tail]))
                    else ()
                  val _=ensure (label^": substitution/opening types")
                    (Type.compare (C.type_of syntax,
                       Term.type_of native)=EQUAL andalso
                     Type.compare (C.type_of rest,Term.type_of tail)=EQUAL)
                  fun constant_shape (term,value) constant =
                    ensure (label^": exact constant shape")
                      (C.is_constant observe constant value =
                       (Term.is_const term andalso
                        Term.same_const term constant))
                  val _=List.app (fn constant =>
                    (constant_shape (native,syntax) constant;
                     constant_shape (tail,rest) constant))
                    [boolSyntax.T,boolSyntax.F]
                in () end
              val _=compare "" raw source
              val _=List.app (fn variable => compare
                ("/capture-probe-"^ #1 (Term.dest_var variable))
                (Term.mk_abs (variable,raw))
                (C.abstraction (variable,source))) [x,prime]
            in ensure (label^": uncharged substitution observation")
                 (!spent>0) end
        in List.app representation [0,1,2,3] end
    in List.app check cases; List.app substitution substitutions end

  (* Admit tiny raw native callbacks before publishing their source shape.
     In particular, no substitution may silently freshen the value binder
     before the descriptor comparison. Run every representation through all
     four parser routes; accepted outcomes need a clean checked bridge. *)
  fun raw_comprehensions () =
    let
      val x=Term.mk_var ("task33_x",Type.bool)
      val xi=Term.mk_var ("task33_x",intSyntax.int_ty)
      val y=Term.mk_var ("task33_y",Type.bool)
      val prime=Term.mk_var ("task33_x'",Type.bool)
      val same=boolSyntax.mk_eq (xi,xi)
      val cases=
        [(([x],boolSyntax.T),([x],xi)),
         (([x],boolSyntax.T),([x],same)),
         (([x,x],boolSyntax.T),([x,x],xi)),
         (([x],x),([x],x)),
         (([x,xi],same),([x,xi],xi)),
         (([x,prime],boolSyntax.mk_conj (x,prime)),([x,prime],x)),
         (([x,prime],boolSyntax.mk_conj (x,same)),([x,prime],xi)),
         (([x],x),([y],y))]
      val text="(set.comprehension structured_raw_p structured_raw_v)"
      (* Like the small opaque-constructor oracle, measure the retained
         native term with a hard visitor. Recording an opening does not
         replace the original opaque IDs in the result. This oracle is
         local to these prebounded raw callbacks, never shared-DAG tests. *)
      fun raw_graph graph node =
        let val raw=G.representative graph node
        in ensure "raw comprehension output bound"
             (Option.isSome
               (SmtReplayImport.bounded_raw_size maximum raw));
           raw
        end
      fun raw_value context value =
        let
          val root=PV.proof_term context value
          val left=ref maximum
          fun opaque term =
            case PV.proof_graph_reference context term of
                SOME {graph,node,...} => G.representative graph node
              | NONE => raise Fail "raw callback lacks retained backing"
          fun bound term =
            case PV.proof_view context term of
                PV.ProofOpaque =>
                  (case SmtReplayImport.bounded_raw_size (!left)
                          (opaque term) of
                       SOME size => left := !left-size
                     | NONE => raise Fail "raw callback output bound")
              | view =>
                  (left := !left-1;
                   ensure "raw value output bound" (!left>=0);
                   case view of
                       PV.ProofApplication (f,x) => (bound f;bound x)
                     | PV.ProofAbstraction {binder,body,...} =>
                         (bound binder;bound body)
                     | _ => ())
          val _=bound root
          fun lookup key [] = NONE
            | lookup key ((held,term)::rest) =
                if key=held then SOME term else lookup key rest
          fun walk environment term =
            case PV.proof_view context term of
                PV.ProofVariable (_,lexical) =>
                  (case lookup (PV.proof_key context term) environment of
                       SOME bound => bound | NONE => lexical)
              | PV.ProofConstant atom => atom
              | PV.ProofApplication (f,x) =>
                  Term.mk_comb (walk environment f,walk environment x)
              | PV.ProofAbstraction {binder,body,...} =>
                  let val variable=Term.genvar
                        (PV.proof_type_of context binder)
                  in Term.mk_abs (variable,walk
                    ((PV.proof_key context binder,variable)::environment)
                    body) end
              | PV.ProofOpaque => opaque term
        in walk [] root end
      fun check ((pb,pbody),(vb,vbody)) =
        let
          val p=Term.list_mk_abs (pb,pbody)
          val v=Term.list_mk_abs (vb,vbody)
          val _=List.app (fn term => ensure "raw callback admission bound"
            (Option.isSome (SmtReplayImport.bounded_raw_size maximum term)))
            [p,v]
          val (sorts,dictionary)=SmtLib_Logics.parsedicts_of_solver_logic
            "cvc5" (logic "cvc5")
          val dictionary=List.foldl Library.extend_dict dictionary
            [("structured_raw_p",SmtLib_Theories.K_zero_zero p),
             ("structured_raw_v",SmtLib_Theories.K_zero_zero v),
             ("_",native_literal)]
          val expected=Exn.capture (fn () => P.parse_term_with_cfg cfg
            (tokens text) (sorts,dictionary)) ()
          fun representation ((label,ps),(_,vs)) =
            let
              fun parse backend exact observe_source =
                let
                  val frame=B.root backend
                  val (sorts,dictionary)= #dictionaries
                    (if exact then R.select_with_policy_no_override
                       backend policy
                       {logic=logic "cvc5",solver=SOME "cvc5"}
                     else R.select backend limits
                       {logic=logic "cvc5",solver=SOME "cvc5"})
                  fun callback (term,source) frame token indices arguments =
                    let
                      val raw=SmtLib_Theories.K_zero_zero term
                        token indices arguments
                      val value=B.source backend frame raw
                      (* B.source retains native lambdas opaquely. Record
                         this already bounded fixture's opening explicitly;
                         no output or shared operand is opened here. *)
                      val _=observe_source value
                      val _=B.note_constructor_source backend source
                    in value end
                  val dictionary=List.foldl Library.extend_dict dictionary
                    [("structured_raw_p",callback (p,ps)),
                     ("structured_raw_v",callback (v,vs))]
                  val dictionaries=literals backend (sorts,dictionary)
                in if exact then P.parse_term_with_policy
                    (policy_options backend frame) (tokens text) dictionaries
                  else P.parse_term_with_backend
                    (options backend frame) (tokens text) dictionaries end
              fun compare project action = case expected of
                  Exn.Res original => bridge original (project (action ()))
                | Exn.Exn error => ensure
                    (label^": raw comprehension diagnostic/acceptance")
                    (failure action=failure (fn () => raise error))
            in List.app (fn exact =>
              (with_graph exact (fn graph => fn backend =>
                 compare (raw_graph graph) (fn () => parse backend exact
                   (fn node => ignore (G.record_opened_view graph
                     (G.root_scope graph) maximum node))));
               with_values (fn _ => fn context => fn backend =>
                 compare (raw_value context)
                   (fn () => parse backend exact (fn _ => ())))))
              [false,true] end
        in List.app representation (ListPair.zip
          (binder_representations pb pbody,binder_representations vb vbody))
        end
    in List.app check cases end

  fun app name args = "("^name^" "^String.concatWith " " args^")"
  fun unary names x = List.map (fn name => app name [x]) names
  fun binary names x y = List.map (fn name => app name [x,y]) names
  fun ternary names x y z = List.map (fn name => app name [x,y,z]) names
  val array="((as const (Array Int Int)) 7)"
  val sequence="(seq.++ (seq.unit 1) (seq.unit 2))"
  val empty_sequence="(as seq.empty (Seq Int))"
  val set="(set.insert 1 2 (as set.empty (Set Int)))"
  val bag="(bag 1 2)"
  val predicate="(lambda ((x Int)) (> x 0))"
  val mapping="(lambda ((x Int)) (+ x 1))"
  val fold="(lambda ((x Int) (y Int)) (+ x y))"
  val relation="(lambda ((x Int) (y Int)) (= x y))"
  val comprehension=
    "(set.comprehension (lambda ((x Bool)) x) (lambda ((x Bool)) x))"

  val descriptor_cases =
    let
      fun comp (left,right) = app "set.comprehension" [left,right]
      val duplicate = "(lambda ((x Bool) (x Bool)) x)"
      val nested = "(lambda ((x Bool)) (lambda ((x Bool)) x))"
      val renamed = "(lambda ((x Bool) (y Bool)) y)"
      val primed = "(lambda ((x' Bool) (x Bool)) x)"
      val mixed = "(lambda ((x Int) (x Bool)) x)"
      val mixed_nested = "(lambda ((x Int)) (lambda ((x Bool)) x))"
      val cases = List.map comp
        [(duplicate,duplicate),(nested,nested),(duplicate,nested),
         (duplicate,renamed),(nested,primed),(primed,nested),
         (mixed,mixed),(mixed,mixed_nested),
         ("(lambda ((x Bool) (y Bool) (x Bool)) (and x y))",
          "(lambda ((x Bool)) (lambda ((y Bool) (x Bool)) x))")]
    in cases @ List.map (fn text =>
      "(lambda ((x Bool)) "^text^")") cases @
      ["(lambda ((x Bool)) (set.comprehension "^
       "(lambda ((x Bool)) (and x true)) "^
       "(lambda ((y Bool)) x)))"]
    end

  val arrays =
    [array,"(select "^array^" 0)","(store "^array^" 1 9)",
     "(select (store "^array^" 1 9) 1)",
     "((as const (Array Bool Int)) 3)",
     "((as const (Array Int Bool)) true)",
     "((as const (Array Int Bool)) false)",
     "(let ((a "^array^")) (store a 1 (select a 2)))",
     "(lambda ((array_const_index Int)) "^
       "((as const (Array Int Int)) array_const_index))"]
  val sequences =
    [sequence,empty_sequence,"seq.empty","(seq.unit 1)",
     "(seq.unit \"a\")","(seq.unit (seq.unit 1))",
     "(seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))"] @
    unary ["seq.len","seq.rev"] sequence @
    binary ["seq.++","seq.contains","seq.prefixof","seq.suffixof"]
      sequence empty_sequence @
    List.concat (List.map (fn index =>
      binary ["seq.at","seq.nth"] sequence index @
      ternary ["seq.extract"] sequence index "2" @
      ternary ["seq.update","str.update"] sequence index "(seq.unit 3)")
      ["(- 1)","0","99"]) @
    ternary ["seq.indexof"] sequence "(seq.unit 2)" "0" @
    ternary ["seq.replace","seq.replace_all","str.replace_all"]
      sequence "(seq.unit 1)" "(seq.unit 3)" @
    ["(str.rev "^sequence^")"]
  val string_sequences =
    unary ["seq.len","seq.rev","str.rev"] "\"ab\"" @
    binary ["seq.++","seq.contains","seq.prefixof","seq.suffixof"]
      "\"ab\"" "\"a\"" @
    binary ["seq.at"] "\"ab\"" "(- 1)" @
    ternary ["seq.extract"] "\"ab\"" "0" "2" @
    ternary ["seq.indexof"] "\"ab\"" "\"b\"" "0" @
    ternary ["seq.replace","seq.replace_all"]
      "\"ab\"" "\"a\"" "\"b\"" @
    ternary ["seq.update","str.update"] "\"ab\"" "0" "\"c\""
  val z3_sequences =
    [app "seq.map" [mapping,sequence],
     app "seq.foldl" [fold,"0",sequence],
     app "seq.fold_left" [fold,"0",sequence],
     "(_ Char 97)","(seq.unit (_ Char 97))",
     "(seq.nth \"ab\" 0)","(seq.nth \"ab\" (- 1))",
     "(seq.unit (seq.nth \"ab\" 0))",
     "(seq.unit (seq.nth \"ab\" (- 1)))",
     "(seq.unit (ite true (seq.nth \"ab\" 0) (seq.nth \"cd\" 1)))",
     "(seq.unit (let ((s \"ab\")) (seq.nth s 0)))",
     "(let ((s \"ab\")) (seq.unit (seq.nth s 0)))"]
  val strings =
    ["\"\"","\"a\"","\"a\"\"b\"","(_ char #x61)",
     "(str.++ \"a\" \"b\" \"c\")",
     "(str.< \"a\" \"b\" \"c\")","(str.<= \"a\" \"b\" \"c\")"] @
    unary ["str.len","str.is_digit","str.to_code","str.to_int",
           "str.to_re"] "\"12\"" @
    unary ["str.from_code","str.from_int"] "97" @
    binary ["str.at"] "\"ab\"" "(- 1)" @
    binary ["str.prefixof","str.suffixof","str.contains"]
      "\"a\"" "\"ab\"" @
    ternary ["str.substr"] "\"ab\"" "0" "2" @
    ternary ["str.indexof"] "\"ab\"" "\"b\"" "0" @
    ternary ["str.replace","str.replace_all"] "\"ab\"" "\"a\"" "\"c\""
  val regexps =
    ["re.none","re.all","re.allchar",
     "(str.in_re \"ab\" (re.* (re.range \"a\" \"z\")))",
     "(re.range \"a\" \"z\")","((_ re.^ 2) (str.to_re \"a\"))",
     "((_ re.loop 1 3) (str.to_re \"a\"))",
     "((_ re.loop 0 0) re.allchar)"] @
    unary ["re.comp","re.*","re.+","re.opt"] "(str.to_re \"a\")" @
    binary ["re.++","re.union","re.inter","re.diff"]
      "(str.to_re \"a\")" "re.allchar" @
    ternary ["str.replace_re","str.replace_re_all"]
      "\"aba\"" "(str.to_re \"a\")" "\"c\""
  val sets =
    [set,"set.empty","set.universe","(as set.empty (Set Int))",
     "(as set.universe (Set Int))","(set.singleton 1)",
     app "set.member" ["1",set],comprehension,
     "(set.comprehension true 1)",
     "(set.comprehension (lambda ((x Bool)) x) (lambda ((x Bool)) 0))",
     "(set.comprehension (lambda ((x Bool) (y Bool)) (and x y)) "^
       "(lambda ((x Bool) (y Bool)) x))",
     "(set.comprehension (lambda ((x (Set Bool))) (set.is_empty x)) "^
       "(lambda ((x (Set Bool))) (set.card x)))",
     "(set.comprehension (lambda ((x (Bag Bool))) (bag.all "^
       "(lambda ((y Bool)) y) x)) (lambda ((x (Bag Bool))) (bag.card x)))",
     "(lambda ((set_some_x Int)) (set.some "^
       "(lambda ((x Int)) (= x set_some_x)) "^set^"))"] @
    binary ["set.union","set.inter","set.minus","set.subset"]
      set "(set.singleton 3)" @
    unary ["set.complement","set.choose","set.card","set.is_empty",
           "set.is_singleton"] set @
    [app "set.map" [mapping,set],app "set.fold" [fold,"0",set]] @
    List.map (fn name => app name [predicate,set])
      ["set.filter","set.all","set.some"]
  val z3_set="(lambda ((x Int)) (= x 1))"
  val z3_sets =
    unary ["complement"] z3_set @
    binary ["union","intersection","setminus","subset"] z3_set
      "(lambda ((x Int)) (> x 0))" @
    ["((as union (Array Int Bool)) "^z3_set^" "^z3_set^")"]
  val bags =
    [bag,"bag.empty","(as bag.empty (Bag Int))",
     "(bag 1 0)","(bag 1 (- 2))","(bag true 3)",
     app "bag.count" ["1",bag],app "bag.member" ["1",bag],
     app "bag.map" [mapping,bag],app "bag.fold" [fold,"0",bag],
     app "bag.partition" [relation,bag],
     "(lambda ((bag_literal_x Int)) (bag bag_literal_x 2))",
     "(lambda ((bag_some_x Int)) (bag.some "^
       "(lambda ((x Int)) (= x bag_some_x)) "^bag^"))",
     "(lambda ((bag_partition_x Int)) (bag.partition "^relation^
       " (bag bag_partition_x 2)))",
     "(lambda ((bag_partition_x Int) (bag_partition_y Int)) "^
       "(bag.partition (lambda ((x Int) (y Int)) "^
       "(= (+ x bag_partition_x) (+ y bag_partition_y))) "^
       "(bag bag_partition_x 2)))",
     "(lambda ((bag_difference_remove_x Int)) "^
       "(bag.difference_remove (bag bag_difference_remove_x 2) "^bag^"))"] @
    binary ["bag.union_disjoint","bag.union_max","bag.inter_min",
            "bag.difference_subtract","bag.difference_remove","bag.subbag"]
      bag "(bag 2 3)" @
    unary ["bag.choose","bag.card","bag.setof"] bag @
    List.map (fn name => app name [predicate,bag])
      ["bag.filter","bag.all","bag.some"] @
    ["(bag.union_disjoint "^bag^" "^bag^" "^bag^")",
     "(bag.union_max "^bag^" "^bag^" "^bag^")",
     "(bag.inter_min "^bag^" "^bag^" "^bag^")"]

  type native_callback =
    string -> Term.term list -> Term.term list -> Term.term
  type callback_sample =
    {solver:string,entry:R.entry,parse:native_callback,token:string,
     indices:Term.term list,arguments:Term.term list,
     result_type:Type.hol_type}

  fun structured ({theory,...}:R.entry) = List.exists
    (fn family => family=theory)
    ["ArraysEx","UnicodeStrings","Seq_Extensions","CVC5_Seq","Z3_Seq",
     "CVC5_Set","Z3_Set","CVC5_Bag"]
  fun same_callback (entry:R.entry,parse:native_callback)
      (sample:callback_sample) =
    #name entry = #name (#entry sample) andalso
    Portable.pointer_eq (parse,#parse sample)
  fun callback_label ({theory,name,overload,...}:R.entry) =
    theory^"/"^name^"/"^Int.toString overload

  (* Observe AFTER success, leaving declines, overload order and the native
     literal setup untouched. Identity is the registered callback object,
     not its spelling alone. Shared callbacks need only one sample across
     the two solver packets; dialect-specific overloads remain distinct. *)
  fun callback_samples () =
    let
      val samples = ref ([]:callback_sample list)
      val selected = ref ([]:(R.entry * native_callback) list)
      fun collect solver texts =
        let
          val (sorts,dictionary) =
            SmtLib_Logics.parsedicts_of_solver_logic solver (logic solver)
          fun wrap (name,parses) = Lib.mapi (fn overload => fn parse =>
            let val entry=R.describe name overload parse in
              if not (structured entry) then parse else
              (selected := (entry,parse):: !selected;
               fn token => fn indices => fn arguments =>
                 let
                   val result=parse token indices arguments
                   val _=if List.exists (same_callback (entry,parse))
                       (!samples) then () else
                     (List.app (fn term => ensure
                        ("oversized native sample: "^callback_label entry)
                        (Option.isSome
                          (SmtReplayImport.bounded_raw_size maximum term)))
                        (result::indices @ arguments);
                      if name<>"set.comprehension" then () else
                        ensure "large comprehension sample must be binder-free"
                          (null indices andalso length arguments=2 andalso
                           List.all (not o Term.is_abs) arguments);
                      samples := {solver=solver,entry=entry,parse=parse,
                        token=token,indices=indices,arguments=arguments,
                        result_type=Term.type_of result}:: !samples)
                 in result end)
            end) parses
          val dictionary=Redblackmap.map wrap dictionary
          val dictionaries=(sorts,
            Library.extend_dict (("_",native_literal),dictionary))
        in List.app (fn text => ignore
          (P.parse_term_with_cfg cfg (tokens text) dictionaries)) texts end
      (* Inflating lambda operands changes comprehension's accepted binder
         shape. Capture this zero-binder callback FIRST, and never replace
         it with the lambda cases in the ordinary comparison fixtures. *)
      val _=collect "cvc5" ["(set.comprehension true 1)"]
      val _=List.app (fn (solver,texts) => collect solver texts)
        [("cvc5",arrays),("cvc5",sequences),("cvc5",string_sequences),
         ("Z3",z3_sequences),("cvc5",strings),("cvc5",regexps),
         ("cvc5",sets),("Z3",z3_sets),("cvc5",bags),
         (* cvc5's sequence alias shadows Unicode str.replace_all; Z3's
            String fixture reaches that distinct registered callback. *)
         ("Z3",strings)]
      val missing=List.filter (fn identity =>
        not (List.exists (same_callback identity) (!samples))) (!selected)
      val _=ensure ("uncaptured structured callbacks: "^
        String.concatWith ", " (List.map (callback_label o #1) missing))
        (null missing)
    in List.rev (!samples) end

  (* Only the small original arguments are native Terms. Build every ite
     layer through B.application, sharing the same value in both branches.
     In particular, NEVER call a native callback or small_graph/small_value
     with these inflated operands. *)
  fun shared80_value backend frame initial =
    let
      val ty=B.type_of backend initial
      val conditional=Term.inst
        [Type.alpha |-> ty] boolSyntax.conditional
      val head=B.source backend frame conditional
      val truth=B.source backend frame boolSyntax.T
      val choose=B.application backend frame (head,truth)
      fun grow 0 value=value
        | grow n value=grow (n-1)
            (B.application backend frame
              (B.application backend frame (choose,value),value))
    in grow 80 initial end
  fun shared80 backend frame original =
    shared80_value backend frame (B.source backend frame original)

  (* Ascriptions do not pass through the registered callback inventory.
     Exercise the same R callback used by BOTH frontend construction paths.
     Keep the actual list payload outside the tiny native const binders. *)
  fun large_ascribed backend exact =
    let
      val frame=B.root backend
      val original=listSyntax.mk_list ([boolSyntax.T,boolSyntax.F],Type.bool)
      val payload=shared80 backend frame original
      val sort=Type.--> (intSyntax.int_ty,Term.type_of original)
      val description={name="const",constructor=SOME "Array",sort=sort,
                       arguments=[payload]}
      val result=required (if exact then
          R.ascribed_with_policy backend frame policy description
        else R.ascribed backend frame limits description)
      val _=ensure "shared80 ascribed const changed Array Int payloadTy"
        (Type.compare (B.type_of backend result,sort)=EQUAL)
      val _=ensure "shared80 ascribed const inserted payload under a binder"
        (case B.view backend frame result of
           B.Apply (_,actual) => B.same_value backend (actual,payload)
         | _ => false)
    in [payload] end

  fun large_callback backend exact (sample:callback_sample) =
    let
      val {solver,entry,token,indices,arguments,result_type,...}=sample
      val frame=B.root backend
      val (_,dictionary)= #dictionaries
        (if exact then R.select_with_policy_no_override backend policy
           {logic=logic solver,solver=SOME solver}
         else R.select backend limits {logic=logic solver,solver=SOME solver})
      (* Pin the exact selected overload: a successful sibling must not
         disguise a missed or refused callback in the large control. *)
      val parse=List.nth
        (Redblackmap.find (dictionary,#name entry),#overload entry)
      val dictionary=Redblackmap.insert
        (Redblackmap.mkDict String.compare,#name entry,[parse])
      val operands=List.map (shared80 backend frame) arguments
      val result=if exact then P.apply_construction_symbol_with_policy
          (policy_options backend frame) dictionary frame token
          (List.map P.LiteralIndex indices) operands
        else P.apply_construction_symbol (options backend frame)
          dictionary frame token (List.map P.LiteralIndex indices) operands
      val _=ensure ("shared80 result type: "^callback_label entry)
        (Type.compare (B.type_of backend result,result_type)=EQUAL)
      (* Follow recipe syntax only, stopping at every actual input. *)
      fun retained operand =
        let val seen=ref []
            fun scan [] = false
              | scan (value::rest) =
                  if B.same_value backend (operand,value) then true
                  else if List.exists (fn old =>
                      B.same_value backend (old,value)) (!seen) orelse
                      List.exists (fn input =>
                        B.same_value backend (input,value)) operands
                  then scan rest
                  else (seen := value :: !seen;
                    case B.view backend frame value of
                      B.Apply (f,x) => scan (f::x::rest)
                    | _ => scan rest)
        in scan [result] end
      val _=ensure ("lost shared80 operand: "^callback_label entry)
        (List.all retained operands)
    in operands end

  fun large_graph exact construct = with_graph exact
    (fn graph => fn backend =>
    let
      val (operands,statistics)=G.with_node_statistics graph
        (G.root_scope graph) (fn () => construct backend)
      val _=ensure "shared80 structured graph expanded"
        (#node_creations statistics<IntInf.fromInt maximum)
      (* Nullary callbacks have no large input; still check their type and
         construction cost. Each actual operand must exceed the raw bound. *)
      val _=List.app (fn operand => ensure
        "shared80 structured input did not exceed the import bound"
        (case G.unfolded_nodes graph G.RawNodes maximum operand of
           NONE => true | SOME size => size>maximum)) operands
    in () end)

  fun large_value exact construct =
    let
      val graph=G.new () val scope=G.root_scope graph
      val spent=ref (0:IntInf.int)
      fun spend amount =
        (spent := !spent+amount;
         ensure "shared80 structured value work expanded" (!spent<10000000))
      val context=PV.create {graph=graph,scope=scope,
        validate=fn () => (),spend=spend,retire=fn () => ()}
      val held=B.values_with_policy {context=context,graph=graph,scope=scope,
        import_limit=policy_maximum,literal_limit=policy_maximum,
        binder_limit=policy_maximum}
      val backend= #backend held val frame=B.root backend
      (* Fresh sentinels bracket all allocated parser IDs, even when the
         callback returns an earlier interned value. Together with graph
         births and the spend ceiling this detects accidental projection. *)
      fun sentinel ()=PV.key context
        (B.source backend frame (Term.genvar Type.bool))
      val outcome=Exn.capture (fn () =>
        let
          val first=sentinel ()
          val (_,statistics)=G.with_node_statistics graph scope
            (fn () => construct backend)
          val last=sentinel ()
          val _=ensure "shared80 structured value allocated expanded syntax"
            (last-first<maximum andalso
             #node_creations statistics<IntInf.fromInt maximum)
        in () end) ()
      val _=(#close held) () val _=G.close_scope graph scope
    in Exn.release outcome end

  fun large_controls () =
    let
      val samples=callback_samples ()
      val _=print ("\nTASK33_REGISTERED_CALLBACKS "^
        Int.toString (List.length samples)^"\n")
      val _=List.app (fn sample => List.app (fn exact =>
        (large_graph exact (fn backend => large_callback backend exact sample);
         large_value exact (fn backend => large_callback backend exact sample)))
        [false,true]) samples
      val _=List.app (fn exact =>
        (large_graph exact (fn backend => large_ascribed backend exact);
         large_value exact (fn backend => large_ascribed backend exact)))
        [false,true]
    in () end

  (* Arm only AFTER constructing operands. Whole-parser injection from its
     first debit can miss these protected observations entirely. Direct
     observations and real parser callback/retry paths each get a fresh,
     standalone context; neither a frontend owner nor cleanup can mask the
     primary. Both long operands have >32 positive observation debits. *)
  fun primary_structured_errors () =
    let
      exception Injected of unit ref
      val primaries=List.map (fn (s,f,m) => Feedback.mk_HOL_ERR s f m)
        [("GraphStructuredTests","spend","injected resource primary"),
         ("Library","spend","injected resource primary"),
         ("SmtLib_Parser","t_with_args","injected resource primary"),
         ("SmtLib_Theories","spend","injected resource primary"),
         ("Type","dom_rng","injected resource primary"),
         ("SmtLib_GraphBackend","application",
          "application operand type mismatch")] @
        [Fail "injected resource primary",Injected (ref ()),Interrupt]
      val binders=String.concatWith " " (List.tabulate (40,fn i =>
        "(x"^Int.toString i^" Bool)"))
      val predicate="(lambda ("^binders^") true)"
      val value="(lambda ("^binders^") x0)"
      val selector="(seq.nth \"ab\" 0)"

      fun parser_action backend exact arm name operands =
        let
          val frame=B.root backend
          (* Comprehension is cvc5-only; seq.unit's string-selector shape
             is present in the Z3 packet. Preserve every overload/retry. *)
          val solver=if name="seq.unit" then "Z3" else "cvc5"
          val (sorts,dictionary)= #dictionaries
            (if exact then R.select_with_policy_no_override backend policy
               {logic=logic solver,solver=SOME solver}
             else R.select backend limits
               {logic=logic solver,solver=SOME solver})
          val parses=Redblackmap.find (dictionary,name)
          val dictionary=Redblackmap.insert (dictionary,name,
            List.map (fn parse => fn frame => fn token => fn indices =>
              fn arguments => (arm ();parse frame token indices arguments))
              parses)
          val aliases=Lib.mapi (fn i => fn operand =>
            ("structured_operand_"^Int.toString i,operand)) operands
          val dictionary=List.foldl (fn ((name,operand),dictionary) =>
            Library.extend_dict ((name,fn _ => fn _ => fn _ => fn _ =>
              operand),dictionary)) dictionary aliases
          val dictionaries=literals backend (sorts,dictionary)
          val text=app name (List.map #1 aliases)
        in fn () => ignore (if exact then P.parse_term_with_policy
            (policy_options backend frame) (tokens text) dictionaries
          else P.parse_term_with_backend (options backend frame)
            (tokens text) dictionaries) end

      fun check primary exact debit fixture =
        let
          val graph=G.new () val scope=G.root_scope graph
          val armed=ref false val calls=ref 0 val retired=ref 0
          val entries=ref 0
          val secondary=Fail "structured cleanup must not mask primary"
          fun validate ()=if !retired=0 then () else raise secondary
          fun spend amount=if not (!armed) orelse amount<=0 then () else
            (if !retired=0 then () else raise secondary;
             calls := !calls+1;
             if !calls=debit then raise primary else ())
          fun arm ()=(entries := !entries+1;armed := true)
          val context=PV.create {graph=graph,scope=scope,validate=validate,
            spend=spend,retire=fn () =>
              (retired := !retired+1;raise secondary)}
          val held=B.values_with_policy {context=context,graph=graph,
            scope=scope,import_limit=policy_maximum,
            literal_limit=policy_maximum,binder_limit=policy_maximum}
          val backend= #backend held val frame=B.root backend
          val action=if fixture="contains_constant" orelse
              fixture="seq.unit" then
            let val operand=shared80_value backend frame
                  (parsed backend exact "Z3" selector)
                (* Cache the guard before arming: hit the protected scan,
                   not initial transitive liveness validation. *)
                val _=B.type_of backend operand
            in if fixture="seq.unit" then
                parser_action backend exact arm "seq.unit" [operand]
              else
                let val source=B.source_syntax backend frame operand
                in fn () => (arm ();PV.protect context (fn () =>
                  ignore (C.contains_constant (B.syntax_spend backend)
                    {Thy="smtstringz3",Name="seq_nth_i"} source))) end
            end
            else
            let val left=parsed backend exact "cvc5" predicate
                val right=parsed backend exact "cvc5" value
                val _=List.app (fn operand =>
                  ignore (B.type_of backend operand)) [left,right]
            in if fixture="set.comprehension" then
                parser_action backend exact arm "set.comprehension"
                  [left,right]
              else
                let val source=B.source_syntax backend frame left
                in fn () => (arm ();PV.protect context (fn () =>
                  ignore (#1 (C.strip_abs (B.syntax_spend backend) source))))
                end
            end
          val outcome=Exn.capture action ()
          val actual=failure (fn () => Exn.release outcome)
          val expected=failure (fn () => raise primary)
          val identity=case (primary,outcome) of
              (Injected owner,Exn.Exn (Injected actual)) => owner=actual
            | (Injected _,_) => false
            | (_,Exn.Exn _) => true
            | _ => false
          val stopped= !calls=debit andalso !retired>0 andalso
            !entries=1 andalso PV.failure_requires_propagation context
          val _=(#close held) () val _=G.close_scope graph scope
          val label=fixture^" debit "^Int.toString debit
        in ensure (label^" masked/rewrapped primary exception")
             (actual=expected andalso identity);
           ensure (label^" missed expected retirement or retried work") stopped
        end
    in List.app (fn primary => List.app (fn exact =>
      List.app (fn debit => List.app (check primary exact debit)
        ["contains_constant","seq.unit","abstraction_variables",
         "set.comprehension"]) [1,2,4,8,16,32]) [false,true]) primaries
    end

  (* Exact ordinary exception classification, not merely 'both rejected'.
     Wrong arities, operand sorts, index counts and dialect selection. *)
  val malformed =
    [("cvc5",["(select true 0)","(select "^array^")",
       "(store "^array^" 0)","(seq.len true)","(seq.unit)",
       "(seq.extract "^sequence^" 0)","(seq.nth \"ab\" 0)",
       "(seq.contains "^sequence^" true)","(seq.rev true)",
       "(str.len true)","(str.substr \"ab\" 0)","(re.* true)",
       "((_ re.loop 1) re.allchar)","((_ re.^ 1 2) re.allchar)",
       "(set.insert)","(set.member 1 true)","(set.filter true "^set^")",
       "(set.some "^predicate^")",
       "(set.comprehension (lambda ((x Bool)) x) "^
         "(lambda ((y Bool)) y))",
       "(bag 1)","(bag.count 1 true)","(bag.difference_remove "^bag^")",
       "(bag.some true "^bag^")","(bag.partition true "^bag^")",
       "(bag.fold "^fold^" 0)","(seq.map "^mapping^" "^sequence^")",
       "(as set.empty (Seq Int))","(as bag.empty (Set Int))",
       "(as set.empty (Array Bool Bool))",
       "(as set.universe (Array Bool Bool))",
       "(as bag.empty (Array Bool Int))",
       "(as seq.empty String)","(as const (Set Int))",
       "(as set.empty MissingSort)","(as bag.empty MissingSort)",
       "(as seq.empty MissingSort)","(as const MissingSort)",
       "(as union MissingSort)","(as set.universe MissingSort)",
       "((as const (Array Int Int)) true)",
       "((as union (Array Int Bool)) true)",
       "((_ re.^ (bag true 1)) re.allchar)",
       (* Non-parenthesized qualified sorts must consume the same two
          tokens before index recovery as ordinary parse_qualified_type. *)
       "((_ re.^ (as set.empty Int)) re.allchar)",
       "((_ re.^ (as set.universe Int)) re.allchar)",
       "((_ re.^ (as seq.empty Int)) re.allchar)",
       "((_ re.^ (as bag.empty Int)) re.allchar)",
       "((_ re.^ (as union Int)) re.allchar)",
       "((_ re.^ (as const Int)) re.allchar)",
       "((_ seq.unit 0) 1)",
       "((_ set.comprehension 0) (lambda ((x Bool)) x) "^
         "(lambda ((y Bool)) y))"]),
     ("Z3",["(seq.update "^sequence^" 0 "^sequence^")",
       "(seq.rev "^sequence^")","(seq.foldl true 0 "^sequence^")",
       "(seq.nth true 0)","(set.singleton 1)","(bag 1 2)",
       (* The sort refusal precedes operand lookup/arity/type diagnostics.
          These and the bag-valued regex index above are review regressions. *)
       "((as union (Array Int Int)) missing)",
       "((as union (Array Int Int)) true)",
       "((as union (Array Int Int)))",
       "((as union MissingSort) missing)",
       "((as union (Array MissingSort Bool)) missing)"])]

  val session_cases =
    [("cvc5",[array,empty_sequence,"(as set.empty (Set Int))",
       "(as bag.empty (Bag Int))",app "set.filter" [predicate,set],
       comprehension,
       "(set.comprehension (lambda ((and Bool) (|and| Bool)) and) "^
         "(lambda ((and Bool) (|and| Bool)) |and|))",
       "(set.comprehension (lambda ((and (Set Bool)) "^
         "(|and| (Set Bool))) (set.is_empty and)) "^
         "(lambda ((and (Set Bool)) (|and| (Set Bool))) |and|))",
       app "bag.partition" [relation,bag],
       app "bag.some" [predicate,bag],
       app "bag.difference_remove" [bag,"(bag 2 3)"],
       "(lambda ((bag_literal_x Int)) (bag bag_literal_x 2))"]),
     ("Z3",[app "seq.map" [mapping,sequence],
       "((as union (Array Int Bool)) "^z3_set^" "^z3_set^")",
       "(seq.unit (seq.nth \"ab\" 0))"])]

  val source_shape_cases =
    [("Z3",[
       "(let ((c (seq.nth \"ab\" 0))) (seq.unit c))",
       "(let ((c (seq.nth \"ab\" 0))) (seq.unit (! c :named char)))",
       "(seq.unit (let ((c (seq.nth \"ab\" 0))) c))",
       "(seq.unit (let ((c (seq.nth \"ab\" 0))) (_ Char 97)))",
       "(seq.unit (let ((c (seq.nth \"ab\" 0))) 1))",
       "(let ((c (seq.nth \"ab\" 0))) (seq.unit (ite true c c)))"]),
     ("cvc5",[
       "(let ((p (lambda ((x Bool)) x))) (set.comprehension p p))",
       "(let ((p (lambda ((x Bool)) x))) (set.comprehension "^
         "(lambda ((x Bool)) x) p))",
       "(set.comprehension (let ((p (lambda ((x Bool)) x))) p) "^
         "(let ((p (lambda ((x Bool)) x))) p))",
       "(set.comprehension (lambda ((bag_literal_x Bool)) bag_literal_x) "^
         "(bag true 1))",
       "(set.comprehension ((as const (Array Int Bool)) (= 1 1)) "^
         "((as const (Array Int Int)) 7))",
       "(set.comprehension ((as const (Array Int Bool)) true) "^
         "((as const (Array Int Int)) 7))",
       "(lambda ((array_const_index Int)) (set.comprehension "^
         "((as const (Array Int Bool)) (= array_const_index 1)) "^
         "((as const (Array Int Int)) array_const_index)))",
       "(lambda ((array_const_index Int)) (set.comprehension "^
         "((as const (Array Bool Bool)) (= 1 1)) "^
         "((as const (Array Bool Int)) array_const_index)))",
       "(lambda ((bag_literal_x Bool)) (set.comprehension "^
         "(lambda ((|bag_literal_x'| Bool)) |bag_literal_x'|) "^
         "(bag bag_literal_x 1)))"])]
  fun source_shapes () = List.app (fn (solver,cases) =>
    List.app (fn text => case failure (fn () => ordinary solver text) of
      NONE => positive solver text | SOME _ => negative solver text) cases)
      source_shape_cases

  (* Proof-parser construction, not source AST typechecking or prover
     migration. Large controls never use bounded native comparisons;
     declared datatypes have a separate focused fixture. *)
  fun run () =
    let
      fun group (label,solver,texts) =
        (tprint ("Structured "^label^" checked against ordinary parser");
         List.app (positive solver) texts; OK ())
      val _=List.app group
        [("arrays","cvc5",arrays),("sequences","cvc5",sequences),
         ("String sequences","cvc5",string_sequences),
         ("Z3 sequences/provenance","Z3",z3_sequences),
         ("strings","cvc5",strings),("regular languages","cvc5",regexps),
         ("scoped sets","cvc5",sets),("Z3 sets","Z3",z3_sets),
         ("scoped bags","cvc5",bags)]
      val _=tprint "Structured ordinary source-shape/lexical differentials"
      val _=source_shapes ()
      val _=OK ()
      val _=tprint "Structured definition aliases retain ordinary source shape"
      val _=alias_positive "cvc5" "(bag true 1)"
        ("(set.comprehension (lambda ((bag_literal_x Bool)) bag_literal_x) "^
          "structured_alias2)")
      val _=alias_positive "cvc5"
        "(lambda ((bag_literal_x Bool)) (bag bag_literal_x 1))"
        ("(set.comprehension "^
         "(lambda ((|bag_literal_x''| (Bag Bool))) true) "^
         "(bag (structured_alias2 true) 1))")
      val _=alias_positive "Z3" "(seq.nth \"ab\" 0)"
        "(seq.unit structured_alias2)"
      val _=OK ()
      val _=tprint "Structured public binder/native/abstraction/template laws"
      val _=binder_invariants ()
      val _=OK ()
      val _=tprint "Structured admitted raw callback comprehensions"
      val _=raw_comprehensions ()
      val _=OK ()
      val _=tprint "Structured shadowed/duplicate descriptor differential"
      val _=List.app (differential "cvc5") descriptor_cases
      val _=OK ()
      val _=tprint "Structured shared80 callbacks/ascribed const/no projection"
      val _=large_controls ()
      val _=OK ()
      val _=tprint "Structured observations preserve primary errors/Interrupt"
      val _=primary_structured_errors ()
      val _=OK ()
      val _=tprint "Structured public frontend ascriptions and lambdas"
      val _=List.app (fn (solver,texts) =>
        List.app (session_positive solver) texts) session_cases
      val _=OK ()
      val _=print ("TASK33_STRUCTURED_COUNTS positives="^
        Int.toString (List.foldl (fn (xs,n) => List.length xs+n) 0
          [arrays,sequences,string_sequences,z3_sequences,strings,regexps,
           sets,z3_sets,bags])^" malformed="^
        Int.toString (List.foldl (fn ((_,xs),n) => List.length xs+n)
          0 malformed)^" source_cases="^
        Int.toString (List.foldl (fn ((_,xs),n) => List.length xs+n)
          0 source_shape_cases)^" primary=432 routes=4\n")
      val _=tprint "Structured malformed classifications remain exact"
      val _=List.app (fn (solver,texts) =>
        List.app (negative solver) texts) malformed
      val _=OK ()
    in () end
end
