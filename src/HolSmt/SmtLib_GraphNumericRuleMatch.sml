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
  exception Mismatch
  exception HigherOrder
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

  fun prepare (owner as Owner {work,graph,...})
      {schema = schema as Schema {owner = held,binders,free,left,right,...},
       caller,traversal,target} =
    protected owner (fn () =>
      (Shared.same_owner "foreign matching owner" owner held;
       W.with_step work (fn () =>
       let val _ = active owner
           val variables = binders @ free
           val actual = tree owner caller traversal target
           val types = ref ([] : (Type.hol_type * Type.hol_type) list)
           val arguments = ref ([] : (G.node * tree) list)
           fun lookup equal key pending = case pending of
             [] => NONE
           | (k,v)::rest => (tick owner;
               if equal (key,k) then SOME v else lookup equal key rest)
           fun type_match pattern actual =
             (tick owner;
              if Type.is_vartype pattern then
                (case lookup (fn (a,b) => compare_type owner (a,b) = EQUAL)
                    pattern (!types) of
                   NONE => types := (pattern,actual) :: !types
                 | SOME old => if compare_type owner (old,actual) = EQUAL
                     then () else raise Mismatch)
              else if Type.is_vartype actual then raise Mismatch
              else let val p = Type.dest_thy_typeid pattern
                       val a = Type.dest_thy_typeid actual
                   in if #Tyop p = #Tyop a andalso
                         length (#Args p) = length (#Args a) then
                        ListPair.appEq (fn (x,y) => type_match x y)
                          (#Args p,#Args a)
                      else raise Mismatch end)
           fun captures bound value =
             (tick owner;
              List.exists (fn (_,target) => node value = target) bound orelse
              (case #shape (data value) of
                 App (f,x) => captures bound f orelse captures bound x
               | Lam {body,...} => captures bound body | Atom => false))
           fun same bound p a =
             (tick owner;
              if compare_type owner (#ty (data p),#ty (data a)) <> EQUAL
                then false else
              case (#shape (data p),#shape (data a)) of
                (App (f,x),App (g,y)) => same bound f g andalso same bound x y
              | (Lam {binder = b,body = x,...},
                 Lam {binder = c,body = y,...}) => same ((b,c)::bound) x y
              | (Atom,Atom) => (case lookup (op =) (node p) bound of
                  SOME mapped => mapped = node a
                | NONE => (case
                    (G.view graph (node p),G.view graph (node a)) of
                    (G.Constant x,G.Constant y) => x = y
                  | (G.Variable _,G.Variable _) => node p = node a
                  | _ => false))
              | _ => false)
           fun match bound p a =
             (type_match (#ty (data p)) (#ty (data a));tick owner;
              if List.exists (fn b => b = node p) variables then
                (if captures bound a then raise HigherOrder else ();
                 case lookup (op =) (node p) (!arguments) of
                   NONE => arguments := (node p,a) :: !arguments
                 | SOME old => if same [] old a then () else raise Mismatch)
              else case (#shape (data p),#shape (data a)) of
                (App (f,x),App (g,y)) => (match bound f g;match bound x y)
              | (Lam {binder = b,body = x,...},
                 Lam {binder = c,body = y,...}) => match ((b,c)::bound) x y
              | (Atom,Atom) => (case lookup (op =) (node p) bound of
                  SOME mapped => if mapped = node a then () else raise Mismatch
                | NONE => (case
                    (G.view graph (node p),G.view graph (node a)) of
                    (G.Constant x,G.Constant y) =>
                      if x = y then () else raise Mismatch
                  | (G.Variable _,G.Variable _) =>
                      if node p = node a then () else raise Mismatch
                  | _ => raise Mismatch))
              | _ => raise Mismatch)
           fun output_type ty =
             (tick owner;
              case lookup (fn (a,b) => compare_type owner (a,b) = EQUAL)
                  ty (!types) of
                SOME target => type_weight owner target
              | NONE => if Type.is_vartype ty then type_weight owner ty
                else let val {Args,...} = Type.dest_thy_typeid ty
                     in List.foldl (fn (a,n) => n+output_type a) 1 Args end)
           fun forecast value =
             (tick owner;
              if List.exists (fn b => b = node value) variables then
                (case lookup (op =) (node value) (!arguments) of
                  SOME actual => SOME (#profile (data actual)) | NONE => NONE)
              else let val ann = output_type (#ty (data value))
                in case #shape (data value) of
                  Atom => SOME (unit ann)
                | App (f,x) => (case (forecast f,forecast x) of
                    (SOME p,SOME q) => SOME (add (unit ann) (add p q))
                  | _ => NONE)
                | Lam {binder_type,body,...} => (case forecast body of
                    SOME p => SOME (add
                      {raw = 1,inc = 2,ann = ann+output_type binder_type} p)
                  | NONE => NONE) end)
           val result =
             ((match [] left actual;
               let val output = case right of NONE => NONE
                     | SOME rhs => forecast rhs
               in Matched (Match {owner = owner,schema = schema,
                 caller = caller,traversal = traversal,target = actual,
                 types = List.rev (!types),arguments = List.rev (!arguments),
                 output = output,used = ref false}) end)
              handle Mismatch => NoMatch | HigherOrder => NeedsHigherOrder)
           val _ = active owner
       in result end)))
  (* Every retained descendant is checked, not just the root node. No
     callback can turn a completed subtree into a cross-callback cache. *)
  fun retained owner caller value =
    let val Owner {graph,...} = owner val d = data value
        val _ = G.validate_scope graph caller
        val _ = G.validate_scope graph (#frame d)
        val _ = if G.closure_child_node graph caller (#child d) = #node d
          then () else raise ERR "retained" "closure identity changed"
    in case #shape d of
        Atom => ()
      | App (f,x) => (retained owner caller f;retained owner caller x)
      | Lam {body,...} => retained owner caller body end
  fun validate_for expected (Match {owner = owner as Owner
      {work,graph,scope,...},schema = Schema {whole,...},
       caller,traversal,target,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_for" "foreign Work match";
      active owner;
      G.validate_scope graph caller;G.validate_scope graph traversal;
      if G.scope_visible graph caller scope andalso
          G.scope_visible graph traversal caller andalso
          G.scope_visible graph traversal (G.node_scope graph (node target))
        then () else raise ERR "validate_for" "invisible retained match";
      retained owner scope whole;retained owner caller target)
     handle primary => (W.close expected;raise primary))
  fun describe_for expected (value as Match
      {schema = Schema {index,rule,binders,free,conditions,terminal,...},
       types,arguments,target,output,...}) =
    let val _ = validate_for expected value
    in {rule = rule,rule_index = index,terminal = terminal,
      type_bindings = types,
      arguments = List.map (fn (b,t) => (b,node t)) arguments,
      conditions = List.map node conditions,
      missing_arguments = List.filter (fn b =>
        not (List.exists (fn (k,_) => b = k) arguments)) (binders @ free),
      target = node target,output = output} end
  (* This derives a closed CONDITIONAL instance. The literal first-order
     route does not claim Cond_rewr's orientation/condition solver policy. *)
  fun instantiate (value as Match {owner = owner as Owner
      {work,graph,scope,...},schema = schema as Schema
        {whole,rule,free,operations,terminal,left,...},types,arguments,
      caller,traversal,target,used,...}) {check_type} =
    protected owner (fn () => W.with_step work (fn () =>
    let
      val _ = active owner
      val _ = if !used then raise ERR "instantiate" "match already consumed"
        else ()
      val _ = validate_for work value
      val _ = used := true
      val limit = IntInf.fromInt (W.work_limit work)
      val output_cap = IntInf.fromInt
        (#output_limit (W.semantic_limits work))
      val template_cap = IntInf.fromInt
        (#template_limit (W.semantic_limits work))
      fun find equal key pending = case pending of [] => NONE
        | (k,v)::rest => (tick owner;
            if equal (key,k) then SOME v else find equal key rest)
      fun mapped_weight ty =
        (tick owner;
         if Type.is_vartype ty then
           (case find (fn (a,b) => compare_type owner (a,b) = EQUAL)
                ty types of
              NONE => type_weight owner ty | SOME t => type_weight owner t)
         else let val {Args,...} = Type.dest_thy_typeid ty
              in List.foldl (fn (a,n) => n+mapped_weight a) 1 Args end)
      val annotations = ref ([] : Type.hol_type list)
      val actual_annotations = ref ([] : Type.hol_type list)
      fun actual_types current =
        let val d = data current val _ = tick owner
            val _ = actual_annotations := #ty d :: !actual_annotations
        in case #shape d of Atom => ()
          | App (f,x) => (actual_types f;actual_types x)
          | Lam {binder_type,body,...} =>
              (actual_annotations := binder_type :: !actual_annotations;
               actual_types body) end
      fun profile substitutions current =
        let val d = data current val _ = tick owner
            val _ = annotations := #ty d :: !annotations
        in case find (op =) (#node d) substitutions of
          SOME p =>
            (case find (op =) (#node d) arguments of
               SOME target => actual_types target | NONE => ();p)
        | NONE =>
            let val ann = mapped_weight (#ty d)
            in case #shape d of
              Atom => unit ann
            | App (f,x) => add (unit ann)
                (add (profile substitutions f) (profile substitutions x))
            | Lam {binder_type,body,...} =>
                (annotations := binder_type :: !annotations;
                 add {raw = 1,inc = 2,
                   ann = ann+mapped_weight binder_type}
                   (profile substitutions body)) end end
      fun equality (p : profile) : profile =
        {raw = 2 * #raw p+3,inc = 2 * #inc p+3,ann = 2 * #ann p+9}
      fun implication (p : profile) (q : profile) =
        add {raw = 3,inc = 3,ann = 9} (add p q)
      val forecasts = ref ([] : profile list)
      fun record hypotheses (p : profile) =
        let val h = List.foldl (fn (x,a) => add x a)
              {raw = 0,inc = 0,ann = 0} hypotheses
            val full = add p h
            val _ = if #raw p <= output_cap andalso #inc p <= output_cap
                andalso #ann full <= limit then () else
              raise ERR "instantiate" "prospective instance exceeds quota"
        in forecasts := full :: !forecasts;p end
      val initial = profile [] whole
      (* Genuine whole original/canonical bridge: TRANS equality then EQ_MP.
         Alpha-only metadata does not authorize an arbitrary semantic pair. *)
      val _ = record [] (equality initial)
      val _ = record [] initial
      val _ = record [] initial (* INST_TYPE result *)
      val free_substitutions = List.mapPartial (fn binder =>
        case find (op =) binder arguments of
          NONE => NONE
        | SOME value => SOME (binder,#profile (data value))) free
      val _ = if null free_substitutions then () else
        ignore (record [] (profile free_substitutions whole))
      val _ = List.app (fn (binder,actual) =>
        let val ty = G.type_of graph binder
            val _ = annotations := ty :: !annotations
        in ignore (record [] (unit (mapped_weight ty)));
           ignore (record [] actual) end) free_substitutions
      fun play [] current substitutions hypotheses =
            (current,substitutions,hypotheses)
        | play (operation::rest) current substitutions hypotheses =
          (tick owner;
           case operation of
             Specialize binder =>
               let val predicate = case unary owner "bool" "!" current of
                     SOME p => p | NONE =>
                       raise ERR "instantiate" "prepared forall route changed"
                   val body = case #shape (data predicate) of
                     Lam {body,...} => body | _ =>
                       raise ERR "instantiate" "missing prepared binder"
                   val actual = case find (op =) binder arguments of
                     SOME t => #profile (data t)
                   | NONE =>
                       let val ty = G.type_of graph binder
                           val _ = annotations := ty :: !annotations
                       in unit (mapped_weight ty) end
                   val substitutions = (binder,actual)::substitutions
                   val _ = record hypotheses (profile substitutions body)
               in play rest body substitutions hypotheses end
           | Select choose_left =>
               let val (l,r) = case binary owner "bool" "/\\" current of
                     SOME p => p | NONE =>
                       raise ERR "instantiate" "prepared conjunction changed"
                   val next = if choose_left then l else r
                   val _ = record hypotheses (profile substitutions next)
               in play rest next substitutions hypotheses end
           | Undisch =>
               let val (condition,body) =
                     case binary owner "min" "==>" current of
                       SOME p => p | NONE =>
                         raise ERR "instantiate" "prepared implication changed"
                   val h = profile substitutions condition
                   val _ = record [h] h (* ASSUME local condition *)
                   val hypotheses = h::hypotheses
                   val _ = record hypotheses (profile substitutions body)
               in play rest body substitutions hypotheses end)
      val (_,substitutions,hypotheses) =
        play operations whole free_substitutions []
      val p = profile substitutions left
      val terminal_profile = case terminal of
          Equality => (case schema of Schema {right = SOME r,...} =>
            let val rhs = profile substitutions r
                val t = mapped_weight (#ty (data left))
            in add {raw = 3,inc = 3,ann = 6+3*t} (add p rhs) end
          | _ => raise ERR "instantiate" "equality route missing right side")
        | Positive =>
            (ignore (record []
              {raw = 2 * #raw p+7,inc = 2 * #inc p+7,ann = 2 * #ann p+19});
             add p {raw = 4,inc = 4,ann = 10})
        | Negative =>
            (ignore (record []
              {raw = 2 * #raw p+9,inc = 2 * #inc p+9,ann = 2 * #ann p+23});
             add p {raw = 4,inc = 4,ann = 10})
      val _ = record hypotheses terminal_profile
      fun discharge [] p = p
        | discharge (h::rest) p =
            let val q = implication h p val _ = record rest q
            in discharge rest q end
      val final = discharge hypotheses terminal_profile
      val _ = if #raw final <= template_cap andalso
          #inc final <= template_cap then () else
        raise ERR "instantiate" "instance exceeds closed-recording template"
      val _ = record [] p (* prospective operand comparison *)
      val _ = record [] (equality final) (* genuine G import bridge *)
      val _ = record [] (equality final) (* genuine G opened bridge *)
      val _ = record [] (equality final) (* P retained bridge TRANS *)
      val _ = record [] final (* original closed recording EQ_MP *)
      val quote = List.foldl (fn (p,n) =>
          n + #raw p + #inc p + #ann p) (0 : IntInf.int) (!forecasts)
      val _ = if quote <= limit then W.spend work (IntInf.toInt quote) else
        raise ERR "instantiate" "instance portfolio exceeds original Work"
      fun guard action =
        (validate_for work value;
         let val result = action ()
         in validate_for work value;result end)
      (* No future type constructor, policy or proof before all result
         grammars and repeated annotations have been prepared/debited. *)
      val substitution = List.map
        (fn (redex,residue) => {redex = redex,residue = residue}) types
      val checked_types = List.map (fn ty =>
        guard (fn () => Type.type_subst substitution ty)) (!annotations) @
          !actual_annotations
      (* Domains are ONLY original free-variable nodes; ranges come ONLY
         from this completed match. No caller substitution is admitted.
         Detect collapsed free domains before policy/INST_TYPE/INST. *)
      val free_terms = List.mapPartial (fn binder =>
        case find (op =) binder arguments of NONE => NONE
        | SOME value =>
          let val original = guard (fn () => G.representative graph binder)
              val typed = guard (fn () => Term.inst substitution original)
              val target = guard (fn () => G.representative graph (node value))
          in SOME {redex = typed,residue = target} end) free
      fun unique [] = ()
        | unique ({redex,residue}::rest) =
          (List.app (fn {redex = other,residue = target} =>
             if guard (fn () => Term.term_eq redex other) then
               if guard (fn () => Term.aconv residue target) then () else
                 raise ERR "instantiate" "type instance collapses free domains"
             else ()) rest;unique rest)
      val _ = unique free_terms
      val _ = List.app (fn ty => guard (fn () => check_type ty)) checked_types
      val (imported,opened) = guard (fn () =>
        G.imported_opened_source graph scope (Thm.concl rule) (node whole))
      val bridge = guard (fn () =>
        Thm.TRANS (#bridge imported) (#bridge opened))
      val canonical = guard (fn () => Thm.EQ_MP bridge rule)
      val typed = guard (fn () => Thm.INST_TYPE substitution canonical)
      val typed = if null free_terms then typed else
        guard (fn () => Thm.INST free_terms typed)
      fun execute [] theorem conditions = (theorem,conditions)
        | execute (operation::rest) theorem conditions =
          (case operation of
             Specialize binder =>
               let val argument = case find (op =) binder arguments of
                     SOME t => guard (fn () => G.representative graph (node t))
                   | NONE => guard (fn () =>
                       #1 (boolSyntax.dest_forall (Thm.concl theorem)))
                   val next = guard (fn () => Thm.SPEC argument theorem)
               in execute rest next conditions end
           | Select choose_left =>
               let val next = guard (fn () => if choose_left
                     then Thm.CONJUNCT1 theorem else Thm.CONJUNCT2 theorem)
               in execute rest next conditions end
           | Undisch =>
               let val condition = guard (fn () =>
                     #1 (boolSyntax.dest_imp (Thm.concl theorem)))
                   val assumed = guard (fn () => Thm.ASSUME condition)
                   val next = guard (fn () => Thm.MP theorem assumed)
               in execute rest next (condition::conditions) end)
      val (body,conditions) = execute operations typed []
      val body = case terminal of Equality => body
        | Positive => guard (fn () => Drule.EQT_INTRO body)
        | Negative => guard (fn () => Drule.EQF_INTRO body)
      val theorem = List.foldl (fn (condition,th) =>
        guard (fn () => Thm.DISCH condition th)) body conditions
      val _ = if null (Thm.hyp theorem) then () else
        raise ERR "instantiate" "temporary condition hypotheses escaped"
      fun consequent current =
        if boolSyntax.is_imp current then
          consequent (#2 (boolSyntax.dest_imp current)) else current
      val actual_left = guard (fn () =>
        boolSyntax.lhs (consequent (Thm.concl theorem)))
      val wanted = guard (fn () => G.representative graph (node target))
      val _ = if guard (fn () => Term.aconv actual_left wanted) then () else
        raise ERR "instantiate" "proved instance differs from matched operand"
      val imported = guard (fn () => G.import graph traversal
        (#template_limit (W.semantic_limits work)) (Thm.concl theorem))
      val opened = guard (fn () => G.record_opened_view graph traversal
        (#template_limit (W.semantic_limits work)) (#node imported))
      val proof = guard (fn () => P.record_closed_from_import graph traversal
        {node = #node opened,theorem = theorem,
         template_limit = #template_limit (W.semantic_limits work),
         check_type = fn ty => guard (fn () => check_type ty)})
    in Instance {matched = value,theorem = theorem,proof = proof} end))
  fun instance_condition_for expected
      (instance as Instance {matched = value as Match
        {owner = Owner {graph,...},traversal,...},proof,...}) index =
    ((validate_for expected value;
      if index >= 0 then () else
        raise ERR "instance_condition_for" "negative antecedent index";
      P.validate_closed_fact graph traversal
        (#template_limit (W.semantic_limits expected)) proof;
      let val imp_id = #Name (Term.dest_thy_constid boolSyntax.implication)
          fun select current left =
            case G.view graph current of G.Application (partial,next) =>
              (case G.view graph partial of G.Application (head,ant) =>
                 (case G.view graph head of G.Constant id =>
                    if KernelSig.id_compare (id,imp_id) = EQUAL then
                      if left=0 then ant else select next (left-1)
                    else raise ERR "instance_condition_for" "absent condition"
                  | _ => raise ERR "instance_condition_for" "absent condition")
               | _ => raise ERR "instance_condition_for" "absent condition")
            | _ => raise ERR "instance_condition_for" "absent condition"
          val node = select (P.closed_node proof) index
          val child = G.closure_root graph traversal node
          val _ = validate_for expected value
      in {node=node,child=child,traversal=traversal} end)
     handle primary => (W.close expected;raise primary))
  fun instance_target_for expected
      (Instance {matched = value as Match
        {target,caller,traversal,...},...}) =
    (validate_for expected value;
     {node = node target,child = #child (data target),
      caller = caller,traversal = traversal})
  fun instance_fact_for expected
      (Instance {matched = value as Match
        {owner = Owner {graph,...},traversal,...},proof,...}) =
    ((validate_for expected value;
      P.validate_closed_fact graph traversal
        (#template_limit (W.semantic_limits expected)) proof;proof)
     handle primary => (W.close expected;raise primary))
  fun pattern_for expected (Schema
      {owner=owner as Owner {work,graph,scope,...},whole,left,right,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "pattern_for" "foreign expected Work";
      active owner;retained owner scope whole;
      let val target = case right of SOME value => value
            | NONE => raise ERR "pattern_for" "not a canonical equality clause"
          val l = G.representative graph (node left)
          val r = G.representative graph (node target)
          val _ = active owner;val _ = retained owner scope whole
      in {left=l,right=r} end)
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
  exception Mismatch
  exception HigherOrder
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

  fun prepare_with_policy (policy_owner as PolicyOwner {work,graph,...})
      {policy_schema = policy_schema as PolicySchema {policy_owner =
        held,binders,free,left,right,...},
       caller,traversal,target} =
    protected policy_owner (fn () =>
      (Shared.same_owner "foreign matching policy_owner" policy_owner
         held;
       W.with_step work (fn () =>
       let val _ = active policy_owner
           val variables = binders @ free
           val actual = tree policy_owner caller traversal target
           val native=NC.for_work work
             (case policy_owner of PolicyOwner {native_contract,...}=>
               native_contract)
           val input_cap=IntInf.fromInt
             (#input_limit (#semantic_limits native))
           val footprint= #profile (data actual)
           val _=if #raw footprint<=input_cap andalso
               #inc footprint<=input_cap then () else
             raise ERR "prepare_with_policy" "native input exceeds limit"
           val types = ref ([] : (Type.hol_type * Type.hol_type) list)
           val arguments = ref ([] : (G.node * tree) list)
           fun lookup equal key pending = case pending of
             [] => NONE
           | (k,v)::rest => (tick policy_owner;
               if equal (key,k) then SOME v else lookup equal key rest)
           fun type_match pattern actual =
             (tick policy_owner;
              if Type.is_vartype pattern then
                (case lookup (fn (a,b) => compare_type policy_owner (a,b) =
                  EQUAL)
                    pattern (!types) of
                   NONE => types := (pattern,actual) :: !types
                 | SOME old => if compare_type policy_owner (old,actual) =
                   EQUAL
                     then () else raise Mismatch)
              else if Type.is_vartype actual then raise Mismatch
              else let val p = Type.dest_thy_typeid pattern
                       val a = Type.dest_thy_typeid actual
                   in if #Tyop p = #Tyop a andalso
                         length (#Args p) = length (#Args a) then
                        ListPair.appEq (fn (x,y) => type_match x y)
                          (#Args p,#Args a)
                      else raise Mismatch end)
           fun captures bound value =
             (tick policy_owner;
              List.exists (fn (_,target) => node value = target) bound orelse
              (case #shape (data value) of
                 App (f,x) => captures bound f orelse captures bound x
               | Lam {body,...} => captures bound body | Atom => false))
           fun same bound p a =
             (tick policy_owner;
              if compare_type policy_owner (#ty (data p),#ty (data a)) <> EQUAL
                then false else
              case (#shape (data p),#shape (data a)) of
                (App (f,x),App (g,y)) => same bound f g andalso same bound x y
              | (Lam {binder = b,body = x,...},
                 Lam {binder = c,body = y,...}) => same ((b,c)::bound) x y
              | (Atom,Atom) => (case lookup (op =) (node p) bound of
                  SOME mapped => mapped = node a
                | NONE => (case
                    (G.view graph (node p),G.view graph (node a)) of
                    (G.Constant x,G.Constant y) => x = y
                  | (G.Variable _,G.Variable _) => node p = node a
                  | _ => false))
              | _ => false)
           fun match bound p a =
             (type_match (#ty (data p)) (#ty (data a));tick policy_owner;
              if List.exists (fn b => b = node p) variables then
                (if captures bound a then raise HigherOrder else ();
                 case lookup (op =) (node p) (!arguments) of
                   NONE => arguments := (node p,a) :: !arguments
                 | SOME old => if same [] old a then () else raise Mismatch)
              else case (#shape (data p),#shape (data a)) of
                (App (f,x),App (g,y)) => (match bound f g;match bound x y)
              | (Lam {binder = b,body = x,...},
                 Lam {binder = c,body = y,...}) => match ((b,c)::bound) x y
              | (Atom,Atom) => (case lookup (op =) (node p) bound of
                  SOME mapped => if mapped = node a then () else raise Mismatch
                | NONE => (case
                    (G.view graph (node p),G.view graph (node a)) of
                    (G.Constant x,G.Constant y) =>
                      if x = y then () else raise Mismatch
                  | (G.Variable _,G.Variable _) =>
                      if node p = node a then () else raise Mismatch
                  | _ => raise Mismatch))
              | _ => raise Mismatch)
           fun output_type ty =
             (tick policy_owner;
              case lookup (fn (a,b) => compare_type policy_owner (a,b) = EQUAL)
                  ty (!types) of
                SOME target => type_weight policy_owner target
              | NONE => if Type.is_vartype ty then type_weight policy_owner ty
                else let val {Args,...} = Type.dest_thy_typeid ty
                     in List.foldl (fn (a,n) => n+output_type a) 1 Args end)
           fun forecast value =
             (tick policy_owner;
              if List.exists (fn b => b = node value) variables then
                (case lookup (op =) (node value) (!arguments) of
                  SOME actual => SOME (#profile (data actual)) | NONE => NONE)
              else let val ann = output_type (#ty (data value))
                in case #shape (data value) of
                  Atom => SOME (unit ann)
                | App (f,x) => (case (forecast f,forecast x) of
                    (SOME p,SOME q) => SOME (add (unit ann) (add p q))
                  | _ => NONE)
                | Lam {binder_type,body,...} => (case forecast body of
                    SOME p => SOME (add
                      {raw = 1,inc = 2,ann = ann+output_type binder_type} p)
                  | NONE => NONE) end)
           val policy_result =
             ((match [] left actual;
               let val output = case right of NONE => NONE
                     | SOME rhs => forecast rhs
               in PolicyMatched (PolicyMatch {policy_owner =
                 policy_owner,policy_schema = policy_schema,
                 caller = caller,traversal = traversal,target = actual,
                 types = List.rev (!types),arguments = List.rev (!arguments),
                 output = output,used = ref false}) end)
              handle Mismatch => PolicyNoMatch | HigherOrder =>
                PolicyNeedsHigherOrder)
           val _ = active policy_owner
       in policy_result end)))
  (* Every retained descendant is checked, not just the root node. No
     callback can turn a completed subtree into a cross-callback cache. *)
  fun retained policy_owner caller value =
    let val PolicyOwner {graph,...} = policy_owner val d = data value
        val _ = G.validate_scope graph caller
        val _ = G.validate_scope graph (#frame d)
        val _ = if G.closure_child_node graph caller (#child d) = #node d
          then () else raise ERR "retained" "closure identity changed"
    in case #shape d of
        Atom => ()
      | App (f,x) => (retained policy_owner caller f;retained policy_owner
        caller x)
      | Lam {body,...} => retained policy_owner caller body end
  fun validate_with_policy_for expected (PolicyMatch {policy_owner =
    policy_owner as PolicyOwner
      {work,graph,scope,...},policy_schema = PolicySchema {whole,...},
       caller,traversal,target,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_with_policy_for" "foreign Work match";
      active policy_owner;
      G.validate_scope graph caller;G.validate_scope graph traversal;
      if G.scope_visible graph caller scope andalso
          G.scope_visible graph traversal caller andalso
          G.scope_visible graph traversal (G.node_scope graph (node target))
        then () else raise ERR "validate_with_policy_for"
          "invisible retained match";
      retained policy_owner scope whole;retained policy_owner caller target)
     handle primary => (W.close expected;raise primary))
  fun describe_with_policy_for expected (value as PolicyMatch
      {policy_schema = PolicySchema
        {index,rule,binders,free,conditions,terminal,...},
       types,arguments,target,output,...}) =
    let val _ = validate_with_policy_for expected value
    in {rule = rule,rule_index = index,terminal = terminal,
      type_bindings = types,
      arguments = List.map (fn (b,t) => (b,node t)) arguments,
      conditions = List.map node conditions,
      missing_arguments = List.filter (fn b =>
        not (List.exists (fn (k,_) => b = k) arguments)) (binders @ free),
      target = node target,output = output} end
  (* This derives a closed CONDITIONAL instance. The literal first-order
     route does not claim Cond_rewr's orientation/condition solver policy. *)
  fun instantiate_with_policy (value as PolicyMatch {policy_owner =
    policy_owner as PolicyOwner
      {work,graph,scope,...},policy_schema = policy_schema as PolicySchema
        {whole,rule,free,operations,terminal,left,...},types,arguments,
      caller,traversal,target,used,...}) {check_type} =
    protected policy_owner (fn () => W.with_step work (fn () =>
    let
      val _ = active policy_owner
      val _ = if !used then raise ERR "instantiate_with_policy"
        "match already consumed"
        else ()
      val _ = validate_with_policy_for work value
      val _ = used := true
      val native=NC.for_work work
        (case policy_owner of PolicyOwner
          {native_contract,...}=>native_contract)
      val limit=IntInf.fromInt (#type_work_limit native)
      val output_cap=IntInf.fromInt
        (#output_limit (#semantic_limits native))
      val template_cap=IntInf.fromInt
        (#template_limit (#semantic_limits native))
      val metadata=W.semantic_policy work
      fun find equal key pending = case pending of [] => NONE
        | (k,v)::rest => (tick policy_owner;
            if equal (key,k) then SOME v else find equal key rest)
      fun mapped_weight ty =
        (tick policy_owner;
         if Type.is_vartype ty then
           (case find (fn (a,b) => compare_type policy_owner (a,b) = EQUAL)
                ty types of
              NONE => type_weight policy_owner ty | SOME t => type_weight
                policy_owner t)
         else let val {Args,...} = Type.dest_thy_typeid ty
              in List.foldl (fn (a,n) => n+mapped_weight a) 1 Args end)
      val annotations = ref ([] : Type.hol_type list)
      val actual_annotations = ref ([] : Type.hol_type list)
      fun actual_types current =
        let val d = data current val _ = tick policy_owner
            val _ = actual_annotations := #ty d :: !actual_annotations
        in case #shape d of Atom => ()
          | App (f,x) => (actual_types f;actual_types x)
          | Lam {binder_type,body,...} =>
              (actual_annotations := binder_type :: !actual_annotations;
               actual_types body) end
      fun profile substitutions current =
        let val d = data current val _ = tick policy_owner
            val _ = annotations := #ty d :: !annotations
        in case find (op =) (#node d) substitutions of
          SOME p =>
            (case find (op =) (#node d) arguments of
               SOME target => actual_types target | NONE => ();p)
        | NONE =>
            let val ann = mapped_weight (#ty d)
            in case #shape d of
              Atom => unit ann
            | App (f,x) => add (unit ann)
                (add (profile substitutions f) (profile substitutions x))
            | Lam {binder_type,body,...} =>
                (annotations := binder_type :: !annotations;
                 add {raw = 1,inc = 2,
                   ann = ann+mapped_weight binder_type}
                   (profile substitutions body)) end end
      fun equality (p : profile) : profile =
        {raw = 2 * #raw p+3,inc = 2 * #inc p+3,ann = 2 * #ann p+9}
      fun implication (p : profile) (q : profile) =
        add {raw = 3,inc = 3,ann = 9} (add p q)
      val forecasts = ref ([] : profile list)
      fun record hypotheses (p : profile) =
        let val h = List.foldl (fn (x,a) => add x a)
              {raw = 0,inc = 0,ann = 0} hypotheses
            val full = add p h
            val _ = if #raw p <= output_cap andalso #inc p <= output_cap
                andalso RP.allows (#output_limit metadata) (#raw p)
                andalso RP.allows (#output_limit metadata) (#inc p)
                andalso #ann full <= limit then () else
              raise ERR "instantiate_with_policy"
                "prospective policy_instance exceeds quota"
        in forecasts := full :: !forecasts;p end
      val initial = profile [] whole
      (* Genuine whole original/canonical bridge: TRANS equality then EQ_MP.
         Alpha-only metadata does not authorize an arbitrary semantic pair. *)
      val _ = record [] (equality initial)
      val _ = record [] initial
      val _ = record [] initial (* INST_TYPE result *)
      val free_substitutions = List.mapPartial (fn binder =>
        case find (op =) binder arguments of
          NONE => NONE
        | SOME value => SOME (binder,#profile (data value))) free
      val _ = if null free_substitutions then () else
        ignore (record [] (profile free_substitutions whole))
      val _ = List.app (fn (binder,actual) =>
        let val ty = G.type_of graph binder
            val _ = annotations := ty :: !annotations
        in ignore (record [] (unit (mapped_weight ty)));
           ignore (record [] actual) end) free_substitutions
      fun play [] current substitutions hypotheses =
            (current,substitutions,hypotheses)
        | play (operation::rest) current substitutions hypotheses =
          (tick policy_owner;
           case operation of
             Specialize binder =>
               let val predicate = case unary policy_owner "bool" "!" current
                 of
                     SOME p => p | NONE =>
                       raise ERR "instantiate_with_policy"
                         "prepared forall route changed"
                   val body = case #shape (data predicate) of
                     Lam {body,...} => body | _ =>
                       raise ERR "instantiate_with_policy"
                         "missing prepared binder"
                   val actual = case find (op =) binder arguments of
                     SOME t => #profile (data t)
                   | NONE =>
                       let val ty = G.type_of graph binder
                           val _ = annotations := ty :: !annotations
                       in unit (mapped_weight ty) end
                   val substitutions = (binder,actual)::substitutions
                   val _ = record hypotheses (profile substitutions body)
               in play rest body substitutions hypotheses end
           | Select choose_left =>
               let val (l,r) = case binary policy_owner "bool" "/\\" current of
                     SOME p => p | NONE =>
                       raise ERR "instantiate_with_policy"
                         "prepared conjunction changed"
                   val next = if choose_left then l else r
                   val _ = record hypotheses (profile substitutions next)
               in play rest next substitutions hypotheses end
           | Undisch =>
               let val (condition,body) =
                     case binary policy_owner "min" "==>" current of
                       SOME p => p | NONE =>
                         raise ERR "instantiate_with_policy"
                           "prepared implication changed"
                   val h = profile substitutions condition
                   val _ = record [h] h (* ASSUME local condition *)
                   val hypotheses = h::hypotheses
                   val _ = record hypotheses (profile substitutions body)
               in play rest body substitutions hypotheses end)
      val (_,substitutions,hypotheses) =
        play operations whole free_substitutions []
      val p = profile substitutions left
      val terminal_profile = case terminal of
          Equality => (case policy_schema of PolicySchema {right = SOME r,...}
            =>
            let val rhs = profile substitutions r
                val t = mapped_weight (#ty (data left))
            in add {raw = 3,inc = 3,ann = 6+3*t} (add p rhs) end
          | _ => raise ERR "instantiate_with_policy"
            "equality route missing right side")
        | Positive =>
            (ignore (record []
              {raw = 2 * #raw p+7,inc = 2 * #inc p+7,ann = 2 * #ann p+19});
             add p {raw = 4,inc = 4,ann = 10})
        | Negative =>
            (ignore (record []
              {raw = 2 * #raw p+9,inc = 2 * #inc p+9,ann = 2 * #ann p+23});
             add p {raw = 4,inc = 4,ann = 10})
      val _ = record hypotheses terminal_profile
      fun discharge [] p = p
        | discharge (h::rest) p =
            let val q = implication h p val _ = record rest q
            in discharge rest q end
      val final = discharge hypotheses terminal_profile
      val _ = if #raw final <= template_cap andalso
          #inc final <= template_cap andalso
          RP.allows (#template_limit metadata) (#raw final) andalso
          RP.allows (#template_limit metadata) (#inc final) then () else
        raise ERR "instantiate_with_policy"
          "policy_instance exceeds closed-recording template"
      val _ = record [] p (* prospective operand comparison *)
      val _ = record [] (equality final) (* genuine G import bridge *)
      val _ = record [] (equality final) (* genuine G opened bridge *)
      val _ = record [] (equality final) (* P retained bridge TRANS *)
      val _ = record [] final (* original closed recording EQ_MP *)
      val quote = List.foldl (fn (p,n) =>
          n + #raw p + #inc p + #ann p) (0 : IntInf.int) (!forecasts)
      val _ = if quote <= limit andalso
          RP.allows (W.remaining_policy work) quote then
          W.spend_policy work quote else
        raise ERR "instantiate_with_policy"
          "policy_instance portfolio exceeds original_with_policy Work"
      fun guard action =
        (validate_with_policy_for work value;
         let val policy_result = action ()
         in validate_with_policy_for work value;policy_result end)
      (* No future type constructor, policy or proof before all result
         grammars and repeated annotations have been prepared/debited. *)
      val substitution = List.map
        (fn (redex,residue) => {redex = redex,residue = residue}) types
      val checked_types = List.map (fn ty =>
        guard (fn () => Type.type_subst substitution ty)) (!annotations) @
          !actual_annotations
      (* Domains are ONLY original free-variable nodes; ranges come ONLY
         from this completed match. No caller substitution is admitted.
         Detect collapsed free domains before policy/INST_TYPE/INST. *)
      val free_terms = List.mapPartial (fn binder =>
        case find (op =) binder arguments of NONE => NONE
        | SOME value =>
          let val original_with_policy = guard (fn () => G.representative
            graph binder)
              val typed = guard (fn () => Term.inst substitution
                original_with_policy)
              val target = guard (fn () => G.representative graph (node value))
          in SOME {redex = typed,residue = target} end) free
      fun unique [] = ()
        | unique ({redex,residue}::rest) =
          (List.app (fn {redex = other,residue = target} =>
             if guard (fn () => Term.term_eq redex other) then
               if guard (fn () => Term.aconv residue target) then () else
                 raise ERR "instantiate_with_policy"
                   "type policy_instance collapses free domains"
             else ()) rest;unique rest)
      val _ = unique free_terms
      val _ = List.app (fn ty => guard (fn () => check_type ty)) checked_types
      val (imported,opened) = guard (fn () =>
        G.imported_opened_source graph scope (Thm.concl rule) (node whole))
      val bridge = guard (fn () =>
        Thm.TRANS (#bridge imported) (#bridge opened))
      val canonical = guard (fn () => Thm.EQ_MP bridge rule)
      val typed = guard (fn () => Thm.INST_TYPE substitution canonical)
      val typed = if null free_terms then typed else
        guard (fn () => Thm.INST free_terms typed)
      fun execute [] theorem conditions = (theorem,conditions)
        | execute (operation::rest) theorem conditions =
          (case operation of
             Specialize binder =>
               let val argument = case find (op =) binder arguments of
                     SOME t => guard (fn () => G.representative graph (node t))
                   | NONE => guard (fn () =>
                       #1 (boolSyntax.dest_forall (Thm.concl theorem)))
                   val next = guard (fn () => Thm.SPEC argument theorem)
               in execute rest next conditions end
           | Select choose_left =>
               let val next = guard (fn () => if choose_left
                     then Thm.CONJUNCT1 theorem else Thm.CONJUNCT2 theorem)
               in execute rest next conditions end
           | Undisch =>
               let val condition = guard (fn () =>
                     #1 (boolSyntax.dest_imp (Thm.concl theorem)))
                   val assumed = guard (fn () => Thm.ASSUME condition)
                   val next = guard (fn () => Thm.MP theorem assumed)
               in execute rest next (condition::conditions) end)
      val (body,conditions) = execute operations typed []
      val body = case terminal of Equality => body
        | Positive => guard (fn () => Drule.EQT_INTRO body)
        | Negative => guard (fn () => Drule.EQF_INTRO body)
      val theorem = List.foldl (fn (condition,th) =>
        guard (fn () => Thm.DISCH condition th)) body conditions
      val _ = if null (Thm.hyp theorem) then () else
        raise ERR "instantiate_with_policy"
          "temporary condition hypotheses escaped"
      fun consequent current =
        if boolSyntax.is_imp current then
          consequent (#2 (boolSyntax.dest_imp current)) else current
      val actual_left = guard (fn () =>
        boolSyntax.lhs (consequent (Thm.concl theorem)))
      val wanted = guard (fn () => G.representative graph (node target))
      val _ = if guard (fn () => Term.aconv actual_left wanted) then () else
        raise ERR "instantiate_with_policy"
          "proved policy_instance differs from policy_matched operand"
      val imported = guard (fn () => G.import_with_policy graph traversal
        (RP.AtMost (IntInf.fromInt (#import_limit native)))
        (Thm.concl theorem))
      val opened = guard (fn () => G.record_opened_view_with_policy graph
        traversal
        (RP.AtMost template_cap) (#node imported))
      val proof = guard (fn () => P.record_closed_from_import_with_policy
        graph traversal
        {node = #node opened,theorem = theorem,
         template_limit = #template_limit (W.semantic_policy work),
         check_type = fn ty => guard (fn () => check_type ty)})
    in PolicyInstance {policy_matched = value,theorem = theorem,proof = proof}
      end))
  fun instance_condition_with_policy_for expected
      (policy_instance as PolicyInstance {policy_matched = value as PolicyMatch
        {policy_owner = PolicyOwner {graph,...},traversal,...},proof,...})
          index =
    ((validate_with_policy_for expected value;
      if index >= 0 then () else
        raise ERR "instance_condition_with_policy_for"
          "negative antecedent index";
      P.validate_closed_fact_with_policy graph traversal
        (#template_limit (W.semantic_policy expected)) proof;
      let val imp_id = #Name (Term.dest_thy_constid boolSyntax.implication)
          fun select current left =
            case G.view graph current of G.Application (partial,next) =>
              (case G.view graph partial of G.Application (head,ant) =>
                 (case G.view graph head of G.Constant id =>
                    if KernelSig.id_compare (id,imp_id) = EQUAL then
                      if left=0 then ant else select next (left-1)
                    else raise ERR "instance_condition_with_policy_for"
                      "absent condition"
                  | _ => raise ERR "instance_condition_with_policy_for"
                    "absent condition")
               | _ => raise ERR "instance_condition_with_policy_for"
                 "absent condition")
            | _ => raise ERR "instance_condition_with_policy_for"
              "absent condition"
          val node = select (P.closed_node proof) index
          val child = G.closure_root graph traversal node
          val _ = validate_with_policy_for expected value
      in {node=node,child=child,traversal=traversal} end)
     handle primary => (W.close expected;raise primary))
  fun instance_target_with_policy_for expected
      (PolicyInstance {policy_matched = value as PolicyMatch
        {target,caller,traversal,...},...}) =
    (validate_with_policy_for expected value;
     {node = node target,child = #child (data target),
      caller = caller,traversal = traversal})
  fun instance_fact_with_policy_for expected
      (PolicyInstance {policy_matched = value as PolicyMatch
        {policy_owner = PolicyOwner {graph,...},traversal,...},proof,...}) =
    ((validate_with_policy_for expected value;
      P.validate_closed_fact_with_policy graph traversal
        (#template_limit (W.semantic_policy expected)) proof;proof)
     handle primary => (W.close expected;raise primary))
  fun pattern_with_policy_for expected (PolicySchema
      {policy_owner=policy_owner as PolicyOwner
        {work,graph,scope,...},whole,left,right,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "pattern_with_policy_for" "foreign expected Work";
      active policy_owner;retained policy_owner scope whole;
      let val target = case right of SOME value => value
            | NONE => raise ERR "pattern_with_policy_for"
              "not a canonical equality clause"
          val l = G.representative graph (node left)
          val r = G.representative graph (node target)
          val _ = active policy_owner;val _ = retained policy_owner scope whole
      in {left=l,right=r} end)
     handle primary => (W.close expected;raise primary))

  fun instance_native_contract_for expected
      (held as PolicyInstance {policy_matched=value as PolicyMatch
        {policy_owner=PolicyOwner {native_contract,...},...},...}) =
    (validate_with_policy_for expected value;native_contract)

end
