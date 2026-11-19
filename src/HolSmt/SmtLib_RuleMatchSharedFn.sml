(* Compile, prepare and instantiate steps shared by the rule matchers.  The
   closure-tree walk comes from SmtLib_RuleMatchTreeFn, applied here to the
   same owner.  Each matcher keeps its own owner, schema, match and instance
   datatypes, its validation, its result constructors and its diagnostic
   origin; this functor takes the owner's operations as arguments and runs
   every metered step in the order the matchers always ran it. *)
signature SmtLib_RuleMatchSharedOwner =
sig
  include SmtLib_RuleMatchOwner
  datatype terminal = Equality | Positive | Negative
end

signature SmtLib_RuleMatchShared =
sig
  type owner
  type terminal
  structure Walk : SmtLib_RuleMatchTree where type walk_owner = owner
  datatype operation = Specialize of SmtReplayGraph.node | Select of bool
    | Undisch
  (* The resource accounting of the instantiating owner: the ordinary int
     Work (`Plain`) or the policy Work with its native contract
     (`Policied`).  An int owner is never routed through the policy
     accounting. *)
  datatype regime =
      Plain of SmtReplayInvocationWork.portfolio
    | Policied of {work : SmtReplayInvocationWork.portfolio,
                   contract : SmtReplayNativeContract.contract}
  (* One clause of a compiled rule: the routes peeled off its root. *)
  type leaf =
    {binders : SmtReplayGraph.node list,conditions : Walk.tree list,
     left : Walk.tree,right : Walk.tree option,terminal : terminal,
     operations : operation list}
  datatype found =
      Missed
    | HigherOrder
    | Found of
        {target : Walk.tree,
         types : (Type.hol_type * Type.hol_type) list,
         arguments : (SmtReplayGraph.node * Walk.tree) list,
         output : Walk.profile option}
  datatype canonical =
      (* Bridge the rule through the owner's Scope: TRANS, then EQ_MP. *)
      Bridge
      (* The owner proves its own provenance (the thunk raises otherwise). *)
    | Provenance of (unit -> unit)
  (* The text of every refusal `instantiate` raises, spelt by its owner. *)
  type words =
    {fname : string,quota : string,template : string,portfolio : string,
     collapsed : string,operand : string}
  (* The wording of the matchers over the ordinary Work. *)
  val plain_words : words
  val same_owner : string -> owner -> owner -> unit
  val leaves : owner -> string -> Walk.tree -> leaf list
  (* Metered walk over a rule list: `per_rule` turns the closure tree of the
     index-th rule into the owner's schemas. *)
  val compile_rules : owner ->
    {caller : string,scope : SmtReplayGraph.scope,original_changed : string,
     length_mismatch : string,originals : Thm.thm list,
     facts : SmtReplayProof.closed_fact list,
     validate_fact : SmtReplayProof.closed_fact -> unit,
     per_rule : int -> Thm.thm -> Walk.tree -> 'a list} -> 'a list
  val search : owner ->
    {binders : SmtReplayGraph.node list,free : SmtReplayGraph.node list,
     rigid_types : Type.hol_type list,left : Walk.tree,
     right : Walk.tree option,caller : SmtReplayGraph.scope,
     traversal : SmtReplayGraph.scope,
     target : SmtReplayGraph.closure_child,
     admit_target : Walk.tree -> unit} -> found
  val validate_match : owner -> string ->
    {known : bool,rulescope : SmtReplayGraph.scope,whole : Walk.tree,
     caller : SmtReplayGraph.scope,traversal : SmtReplayGraph.scope,
     target : Walk.tree} -> unit
  val describe :
    {rule : Thm.thm,index : int,binders : SmtReplayGraph.node list,
     free : SmtReplayGraph.node list,conditions : Walk.tree list,
     terminal : terminal,
     types : (Type.hol_type * Type.hol_type) list,
     arguments : (SmtReplayGraph.node * Walk.tree) list,
     target : Walk.tree,output : Walk.profile option} ->
    {rule : Thm.thm,rule_index : int,terminal : terminal,
     type_bindings : (Type.hol_type * Type.hol_type) list,
     arguments : (SmtReplayGraph.node * SmtReplayGraph.node) list,
     conditions : SmtReplayGraph.node list,
     missing_arguments : SmtReplayGraph.node list,
     target : SmtReplayGraph.node,output : Walk.profile option}
  val instantiate : owner -> regime ->
    {words : words,validate : unit -> unit,used : bool ref,
     check_type : Type.hol_type -> unit,whole : Walk.tree,rule : Thm.thm,
     free : SmtReplayGraph.node list,operations : operation list,
     terminal : terminal,left : Walk.tree,right : Walk.tree option,
     target : Walk.tree,traversal : SmtReplayGraph.scope,
     types : (Type.hol_type * Type.hol_type) list,
     arguments : (SmtReplayGraph.node * Walk.tree) list,
     canonical : canonical} ->
    {theorem : Thm.thm,proof : SmtReplayProof.closed_fact}
  (* The closed fact of an instance after the owner's match validation and
     the regime's closed-fact validation; any refusal retires the Work. *)
  val fact_of : owner -> regime ->
    {validate_match : unit -> unit,traversal : SmtReplayGraph.scope,
     proof : SmtReplayProof.closed_fact} -> SmtReplayProof.closed_fact
  val condition_of : owner -> regime -> string ->
    {validate_match : unit -> unit,traversal : SmtReplayGraph.scope,
     proof : SmtReplayProof.closed_fact,index : int} ->
    {node : SmtReplayGraph.node,child : SmtReplayGraph.closure_child,
     traversal : SmtReplayGraph.scope}
  val target_of : Walk.tree -> SmtReplayGraph.scope ->
    SmtReplayGraph.scope ->
    {node : SmtReplayGraph.node,child : SmtReplayGraph.closure_child,
     caller : SmtReplayGraph.scope,traversal : SmtReplayGraph.scope}
  val pattern : owner -> string ->
    {known : bool,rulescope : SmtReplayGraph.scope,whole : Walk.tree,
     left : Walk.tree,right : Walk.tree option} ->
    {left : Term.term,right : Term.term}
end

functor SmtLib_RuleMatchSharedFn (A : SmtLib_RuleMatchSharedOwner) :
    SmtLib_RuleMatchShared where type owner = A.owner
                           where type terminal = A.terminal =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure Walk = SmtLib_RuleMatchTreeFn (A)
  open Walk
  type owner = A.owner
  type terminal = A.terminal
  datatype operation = Specialize of G.node | Select of bool | Undisch
  structure W = SmtReplayInvocationWork
  structure RP = SmtReplayResourcePolicy
  structure NC = SmtReplayNativeContract
  datatype regime =
      Plain of W.portfolio
    | Policied of {work : W.portfolio,contract : NC.contract}
  type leaf =
    {binders : G.node list,conditions : tree list,left : tree,
     right : tree option,terminal : terminal,operations : operation list}
  datatype found =
      Missed
    | HigherOrder
    | Found of
        {target : tree,types : (Type.hol_type * Type.hol_type) list,
         arguments : (G.node * tree) list,output : profile option}
  datatype canonical = Bridge | Provenance of (unit -> unit)
  type words =
    {fname : string,quota : string,template : string,portfolio : string,
     collapsed : string,operand : string}
  val plain_words =
      {fname = "instantiate",quota = "prospective instance exceeds quota",
       template = "instance exceeds closed-recording template",
       portfolio = "instance portfolio exceeds original Work",
       collapsed = "type instance collapses free domains",
       operand = "proved instance differs from matched operand"}
  exception Mismatch
  exception CapturesBinder

  fun same_owner message owner other =
    if Portable.pointer_eq (owner,other) then () else
      raise A.err "same_owner" message

  (* Peel the forall, conjunction and implication routes off a rule root. *)
  fun leaves owner caller whole =
    let fun peel binders conditions operations value =
          case unary owner "bool" "!" value of
            SOME predicate => (case #shape (data predicate) of
              Lam {binder,body,...} =>
                peel (binders @ [binder]) conditions
                  (operations @ [Specialize binder]) body
            | _ => raise A.err caller "forall has no genuine lambda")
          | NONE => (case binary owner "bool" "/\\" value of
              SOME (l,r) =>
                peel binders conditions (operations @ [Select true]) l @
                peel binders conditions (operations @ [Select false]) r
            | NONE => (case binary owner "min" "==>" value of
                SOME (condition,body) =>
                  peel binders (conditions @ [condition])
                    (operations @ [Undisch]) body
              | NONE =>
                  let val (terminal,left,right) =
                    case binary owner "min" "=" value of
                      SOME (l,r) => (A.Equality,l,SOME r)
                    | NONE => (case unary owner "bool" "~" value of
                        SOME p => (A.Negative,p,NONE)
                      | NONE => (A.Positive,value,NONE))
                  in [{binders = binders,conditions = conditions,left = left,
                       right = right,terminal = terminal,
                       operations = operations}] end))
    in peel [] [] [] whole end

  fun compile_rules owner {caller,scope,original_changed,length_mismatch,
      originals,facts,validate_fact,per_rule} =
    let val graph = A.graph owner
        fun loop [] [] _ = []
          | loop (rule::rest) (fact::more) index =
            let val _ = A.tick owner
                val n = P.closed_node fact
                val _ = validate_fact fact
                val _ = if Portable.pointer_eq
                  (rule,P.closed_original fact) then () else
                  raise A.err caller original_changed
                val root = G.closure_root graph scope n
                val whole = tree owner scope scope root
            in per_rule index rule whole @ loop rest more (index+1) end
          | loop _ _ _ = raise A.err caller length_mismatch
    in loop originals facts 0 end

  (* The pattern is matched against one target.  `rigid_types` are never
     bound (a local context's Hyp types); `admit_target` is the owner's
     check on the freshly walked target. *)
  fun search owner {binders,free,rigid_types,left,right,caller,traversal,
      target,admit_target} =
    let val graph = A.graph owner
        val _ = A.active owner
        val variables = binders @ free
        val actual = tree owner caller traversal target
        val _ = admit_target actual
        val types = ref ([] : (Type.hol_type * Type.hol_type) list)
        val arguments = ref ([] : (G.node * tree) list)
        fun lookup equal key pending = case pending of
          [] => NONE
        | (k,v)::rest => (A.tick owner;
            if equal (key,k) then SOME v else lookup equal key rest)
        fun type_match pattern actual =
          (A.tick owner;
           if Type.is_vartype pattern then
             (if List.exists (fn rigid =>
                 compare_type owner (rigid,pattern) = EQUAL) rigid_types then
                if compare_type owner (pattern,actual) = EQUAL then ()
                  else raise Mismatch
              else case lookup
                (fn (a,b) => compare_type owner (a,b) = EQUAL)
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
          (A.tick owner;
           List.exists (fn (_,target) => node value = target) bound orelse
           (case #shape (data value) of
              App (f,x) => captures bound f orelse captures bound x
            | Lam {body,...} => captures bound body | Atom => false))
        fun same bound p a =
          (A.tick owner;
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
          (type_match (#ty (data p)) (#ty (data a));A.tick owner;
           if List.exists (fn b => b = node p) variables then
             (if captures bound a then raise CapturesBinder else ();
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
          (A.tick owner;
           case lookup (fn (a,b) => compare_type owner (a,b) = EQUAL)
               ty (!types) of
             SOME target => type_weight owner target
           | NONE => if Type.is_vartype ty then type_weight owner ty
             else let val {Args,...} = Type.dest_thy_typeid ty
                  in List.foldl (fn (a,n) => n+output_type a) 1 Args end)
        fun forecast value =
          (A.tick owner;
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
            in Found {target = actual,types = List.rev (!types),
              arguments = List.rev (!arguments),output = output} end)
           handle Mismatch => Missed | CapturesBinder => HigherOrder)
        val _ = A.active owner
    in result end

  (* Every retained descendant is checked, not just the root node. No
     callback can turn a completed subtree into a cross-callback cache. *)
  fun retained owner caller value =
    let val graph = A.graph owner val d = data value
        val _ = G.validate_scope graph caller
        val _ = G.validate_scope graph (#frame d)
        val _ = if G.closure_child_node graph caller (#child d) = #node d
          then () else raise A.err "retained" "closure identity changed"
    in case #shape d of
        Atom => ()
      | App (f,x) => (retained owner caller f;retained owner caller x)
      | Lam {body,...} => retained owner caller body end

  fun validate_match owner caller_name {known,rulescope,whole,caller,
      traversal,target} =
    let val graph = A.graph owner val scope = A.scope owner
    in (if known then () else
          raise A.err caller_name "foreign Work match";
        A.active owner;
        G.validate_scope graph caller;G.validate_scope graph traversal;
        if G.scope_visible graph caller scope andalso
            G.scope_visible graph traversal caller andalso
            G.scope_visible graph traversal
              (G.node_scope graph (node target))
          then () else raise A.err caller_name "invisible retained match";
        retained owner rulescope whole;retained owner caller target) end

  fun describe {rule,index,binders,free,conditions,terminal,types,arguments,
      target,output} =
    {rule = rule,rule_index = index,terminal = terminal,
     type_bindings = types,
     arguments = List.map (fn (b,t) => (b,node t)) arguments,
     conditions = List.map node conditions,
     missing_arguments = List.filter (fn b =>
       not (List.exists (fn (k,_) => b = k) arguments)) (binders @ free),
     target = node target,output = output}

  (* Limits and charges of the instantiating owner's Work.  The int regime
     compares plain ints; the policy regime also consults its policy caps and
     debits the IntInf quote itself. *)
  fun budget (Plain work) =
      {limit = IntInf.fromInt (W.work_limit work),
       output_cap = IntInf.fromInt (#output_limit (W.semantic_limits work)),
       template_cap =
         IntInf.fromInt (#template_limit (W.semantic_limits work)),
       allows_output = fn (_ : IntInf.int) => true,
       allows_template = fn (_ : IntInf.int) => true,
       allows_quote = fn (_ : IntInf.int) => true,
       debit = fn quote => W.spend work (IntInf.toInt quote)}
    | budget (Policied {work,contract}) =
      let val native = NC.for_work work contract
          val metadata = W.semantic_policy work
      in {limit = IntInf.fromInt (#type_work_limit native),
          output_cap =
            IntInf.fromInt (#output_limit (#semantic_limits native)),
          template_cap =
            IntInf.fromInt (#template_limit (#semantic_limits native)),
          allows_output = RP.allows (#output_limit metadata),
          allows_template = RP.allows (#template_limit metadata),
          allows_quote = fn quote =>
            RP.allows (W.remaining_policy work) quote,
          debit = fn quote => W.spend_policy work quote} end

  fun instantiate owner regime {words,validate,used,check_type,whole,rule,
      free,operations,terminal,left,right,target,traversal,types,arguments,
      canonical} =
    let
      val graph = A.graph owner val scope = A.scope owner
      val {fname,quota,template,portfolio,collapsed,operand} = words
      val err = A.err fname
      val _ = A.active owner
      val _ = if !used then raise err "match already consumed" else ()
      val _ = validate ()
      val _ = used := true
      val {limit,output_cap,template_cap,allows_output,allows_template,
           allows_quote,debit} = budget regime
      fun find equal key pending = case pending of [] => NONE
        | (k,v)::rest => (A.tick owner;
            if equal (key,k) then SOME v else find equal key rest)
      fun mapped_weight ty =
        (A.tick owner;
         if Type.is_vartype ty then
           (case find (fn (a,b) => compare_type owner (a,b) = EQUAL)
                ty types of
              NONE => type_weight owner ty | SOME t => type_weight owner t)
         else let val {Args,...} = Type.dest_thy_typeid ty
              in List.foldl (fn (a,n) => n+mapped_weight a) 1 Args end)
      val annotations = ref ([] : Type.hol_type list)
      val actual_annotations = ref ([] : Type.hol_type list)
      fun actual_types current =
        let val d = data current val _ = A.tick owner
            val _ = actual_annotations := #ty d :: !actual_annotations
        in case #shape d of Atom => ()
          | App (f,x) => (actual_types f;actual_types x)
          | Lam {binder_type,body,...} =>
              (actual_annotations := binder_type :: !actual_annotations;
               actual_types body) end
      fun profile substitutions current =
        let val d = data current val _ = A.tick owner
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
                andalso allows_output (#raw p) andalso
                allows_output (#inc p) andalso #ann full <= limit then () else
              raise err quota
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
          (A.tick owner;
           case operation of
             Specialize binder =>
               let val predicate = case unary owner "bool" "!" current of
                     SOME p => p | NONE =>
                       raise err "prepared forall route changed"
                   val body = case #shape (data predicate) of
                     Lam {body,...} => body | _ =>
                       raise err "missing prepared binder"
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
                       raise err "prepared conjunction changed"
                   val next = if choose_left then l else r
                   val _ = record hypotheses (profile substitutions next)
               in play rest next substitutions hypotheses end
           | Undisch =>
               let val (condition,body) =
                     case binary owner "min" "==>" current of
                       SOME p => p | NONE =>
                         raise err "prepared implication changed"
                   val h = profile substitutions condition
                   val _ = record [h] h (* ASSUME local condition *)
                   val hypotheses = h::hypotheses
                   val _ = record hypotheses (profile substitutions body)
               in play rest body substitutions hypotheses end)
      val (_,substitutions,hypotheses) =
        play operations whole free_substitutions []
      val p = profile substitutions left
      val terminal_profile = case terminal of
          A.Equality => (case right of SOME r =>
            let val rhs = profile substitutions r
                val t = mapped_weight (#ty (data left))
            in add {raw = 3,inc = 3,ann = 6+3*t} (add p rhs) end
          | NONE => raise err "equality route missing right side")
        | A.Positive =>
            (ignore (record []
              {raw = 2 * #raw p+7,inc = 2 * #inc p+7,ann = 2 * #ann p+19});
             add p {raw = 4,inc = 4,ann = 10})
        | A.Negative =>
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
          allows_template (#raw final) andalso
          allows_template (#inc final) then () else
        raise err template
      val _ = record [] p (* prospective operand comparison *)
      val _ = record [] (equality final) (* genuine G import bridge *)
      val _ = record [] (equality final) (* genuine G opened bridge *)
      val _ = record [] (equality final) (* P retained bridge TRANS *)
      val _ = record [] final (* original closed recording EQ_MP *)
      val quote = List.foldl (fn (p,n) =>
          n + #raw p + #inc p + #ann p) (0 : IntInf.int) (!forecasts)
      val _ = if quote <= limit andalso allows_quote quote then debit quote
        else raise err portfolio
      fun guard action =
        (validate ();
         let val result = action ()
         in validate ();result end)
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
                 raise err collapsed
             else ()) rest;unique rest)
      val _ = unique free_terms
      val _ = List.app (fn ty => guard (fn () => check_type ty)) checked_types
      val canonical = case canonical of
          Bridge =>
            let val (imported,opened) = guard (fn () =>
                  G.imported_opened_source graph scope (Thm.concl rule)
                    (node whole))
                val bridge = guard (fn () =>
                  Thm.TRANS (#bridge imported) (#bridge opened))
            in guard (fn () => Thm.EQ_MP bridge rule) end
        | Provenance check => guard (fn () => (check ();rule))
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
      val body = case terminal of A.Equality => body
        | A.Positive => guard (fn () => Drule.EQT_INTRO body)
        | A.Negative => guard (fn () => Drule.EQF_INTRO body)
      val theorem = List.foldl (fn (condition,th) =>
        guard (fn () => Thm.DISCH condition th)) body conditions
      val _ = if null (Thm.hyp theorem) then () else
        raise err "temporary condition hypotheses escaped"
      fun consequent current =
        if boolSyntax.is_imp current then
          consequent (#2 (boolSyntax.dest_imp current)) else current
      val actual_left = guard (fn () =>
        boolSyntax.lhs (consequent (Thm.concl theorem)))
      val wanted = guard (fn () => G.representative graph (node target))
      val _ = if guard (fn () => Term.aconv actual_left wanted) then () else
        raise err operand
      val guarded_check = fn ty => guard (fn () => check_type ty)
      val proof = case regime of
          Plain work =>
            let val template_limit = #template_limit (W.semantic_limits work)
                val imported = guard (fn () => G.import graph traversal
                  template_limit (Thm.concl theorem))
                val opened = guard (fn () => G.record_opened_view graph
                  traversal template_limit (#node imported))
            in guard (fn () => P.record_closed_from_import graph traversal
                 {node = #node opened,theorem = theorem,
                  template_limit = template_limit,
                  check_type = guarded_check}) end
        | Policied {work,contract} =>
            let val native = NC.for_work work contract
                val imported = guard (fn () => G.import_with_policy graph
                  traversal (RP.AtMost (IntInf.fromInt (#import_limit native)))
                  (Thm.concl theorem))
                val opened = guard (fn () => G.record_opened_view_with_policy
                  graph traversal (RP.AtMost template_cap) (#node imported))
            in guard (fn () => P.record_closed_from_import_with_policy
                 graph traversal
                 {node = #node opened,theorem = theorem,
                  template_limit = #template_limit (W.semantic_policy work),
                  check_type = guarded_check}) end
    in {theorem = theorem,proof = proof} end

  fun regime_work (Plain work) = work
    | regime_work (Policied {work,...}) = work

  (* Closed-fact validation under the template limit of the regime. *)
  fun validate_proof owner regime traversal proof =
    let val graph = A.graph owner
    in case regime of
         Plain work => P.validate_closed_fact graph traversal
           (#template_limit (W.semantic_limits work)) proof
       | Policied {work,...} => P.validate_closed_fact_with_policy graph
           traversal (#template_limit (W.semantic_policy work)) proof end

  fun fact_of owner regime {validate_match,traversal,proof} =
    ((validate_match ();validate_proof owner regime traversal proof;proof)
     handle primary => (W.close (regime_work regime);raise primary))

  fun condition_of owner regime caller {validate_match,traversal,proof,
      index} =
    let val graph = A.graph owner
    in (validate_match ();
       if index >= 0 then () else
         raise A.err caller "negative antecedent index";
       validate_proof owner regime traversal proof;
       let val imp_id = #Name (Term.dest_thy_constid boolSyntax.implication)
           fun absent () = raise A.err caller "absent condition"
           fun select current left =
             case G.view graph current of G.Application (partial,next) =>
               (case G.view graph partial of G.Application (head,ant) =>
                  (case G.view graph head of G.Constant id =>
                     if KernelSig.id_compare (id,imp_id) = EQUAL then
                       if left=0 then ant else select next (left-1)
                     else absent ()
                   | _ => absent ())
                | _ => absent ())
             | _ => absent ()
           val node = select (P.closed_node proof) index
           val child = G.closure_root graph traversal node
           val _ = validate_match ()
       in {node=node,child=child,traversal=traversal} end)
       handle primary => (W.close (regime_work regime);raise primary) end

  fun target_of target caller traversal =
    {node = node target,child = #child (data target),
     caller = caller,traversal = traversal}

  fun pattern owner caller {known,rulescope,whole,left,right} =
    let val graph = A.graph owner
    in (if known then () else raise A.err caller "foreign expected Work";
        A.active owner;retained owner rulescope whole;
        let val target = case right of SOME value => value
              | NONE => raise A.err caller "not a canonical equality clause"
            val l = G.representative graph (node left)
            val r = G.representative graph (node target)
            val _ = A.active owner;val _ = retained owner rulescope whole
        in {left=l,right=r} end) end
end
