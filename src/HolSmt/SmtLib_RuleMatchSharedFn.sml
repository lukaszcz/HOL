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
  val same_owner : string -> Walk.walk_owner -> Walk.walk_owner -> unit
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
  val retained : owner -> SmtReplayGraph.scope -> Walk.tree -> unit
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
  val condition_of : owner -> string ->
    {validate_match : unit -> unit,validate_fact : unit -> unit,
     traversal : SmtReplayGraph.scope,proof : SmtReplayProof.closed_fact,
     index : int} ->
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
  type leaf =
    {binders : G.node list,conditions : tree list,left : tree,
     right : tree option,terminal : terminal,operations : operation list}
  datatype found =
      Missed
    | HigherOrder
    | Found of
        {target : tree,types : (Type.hol_type * Type.hol_type) list,
         arguments : (G.node * tree) list,output : profile option}
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

  fun condition_of owner caller {validate_match,validate_fact,traversal,proof,
      index} =
    let val graph = A.graph owner
    in validate_match ();
       if index >= 0 then () else
         raise A.err caller "negative antecedent index";
       validate_fact ();
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
       in {node=node,child=child,traversal=traversal} end end

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
