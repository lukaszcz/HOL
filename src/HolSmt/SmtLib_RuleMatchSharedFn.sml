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
end
