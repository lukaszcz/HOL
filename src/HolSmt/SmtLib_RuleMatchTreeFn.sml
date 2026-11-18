(* Closure-tree walk shared by the rule matchers.  The functor applies the
   owner's `active`, `tick` and `spend` at fixed points of the walk, so each
   matcher keeps its own charges, allowances and diagnostic origin.  `active`
   is whatever validation the owner requires; for the policy owner it
   includes native-contract validation, and its `tick` also enforces the
   native matching allowance. *)
signature SmtLib_RuleMatchOwner =
sig
  type owner
  val graph : owner -> SmtReplayGraph.graph
  val scope : owner -> SmtReplayGraph.scope
  (* Owner validation: retirement, Work, catalogue and symbol epoch. *)
  val active : owner -> unit
  (* One metered control step, including the owner's own allowances. *)
  val tick : owner -> unit
  (* Debit the owner's Work portfolio. *)
  val spend : owner -> int -> unit
  (* The matcher's diagnostic origin, as Feedback.mk_HOL_ERR builds it. *)
  val err : string -> string -> exn
end

signature SmtLib_RuleMatchTree =
sig
  type owner
  type profile = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int}
  datatype shape = Atom | App of tree * tree
    | Lam of {binder : SmtReplayGraph.node,binder_type : Type.hol_type,
              body : tree}
  and tree = Tree of
    {node : SmtReplayGraph.node,child : SmtReplayGraph.closure_child,
     frame : SmtReplayGraph.scope,ty : Type.hol_type,shape : shape,
     profile : profile}
  val data : tree -> {node : SmtReplayGraph.node,
    child : SmtReplayGraph.closure_child,frame : SmtReplayGraph.scope,
    ty : Type.hol_type,shape : shape,profile : profile}
  val node : tree -> SmtReplayGraph.node
  val guarded : owner -> (unit -> 'a) -> 'a
  val add : profile -> profile -> profile
  val unit : IntInf.int -> profile
  val type_weight : owner -> Type.hol_type -> IntInf.int
  val compare_type : owner -> Type.hol_type * Type.hol_type -> order
  val closure_guard : owner -> SmtReplayGraph.scope -> SmtReplayGraph.scope ->
    SmtReplayGraph.closure_child -> SmtReplayGraph.node
  val tree : owner -> SmtReplayGraph.scope -> SmtReplayGraph.scope ->
    SmtReplayGraph.closure_child -> tree
  val const_name : owner -> tree -> {Thy : string,Name : string} option
  val head_is : owner -> string -> string -> tree -> bool
  val unary : owner -> string -> string -> tree -> tree option
  val binary : owner -> string -> string -> tree -> (tree * tree) option
  val free_nodes : owner -> tree -> SmtReplayGraph.node list
end

functor SmtLib_RuleMatchTreeFn (A : SmtLib_RuleMatchOwner) :
    SmtLib_RuleMatchTree where type owner = A.owner =
struct
  structure G = SmtReplayGraph
  type owner = A.owner
  type profile = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int}
  datatype shape = Atom | App of tree * tree
    | Lam of {binder : G.node,binder_type : Type.hol_type,body : tree}
  and tree = Tree of
    {node : G.node,child : G.closure_child,frame : G.scope,
     ty : Type.hol_type,shape : shape,profile : profile}
  fun data (Tree x) = x
  fun node tree = #node (data tree)
  fun guarded owner action =
    (A.active owner;
     let val value = action () in A.active owner;value end)
  fun add ({raw = a,inc = b,ann = c} : profile)
      ({raw = d,inc = e,ann = f} : profile) : profile =
    {raw = a+d,inc = b+e,ann = c+f}
  fun unit ann : profile = {raw = 1,inc = 1,ann = ann}
  fun type_weight owner ty =
    let fun walk current =
      (A.tick owner;
       if Type.is_vartype current then
         let val name = Type.dest_vartype current
             val _ = A.spend owner (String.size name)
         in 1 : IntInf.int end
       else let val {Thy,Tyop,Args} = Type.dest_thy_type current
                val _ = A.spend owner (String.size Thy+String.size Tyop)
            in List.foldl (fn (a,n) => n+walk a) 1 Args end)
    in guarded owner (fn () => walk ty) end
  fun compare_type owner (a,b) =
    let val _ = type_weight owner a val _ = type_weight owner b
    in guarded owner (fn () => Type.compare (a,b)) end
  fun closure_guard owner caller traversal child =
    let val graph = A.graph owner
        val scope = A.scope owner
        val _ = A.active owner
        val _ = G.validate_scope graph caller
        val _ = G.validate_scope graph traversal
        val _ = A.tick owner
        val n = G.closure_child_node graph caller child
        val _ = A.tick owner val frame = G.node_scope graph n
    in if G.scope_visible graph caller scope andalso
          G.scope_visible graph traversal caller andalso
          G.scope_visible graph traversal frame then n else
       raise A.err "closure_guard" "foreign or invisible closure path" end
  fun tree owner caller traversal child =
    let val graph = A.graph owner
        val n = closure_guard owner caller traversal child
        val _ = A.tick owner val ty = G.type_of graph n
        val ann = type_weight owner ty
        val _ = A.tick owner
        val (shape,profile) = case G.view graph n of
          G.Application _ =>
            let val _ = A.tick owner
                val (f,x) = G.closure_application_children graph caller child
                val ft = tree owner caller traversal f
                val xt = tree owner caller traversal x
            in (App (ft,xt),add (unit ann)
                 (add (#profile (data ft)) (#profile (data xt)))) end
        | G.AdmittedBinder _ =>
            let val _ = A.tick owner
                val closure = G.closure_child_binder graph caller child
                val _ = A.tick owner
                val b = G.binder_closure_data graph caller closure
                val _ = A.tick owner
                val bt = G.type_of graph (#binder b)
                val ba = type_weight owner bt
                val _ = A.tick owner
                val body = G.binder_closure_body graph caller closure
                val subtree = tree owner caller (#body_frame b) body
            in (Lam {binder = #binder b,binder_type = bt,body = subtree},
                 add {raw = 1,inc = 2,ann = ann+ba}
                   (#profile (data subtree))) end
        | G.OpaqueRetained =>
            raise A.err "tree" "relevant opaque syntax needs a genuine recipe"
        | _ => (Atom,unit ann)
    in Tree {node = n,child = child,frame = traversal,ty = ty,
      shape = shape,profile = profile} end
  fun const_name owner value =
    let val graph = A.graph owner val _ = A.tick owner
    in case G.view graph (node value) of
      G.Constant id => SOME (KernelSig.name_of_id id) | _ => NONE end
  fun head_is owner thy name value =
    case const_name owner value of
      SOME {Thy,Name} => Thy = thy andalso Name = name | NONE => false
  fun unary owner thy name value = case #shape (data value) of
      App (f,x) => if head_is owner thy name f then SOME x else NONE
    | _ => NONE
  fun binary owner thy name value = case #shape (data value) of
      App (f,y) => (case #shape (data f) of
        App (c,x) => if head_is owner thy name c then SOME (x,y) else NONE
      | _ => NONE)
    | _ => NONE
  (* SPEC_ALL stock clauses can contain genuine FREE schematic variables.
     Capture only the original whole rule's free nodes, never lambda locals. *)
  fun free_nodes owner whole =
    let val graph = A.graph owner
        fun visit bound value found =
          (A.tick owner;
           case #shape (data value) of
             App (f,x) => visit bound x (visit bound f found)
           | Lam {binder,body,...} => visit (binder::bound) body found
           | Atom => (case G.view graph (node value) of
               G.Variable _ =>
                 if List.exists (fn n => n = node value) (bound @ found)
                   then found else node value::found
             | _ => found))
    in List.rev (visit [] whole []) end
end
