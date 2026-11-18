(* Shared closure-tree walk of the rule matchers.  Each matcher supplies its
   own abstract owner together with the owner's validation (`active`), its
   metered `tick` and its Work spending; the functor applies them at exactly
   the points the matchers used before, so charges and diagnostics keep
   their order and origin. *)
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

functor SmtLib_RuleMatchTreeFn (A : SmtLib_RuleMatchOwner) =
struct
  structure G = SmtReplayGraph
  val _ = SmtReplayGraph.closure_root
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
