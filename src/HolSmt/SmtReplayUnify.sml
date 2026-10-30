(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayUnify :> SmtReplayUnify =
struct
  open SmtReplayGraph
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtReplayUnify"
  type assignment = {variable : G.node, residue : G.node}
  datatype assumption_kind = ConstructorEquation of G.node
    | SolverAssignment of assignment
    | BinderEquality of G.node * G.node
  type assumption = {kind : assumption_kind, equation : Term.term}
  datatype failure = TypeMismatch | RigidMismatch | OccursCheck
    | NeedsBinderAdmission | EscapingScope
  datatype result = Result of
    {graph : G.graph, scope : G.scope,
     assignments : assignment list, assumptions : assumption list,
     roots : G.node list, context : Term.term,
     proofs : ((G.node * G.node) * Thm.thm) list,
     projections : Thm.thm vector}
  datatype outcome = Unified of result | NoMatch of failure
  fun validate_result graph scope (Result {graph = owner,scope = frame,...}) =
    (G.validate_scope graph scope;
     G.validate_scope owner frame;
     if G.root_scope graph = G.root_scope owner andalso scope = frame then ()
     else raise ERR "validate_result" "result belongs to another graph/scope")
  fun assignments (Result {assignments,...}) = assignments
  fun assumptions (Result {assumptions,...}) = assumptions
  fun roots (Result {roots,...}) = roots
  fun context (Result {graph,scope,context,...}) =
    (G.validate_scope graph scope; context)
  fun proofs (Result {graph,scope,proofs,...}) =
    (G.validate_scope graph scope; proofs)
  fun projection (Result {graph,scope,projections,...}) index =
    (G.validate_scope graph scope;
    if index >= 0 andalso index < Vector.length projections then
      Vector.sub (projections,index)
    else raise ERR "projection" "unknown dependency leaf")
  fun pair_compare ((a,b),(c,d)) =
    case Int.compare (a,c) of EQUAL => Int.compare (b,d) | order => order

  datatype boundary = Empty | Leaf of int | Split of boundary * boundary
  fun split start count =
    if count = 0 then Empty
    else if count = 1 then Leaf start
    else let val half = count div 2 in
      Split (split start half,split (start+half) (count-half)) end
  fun balanced terms Empty = boolSyntax.T
    | balanced terms (Leaf index) = Vector.sub (terms,index)
    | balanced terms (Split (left,right)) =
        boolSyntax.mk_conj (balanced terms left,balanced terms right)
  fun project Empty _ = []
    | project (Leaf _) theorem = [theorem]
    | project (Split (left,right)) theorem =
        project left (Thm.CONJUNCT1 theorem) @
        project right (Thm.CONJUNCT2 theorem)

  fun unify_with_binders graph discover {scope,flexible,equations,binders} =
    let
      exception Mismatch of failure
      val _ = G.validate_scope graph scope
      fun check_node node = ignore (G.type_of graph node)
      fun allowed (node,table) =
        (check_node node;
         case G.view graph node of
           G.Variable (G.SolverFlexible,_) =>
             if G.scope_visible graph scope (G.node_scope graph node) then
               Redblackset.add (table,G.node_id node)
             else raise ERR "unify" "flexible node outside active scope"
         | _ => raise ERR "unify" "permission to assign a rigid variable")
      val permitted = List.foldl allowed
        (Redblackset.empty Int.compare) flexible
      val _ = List.app (fn (left,right) =>
        (check_node left;check_node right)) equations
      fun pair_key left right = if G.node_id left < G.node_id right then
          (G.node_id left,G.node_id right)
        else (G.node_id right,G.node_id left)
      fun binder ((left,right),table) =
        let
          fun valid node =
            (check_node node;
             if G.scope_visible graph scope (G.node_scope graph node) then ()
             else raise ERR "unify_using" "binder outside active scope";
             case G.view graph node of G.AdmittedBinder _ => ()
               | _ => raise ERR "unify_using" "unadmitted binder obligation")
          val _ = valid left
          val _ = valid right
          val _ = if G.type_id graph left = G.type_id graph right then ()
            else raise ERR "unify_using" "binder obligation type mismatch"
        in Redblackmap.insert (table,pair_key left right,(left,right)) end
      val admitted = List.foldl binder (Redblackmap.mkDict pair_compare) binders
      val used_binders = ref (Redblackmap.mkDict pair_compare)
      val substitution = ref
        (Redblackmap.mkDict Int.compare : (int,assignment) Redblackmap.dict)
      fun flexible_node node =
        Redblackset.member (permitted,G.node_id node)
      fun assigned node =
        Redblackmap.peek (!substitution,G.node_id node)
      fun dereference node = case assigned node of
          SOME {residue,...} => dereference residue | NONE => node
      fun same_type left right =
        if G.type_id graph left = G.type_id graph right then ()
        else raise Mismatch TypeMismatch
      fun scope_leaf declaration node = case G.view graph node of
          G.Variable _ =>
            if G.scope_visible graph declaration (G.node_scope graph node)
            then ()
            else raise Mismatch EscapingScope
        | _ => ()
      (* Follow assignment edges too. A binder frame removes only its own
         bound IDs; an opaque atom cannot certify an occurs/scope absence. *)
      fun admissible_residue variable residue =
        let
          val declaration = G.node_scope graph variable
          fun visit [] _ = ()
            | visit ((node,excluded)::rest) visited =
              let
                val node = dereference node
                val key = (G.node_id node,Redblackset.listItems excluded)
              in
                if node = variable then raise Mismatch OccursCheck
                else if Redblackset.member (visited,key) then
                  visit rest visited
                else
                  let
                    val visited = Redblackset.add (visited,key)
                    fun next pending = visit pending visited
                  in case G.view graph node of
                      G.OpaqueRetained => raise Mismatch NeedsBinderAdmission
                    | G.Application (left,right) =>
                        next ((left,excluded)::(right,excluded)::rest)
                    | G.AdmittedBinder {binder,body,...} =>
                        next ((body,Redblackset.add
                          (excluded,G.node_id binder))::rest)
                    | G.Variable (G.Bound,_) =>
                        (if Redblackset.member (excluded,G.node_id node) then
                           () else scope_leaf declaration node;
                         next rest)
                    | _ => (scope_leaf declaration node;next rest)
                  end
              end
          fun compare ((a,xs),(b,ys)) = case Int.compare (a,b) of
              EQUAL => List.collate Int.compare (xs,ys) | order => order
        in visit [(residue,Redblackset.empty Int.compare)]
          (Redblackset.empty compare) end
      fun orient left right =
        let
          val left_scope = G.node_scope graph left
          val right_scope = G.node_scope graph right
          val left_name = #1 (Term.dest_var (G.representative graph left))
          val right_name = #1 (Term.dest_var (G.representative graph right))
        in if left_scope <> right_scope then
             if G.scope_visible graph left_scope right_scope then
               (left,right)
             else if G.scope_visible graph right_scope left_scope then
               (right,left)
             else raise Mismatch EscapingScope
           else case String.compare (left_name,right_name) of
            LESS => (left,right) | GREATER => (right,left)
          | EQUAL => if G.node_id left < G.node_id right then (left,right)
                     else (right,left)
        end
      fun assign variable residue =
        (same_type variable residue;
         admissible_residue variable residue;
         substitution := Redblackmap.insert (!substitution,
           G.node_id variable,{variable = variable,residue = residue}))
      val compared = ref (Redblackset.empty pair_compare)
      fun search [] = ()
        | search ((original_left,original_right)::pending) =
          let
            val _ = List.app (fn node =>
              if G.scope_visible graph scope (G.node_scope graph node) then ()
              else raise Mismatch EscapingScope)
              [original_left,original_right]
            val left = dereference original_left
            val right = dereference original_right
            val _ = same_type left right
            val pair = if G.node_id left < G.node_id right then
                (G.node_id left,G.node_id right)
              else (G.node_id right,G.node_id left)
          in
            if Redblackset.member (!compared,pair) then search pending
            else
              (compared := Redblackset.add (!compared,pair);
            if left = right then search pending
            else if flexible_node left andalso flexible_node right then
              let val (variable,residue) = orient left right in
                assign variable residue;search pending end
            else if flexible_node left then
              (assign left right;search pending)
            else if flexible_node right then
              (assign right left;search pending)
            else
              case (G.view graph left,G.view graph right) of
                (G.Application (lf,lx),G.Application (rf,rx)) =>
                  search ((lf,rf)::(lx,rx)::pending)
              | (G.OpaqueRetained,_) => raise Mismatch NeedsBinderAdmission
              | (_,G.OpaqueRetained) => raise Mismatch NeedsBinderAdmission
              | (G.AdmittedBinder _,G.AdmittedBinder _) =>
                  (case Redblackmap.peek (admitted,pair_key left right) of
                       SOME relation =>
                         (used_binders := Redblackmap.insert
                           (!used_binders,pair_key left right,relation);
                          search pending)
                     | NONE =>
                         (case discover (left,right) of
                              NONE => raise Mismatch NeedsBinderAdmission
                            | SOME assignments =>
                                (used_binders := Redblackmap.insert
                                   (!used_binders,pair_key left right,
                                    (left,right));
                                 search (List.map
                                   (fn {variable,residue} =>
                                     if flexible_node variable then
                                       (variable,residue)
                                     else raise ERR "unify_with_binders"
                                       "binder assigned an unpermitted node")
                                   assignments @ pending))))
              | _ => raise Mismatch RigidMismatch)
          end
      val searched = (search equations;NONE)
        handle Mismatch reason => SOME reason
    in case searched of
        SOME reason => NoMatch reason
      | NONE =>
        let
          (* Order dependencies before users without constructing normalized
             expanded residues or retaining variable sets at every node. *)
          val ordered = ref ([] : assignment list)
          val visited = ref (Redblackset.empty Int.compare)
          fun order node =
            if Redblackset.member (!visited,G.node_id node) then () else
            (visited := Redblackset.add (!visited,G.node_id node);
             case assigned node of
               SOME (assignment as {residue,...}) =>
                 (order residue;ordered := assignment :: !ordered)
             | NONE => case G.view graph node of
                 G.Application (left,right) => (order left;order right)
               | G.AdmittedBinder {body,...} => order body
               | _ => ())
          val _ = Redblackmap.app
            (fn (_, {variable,...}) => order variable) (!substitution)
          val assignments = List.rev (!ordered)
          (* Callback assignments can name variables found only beneath a
             binder boundary. Every name in the compact assignment context
             must participate in realization, not just its residue. Keep the
             traversal block-local; do not open binder bodies to find them. *)
          val roots = G.block_reachable graph
            (List.concat
              (List.map (fn (left,right) => [left,right]) equations) @
             List.concat (List.map (fn {variable,residue} =>
               [variable,residue]) assignments))
          val binder_relations = List.map #2
            (Redblackmap.listItems (!used_binders))
          fun name node = G.placeholder graph node
          fun constructor node = case G.view graph node of
              G.Application (operator,operand) =>
                [{kind = ConstructorEquation node,
                  equation = boolSyntax.mk_eq
                    (name node,Term.mk_comb (name operator,name operand))}]
            | _ => []
          fun solver (assignment as {variable,residue}) =
            {kind = SolverAssignment assignment,
             equation = boolSyntax.mk_eq (name variable,name residue)}
          fun relation (left,right) =
            {kind = BinderEquality (left,right),
             equation = boolSyntax.mk_eq (name left,name right)}
          val assumptions = List.concat (List.map constructor roots) @
            List.map solver assignments @ List.map relation binder_relations
          val leaves = Vector.fromList assumptions
          val tree = split 0 (Vector.length leaves)
          val context = balanced (Vector.map #equation leaves) tree
          val projections = Vector.fromList
            (project tree (Thm.ASSUME context))
          val constructors = ref (Redblackmap.mkDict Int.compare)
          val solvers = ref (Redblackmap.mkDict Int.compare)
          val relations = ref (Redblackmap.mkDict pair_compare)
          val _ = Vector.appi (fn (index,{kind,...}) => case kind of
              ConstructorEquation node => constructors := Redblackmap.insert
                (!constructors,G.node_id node,Vector.sub (projections,index))
            | SolverAssignment {variable,...} =>
                solvers := Redblackmap.insert
                  (!solvers,G.node_id variable,Vector.sub (projections,index))
            | BinderEquality (left,right) =>
                relations := Redblackmap.insert
                  (!relations,pair_key left right,
                   (left,right,Vector.sub (projections,index))))
            leaves
          val memo = ref (Redblackmap.mkDict pair_compare)
          fun proof left right =
            case Redblackmap.peek (!memo,(G.node_id left,G.node_id right)) of
              SOME theorem => theorem
            | NONE =>
              let
                val theorem =
                  if left = right then Thm.REFL (name left)
                  else case assigned left of
                      SOME {residue,...} =>
                        Thm.TRANS (Redblackmap.find (!solvers,G.node_id left))
                          (proof residue right)
                    | NONE => case assigned right of
                        SOME {residue,...} =>
                          Thm.TRANS (proof left residue)
                            (Thm.SYM (Redblackmap.find
                              (!solvers,G.node_id right)))
                      | NONE => case (G.view graph left,G.view graph right) of
                          (G.Application (lf,lx),G.Application (rf,rx)) =>
                            Thm.TRANS (Redblackmap.find
                              (!constructors,G.node_id left))
                              (Thm.TRANS (Thm.MK_COMB
                                (proof lf rf,proof lx rx))
                                (Thm.SYM (Redblackmap.find
                                  (!constructors,G.node_id right))))
                        | _ =>
                            (case Redblackmap.peek
                                (!relations,pair_key left right) of
                                 SOME (saved_left,_,theorem) =>
                                   if left = saved_left then theorem
                                   else Thm.SYM theorem
                               | NONE => raise ERR "unify"
                                   "successful search has no witness")
                val _ = memo := Redblackmap.insert
                  (!memo,(G.node_id left,G.node_id right),theorem)
              in theorem end
          val proofs = List.map (fn (left,right) =>
            ((left,right),proof left right)) equations
        in Unified (Result
          {graph = graph,scope = scope,assignments = assignments,
           assumptions = assumptions,roots = roots,
           context = context,proofs = proofs,projections = projections}) end
    end
  fun unify_using graph input = unify_with_binders graph (fn _ => NONE) input
  fun unify graph {scope,flexible,equations} = unify_using graph
    {scope = scope,flexible = flexible,equations = equations,binders = []}
end
