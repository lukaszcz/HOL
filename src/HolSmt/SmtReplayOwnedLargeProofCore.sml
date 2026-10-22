structure SmtReplayOwnedLargeProofCore :> SmtReplayOwnedLargeProofCore =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure Scope = SmtReplayOwnedScopeReceipt
  val _ = SmtReplayOwnedScopeReceipt.description_for
  structure P = SmtReplayProof
  val _ = SmtReplayProof.prepare_owned_realization_tables
  structure C = SmtReplayCanonGraph
  val _ = SmtReplayCanonGraph.graph_recipe_steps
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedLargeProofCore"
  type owner = {graph : G.graph,root : G.scope,scope : G.scope,
                frame : Scope.receipt,sources : S.sources,
                work : W.portfolio,limits : W.limits,epoch : int,
                symbols : int}
  datatype shape = Actual of Type.hol_type | Boolean | Arrow of shape * shape
  type size = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int,
               ty : IntInf.int,shape : shape}
  type summary =
    {leaves : int,steps : int,public_operations : int,
     assembly_work : IntInf.int,realization_work : IntInf.int,
     dictionary_work : IntInf.int,type_projection_work : IntInf.int,
     compact_context : IntInf.int * IntInf.int * IntInf.int,
     comparison_context : IntInf.int * IntInf.int * IntInf.int}
  datatype held = Held of G.closure_child
    | OpaqueProjection of {node:G.node,depth:IntInf.int,
                           receipt:G.opaque_type_projection}
  datatype plan = Plan of
    {owner : owner,graph_conversion : C.graph_conversion,
     roots : G.node list,facts : P.closed_fact list,
     conversions : P.closed_conversion list,held : held list,
     tables : P.realization_tables_plan,
     types : shape list,check_type : Type.hol_type -> unit,
     summary : summary,used : bool ref}
  datatype result = Result of {plan : plan,receipt : P.realization}
  datatype tree = Empty | Leaf of size * size | Split of tree * tree
  fun protected work action = action ()
    handle primary => (W.close work;raise primary)
  fun active (owner : owner) =
    (W.validate (#work owner) (#graph owner) (#root owner)
       (#sources owner) (#limits owner);
     let val actual = Scope.description_for (#work owner) (#frame owner)
     in if Portable.pointer_eq (#graph actual,#graph owner) andalso
         #root actual = #root owner andalso #scope actual = #scope owner andalso
         Portable.pointer_eq (#sources actual,#sources owner) then () else
       raise ERR "active" "authentic traversal frame differs" end;
     if Type.type_epoch () = #epoch owner andalso
         Term.term_epoch () = #symbols owner then () else
       raise ERR "active" "type or term retirement epoch changed")
  fun validate work (Plan {owner,graph_conversion,roots,facts,conversions,
                           held,tables,...}) =
    protected work (fn () =>
      (if Portable.pointer_eq (work,#work owner) then () else
         raise ERR "validate" "different original Work";
       C.validate_conversion_for work graph_conversion;
       active owner;P.validate_realization_tables work tables;
       List.app (fn node =>
         if G.scope_visible (#graph owner) (#scope owner)
             (G.node_scope (#graph owner) node) then () else
           raise ERR "validate" "retained recipe root escapes owner") roots;
       List.app (P.validate_closed_fact (#graph owner) (#scope owner)
         (#template_limit (#limits owner))) facts;
       List.app (P.validate_conversion_for work) conversions;
       List.app (P.validate_conversion (#graph owner) (#scope owner)
         (#template_limit (#limits owner))) conversions;
       List.app (fn Held child =>
           ignore (G.closure_child_node (#graph owner) (#scope owner) child)
         | OpaqueProjection {node,depth,receipt} =>
             if #node (G.opaque_type_projection_data (#graph owner)
                 (#scope owner) receipt depth) = node then () else
               raise ERR "validate" "opaque projection owner differs")
         held;active owner))
  fun report (Plan {summary,...}) = summary

  fun prepare_in_scope work {frame,conversion,ordinal,check_type} =
    protected work (fn () =>
    W.with_step work (fn () =>
    let
      val incoming = Scope.description_for work frame
      val sources = #sources incoming
      val graph = #graph incoming and scope = #scope incoming
      val limits = W.semantic_limits work
      val owner = {graph = graph,root = #root incoming,scope = scope,
        frame = frame,sources = sources,work = work,limits = limits,
        epoch = Type.type_epoch (),symbols = Term.term_epoch ()} : owner
      val _ = if ordinal >= 0 then () else
        raise ERR "prepare" "negative assembly ordinal"
      val _ = active owner
      (* Passive diagnostics only; no proof getter or guard is delegated. *)
      val diagnostics =
        (OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS" = SOME "1")
        handle _ => false
      fun phase label describe = if not diagnostics then () else
        ((let val audit = W.audit work
          in TextIO.output (TextIO.stdErr,
            "CORE_WORK phase=" ^ label ^ " charged=" ^
            Int.toString (#charged audit) ^ " retired=" ^
            Bool.toString (#retired audit) ^ describe () ^ "\n");
            TextIO.flushOut TextIO.stdErr end) handle _ => ())
      val _ = phase "prepare.entry" (fn () =>
        " ordinal=" ^ Int.toString ordinal)
      val converted = conversion
      val _ = C.validate_conversion_for work converted
      val ceiling = IntInf.fromInt (W.work_limit work)
      val cap = IntInf.fromInt (#template_limit limits)
      fun plus a b = IntInf.min (ceiling+1,a+b)
      fun times a b = IntInf.min (ceiling+1,a*b)
      fun charge () = (active owner;W.spend work 1)
      fun lookup key [] = NONE
        | lookup key ((old,value)::rest) =
            (charge ();if old = key then SOME value else lookup key rest)
      val _ = charge ()
      val held = ref ([] : held list)
      val _ = charge ()
      val policies = ref ([] : shape list)
      fun same_shape (Actual a) (Actual b) =
            (charge ();Portable.pointer_eq (a,b))
        | same_shape Boolean Boolean = (charge ();true)
        | same_shape (Arrow (a,b)) (Arrow (c,d)) =
            (charge ();same_shape a c andalso same_shape b d)
        | same_shape _ _ = (charge ();false)
      fun save_shape shape =
        let fun seen [] = false
              | seen (old::rest) =
                  (charge ();same_shape old shape orelse seen rest)
        in if seen (!policies) then () else
          (charge ();policies := shape :: !policies) end
      fun save_type ty = save_shape (Actual ty)
      (* Borrow original argument spines; no Args@pending copy. *)
      fun type_size ty =
        let fun walk [] total = total
              | walk (pending::more) total =
                (charge ();case pending of [] => walk more total
                 | current::rest =>
                   let val _ = charge ()
                       (* Type variable comparisons may inspect every byte.
                          Fixed type-operator identity uses kernel IDs. *)
                       val bytes = if Type.is_vartype current then
                         IntInf.fromInt
                           (String.size (Type.dest_vartype current)) else 0
                       val total = plus total (plus 1 bytes)
                       val _ = if total <= ceiling then () else
                         raise ERR "prepare" "type forest exceeds Work"
                   in if Type.is_vartype current then walk (rest::more) total
                      else walk (#2 (Type.dest_type current)::rest::more)
                        total end)
        in walk [[ty]] 0 end
      fun annotation node =
        let val _ = charge () val ty = G.type_of graph node
            val _ = save_type ty
        in (type_size ty,Actual ty) end
      fun atom (ty,shape) : size =
        {raw = 1,inc = 1,ann = ty,ty = ty,shape = shape}
      fun app (a : size) (b : size) (ty,shape) : size =
        {raw = plus 1 (plus (#raw a) (#raw b)),
         inc = plus 1 (plus (#inc a) (#inc b)),
         ann = plus ty (plus (#ann a) (#ann b)),ty = ty,shape = shape}
      fun named node = atom (annotation node)
      val _ = charge ()
      val projection_memo = ref ([] : (G.node * IntInf.int) list)
      val _ = charge ()
      val projection_work = ref (0 : IntInf.int)
      (* This receipt comes ONLY from a completed genuine no-op scan.
         Its exact representative/backing paths are validated and retained
         before any semantic-node cache hit. No raw/type scalar or external
         caller field becomes projection provenance. Logical type_of units
         exclude unpriced private Clos/Subst forcing and getter internals. *)
      fun opaque_projection depth node =
        let val _ = charge ()
            val receipt = case
                G.opaque_type_projection_for graph scope node of
                  SOME receipt => receipt
                | NONE => raise ERR "prepare"
                    "missing actual opaque type_of projection receipt"
            val data = G.opaque_type_projection_data graph scope receipt depth
            val _ = if #node data = node then () else
              raise ERR "prepare" "opaque projection node differs"
            val _ = charge ()
            val _ = held := OpaqueProjection
              {node = node,depth = depth,receipt = receipt} :: !held
            val _ = List.app (fn ty =>
              (charge ();save_type ty;ignore (type_size ty)))
              (#binder_types data)
        in #work data end

      (* Actual type_of follows only the rator/body projection. Inside a
         canonical abstraction a variable lookup uses at most the retained
         binder depth. This is a source-derived upper envelope, not a cached
         result-type scalar standing in for an arbitrary opaque path. *)
      fun projection depth child =
        let val _ = charge ()
            val node = G.closure_child_node graph scope child
            val _ = charge () val _ = held := Held child :: !held
            val own = case G.view graph node of
                G.Variable _ => plus 1 depth
              | _ => 1
        in case G.view graph node of
            G.Application _ =>
              let val _ = charge ()
                  val (operator,_) =
                    G.closure_application_children graph scope child
              in plus own (plus 1 (projection depth operator)) end
          | G.AdmittedBinder _ =>
              let val _ = charge ()
                  val closure = G.closure_child_binder graph scope child
                  val _ = charge ()
                  val data = G.binder_closure_data graph scope closure
                  val _ = annotation (#binder data)
                  val _ = charge ()
                  val body = G.binder_closure_body graph scope closure
                  val _ = charge ()
              in plus own (plus 1 (projection (plus depth 1) body)) end
          | G.OpaqueRetained => opaque_projection depth node
          | _ => own
        end
      fun residue node =
        let val _ = charge ()
            val child = G.closure_root graph scope node
            val _ = ignore (G.closure_child_node graph scope child)
            val _ = charge () val _ = held := Held child :: !held
            (* An incoming opaque receipt is never dropped by a memo hit.
               It may have a different actual backing/ready path. *)
            val admitted = case G.view graph node of
                G.OpaqueRetained => SOME (opaque_projection 0 node)
              | _ => NONE
            val work = case lookup node (!projection_memo) of
                SOME amount => amount
              | NONE =>
                  let val _ = charge ()
                      val amount = case admitted of SOME amount => amount
                        | NONE => projection 0 child
                      val _ = charge ()
                      val _ = projection_memo :=
                        (node,amount) :: !projection_memo
                  in amount end
            val _ = projection_work := plus (!projection_work) work
        in atom (annotation node) end
      (* A retained comparison hole is NOT an unfolded term-size claim.
         Its identity comes only from P's held node/placeholder substitution
         and exact constructor/discharge grammar, never a caller parameter. *)
      fun actual node = residue node
      fun bound label (s : size) =
        if #raw s <= cap andalso #inc s <= cap then () else
          raise ERR "prepare" (label ^ " exceeds original template cap")
      fun equal (a : size) (b : size) : size =
        let val _ = charge ()
            val t = #ty a
            val _ = if t = #ty b then () else
              raise ERR "prepare" "different equality type shape"
            val _ = save_shape Boolean
            val _ = save_shape (Arrow (#shape a,Boolean))
            val _ = save_shape
              (Arrow (#shape a,Arrow (#shape a,Boolean)))
        in {raw = plus 3 (plus (#raw a) (#raw b)),
            inc = plus 3 (plus (#inc a) (#inc b)),
            ann = plus (plus 6 (times 3 t)) (plus (#ann a) (#ann b)),
            ty = 1,shape = Boolean} end
      fun join (a : size) (b : size) : size =
        {raw = plus 3 (plus (#raw a) (#raw b)),
         inc = plus 3 (plus (#inc a) (#inc b)),
         ann = plus 9 (plus (#ann a) (#ann b)),ty = 1,shape = Boolean}
      val _ = charge ()
      val _ = C.validate_conversion_for work converted
      val {root = recipe_root,steps} = C.graph_recipe_steps graph scope
        {observe = charge} converted
      fun count [] n = n | count (_::rest) n = (charge ();count rest (n+1))
      val step_count = count steps 0
      val _ = charge ()
      val facts = C.graph_closed_facts converted
      val conversions = C.graph_conversions converted
      val _ = charge ()
      val roots = C.graph_roots converted
      (* Name/open operations execute this exact constructor rator spine.
         A realized endpoint cut must not hide a definition demanded there.
         Direct realized child rows have equality NONE and add no wrapper. *)
      fun constructor_roots node =
        (charge ();case G.view graph node of
           G.Application (operator,_) =>
             (charge ();node :: constructor_roots operator)
         | G.Constant _ => (charge ();[node])
         | _ => [])
      fun prepend [] rest = rest
        | prepend (node::more) rest =
            (charge ();charge ();node :: prepend more rest)
      fun demanded [] = []
        | demanded ((step : C.recipe_step)::rest) =
            let val _ = charge ()
                val equality = case #equality step of NONE => []
                  | SOME node => constructor_roots node
                val closed = case #closed step of NONE => []
                  | SOME fact => constructor_roots (P.closed_node fact)
                val _ = charge ()
            in prepend equality (prepend closed (demanded rest)) end
      val roots = prepend roots (demanded steps)
      val target = C.graph_equality converted
      (* Consume the SAME genuine receipt-derived frontier as P. Names
         still include every retained residue; only private atom definitions
         are cut, never an independently supplied count/category flag. *)
      val _ = phase "frontier.before" (fn () => "")
      val frontier = P.prepare_realization_frontier work
        {frame = #frame owner,roots = roots,closed_facts = facts,
         conversions = conversions}
      val frontier_data = P.realization_frontier_data_for work frontier
      val reachable = #reachable frontier_data
      val atoms = #atoms frontier_data
      val _ = phase "frontier.after" (fn () => "")
      fun is_atom node [] = false
        | is_atom node (atom::rest) =
            (charge ();node = atom orelse is_atom node rest)
      fun definition node =
        if is_atom node atoms then NONE else case G.view graph node of
          G.Constant _ => SOME (equal (named node) (named node),
                                 equal (actual node) (actual node))
        | G.Application (a,b) =>
            SOME (equal (named node) (app (named a) (named b)
                    (annotation node)),equal (actual node)
                    (app (actual a) (actual b) (annotation node)))
        | _ => NONE
      fun definitions [] result = List.rev result
        | definitions (node::rest) result = (charge ();
            case definition node of NONE => definitions rest result
            | SOME pair => (charge ();definitions rest (pair::result)))
      val definition_leaves = definitions reachable []
      fun closed_leaves [] result = List.rev result
        | closed_leaves (fact::rest) result = (charge ();
            let val node = P.closed_node fact in
              closed_leaves rest ((named node,actual node)::result) end)
      fun converted_leaves [] result = List.rev result
        | converted_leaves (item::rest) result = (charge ();
            let val a = P.conversion_source item
                val b = P.conversion_target item
            in converted_leaves rest
              ((equal (named a) (named b),equal (actual a) (actual b))::result)
            end)
      val leaves = closed_leaves facts [] @ converted_leaves conversions []
        @ definition_leaves
      val leaf_count = count leaves 0
      val _ = if leaf_count <= #template_limit limits then () else
        raise ERR "prepare" "actual leaf portfolio exceeds template cap"
      (* The same balanced grammar as P.make_tree, including empty TRUE. *)
      fun tree [] = Empty
        | tree [pair] = Leaf pair
        | tree pairs =
          let val n = count pairs 0 val half = n div 2
              fun split 0 rest left = (List.rev left,rest)
                | split n (x::rest) left =
                    (charge ();split (n-1) rest (x::left))
                | split _ [] _ = raise Fail "assembly tree split"
              val (a,b) = split half pairs []
          in charge ();Split (tree a,tree b) end
      val tree = tree leaves
      val bool = atom (1,Boolean)
      fun context actual Empty = bool
        | context actual (Leaf (a,b)) = if actual then b else a
        | context actual (Split (a,b)) =
            (charge ();join (context actual a) (context actual b))
      val compact_context = context false tree
      val comparison_context = context true tree
      val _ = bound "compact P context" compact_context
      val _ = bound "P comparison skeleton" comparison_context
      val _ = charge () val assembly_work = ref (0 : IntInf.int)
      val _ = charge () val realization_work = ref (0 : IntInf.int)
      val _ = charge () val operations = ref 0
      fun quote tally hypotheses (term : size) =
        let val _ = charge () val _ = bound "public proof result" term
            fun weight (s : size) = plus (#raw s) (plus (#inc s) (#ann s))
            fun add [] total = total
              | add (hyp::rest) total = (charge ();bound "proof Hyp" hyp;
                  add rest (plus total (weight hyp)))
            val amount = add hypotheses (plus 1 (weight term))
            val _ = tally := plus (!tally) amount
            val _ = operations := !operations+1
            val _ = if !tally <= ceiling then () else
              raise ERR "prepare" "public proof portfolio exceeds Work"
        in () end
      fun compact s = (quote assembly_work [compact_context] s;s)
      fun realized s = (quote realization_work [] s;s)
      fun reflexive node =
        let val term = equal (named node) (named node)
            val _ = quote assembly_work [] term
        in term end
      fun projections actual t =
        let val common = if actual then comparison_context else compact_context
            val tally = if actual then realization_work else assembly_work
            fun descend Empty = () | descend (Leaf _) = ()
              | descend (Split (a,b)) =
                (quote tally [common] (context actual a);
                 quote tally [common] (context actual b);
                 descend a;descend b)
        in quote tally [common] common;descend t end
      val _ = projections false tree
      val _ = charge () val assembly_memo = ref ([] : (int * size) list)
      fun constructor node =
        case G.view graph node of G.Constant _ => named node
        | G.Application (a,b) =>
            let val expansion = constructor a
                val result = app expansion (named b) (annotation node)
                val _ = compact (equal
                  (app (named a) (named b) (annotation node)) result)
                val _ = compact (equal (named node) result)
            in result end
        | _ => (ignore (reflexive node);named node)
      fun step_for id [] = raise ERR "prepare" "missing retained recipe ID"
        | step_for id ((step : C.recipe_step)::rest) =
            (charge ();if #id step = id then step else step_for id rest)
      (* Exactly the actual per-frame naming wrapper. Child opened receipts
         then use this same equality's constructor before public EQ_MP. *)
      fun name_equality equality =
        let val (partial,right) = case G.view graph equality of
                G.Application pair => pair | _ => raise ERR "prepare" "Eq"
            val (head,left) = case G.view graph partial of
                G.Application pair => pair | _ => raise ERR "prepare" "Eq"
            val expanded_partial = app (named head) (named left)
              (annotation partial)
            val head_applied = app (atom (annotation head)) (named left)
              (annotation partial)
            val _ = compact (equal expanded_partial head_applied)
            val _ = compact (equal (named partial) head_applied)
            val expanded = app head_applied (named right) (annotation equality)
            val _ = compact (equal
              (app (named partial) (named right) (annotation equality)) expanded)
            val _ = compact (equal (named equality) expanded)
            val _ = compact (equal expanded (named equality))
        in compact (named equality) end
      fun assemble id = case lookup id (!assembly_memo) of
          SOME value => value
        | NONE =>
          let val step = step_for id steps
              val source = #source step val current = #current step
              fun opened child_id =
                let val proof = assemble child_id
                    val child = step_for child_id steps
                in case #equality child of NONE => proof
                  | SOME equality =>
                    let val expanded = constructor equality
                    in compact expanded end
                end
              val initial = case #prefix step of SOME prefix => opened prefix
                | NONE => (case #children step of NONE => reflexive source
                  | SOME (left,right) =>
                    if #kind step = C.LegacyStep andalso current = source then
                      reflexive source
                    else let val _ = if #kind step = C.ApplicationRecipe then
                                     (ignore (opened left);ignore (opened right))
                                   else (ignore (assemble left);
                                         ignore (assemble right))
                             val (a,b) = case G.view graph source of
                               G.Application pair => pair
                             | _ => raise ERR "prepare" "old app shape"
                             val (ca,cb) = case G.view graph current of
                               G.Application pair => pair
                             | _ => raise ERR "prepare" "new app shape"
                             val old = app (named a) (named b)
                               (annotation source)
                             val new = app (named ca) (named cb)
                               (annotation current)
                             val _ = compact (equal old new)
                             val _ = compact (equal new (named current))
                             val _ = compact (equal old (named current))
                         in compact (equal (named source) (named current)) end)
              val _ = initial
              val _ = case (#closed step,#conversion step) of
                  (SOME fact,NONE) =>
                    let val expansion = constructor (P.closed_node fact)
                        val _ = compact expansion
                    in ignore (compact (equal (named source)
                      (named (case #continuation step of
                         SOME next => #source (step_for next steps)
                       | NONE => #result step)))) end
                | (NONE,SOME _) => ignore (compact (equal (named source)
                    (named (case #continuation step of
                       SOME next => #source (step_for next steps)
                     | NONE => #result step))))
                | (NONE,NONE) => ()
                | _ => raise ERR "prepare" "two local witness slots"
              val equation = case #continuation step of NONE =>
                    equal (named source) (named (#result step))
                | SOME next =>
                    (if #kind step = C.SequenceRecipe then
                       ignore (opened next) else ignore (assemble next);
                     compact (equal (named source) (named (#result step))))
              val value = case #equality step of NONE => equation
                | SOME equality => name_equality equality
              val _ = charge ()
              val _ = assembly_memo := (id,value) :: !assembly_memo
          in value end
      val _ = assemble recipe_root
      val target_actual = actual target
      val _ = realized (join compact_context (named target)) (* DISCH *)
      (* INST's expanded conclusion is not a new syntax template. *)
      val _ = realized (join comparison_context target_actual)
      val _ = projections true tree
      val _ = List.app (fn (_,term) => ignore (realized term)) definition_leaves
      fun tree_proof Empty = (ignore (realized bool);bool)
        | tree_proof (Leaf (_,term)) = term
        | tree_proof (Split (a,b)) =
            realized (join (tree_proof a) (tree_proof b))
      val _ = tree_proof tree
      val _ = realized target_actual (* MP *)
      (* Quote render trees and every supplied policy argument BEFORE either
         Type.mk_type or the first callback. Policies are not cost authority. *)
      val _ = save_shape (Arrow (Boolean,Arrow (Boolean,Boolean)))
      val _ = save_shape (Arrow (Boolean,Boolean))
      val _ = save_shape Boolean
      fun render_size (Actual ty) = plus 1 (type_size ty)
        | render_size Boolean = 2
        | render_size (Arrow (a,b)) =
            plus 2 (plus (render_size a) (render_size b))
      fun render_work [] total = total
        | render_work (ty::rest) total =
            (charge ();render_work rest (plus total (render_size ty)))
      (* Kernel INST builds its OWN fixed variable-key dictionary. Every
         redex is a genuine graph-generated placeholder: the name is the
         fixed prefix plus a nonnegative MACHINE Int. No caller comparator,
         dictionary, row count or name certificate enters this forecast. *)
      val max_integer = case Int.maxInt of SOME bound => bound
        | NONE => raise ERR "prepare" "unbounded placeholder index format"
      val name_bytes = IntInf.fromInt
        (String.size "__smt_replay_" + String.size (Int.toString max_integer))
      val sigma_rows = count reachable 0
      (* Conservative path bound for the selected Binarymap's weight-3
         invariant: child-size+1 <= 3*(parent-size+1)/4. Its special small
         cases satisfy the same bound. No numItems or arbitrary old map. *)
      fun height n = if n = 0 then 0 else
        (charge ();plus 1
          (height (IntInf.max (0,(3*(n+1) div 4)-1))))
      val comparison = plus 1 (times 2 name_bytes)
      fun inserts [] n total = total
        | inserts (_::rest) n total =
            let val _ = charge ()
                val path = height (IntInf.fromInt n)
                (* Per ancestor: comparison/branch, up to THREE explicit
                   tree constructors in a double rotation. Leaf+dict too. *)
                val row = plus 2
                  (times path (plus comparison 4))
            in inserts rest (n+1) (plus total row) end
      val input_law = join compact_context (named target)
      (* Each compact syntax occurrence can perform at most one key lookup.
         Counts include constants/constructors as a safe input-tree envelope;
         inserted residues are NOT recursively visited by either subst. *)
      val lookup_work = times (#raw input_law)
        (plus 1 (times (height (IntInf.fromInt sigma_rows)) comparison))
      fun sigma_types [] total = total
        | sigma_types (node::rest) total =
            let val _ = charge ()
                val (ty,_) = annotation node
                val _ = actual node
            in sigma_types rest (plus total (plus 2 (times 2 ty))) end
      val dictionary_work = plus (inserts reachable 0 0)
        (plus lookup_work (sigma_types reachable 0))
      val assembly_amount = plus (!assembly_work)
        (render_work (!policies) 0)
      val _ = realization_work := plus (!realization_work)
        (plus dictionary_work (!projection_work))
      val realization_amount = !realization_work
      val _ = if plus assembly_amount realization_amount <= ceiling then ()
        else raise ERR "prepare" "combined public proof quote exceeds Work"
      fun reserve role amount =
        let val token = W.reserve work
              {role = role,ordinal = ordinal,amount = IntInf.toInt amount}
        in W.consume work token (IntInf.toInt amount) end
      val _ = phase "assembly.reserve.before" (fn () =>
        " amount=" ^ IntInf.toString assembly_amount)
      val _ = reserve W.FactAssembly assembly_amount
      val _ = phase "assembly.reserve.after" (fn () => "")
      val _ = phase "realization.reserve.before" (fn () =>
        " amount=" ^ IntInf.toString realization_amount)
      val _ = reserve W.FinalFreeze realization_amount
      val _ = phase "realization.reserve.after" (fn () => "")
      val _ = List.app (P.validate_closed_fact graph scope
        (#template_limit limits)) facts
      val _ = List.app (P.validate_conversion_for work) conversions
      val _ = List.app (P.validate_conversion graph scope
        (#template_limit limits)) conversions
      (* Both exact deferred table batches/listings are prepared and
         debited NOW, before every caller policy and placeholder payload.
         The original Work/Scope/Source are held; execute cannot re-plan. *)
      val _ = phase "retained.guards.after" (fn () => "")
      val tables = P.prepare_owned_realization_tables work frontier
      val _ = phase "tables.after" (fn () => "")
      (* Exact validate program: final prepare guard, five execute guards,
         two policy
         guards per retained shape, and two guards at each rendered arrow.
         Mint and freeze own their separate same-plan guard reservations. *)
      fun arrows (Actual _) = (W.spend work 1;0 : IntInf.int)
        | arrows Boolean = (W.spend work 1;0)
        | arrows (Arrow (left,right)) =
            (W.spend work 1;plus 1 (plus (arrows left) (arrows right)))
      fun future_guards [] = (W.spend work 1;6 : IntInf.int)
        | future_guards (shape::rest) =
            (W.spend work 1;plus 2
              (plus (times 2 (arrows shape)) (future_guards rest)))
      val guard_amount = times (future_guards (!policies))
        (P.realization_tables_guard_work work tables)
      val _ = phase "guards.debit.before" (fn () =>
        " amount=" ^ IntInf.toString guard_amount)
      val _ = if guard_amount <= IntInf.fromInt
          (W.work_limit work - #charged (W.audit work)) then
            W.spend work (IntInf.toInt guard_amount)
        else raise ERR "prepare" "original placeholder guard Work exhausted"
      val _ = phase "guards.debit.after" (fn () => "")

      fun triple (s : size) = (#raw s,#inc s,#ann s)
      val summary = {leaves = leaf_count,steps = step_count,
        public_operations = !operations,assembly_work = assembly_amount,
        realization_work = realization_amount,
        dictionary_work = dictionary_work,
        type_projection_work = !projection_work,
        compact_context = triple compact_context,
        comparison_context = triple comparison_context}
      val _ = charge ()
      val result = Plan {owner = owner,
        graph_conversion = converted,roots = roots,facts = facts,
        conversions = conversions,held = !held,tables = tables,
        types = !policies,
        check_type = check_type,summary = summary,used = ref false}
      val _ = validate work result
    in result end))

  fun prepare work {conversion,ordinal,check_type} =
    let val frame = Scope.root work
    in prepare_in_scope work
      {frame = frame,conversion = conversion,ordinal = ordinal,
       check_type = check_type} end

  fun execute work (plan as Plan {owner,graph_conversion,roots,facts,
      conversions,tables,types,check_type,used,...}) = protected work (fn () =>
    (validate work plan;W.with_step work (fn () =>
      let val _ = validate work plan
          val _ = if !used then raise ERR "execute" "plan already executed"
            else used := true
          fun render (Actual ty) = ty | render Boolean = Type.bool
            | render (Arrow (a,b)) =
                let val x = render a and y = render b
                    val _ = validate work plan
                    val ty = Type.mk_type ("fun",[x,y])
                    val _ = validate work plan
                in ty end
          fun policy shape =
            let val ty = render shape val _ = validate work plan
                val _ = check_type ty val _ = validate work plan
            in () end
          val _ = List.app policy types
          val block = P.freeze_owned_realization_tables_plan work tables
          val _ = validate work plan
          val edge = C.graph_assemble_for work (#graph owner) block
            graph_conversion
          val _ = validate work plan
          val receipt = P.realize_owned_receipt work block
            (C.graph_equality graph_conversion) edge
          val theorem = P.realization_theorem_for work receipt
          val _ = validate work plan
          val _ = if null (Thm.hyp theorem) andalso
              null (Tag.axioms_of (Thm.tag theorem)) andalso
              List.all (fn tag => tag = "DISK_THM")
                (#1 (Tag.dest_tag (Thm.tag theorem))) andalso
              Portable.pointer_eq (Thm.concl theorem,G.representative
                (#graph owner) (C.graph_equality graph_conversion)) then ()
            else raise ERR "execute" "realized closed endpoint changed"
      in Result {plan = plan,receipt = receipt} end)))
  fun theorem_for work (Result {plan,receipt}) =
    (validate work plan;P.realization_theorem_for work receipt)
  fun realization_for work (Result {plan,receipt}) =
    (validate work plan;P.validate_realization_for work receipt;receipt)
  fun conversion_description_for work
      (Result {plan = plan as Plan {owner,graph_conversion,...},...}) =
    let val _ = validate work plan
    in {graph = #graph owner,root = #root owner,scope = #scope owner,
        sources = #sources owner,
        source = C.graph_source graph_conversion,
        target = C.graph_result graph_conversion} end
  (* A closed conversion is assembled on compact names and realized once.
     The genuine receipt, original frame and native contract stay attached.
     This programme makes no private-runtime or universal tariff claim. *)
  structure PolicyCore =
  struct
    structure NC=SmtReplayNativeContract
    structure RP=SmtReplayResourcePolicy
    type owner=
      {work:W.portfolio,graph:G.graph,root:G.scope,scope:G.scope,
       sources:S.sources,frame:Scope.receipt,contract:NC.contract,
       limits:RP.semantic_policy,epoch:int,symbols:int}
    datatype plan=Plan of
      {owner:owner,conversion:C.graph_conversion,
       tables:P.policy_realization_tables_plan,
       freeze:P.policy_native_freeze_plan,used:bool ref}
    datatype result=Result of
      {plan:plan,receipt:P.policy_source_realization}
    fun protect work operation=operation() handle primary=>
      (W.close work;raise primary)
    fun active (held:owner)=
      let val work= #work held
          val _=NC.validate_for work (#contract held)
          val _=W.validate_policy work (#graph held) (#root held)
            (#sources held) (#limits held)
          val actual=Scope.description_with_policy_for work (#frame held)
      in if Portable.pointer_eq(#graph actual,#graph held) andalso
          #root actual= #root held andalso #scope actual= #scope held andalso
          Portable.pointer_eq(#sources actual,#sources held) andalso
          #limits actual= #limits held andalso
          Type.type_epoch()= #epoch held andalso
          Term.term_epoch()= #symbols held then () else
        raise ERR "policy_core" "original frame, policy or epoch changed"
      end
    fun validate work (Plan{owner,conversion,tables,...})=protect work
      (fn()=>
        (if Portable.pointer_eq(work,#work owner) then () else
           raise ERR "policy_core" "different original Work";
         active owner;C.validate_conversion_with_policy work conversion;
         P.validate_realization_tables_with_policy work tables;
         active owner))
    fun prepare_in_scope work
        {frame,conversion,ordinal,native_contract,profiles,check_type}=
      protect work (fn()=>
      (NC.validate_for work native_contract;W.with_step work (fn()=>
      let
        val incoming=Scope.description_with_policy_for work frame
        val owner={work=work,graph= #graph incoming,root= #root incoming,
          scope= #scope incoming,sources= #sources incoming,frame=frame,
          contract=native_contract,limits= #limits incoming,
          epoch=Type.type_epoch(),symbols=Term.term_epoch()}:owner
        fun guard()=(active owner;
          C.validate_conversion_with_policy work conversion;active owner)
        val _=guard()
        val _=if ordinal>=0 then () else
          raise ERR "policy_core" "negative caller ordinal"
        val graph= #graph owner val scope= #scope owner
        val roots=C.graph_roots_with_policy work graph scope conversion
        val facts=C.graph_closed_facts conversion
        val conversions=C.graph_conversions conversion
        fun visible node=
          (guard();W.spend_policy work 1;
           if G.scope_visible graph scope (G.node_scope graph node) then ()
           else raise ERR "policy_core" "recipe root escapes actual frame")
        val _=List.app visible roots
        val _=List.app (fn fact=>
          (guard();W.spend_policy work 1;
           P.validate_closed_fact_with_policy graph scope
             (#template_limit(#limits owner)) fact)) facts
        val _=List.app (fn converted=>
          (guard();W.spend_policy work 1;
           P.validate_conversion_for work converted;
           P.validate_conversion_with_policy graph scope
             (#template_limit(#limits owner)) converted)) conversions
        val frontier=P.prepare_realization_frontier_with_policy work
          {frame=frame,roots=roots,closed_facts=facts,
           conversions=conversions}
        val tables=P.prepare_owned_realization_tables_with_policy work
          frontier
        val freeze=P.prepare_native_realization_freeze_with_policy work
          {tables=tables,contract=native_contract,profiles=profiles,
           ordinal=ordinal,check_type=fn ty=>
             (guard();check_type ty;guard())}
        val plan=Plan{owner=owner,conversion=conversion,tables=tables,
          freeze=freeze,used=ref false}
        val _=validate work plan
      in plan end)))
    fun execute work (plan as Plan{owner,conversion,freeze,used,...})=
      protect work (fn()=>
      (validate work plan;W.with_step work (fn()=>
      let
        val _=validate work plan
        val _=if !used then raise ERR "policy_core" "plan already executed"
          else used:=true
        val block=P.freeze_owned_realization_tables_with_policy work freeze
        val _=validate work plan
        val edge=C.graph_assemble_with_policy work (#graph owner) block
          conversion
        val _=validate work plan
        val receipt=P.execute_realization_with_policy work
          (P.prepare_realization_with_policy work block
            (C.graph_equality conversion) edge)
        val data=P.policy_source_realization_data_for work receipt
        val _=if Portable.pointer_eq(#graph data,#graph owner) andalso
            #root data= #root owner andalso #scope data= #scope owner andalso
            Portable.pointer_eq(#sources data,#sources owner) andalso
            Portable.pointer_eq(#native_contract data,#contract owner)
            andalso #equality data=C.graph_equality conversion andalso
            #source data=C.graph_source conversion andalso
            #target data=C.graph_result conversion then () else
          raise ERR "policy_core" "closed realized endpoints changed"
        val _=validate work plan
      in Result{plan=plan,receipt=receipt} end)))
    (* Metadata getters own no Work action and mint no native proof.
       They remain usable inside a caller's existing action. *)
    fun data_for work (Result{plan=plan as Plan{owner,conversion,...},
                              receipt})=protect work (fn()=>
      let val _=validate work plan
          val actual=P.policy_source_realization_data_for work receipt
          val _=if Portable.pointer_eq(#graph actual,#graph owner) andalso
              #root actual= #root owner andalso
              #scope actual= #scope owner andalso
              Portable.pointer_eq(#sources actual,#sources owner) andalso
              Portable.pointer_eq(#native_contract actual,#contract owner)
              andalso #source actual=C.graph_source conversion andalso
              #target actual=C.graph_result conversion andalso
              #equality actual=C.graph_equality conversion then () else
            raise ERR "policy_core" "retained result differs"
      in actual end)
    fun theorem_for work (result as Result{receipt,...})=
      (ignore(data_for work result);
       P.policy_source_realization_theorem_for work receipt)
    fun realization_for work (result as Result{receipt,...})=
      (ignore(data_for work result);receipt)
    fun description_for work result=
      let val actual=data_for work result
      in {graph= #graph actual,root= #root actual,scope= #scope actual,
          sources= #sources actual,source= #source actual,
          target= #target actual} end
    fun native_contract_for work result= #native_contract(data_for work result)
    fun conversion_for work result=
      P.conversion_from_policy_source_realization_for work
        (realization_for work result)
  end
  type policy_plan=PolicyCore.plan
  type policy_result=PolicyCore.result
  val prepare_in_scope_with_policy=PolicyCore.prepare_in_scope
  val execute_with_policy=PolicyCore.execute
  val theorem_with_policy_for=PolicyCore.theorem_for
  val realization_with_policy_for=PolicyCore.realization_for
  val conversion_description_with_policy_for=PolicyCore.description_for
  val native_contract_with_policy_for=PolicyCore.native_contract_for
  val conversion_with_policy_for=PolicyCore.conversion_for

end
