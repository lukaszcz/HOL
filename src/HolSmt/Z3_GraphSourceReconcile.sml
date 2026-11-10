(* Copyright (c) 2026 The HOL4 contributors. *)
structure Z3_GraphSourceReconcile :> Z3_GraphSourceReconcile =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  val ERR = Feedback.mk_HOL_ERR "Z3_GraphSourceReconcile"
  fun need ok message = if ok then () else raise ERR "prepare" message
  fun clean proof =
    let val (tags,_) = Tag.dest_tag (Thm.tag proof) in
      List.null (Thm.hyp proof) andalso
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag proof))
    end
  datatype binding = Binding of
    {replay : G.node, original : int, law : int option}
  datatype plan = Plan of
    {graph : G.graph, scope : G.scope, originals : S.sources,
     original_nodes : G.node list, source_nodes : G.node list,
     replay : G.node list, bindings : (int,binding) Redblackmap.dict,
     laws : (int,G.node * Thm.thm) Redblackmap.dict}

  fun active (Plan {graph,scope,originals,original_nodes,
                    source_nodes,replay,...}) =
    (G.validate_scope graph scope;
     need (List.map #node (S.reconciliation_sources originals) =
       original_nodes) "original Source portfolio changed";
     List.app (fn node => need
       (G.scope_visible graph scope (G.node_scope graph node))
       "foreign or retired reconciliation node") (source_nodes @ replay))

  fun prepare graph scope
      {sources = originals,replay,views,
       admission = {raw_limit,binder_limit,step_limit,check_type}} =
    let
      val _ = G.validate_scope graph scope
      val _ = need (raw_limit > 0 andalso binder_limit > 0 andalso
        step_limit > 0) "nonpositive reconciliation admission"
      val original_sources = S.reconciliation_sources originals
      val original_nodes = List.map #node original_sources
      val all = original_nodes @ replay
      val _ = List.app (fn node =>
        need (G.scope_visible graph scope (G.node_scope graph node))
          "foreign or retired reconciliation endpoint") all
      val (_,original_indices) = List.foldl
        (fn (node,(index,table)) => (index+1,
          if Redblackmap.inDomain (table,G.node_id node) then table
          else Redblackmap.insert (table,G.node_id node,index)))
        (0,Redblackmap.mkDict Int.compare) original_nodes
      fun original_index node =
        Redblackmap.peek (original_indices,G.node_id node)
      (* Validate EVERY supplied key and candidate before ID indexing.
         Foreign numeric-ID collisions and ignored duplicate/unused entries
         cannot acquire this graph's recorded provenance. *)
      val _ = List.app (fn (node,view) =>
        G.validate_opened_view graph scope node view) views
      val view_index = List.foldl
        (fn ((node,view),table) =>
          if Redblackmap.inDomain (table,G.node_id node) then table
          else Redblackmap.insert (table,G.node_id node,view))
        (Redblackmap.mkDict Int.compare) views
      val changed = List.exists
        (fn node => not (Option.isSome (original_index node))) replay
      val remaining = ref step_limit
      fun charge operation =
        (need (!remaining > 0) ("reconciliation budget before " ^ operation);
         remaining := !remaining-1)
      fun call operation action = (charge operation;action ())
      (* These counts inspect only already graph-admitted bounded terms or
         prospectively admitted callback results. They never call count_body,
         Thm.Beta, REFL or another count-only theorem primitive. *)
      fun sum extra limit left right =
        (need (extra <= limit andalso left <= limit-extra andalso
          right <= limit-extra-left)
          "prospective normalization result exceeds admission";
         extra+left+right)
      fun application_size (fr,fb) (xr,xb) =
        (sum 1 raw_limit fr xr,sum 1 binder_limit fb xb)
      fun abstraction_size (r,b) =
        (sum 1 raw_limit r 0,sum 2 binder_limit b 0)
      fun measure term =
        let
          (* Stop before opening an unadmitted abstraction, including a
             malformed caller view whose old endpoint is unexpectedly big. *)
          fun walk [] raw binder = (raw_limit-raw,binder_limit-binder)
            | walk (term :: rest) raw binder =
                let val slots = if Term.is_abs term then 2 else 1
                    val _ = need (raw > 0 andalso binder >= slots)
                      "normalization operand exceeds admission"
                    val raw = raw-1 val binder = binder-slots
                in if Term.is_comb term then
                    let val (f,x) = Term.dest_comb term in
                      walk (f :: x :: rest) raw binder end
                  else if Term.is_abs term then
                    let val (_,body) = Term.dest_abs term in
                      walk (body :: rest) raw binder end
                  else walk rest raw binder
                end
        in walk [term] raw_limit binder_limit end
      fun within (r,b) = need
        (r <= raw_limit andalso b <= binder_limit)
        "prospective normalization result exceeds admission"
      fun equality_size (lr,lb) (rr,rb) =
        (sum 3 raw_limit lr rr,sum 3 binder_limit lb rb)
      fun admit_equality left right =
        within (equality_size (measure left) (measure right))
      fun trans left right =
        let val a = boolSyntax.lhs (Thm.concl left)
            val b = boolSyntax.rhs (Thm.concl right)
            val _ = admit_equality a b
        in call "TRANS" (fn () => Thm.TRANS left right) end
      fun bridge_endpoints left right proof =
        let val (a,b) = Term.dest_eq (Thm.concl proof) in
          need (clean proof andalso Portable.pointer_eq (a,left) andalso
            Portable.pointer_eq (b,right))
            "normalization bridge endpoints/Hyp/tags differ"
        end
      val admitted = ref (Redblackmap.mkDict Int.compare)
      (* Admit ALL requested graph-recorded views before any type policy or
         conversion callback. The private syntax recipe is checked before
         cached metrics, dest_abs or aconv can inspect original syntax. *)
      fun admit node =
        if Redblackmap.inDomain (!admitted,G.node_id node) then () else
        let
          val view = case Redblackmap.peek (view_index,G.node_id node) of
              SOME source => source
            | NONE => raise ERR "prepare"
                "missing recorded opened Source view"
          (* Registry identity precedes old opaque syntax, metric traversal,
             Boolean/type policy and every normalization callback. *)
          val _ = G.validate_opened_view graph scope node view
          val rich = #node view
          val _ = need
            (G.scope_visible graph scope (G.node_scope graph rich))
            "opened view is foreign or retired"
          fun size metric limit = case G.unfolded_nodes graph metric limit
              rich of SOME n => need (n <= limit) "opened view exceeds limit"
            | NONE => raise ERR "prepare" "unknown opened-binder metric"
          val _ = size G.RawNodes raw_limit
          val _ = size G.BinderInclusiveNodes binder_limit
          val term = G.representative graph node
          val _ = need (Portable.pointer_eq (#original view,term))
            "opened view did not retain original endpoint"
          val _ = bridge_endpoints term (G.representative graph rich)
            (#bridge view)
          val _ = admit_equality term (G.representative graph rich)
          val _ = need (Term.aconv term (G.representative graph rich))
            "opened view is not syntax-preserving alpha"
          val free = case G.free_variable_nodes graph rich of SOME nodes =>
                nodes | NONE => raise ERR "prepare" "unknown view variables"
          val _ = List.app (fn variable => case G.view graph variable of
              G.Variable (G.RigidSource,_) => ()
            | _ => raise ERR "prepare" "nonrigid Source variable in view") free
          val _ = admitted := Redblackmap.insert
            (!admitted,G.node_id node,view)
        in () end
      val _ = if changed then List.app admit all else ()
      val _ = List.app (fn node => need
        (Type.compare (G.type_of graph node,Type.bool) = EQUAL)
        "non-Boolean reconciliation endpoint") all
      val _ = if changed then List.app
        (check_type o G.type_of graph)
        (G.reachable graph (List.map (#node o #2)
          (Redblackmap.listItems (!admitted)))) else ()

      (* Predict beta substitution size without constructing a substituted
         Term. Shadowing prevents replacement beneath the same binder. *)
      fun substituted variable argument body =
        if Term.is_var body andalso Term.term_eq body variable then argument
        else if Term.is_comb body then
          let val (f,x) = Term.dest_comb body
              val (fr,fb) = substituted variable argument f
              val (xr,xb) = substituted variable argument x
          in application_size (fr,fb) (xr,xb) end
        else if Term.is_abs body then
          let val (v,b) = Term.dest_abs body in
            if Term.term_eq v variable then measure body
            else let val (r,i) = substituted variable argument b
                 in abstraction_size (r,i) end
          end
        else (1,1)
      fun normalization beta term =
        let
          fun walk term =
            let
              val _ = within (measure term)
              val proof = if Term.is_comb term then
                  let val (f,x) = Term.dest_comb term
                      val left = walk f val right = walk x
                      val lf = boolSyntax.rhs (Thm.concl left)
                      val rx = boolSyntax.rhs (Thm.concl right)
                      val (fr,fb) = measure lf val (xr,xb) = measure rx
                      val rhs_size = application_size (fr,fb) (xr,xb)
                      val _ = within (equality_size (measure term) rhs_size)
                  in call "MK_COMB" (fn () => Thm.MK_COMB (left,right)) end
                else if Term.is_abs term then
                  let val (v,b) = Term.dest_abs term val body = walk b
                      val (r,i) = measure (boolSyntax.rhs (Thm.concl body))
                      val rhs_size = abstraction_size (r,i)
                      val _ = within (equality_size (measure term) rhs_size)
                  in call "ABS" (fn () => Thm.ABS v body) end
                else (admit_equality term term;
                  call "REFL" (fn () => Thm.REFL term))
              val current = boolSyntax.rhs (Thm.concl proof)
              val conversion = if beta andalso Term.is_comb current then
                  let val (operator,argument) = Term.dest_comb current in
                    if not (Term.is_abs operator) then NONE else
                    let val (v,b) = Term.dest_abs operator
                        val rhs_size = substituted v (measure argument) b
                        val _ = within
                          (equality_size (measure current) rhs_size)
                    in SOME (call "BETA_CONV"
                      (fn () => Thm.BETA_CONV current)) end
                  end
                else if not beta andalso Term.is_abs current then
                  let val (v,b) = Term.dest_abs current in
                    if not (Term.is_comb b) then NONE else
                    let val (f,x) = Term.dest_comb b in
                      if Term.term_eq v x andalso not (Term.free_in v f)
                      then (admit_equality current f;SOME (call "ETA_CONV"
                        (fn () => Drule.ETA_CONV current))) else NONE
                    end
                  end
                else NONE
            in case conversion of NONE => proof
              | SOME equality =>
                  let val next = boolSyntax.rhs (Thm.concl equality)
                      val _ = bridge_endpoints current next equality
                      val rest = walk next
                  in trans proof (trans equality rest) end
            end
        in walk term end
      val normal = ref (Redblackmap.mkDict Int.compare)
      fun normalize node = case Redblackmap.peek (!normal,G.node_id node) of
          SOME proof => proof
        | NONE =>
          let val view = Redblackmap.find (!admitted,G.node_id node)
              val term = G.representative graph (#node view)
              val beta = normalization true term
              val eta = normalization false
                (boolSyntax.rhs (Thm.concl beta))
              val proof = trans (#bridge view) (trans beta eta)
              val right = boolSyntax.rhs (Thm.concl proof)
              val _ = bridge_endpoints (G.representative graph node) right proof
              val _ = normal := Redblackmap.insert
                (!normal,G.node_id node,proof)
          in proof end
      val _ = if changed then List.app (fn node => ignore (normalize node))
        all else ()
      val expected_index = List.foldl
        (fn (node,(index,table)) =>
          let val equality = if changed then SOME (normalize node) else NONE
          in case equality of NONE => (index+1,table)
            | SOME proof =>
              let val term = boolSyntax.rhs (Thm.concl proof) in
                (index+1,if Redblackmap.inDomain (table,term) then table
                  else Redblackmap.insert (table,term,(index,proof)))
              end
          end) (0,Redblackmap.mkDict Term.compare) original_nodes
      val expected_index = #2 expected_index
      val law_nodes = ref ([] : G.node list)
      val law_proofs = ref (Redblackmap.mkDict Int.compare)
      val next_law = ref (length original_nodes)
      fun bind node = case original_index node of SOME index =>
            Binding {replay = node,original = index,law = NONE}
        | NONE =>
          let
            val hyp = normalize node
            val canonical = boolSyntax.rhs (Thm.concl hyp)
            val (index,expected) = case Redblackmap.peek
                (expected_index,canonical) of SOME value => value
              | NONE => raise ERR "prepare"
                  "unsupported extra hypothesis: beta-eta-canonical-lookup"
            val right = boolSyntax.rhs (Thm.concl expected)
            val _ = admit_equality right canonical
            val alpha = call "ALPHA-normal-form"
              (fn () => Thm.ALPHA right canonical)
            val _ = admit_equality canonical (boolSyntax.lhs (Thm.concl hyp))
            val reverse = call "SYM" (fn () => Thm.SYM hyp)
            val equality = trans expected (trans alpha reverse)
            val _ = bridge_endpoints
              (G.representative graph (List.nth (original_nodes,index)))
              (G.representative graph node) equality
            val law_term = Thm.concl equality
            val _ = within (measure law_term)
            val imported = G.plan_import graph scope raw_limit law_term
            val _ = List.app check_type (G.import_types imported)
            val law_source = call "execute-import"
              (fn () => G.execute_import imported)
            val proof = call "EQ_MP-import" (fn () =>
              Thm.EQ_MP (#bridge law_source) equality)
            val _ = need (clean proof andalso Portable.pointer_eq
              (Thm.concl proof,G.representative graph (#node law_source)))
              "closed named law endpoint/Hyp/tags differ"
            val law_index = !next_law
            val _ = next_law := law_index+1
            val _ = law_nodes := #node law_source :: !law_nodes
            val _ = law_proofs := Redblackmap.insert
              (!law_proofs,law_index,(#node law_source,proof))
          in Binding {replay = node,original = index,law = SOME law_index} end
      val bindings = List.foldl (fn (node,table) =>
          if Redblackmap.inDomain (table,G.node_id node) then table
          else Redblackmap.insert (table,G.node_id node,bind node))
        (Redblackmap.mkDict Int.compare) replay
      val plan = Plan {graph = graph,scope = scope,originals = originals,
        original_nodes = original_nodes,
        source_nodes = original_nodes @ List.rev (!law_nodes),replay = replay,
        bindings = bindings,laws = !law_proofs}
      val _ = active plan
    in plan end

  fun sources (plan as Plan {source_nodes,...}) = (active plan;source_nodes)
  fun roots (plan as Plan {source_nodes,replay,...}) =
    (active plan;source_nodes @ replay)
  fun witness (plan as Plan {laws,...}) (index,node) =
    (active plan;case Redblackmap.peek (laws,index) of
        SOME (endpoint,proof) => if endpoint = node then SOME proof else NONE
      | NONE => NONE)
  fun assemble (plan as Plan {graph,bindings,source_nodes,...}) block node =
    let
      val _ = active plan
      val current = P.sources block
      val _ = need (length current >= length source_nodes andalso
        List.take (current,length source_nodes) = source_nodes)
        "reconciliation block changed original occurrence portfolio"
      val Binding {original,law,...} = case Redblackmap.peek
          (bindings,G.node_id node) of
          SOME value => value | NONE => raise ERR "assemble"
            "unrecorded replay Source"
      val premise = (List.nth (source_nodes,original),P.source block original)
    in case law of NONE => #2 premise
      | SOME index => SmtReplayRules.apply_law graph block
          {law = (List.nth (source_nodes,index),P.source block index),
           target = node,premises = [premise]}
    end
end
