(* Arithmetic remains owned by the existing checked procedures. This adapter
   changes their operands, not their mathematical fragment or solver ladder. *)
structure SmtReplayArithmetic :> SmtReplayArithmetic =
struct
  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure P = SmtReplayProof
  val ERR = Feedback.mk_HOL_ERR "SmtReplayArithmetic"

  fun has_numeric_operand graph scope {inputs,observe} =
    let
      fun header node =
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "has_numeric_operand" "invisible arithmetic operand")
      val _ = G.validate_scope graph scope
      val _ = List.app header inputs
      fun tick () = (G.validate_scope graph scope;observe ();
        G.validate_scope graph scope)
      fun compare pair = (tick ();Int.compare pair)
      val seen = ref (Redblackset.empty compare)
      fun visit node =
        (ignore (G.type_of graph node);tick ();
         if Redblackset.member (!seen,G.node_id node) then false else
           (seen := Redblackset.add (!seen,G.node_id node);
            SmtReplayCanon.is_arith_type (G.type_of graph node) orelse
            (case G.view graph node of
               G.Application (f,x) => visit f orelse visit x
             | G.AdmittedBinder _ =>
                 (case G.recorded_binder_closure graph
                     (G.node_scope graph node) node of
                    SOME closure => visit (#body (G.binder_closure_data graph
                      (G.node_scope graph node) closure))
                  | NONE => true)
             (* Unknown syntax cannot certify absence of arithmetic. The
                bounded adapter checks it BEFORE opening any native body. *)
             | G.OpaqueRetained => true
             | _ => false)))
    in List.exists visit inputs end

  fun prove graph scope {inputs,template_limit,observe,procedure} =
    let
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      fun guard () =
        (G.validate_scope graph scope;
         if epoch = Type.type_epoch () andalso symbols = Term.term_epoch ()
         then () else raise ERR "prove" "arithmetic declarations retired")
      fun charge amount = (guard ();observe amount;guard ())
      fun tick () = charge 1
      fun authenticate node =
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "prove" "arithmetic operand outside active scope")
      fun visible node = (authenticate node;tick ())
      (* Authenticate ALL roots before any ID lookup, callback or debit. *)
      val _ = guard ()
      val _ = List.app authenticate inputs
      (* Annotation syntax, not word semantics: arithmetic can legitimately
         contain an opaque LENGTH over words of a polymorphic dimension. *)
      fun check_type ty =
        let fun walk [] _ = ()
              | walk (ty::rest) count =
                  (tick ();if count >= template_limit then
                     raise ERR "prove"
                       "arithmetic Type exceeds local admission"
                   else walk ((if Type.is_vartype ty then [] else
                     #2 (Type.dest_type ty)) @ rest) (count+1))
        in walk [ty] 0 end
      val sizes = ref (Redblackmap.mkDict Int.compare)
      val opaque_nodes = ref ([] : G.node list)
      fun variable_compare (a,b) = (tick ();Term.compare (a,b))
      val operand_variables = ref (Redblackmap.mkDict Int.compare)
      val visits = ref 0
      fun admit node =
        (visible node;
         case Redblackmap.peek (!sizes,G.node_id node) of SOME size => size
         | NONE =>
             let
               (* Prospective traversal fuel, independently of the unfolded
                  schema size. Never descend an unbounded rejected spine. *)
               val _ = if !visits < template_limit then () else
                 raise ERR "prove" "arithmetic input exceeds local admission"
               val _ = visits := !visits + 1
               val size = case G.view graph node of
                   G.Application (operator,argument) =>
                     SmtResource.saturated_add 1 (SmtResource.saturated_add
                       (admit operator) (admit argument))
                 | G.AdmittedBinder _ =>
                     (opaque_nodes := node :: !opaque_nodes;1)
                 | G.OpaqueRetained =>
                     (opaque_nodes := node :: !opaque_nodes;1)
                 | G.Variable _ =>
                     (operand_variables := Redblackmap.insert
                        (!operand_variables,G.node_id node,node);1)
                 | _ => 1
               val _ = if size <= template_limit then () else
                 raise ERR "prove" "arithmetic input exceeds local admission"
               val _ = check_type (G.type_of graph node)
               val _ = sizes := Redblackmap.insert
                 (!sizes,G.node_id node,size)
             in size end)
      (* These are schema sizes, NOT replacements for original call-site
         resource metrics. Repeated roots keep their original per-input cap. *)
      val _ = List.app (fn node => (visits := 0;ignore (admit node))) inputs
      fun bounded term =
        case SmtReplayImport.bounded_raw_size_with_type_check_observed
            {check_type=check_type,observe=tick,limit=template_limit} term of
          SOME _ => () | NONE => raise ERR "prove"
            "arithmetic operator schema exceeds local admission"
      fun annotations term =
        (tick ();check_type (Term.type_of term);
         if Term.is_comb term then
           let val (f,x) = Term.dest_comb term
           in annotations f;annotations x end
         else if Term.is_abs term then
           let val (v,b) = SmtReplayImport.dest_abs_preserving_names term
           in annotations v;annotations b end else ())
      (* This private namespace is disjoint from G.placeholder's namespace.
         checked_graph_schema reserves it before realization allocates names.
         Fixed-width IDs preserve numeric order for arithmetic elimination
         and avoid defeating the existing procedures' ordinary caches;
         no optional cache or global fresh-name dependency is introduced. *)
      fun allocate nodes = List.map (fn node =>
        (tick ();(node,Term.mk_var
          ("__smt_arith_" ^ StringCvt.padLeft #"0" 16
             (Int.fmt StringCvt.HEX (G.node_id node)),
           G.type_of graph node)))) nodes
      fun clean theorem =
        let val tag = Thm.tag theorem
        in null (Thm.hyp theorem) andalso null (Tag.axioms_of tag) andalso
          List.all (fn tag => tag = "DISK_THM") (#1 (Tag.dest_tag tag)) end
      fun finish node theorem =
        let val _ = guard ()
            val original = G.representative graph node
            val theorem = Thm.EQ_MP
              (Thm.ALPHA (Thm.concl theorem) original) theorem
        in {theorem = theorem,node = node} end
      (* Native binder procedures are still available, but ONLY on a fully
         bounded variable-only schema. No compound graph operand is inserted
         under a binder. The full input/Hyp/result and their Types are audited
         before FV, matching, substitution, opening or generalization. *)
      fun binder_schema () =
        let
          val originals = List.map (G.representative graph) inputs
          val _ = List.app bounded originals
          val _ = List.app annotations originals
          (* Read retained constructor identities where available. A native
             x can name distinct scoped/kinded nodes, even WITHIN one binder;
             a single native-variable substitution would silently merge them.
             No construction or rehome in the input's frames is authorized. *)
          val named = ref (Redblackmap.mkDict Int.compare)
          fun hole node =
            case Redblackmap.peek (!named,G.node_id node) of
              SOME (_,term) => term
            | NONE =>
                let val pair = hd (allocate [node])
                in named := Redblackmap.insert
                     (!named,G.node_id node,pair);#2 pair end
          fun literal bound node =
            let
              fun name variable =
                case Redblackmap.peek (bound,variable) of
                  SOME term => term
                | NONE =>
                    let val actual = G.resolve_variable graph
                          (G.node_scope graph node) variable
                        val actual = case G.view graph actual of
                            G.Variable (_,term) =>
                              if Term.aconv term variable then actual else
                                G.variable graph (G.root_scope graph)
                                  G.RigidSource variable
                          | _ => G.variable graph (G.root_scope graph)
                              G.RigidSource variable
                    in hole actual end
              val term = G.representative graph node
            in Term.subst (List.map (fn variable =>
                 {redex=variable,residue=name variable}) (Term.free_vars term))
                 term end
          fun expose bound native node =
            (tick ();case G.view graph node of
               G.Constant _ => G.representative graph node
             | G.Variable _ =>
                 (case Redblackmap.peek (bound,G.node_id node) of
                    SOME term => term | NONE => hole node)
             | G.Application (f,x) =>
                 Term.mk_comb (expose bound native f,expose bound native x)
             | G.AdmittedBinder _ =>
                 (case G.recorded_binder_closure graph
                     (G.node_scope graph node) node of
                    NONE => literal native node
                  | SOME closure =>
                      let val {binder,binder_term,body,...} =
                            G.binder_closure_data graph
                              (G.node_scope graph node) closure
                          val variable = Term.mk_var
                            ("__smt_arith_bound_" ^
                               Int.toString (G.node_id binder),
                             G.type_of graph binder)
                          val body = expose
                            (Redblackmap.insert
                              (bound,G.node_id binder,variable))
                            (Redblackmap.insert (native,binder_term,variable))
                            body
                      in Term.mk_abs (variable,body) end)
             | G.OpaqueRetained => literal native node)
          val templates = List.map
            (expose (Redblackmap.mkDict Int.compare)
              (Redblackmap.mkDict variable_compare)) inputs
          val bindings = List.map #2 (Redblackmap.listItems (!named))
          val _ = List.app bounded templates
          val theorem = procedure templates
          val _ = bounded (Thm.concl theorem)
          val _ = List.app bounded (Thm.hyp theorem)
          val _ = annotations (Thm.concl theorem)
          val _ = if clean theorem then () else raise ERR "prove"
            "arithmetic binder schema is not closed and clean"
          val holes = HOLset.addList (Term.empty_tmset,List.map #2 bindings)
          val _ = if HOLset.isSubset
              (Term.FVL [Thm.concl theorem] Term.empty_tmset,holes) then ()
            else raise ERR "prove" "unowned arithmetic binder schema variable"
          val operands = List.foldl (fn ((node,hole),table) =>
            Redblackmap.insert (table,hole,node))
            (Redblackmap.mkDict variable_compare) bindings
          fun tree frame bound term =
            (tick ();
             if Term.is_var term then
               (case Redblackmap.peek (bound,term) of
                  SOME node => node
                | NONE => raise ERR "prove" "unowned binder recipe variable")
             else if Term.is_const term then G.constant graph frame term
             else if Term.is_comb term then
               let val (f,x) = Term.dest_comb term
               in G.application graph frame (tree frame bound f,
                    tree frame bound x) end
             else
               let val (variable,body) =
                     SmtReplayImport.dest_abs_preserving_names term
                   val child = G.new_scope graph frame []
                   val binder = G.fresh_bound_variable graph child variable
                   val result = tree child
                     (Redblackmap.insert (bound,variable,binder)) body
                   val node = G.recorded_abstraction graph frame template_limit
                     {binder=binder,body=result,body_frame=child}
                   (* Recorded closure children share the owner's lifetime;
                      later consumers must still be able to inspect them. *)
               in node end)
          (* Discover the entire successful result before its single native
             INST. This is the bounded binder realization, and substitutes
             VARIABLES only, never an expanded graph below a binder. *)
          val node = tree scope operands (Thm.concl theorem)
          val substitution = List.map (fn (actual,hole) =>
            {redex=hole,residue=G.representative graph actual}) bindings
          val _ = guard ()
          val realized = SmtReplayRuleObservation.INST substitution theorem
        in finish node realized end
      fun operator_schema () =
        let
          (* One stable typed name for each distinct graph Variable node. *)
          val bindings = allocate (List.map #2
            (Redblackmap.listItems (!operand_variables)))
          val holes = List.foldl (fn ((node,term),table) =>
            Redblackmap.insert (table,G.node_id node,(node,term)))
            (Redblackmap.mkDict Int.compare) bindings
          val syntax = ref (Redblackmap.mkDict Int.compare)
          fun operand node = #2 (Redblackmap.find (holes,G.node_id node))
          fun expose node =
            (visible node;
             case Redblackmap.peek (!syntax,G.node_id node) of
               SOME term => term
             | NONE =>
                 let val term = case G.view graph node of
                         G.Constant _ => G.representative graph node
                       | G.Application (operator,argument) =>
                           Term.mk_comb (expose operator,expose argument)
                       | _ => operand node
                     val _ = syntax := Redblackmap.insert
                       (!syntax,G.node_id node,term)
                 in term end)
          val templates = List.map expose inputs
          val _ = List.app bounded templates
          val proof = procedure templates
          val _ = bounded (Thm.concl proof)
          val _ = List.app bounded (Thm.hyp proof)
          val _ = List.app annotations (Thm.concl proof :: Thm.hyp proof)
          val pairs = List.map #2 (Redblackmap.listItems holes)
          (* The four extra nodes are ONLY EQT_INTRO's fixed wrapper, not an
             increased input, result, skeleton, BV, binder or runtime cap. *)
          val schema = C.checked_graph_schema graph scope
            {theorem = Drule.EQT_INTRO proof,holes = List.map #2 pairs,
             operands = List.map #1 pairs,template_limit = template_limit+4}
          val node = C.graph_schema_source schema
          val conversion = C.graph_schema_leaf graph scope
            {schema=schema,observe=tick}
          val equality = case C.realize_typed_root_schema graph scope
              template_limit conversion of SOME theorem => theorem
            | NONE =>
                let val block = P.freeze graph
                      {scope=scope,roots=C.graph_roots conversion,sources=[],
                       template_limit=template_limit+4}
                    val edge = C.graph_assemble graph block conversion
                in P.realize block (C.graph_equality conversion) edge end
        in finish node (Drule.EQT_ELIM equality) end
    in if null (!opaque_nodes) then operator_schema ()
       else binder_schema () end
end
