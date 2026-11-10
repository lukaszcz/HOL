(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayUnifyBinder :> SmtReplayUnifyBinder =
struct
  open SmtReplayGraph SmtReplayUnify
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtReplayUnifyBinder"
  type definition = {variable : G.node,residue : G.node,equation : G.node}
  datatype relation = Relation of
    {graph : G.graph,scope : G.scope,left : G.node,right : G.node,
     assignments : SmtReplayUnify.assignment list,limit : int,
     internal_types : bool}
  fun active (Relation {graph,scope,...}) = G.validate_scope graph scope
  fun assignments (relation as Relation {assignments,...}) =
    (active relation;assignments)
  fun left (relation as Relation {left,...}) = (active relation;left)
  fun right (relation as Relation {right,...}) = (active relation;right)
  fun raw limit term =
    case SmtReplayImport.bounded_raw_size limit term of SOME _ => ()
      | NONE => raise ERR "admission" "bounded binder operand/output exhausted"
  fun types limit ty =
    let
      fun walk [] _ = ()
        | walk (ty::rest) count =
            if count >= limit then raise ERR "admission"
              "bounded binder type exhausted"
            else walk ((if Type.is_vartype ty then [] else
              #2 (Type.dest_type ty)) @ rest) (count+1)
    in walk [ty] 0 end
  fun admitted internal_types graph limit nodes =
    let
      val _ = if limit >= 1 then () else
        raise ERR "admission" "nonpositive binder admission limit"
      val _ = List.app (raw limit o G.representative graph) nodes
      val types_seen = ref (Redblackset.empty Int.compare)
      val _ = List.app (fn node =>
        if Redblackset.member (!types_seen,G.type_id graph node) then ()
        else (types_seen := Redblackset.add (!types_seen,G.type_id graph node);
              types limit (G.type_of graph node)))
          (if internal_types then G.reachable graph nodes else [])
    in () end

  fun admit_using check_types graph limit (saved : G.source) : G.source =
    let
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun visit node = case Redblackmap.peek (!memo,G.node_id node) of
          SOME result => result
        | NONE =>
            let
              val original = G.representative graph node
              val result = case G.view graph node of
                  G.OpaqueRetained =>
                    (case SmtReplayImport.bounded_raw_size limit original of
                         NONE => (node,Thm.REFL original)
                       | SOME _ =>
                           let
                             val _ = if check_types then
                               types limit (G.type_of graph node) else ()
                             val source = G.admit_binder graph
                               (G.node_scope graph node) limit original
                           in (#node source,#bridge source) end)
                | G.Application (operator,operand) =>
                    let val (operator',lhs) = visit operator
                        val (operand',rhs) = visit operand in
                      if operator = operator' andalso operand = operand' then
                        (node,Thm.REFL original)
                      else
                        let
                          val current = G.application graph
                            (G.node_scope graph node) (operator',operand')
                          val combined = Thm.MK_COMB (lhs,rhs)
                          val (rebuilt,result) = Term.dest_eq
                            (Thm.concl combined)
                          val bridge = Thm.TRANS (Thm.ALPHA original rebuilt)
                            (Thm.TRANS combined (Thm.ALPHA result
                              (G.representative graph current)))
                        in (current,bridge) end
                    end
                | _ => (node,Thm.REFL original)
              val _ = memo := Redblackmap.insert (!memo,G.node_id node,result)
            in result end
      val (node,bridge) = visit (#node saved)
    in {node = node,original = #original saved,
        bridge = Thm.TRANS (#bridge saved) bridge} end

  fun admit graph = admit_using true graph

  fun equality graph scope variable residue =
    let
      val marker = Term.genvar (G.type_of graph variable)
      val operator = G.constant graph scope (Term.rator (Term.rator
        (boolSyntax.mk_eq (marker,marker))))
    in G.application graph scope
      (G.application graph scope (operator,variable),residue) end
  fun definition graph scope {variable,residue} : definition =
    {variable = variable,residue = residue,
     equation = equality graph scope variable residue}
  fun checked internal_types graph scope (left,right) limit definitions =
    let
      val admitted = admitted internal_types
      val _ = admitted graph limit [left,right]
      val variables = case
          (G.free_variable_nodes graph left,G.free_variable_nodes graph right)
        of (SOME left,SOME right) => left @ right
         | _ => raise ERR "checked" "unknown admitted binder variables"
      fun needed variable = List.exists (fn saved => saved = variable) variables
      val definitions = List.filter (needed o #variable) definitions
      fun entry ({variable,residue,equation} : definition) =
        let
          val _ = case G.view graph variable of
              G.Variable (G.SolverFlexible,_) => ()
            | _ => raise ERR "checked" "binder definition assigns rigid node"
          val _ = if G.scope_visible graph scope (G.node_scope graph variable)
            then () else raise ERR "checked" "definition outside active scope"
          val _ = admitted graph limit [residue]
          val expected = equality graph scope variable residue
          val _ = if equation = expected then () else
            raise ERR "checked" "wrong canonical binder definition"
        in {redex = G.representative graph variable,
            residue = Thm.ASSUME (G.representative graph equation)} end
      (* Check the simultaneous output tree before asking the bounded kernel
         adapter to rebuild it. Traversal follows graph IDs, including
         admitted binder metadata; bound IDs never alias solver IDs. *)
      val sizes = List.foldl
        (fn ({variable,residue,...} : definition,table) =>
          case SmtReplayImport.bounded_raw_size limit
              (G.representative graph residue) of
              SOME size => Redblackmap.insert (table,G.node_id variable,size)
            | NONE => raise ERR "admission" "bounded binder output exhausted")
        (Redblackmap.mkDict Int.compare) definitions
      val counts = ref (Redblackmap.mkDict Int.compare)
      fun add left right =
        if left > limit-right then
          raise ERR "admission" "bounded binder output exhausted"
        else left+right
      fun count node = case Redblackmap.peek (!counts,G.node_id node) of
          SOME size => size
        | NONE =>
            let
              val size = case Redblackmap.peek (sizes,G.node_id node) of
                  SOME size => size
                | NONE => case G.view graph node of
                    G.Application (operator,operand) =>
                      add 1 (add (count operator) (count operand))
                  | G.AdmittedBinder {body,...} => add 1 (count body)
                  | G.OpaqueRetained => raise ERR "checked"
                      "unadmitted binder output dependency"
                  | _ => 1
              val _ = counts := Redblackmap.insert
                (!counts,G.node_id node,size)
            in size end
      val _ = List.app (ignore o count) [left,right]
      val theta = List.map entry definitions
      val left_term = G.representative graph left
      val right_term = G.representative graph right
      val lhs = Drule.SUBST_CONV theta left_term left_term
      val rhs = Drule.SUBST_CONV theta right_term right_term
      val lhs_result = boolSyntax.rhs (Thm.concl lhs)
      val rhs_result = boolSyntax.rhs (Thm.concl rhs)
      val _ = List.app (raw limit) [lhs_result,rhs_result]
      val _ = if internal_types then
        List.app (types limit o Term.type_of) [lhs_result,rhs_result] else ()
      val bridge = Thm.ALPHA lhs_result rhs_result
    in Thm.TRANS lhs (Thm.TRANS bridge (Thm.SYM rhs)) end

  fun discover_using internal_types graph scope {left,right,flexible,limit} =
    let
      val admitted = admitted internal_types
      val _ = G.validate_scope graph scope
      fun binder node =
        (if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "discover" "binder outside active scope";
         case G.view graph node of G.AdmittedBinder _ => ()
           | _ => raise ERR "discover" "binder has not been admitted")
      val _ = binder left
      val _ = binder right
      val _ = admitted graph limit [left,right]
      fun permit node =
        (if G.scope_visible graph scope (G.node_scope graph node) then ()
         else raise ERR "discover" "flexible outside active scope";
         case G.view graph node of G.Variable (G.SolverFlexible,_) => ()
           | _ => raise ERR "discover" "invalid flexibility permission")
      val _ = List.app permit flexible
      val free = case
          (G.free_variable_nodes graph left,G.free_variable_nodes graph right)
        of (SOME left,SOME right) => left @ right
         | _ => raise ERR "discover" "unknown admitted binder variables"
      val protected = List.map (G.representative graph)
        (List.filter (fn node => not
          (List.exists (fn permitted => permitted = node) flexible)) free)
      (* Canonical HOL names can differ from lexical parser aliases. Preserve
         the known free node's kind/scope when importing a small residue. *)
      val imports = G.new_scope graph scope
        (List.map (fn node => (G.representative graph node,node))
          (flexible @ free))
      fun import_residue residue =
        let
          val source = admit_using internal_types graph limit
            (G.import graph imports limit residue)
          val memo = ref (Redblackmap.mkDict Int.compare)
          fun rehome node = case Redblackmap.peek (!memo,G.node_id node) of
              SOME result => result
            | NONE =>
                let
                  val result = case G.view graph node of
                      G.Application (operator,operand) =>
                        G.application graph scope
                          (rehome operator,rehome operand)
                    | G.AdmittedBinder {binder,body,...} =>
                        G.abstraction graph scope limit (binder,body)
                    | G.OpaqueRetained => raise ERR "discover"
                        "unadmitted bounded residue"
                    | _ => node
                  val _ = memo := Redblackmap.insert
                    (!memo,G.node_id node,result)
                in result end
        in rehome (#node source) end
      fun assignment {redex,residue} =
        let
          val _ = raw limit residue
          val _ = if internal_types then types limit (Term.type_of residue)
            else ()
          val variable = case List.find (fn node =>
              Term.aconv (G.representative graph node) redex) flexible of
                SOME node => node
              | NONE => raise ERR "discover" "unifier assigned a protected node"
        in {variable = variable,residue = import_residue residue} end
      val attempt = Exn.capture (fn () =>
        let
          val substs = Unify.simp_unify_terms protected
            (G.representative graph left) (G.representative graph right)
          val assignments = List.map assignment substs
          (* Reject capture/false matches before exposing candidates. Global
             graph unification separately validates assignment ownership. *)
          val _ = checked internal_types graph scope (left,right) limit
            (List.map (definition graph scope) assignments)
        in Relation {graph = graph,scope = scope,left = left,right = right,
          assignments = assignments,limit = limit,
          internal_types = internal_types} end) ()
      val _ = G.close_scope graph imports
    in SOME (Exn.release attempt) end
    handle Feedback.HOL_ERR error =>
      if Feedback.top_function_of error = "ALPHA" orelse
         List.exists (fn message => Feedback.message_of error = message)
           ["occurs","unify_terms","simp_unify_terms"] then NONE
      else raise Feedback.HOL_ERR error

  fun discover graph = discover_using true graph
  fun discover_raw graph = discover_using false graph

  fun normalize_using internal_types graph scope {node,resolve,limit} =
    let
      val admitted = admitted internal_types
      val _ = G.validate_scope graph scope
      val _ = admitted graph limit [node]
      val free = case G.free_variable_nodes graph node of SOME nodes => nodes
        | NONE => raise ERR "normalize" "unknown binder free nodes"
      val replacements = List.foldl (fn (variable,table) =>
        let val replacement = resolve variable
            val _ = admitted graph limit [replacement]
            val _ = if G.type_id graph variable =
                G.type_id graph replacement then () else
              raise ERR "normalize" "resolved binder variable type mismatch"
        in Redblackmap.insert
          (table,G.node_id variable,replacement) end)
        (Redblackmap.mkDict Int.compare) free
      (* Predict the full output tree before allocating any rebuilt binder.
         A replacement is opaque to simultaneous substitution. *)
      val counts = ref (Redblackmap.mkDict Int.compare)
      fun add left right = if left > limit-right then
          raise ERR "admission" "bounded binder output exhausted"
        else left+right
      fun count original = case Redblackmap.peek
          (!counts,G.node_id original) of SOME size => size
        | NONE =>
            let
              val size = case Redblackmap.peek
                  (replacements,G.node_id original) of
                    SOME replacement =>
                      (case G.unfolded_nodes graph G.RawNodes limit
                          replacement of SOME size =>
                            if size <= limit then size else raise ERR
                              "admission" "bounded binder output exhausted"
                        | NONE => raise ERR "normalize"
                            "unknown normalized binder residue")
                  | NONE => case G.view graph original of
                      G.Application (operator,operand) =>
                        add 1 (add (count operator) (count operand))
                    | G.AdmittedBinder {body,...} => add 1 (count body)
                    | G.OpaqueRetained => raise ERR "normalize"
                        "unadmitted nested binder"
                    | _ => 1
              val _ = counts := Redblackmap.insert
                (!counts,G.node_id original,size)
            in size end
      val _ = ignore (count node)
      val clones = ref (Redblackmap.mkDict
        (fn ((a,b),(c,d)) => case Int.compare (a,c) of
           EQUAL => Int.compare (b,d) | order => order))
      fun clone frame bound original =
        let val key = (G.node_id original,G.scope_id frame) in
          case Redblackmap.peek (!clones,key) of SOME result => result
          | NONE =>
            let val result = case Redblackmap.peek
                (bound,G.node_id original) of SOME replacement => replacement
              | NONE => case Redblackmap.peek
                  (replacements,G.node_id original) of
                    SOME replacement => replacement
                  | NONE => case G.view graph original of
                G.Application (operator,operand) =>
                  G.application graph frame
                    (clone frame bound operator,clone frame bound operand)
              | G.AdmittedBinder {binder,body,...} =>
                  let
                    val nested = G.new_scope graph frame []
                    val fresh = G.fresh_bound_variable graph nested
                      (G.representative graph binder)
                    val bound = Redblackmap.insert
                      (bound,G.node_id binder,fresh)
                    val body = clone nested bound body
                  in G.abstraction graph frame limit (fresh,body) end
              | G.OpaqueRetained => raise ERR "normalize"
                  "unadmitted nested binder"
              | G.Variable (G.Bound,_) => raise ERR "normalize"
                  "bound node outside its recorded frame"
              | _ => original
                val _ = clones := Redblackmap.insert (!clones,key,result)
            in result end
        end
      val normalized = clone scope (Redblackmap.mkDict Int.compare) node
      val _ = admitted graph limit [normalized]
      val relation = Relation {graph = graph,scope = scope,
        left = node,right = normalized,assignments = [],limit = limit,
        internal_types = internal_types}
    in (normalized,relation) end

  fun normalize graph = normalize_using true graph
  fun normalize_raw graph = normalize_using false graph

  fun prove graph scope (relation as Relation
      {graph = owner,scope = frame,left,right,limit,internal_types,...})
      definitions =
    (active relation;G.validate_scope graph scope;
     if G.root_scope owner = G.root_scope graph andalso frame = scope then
       checked internal_types graph scope (left,right) limit definitions
     else raise ERR "prove" "relation belongs to another graph/scope")
end
