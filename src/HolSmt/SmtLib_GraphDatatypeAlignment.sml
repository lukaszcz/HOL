(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphDatatypeAlignment :> SmtLib_GraphDatatypeAlignment =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayImport
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphDatatypeAlignment"
  datatype relation = Same of G.node
    | Application of G.node * G.node * (int * int) * (int * int)
    | Branch of G.node
  datatype work = Visit of G.node * G.node
    | Finish of G.node * G.node * (int * int) * (int * int)
  datatype alignment = Alignment of
    {graph : G.graph, scope : G.scope, source : G.node, parsed : G.node,
     relations : ((int * int),relation) Redblackmap.dict,
     witnesses : (G.node * Thm.thm) list, roots : G.node list,
     order : (int * int) list}
  fun pair_compare ((a,b),(c,d)) = case Int.compare (a,c) of
      EQUAL => Int.compare (b,d) | order => order
  fun key (left,right) = (G.node_id left,G.node_id right)
  fun active (Alignment {graph,scope,...}) = G.validate_scope graph scope
  fun source (alignment as Alignment {source,...}) = (active alignment;source)
  fun parsed (alignment as Alignment {parsed,...}) = (active alignment;parsed)
  fun roots (alignment as Alignment {roots,...}) = (active alignment;roots)
  fun branch_witnesses (alignment as Alignment {witnesses,...}) =
    (active alignment;witnesses)
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem) in
      List.all (fn tag => tag = "DISK_THM") tags andalso
      List.null (Tag.axioms_of (Thm.tag theorem)) end
  fun equation graph scope (left,right) =
    let
      val marker = Term.genvar (G.type_of graph left)
      val operator = G.constant graph scope
        (Term.rator (Term.rator (boolSyntax.mk_eq (marker,marker))))
    in G.application graph scope
      (G.application graph scope (operator,left),right) end

  fun discover graph scope {source,parsed,admit_branch,check_type} =
    let
      val _ = G.validate_scope graph scope
      val relations = ref (Redblackmap.mkDict pair_compare)
      val order = ref []
      val witnesses = ref []
      val roots = ref [source,parsed]
      val types = ref (Redblackset.empty Int.compare)
      fun admit_type node =
        let val id = G.type_id graph node in
          if Redblackset.member (!types,id) then () else
            (check_type (G.type_of graph node);
             types := Redblackset.add (!types,id)) end
      fun visible node =
        if G.scope_visible graph scope (G.node_scope graph node) then () else
          raise ERR "discover" "source/parser node is outside replay scope"
      fun bounded label limit term =
        case SmtReplayImport.bounded_raw_size limit term of SOME _ => ()
        | NONE => raise ERR "discover" (label ^ " exceeds branch admission")
      fun closed node = case G.free_variable_nodes graph node of
          SOME [] => ()
        | _ => raise ERR "discover" "datatype branch is not known closed"
      fun admitted limit node =
        case G.view graph node of
          G.OpaqueRetained =>
            let
              val original = G.representative graph node
              val _ = if Term.is_abs original then () else
                raise ERR "discover" "opaque branch is not an abstraction"
              val _ = bounded "source binder" limit original
              val source = G.admit_binder graph scope limit original
              val _ = closed (#node source)
            in (#node source,#bridge source) end
        | G.AdmittedBinder _ =>
            let
              val _ = case G.unfolded_nodes graph G.RawNodes limit node of
                  SOME size => if size <= limit then () else
                    raise ERR "discover" "parsed binder exceeds admission"
                | NONE => raise ERR "discover" "unknown parsed binder size"
              val _ = closed node
            in (node,Thm.REFL (G.representative graph node)) end
        | _ => raise ERR "discover" "branch pair is not a binder pair"
      fun branch pair =
        let
          val limit = case admit_branch pair of SOME limit => limit
            | NONE => raise ERR "discover" "unadmitted independent binder"
          val _ = if limit > 0 then () else
            raise ERR "discover" "nonpositive branch admission"
          val (left,right) = pair
          (* Preflight the entire local equality before source admission or
             ALPHA. The case root and its scrutinee never enter this metric. *)
          val local_equation = boolSyntax.mk_eq
            (G.representative graph left,G.representative graph right)
          val _ = bounded "local binder equation" limit local_equation
          val (admitted_left,left_bridge) = admitted limit left
          val (admitted_right,right_bridge) = admitted limit right
          val _ = List.app admit_type
            (G.reachable graph [admitted_left,admitted_right])
          val equality = Thm.TRANS left_bridge
            (Thm.TRANS (G.equality graph (admitted_left,admitted_right))
              (Thm.SYM right_bridge))
          val node = equation graph scope pair
          val _ = bounded "completed binder equation" limit
            (G.representative graph node)
          val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl equality)
            (G.representative graph node)) equality
          val _ = if List.null (Thm.hyp exact) andalso clean exact then () else
            raise ERR "discover" "branch witness is not a closed checked law"
          val _ = witnesses := (node,exact) :: !witnesses
          val _ = roots := node :: !roots
        in Branch node end
      fun retain pair relation =
        (relations := Redblackmap.insert (!relations,key pair,relation);
         order := key pair :: !order)
      fun visit [] = ()
        | visit (Finish (left,right,operator,operand) :: rest) =
            (retain (left,right) (Application (left,right,operator,operand));
             visit rest)
        | visit (Visit (pair as (left,right)) :: rest) =
            let
              (* Check owners before the numeric memo key can match. *)
              val _ = visible left
              val _ = visible right
            in case Redblackmap.peek (!relations,key pair) of
                SOME _ => visit rest
              | NONE =>
                  let
                    val _ = admit_type left
                    val _ = admit_type right
                    val _ = if G.type_id graph left = G.type_id graph right
                      then () else raise ERR "discover"
                        "source/parser type mismatch"
                  in if left = right then
                      (retain pair (Same left);visit rest)
                    else case (G.view graph left,G.view graph right) of
                      (G.Application (lf,lx),G.Application (rf,rx)) =>
                        visit (Visit (lf,rf) :: Visit (lx,rx) ::
                          Finish (left,right,key (lf,rf),key (lx,rx)) :: rest)
                    | (G.OpaqueRetained,G.AdmittedBinder _) =>
                        (retain pair (branch pair);visit rest)
                    | (G.AdmittedBinder _,G.OpaqueRetained) =>
                        (retain pair (branch pair);visit rest)
                    | (G.AdmittedBinder _,G.AdmittedBinder _) =>
                        (retain pair (branch pair);visit rest)
                    | (G.OpaqueRetained,G.OpaqueRetained) =>
                        (retain pair (branch pair);visit rest)
                    | _ => raise ERR "discover"
                        "source/parser declarations or shapes differ"
                  end
            end
      val _ = visit [Visit (source,parsed)]
    in Alignment {graph = graph,scope = scope,source = source,parsed = parsed,
      relations = !relations,witnesses = List.rev (!witnesses),
      roots = !roots,order = List.rev (!order)} end

  fun assemble (alignment as Alignment {graph,scope,source,parsed,
                                        relations,witnesses,order,...}) block =
    let
      val _ = active alignment
      val _ = if G.scope_visible graph (P.scope block) scope then () else
        raise ERR "assemble" "proof block is outside alignment scope"
      val (_,indices) = List.foldl
        (fn (node,(index,table)) =>
          (index+1,if Redblackmap.inDomain (table,G.node_id node) then table
            else Redblackmap.insert (table,G.node_id node,index)))
        (0,Redblackmap.mkDict Int.compare) (P.sources block)
      fun index node = case Redblackmap.peek (indices,G.node_id node) of
          SOME index => index
        | NONE => raise ERR "assemble" "closed branch law absent from sources"
      val _ = List.app (fn (node,_) => ignore (index node)) witnesses
      val memo = ref (Redblackmap.mkDict pair_compare)
      fun proof pair = case Redblackmap.peek (!memo,pair) of
          SOME edge => edge
        | NONE => raise ERR "assemble" "parent precedes child congruence"
      fun assemble pair =
        let
          val edge = case Redblackmap.find (relations,pair) of
              Same node => P.checked block (Thm.REFL (P.name block node))
            | Branch node => P.compose block
                (fn [law,bridge] => Thm.EQ_MP bridge law
                  | _ => raise Fail "branch law constructor")
                [P.source block (index node),P.constructor block node]
            | Application (left,right,operator,operand) =>
                P.compose block
                  (fn [left_definition,operator,operand,right_definition] =>
                    Thm.TRANS left_definition
                      (Thm.TRANS (Thm.MK_COMB (operator,operand))
                        (Thm.SYM right_definition))
                    | _ => raise Fail "compact datatype parent congruence")
                  [P.definition block left,proof operator,proof operand,
                   P.definition block right]
        in memo := Redblackmap.insert (!memo,pair,edge) end
      val _ = List.app assemble order
    in proof (key (source,parsed)) end
end
