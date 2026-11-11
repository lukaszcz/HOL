(* Copyright (c) 2026 The HOL4 contributors. *)
(* Checked canonical free-variable IDs in bounded Source binders. *)
structure SmtReplaySourceBinderAlignment :> SmtReplaySourceBinderAlignment =
struct
  open SmtReplayGraph SmtReplayProof SmtReplayImport SmtReplayBinder
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  val ERR = Feedback.mk_HOL_ERR "SmtReplaySourceBinderAlignment"
  type binder_contract =
    {source_variables : G.node list,allow_bound : bool,
     admission : SmtReplayBinder.admission}
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

  fun discover graph scope {source,parsed,admit_binder,check_type} =
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
      fun branch (pair as (left,right)) =
        let
          val {source_variables,allow_bound,
               admission = {metric,input_limit,output_limit,
                            check_type = local_type,refuse}} =
            case admit_binder pair of SOME contract => contract
              | NONE => raise ERR "discover" "unadmitted independent binder"
          fun refusal label =
            (refuse label;raise ERR "discover" ("Source admission: " ^ label))
          val _ = if input_limit >= 1 andalso output_limit >= 1 then () else
            refusal "nonpositive local admission"
          val source_scope = G.node_scope graph left
          val _ = G.validate_scope graph source_scope
          val original = G.representative graph left
          val parsed = G.representative graph right
          val _ = case G.view graph left of G.OpaqueRetained => ()
            | G.AdmittedBinder _ => ()
            | _ => raise ERR "discover" "Source endpoint is not a binder"
          val _ = case G.view graph right of G.AdmittedBinder _ => ()
            | _ => raise ERR "discover" "parsed endpoint is not admitted"
          val _ = if Term.is_abs original then () else
            raise ERR "discover" "opaque Source endpoint is not an abstraction"
          fun raw limit term = case metric of
              G.RawNodes => SmtReplayImport.bounded_raw_size limit term
            | G.BinderInclusiveNodes =>
                SmtReplayImport.bounded_binder_size limit term
          fun bounded label limit term = case raw limit term of
              SOME _ => () | NONE => refusal label
          val _ = bounded "Source binder input" input_limit original
          val _ = case G.unfolded_nodes graph metric input_limit right of
              SOME size => if size <= input_limit then () else
                refusal "parsed binder input"
            | NONE => refusal "unknown parsed binder input"
          val local_equation = boolSyntax.mk_eq (original,parsed)
          val _ = bounded "whole local binder equation" output_limit
            local_equation
          (* The whole local equation is bounded before any body/FV/type
             traversal, ownership matching or kernel ALPHA. *)
          fun term_types [] = ()
            | term_types (term :: rest) =
                (local_type (Term.type_of term);
                 if Term.is_comb term then
                   let val (operator,operand) = Term.dest_comb term in
                     term_types (operator :: operand :: rest) end
                 else if Term.is_abs term then
                   let val (variable,body) = Term.dest_abs term in
                     term_types (variable :: body :: rest) end
                 else term_types rest)
          val _ = term_types [local_equation]
          val _ = List.app (local_type o G.type_of graph)
            (G.reachable graph [right])
          fun owned variable =
            let
              val _ = case G.view graph variable of
                  G.Variable (G.RigidSource,_) => ()
                | G.Variable (G.Bound,_) => if allow_bound then () else
                    raise ERR "discover"
                      "root Source contains a Bound variable"
                | _ => raise ERR "discover"
                    "Source free variable is flexible or generated"
              val _ = local_type (G.type_of graph variable)
              val _ = if G.scope_visible graph scope
                  (G.node_scope graph variable) andalso
                  G.scope_visible graph source_scope
                    (G.node_scope graph variable) then () else
                raise ERR "discover" "Source free variable escapes its owner"
            in G.representative graph variable end
          fun bounded_variables [] _ = ()
            | bounded_variables (_ :: rest) count =
                if count >= input_limit then refusal "Source variable count"
                else bounded_variables rest (count+1)
          val _ = bounded_variables source_variables 0
          val variables = List.map owned source_variables
          val expected_ids = Redblackset.addList
            (Redblackset.empty Int.compare,List.map G.node_id source_variables)
          val _ = if Redblackset.numItems expected_ids =
              List.length source_variables then () else
            raise ERR "discover" "duplicate Source free-variable ID"
          fun different_terms [] = ()
            | different_terms (variable :: rest) =
                (if List.exists (Term.aconv variable) rest then
                   raise ERR "discover" "ambiguous Source variable spelling"
                 else ();different_terms rest)
          val _ = different_terms variables
          val actual_free = Term.free_vars original
          val _ = if List.length actual_free = List.length variables andalso
              List.all (fn variable =>
                List.exists (Term.aconv variable) variables) actual_free
            then ()
            else raise ERR "discover"
              "original typed free-variable set differs"
          fun exact_ids node = case G.free_variable_nodes graph node of
              NONE => raise ERR "discover"
                "unknown admitted Source dependencies"
            | SOME free =>
                let
                  val _ = List.app (fn node => ignore (owned node)) free
                  val ids = Redblackset.addList
                    (Redblackset.empty Int.compare,List.map G.node_id free)
                in if Redblackset.equal (ids,expected_ids) then () else
                  raise ERR "discover" "parsed/source free-variable IDs differ"
                end
          val _ = exact_ids right
          val _ = case G.view graph left of
              G.AdmittedBinder _ => exact_ids left
            | _ => ()
          fun source_admission () = case G.view graph left of
              G.AdmittedBinder _ => (left,Thm.REFL original)
            | _ =>
                let
                  (* Bind exact canonical variables, never solver lexical
                     aliases, and retain the explicit graph IDs. *)
                  val bindings = ListPair.zip (variables,source_variables)
                  val temporary = G.new_scope graph source_scope bindings
                  fun work () =
                    let
                      val admitted = G.admit_binder graph temporary
                        input_limit original
                      val _ = exact_ids (#node admitted)
                      val returned = G.rehome graph scope (#node admitted)
                    in (#node returned,Thm.TRANS (#bridge admitted)
                      (#bridge returned)) end
                  val result = work () handle error =>
                    (G.close_scope graph temporary;raise error)
                  val _ = G.close_scope graph temporary
                in result end
          val (admitted_left,left_bridge) = source_admission ()
          val equality = Thm.TRANS left_bridge
            (G.equality graph (admitted_left,right))
          val node = equation graph scope pair
          val _ = bounded "completed local binder equation" output_limit
            (G.representative graph node)
          val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl equality)
            (G.representative graph node)) equality
          val _ = if List.null (Thm.hyp exact) andalso clean exact then () else
            raise ERR "discover" "Source witness is not a closed checked law"
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
                    | (G.AdmittedBinder _,G.AdmittedBinder _) =>
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
