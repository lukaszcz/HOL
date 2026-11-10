(* Copyright (c) 2026 The HOL4 contributors. *)

(* Bounded graph hole insertion below owned binders. *)
structure SmtLib_GraphScopedRecipe :> SmtLib_GraphScopedRecipe =
struct
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphScopedRecipe"
  val maximum = case Int.maxInt of SOME maximum => maximum
    | NONE => 1073741823
  datatype syntax = Hole of int | Constant of Term.term
    | Bound of int | Application of syntax * syntax
    | Abstraction of Term.term * syntax
  datatype recipe = Recipe of
    {template : Term.term,holes : Term.term list,template_limit : int}
  fun term_types check_type [] = ()
    | term_types check_type (term :: rest) =
        (check_type (Term.type_of term);
         if Term.is_comb term then
           let val (operator,operand) = Term.dest_comb term in
             term_types check_type (operator :: operand :: rest) end
         else if Term.is_abs term then
           let val (variable,body) = Term.dest_abs term in
             term_types check_type (variable :: body :: rest) end
         else term_types check_type rest)
  fun bounded_count label limit values =
    let fun loop [] _ = ()
          | loop (_ :: rest) count =
              if count >= limit then raise ERR label "too many entries"
              else loop rest (count+1)
    in loop values 0 end
  fun exact_holes template holes =
    let
      val _ = List.app (fn hole => if Term.is_var hole then () else
        raise ERR "compile" "operand hole is not a typed variable") holes
      fun unique [] = ()
        | unique (hole :: rest) =
            (if List.exists (Term.aconv hole) rest then
               raise ERR "compile" "duplicate typed operand hole"
             else ();unique rest)
      val _ = unique holes
      val free = Term.free_vars template
      val _ = if List.length free = List.length holes andalso
          List.all (fn variable =>
            List.exists (Term.aconv variable) holes) free then () else
        raise ERR "compile" "template free variables differ from its holes"
    in () end
  fun compile {template,holes,template_limit,check_type} =
    let
      val _ = if template_limit > 0 then () else
        raise ERR "compile" "nonpositive template admission"
      val _ = case SmtReplayImport.bounded_raw_size template_limit template of
          SOME _ => ()
        | NONE => raise ERR "compile" "template exceeds bounded admission"
      val _ = bounded_count "compile" template_limit holes
      val _ = term_types check_type (template :: holes)
      val _ = exact_holes template holes
    in Recipe {template = template,holes = holes,
      template_limit = template_limit} end
  fun syntax template holes =
    let
      fun index variable values =
        let fun find [] _ = NONE
              | find (value :: rest) count =
                  if Term.aconv variable value then SOME count
                  else find rest (count+1)
        in find values 0 end
      fun visit bound term =
        if Term.is_var term then
          (case index term bound of SOME index => Bound index
            | NONE => (case index term holes of SOME index => Hole index
                | NONE => raise ERR "syntax" "unowned template variable"))
        else if Term.is_const term then Constant term
        else if Term.is_comb term then
          let val (operator,operand) = Term.dest_comb term in
            Application (visit bound operator,visit bound operand) end
        else
          let val (variable,body) = Term.dest_abs term in
            Abstraction (variable,visit (variable :: bound) body) end
    in visit [] template end

  fun construct graph scope
      (Recipe {template,holes,template_limit})
      {operands,expected_result_type,
       admission = {metric,input_limit,output_limit,check_type,refuse},
       scope_opened} =
    let
      fun refusal label =
        (refuse label;raise ERR "construct" ("recipe admission: " ^ label))
      val _ = G.validate_scope graph scope
      val _ = if input_limit > 0 andalso output_limit > 0 andalso
          input_limit < maximum andalso output_limit < maximum then () else
        refusal "invalid operand/output admission"
      val _ = bounded_count "construct" template_limit operands
      val _ = if List.length operands = List.length holes then () else
        raise ERR "construct" "recipe operand arity mismatch"
      fun operand_size node =
        let
          val _ = if G.scope_visible graph scope (G.node_scope graph node)
            then () else raise ERR "construct" "operand escapes its owner"
        in case G.unfolded_nodes graph metric input_limit node of
            SOME size => if size <= input_limit then size else
              (refusal "operand input";raise Fail "unreachable refusal")
          | NONE => (refusal "unknown operand input";
              raise Fail "unreachable refusal") end
      (* Every actual size is admitted before any FV/type traversal. *)
      val sizes = Vector.fromList (List.map operand_size operands)
      fun operand_free node =
        let
          val free = case G.free_variable_nodes graph node of
              SOME free => free
            | NONE => (refusal "unknown operand free IDs";
                raise Fail "unreachable refusal")
          val _ = List.app (fn variable =>
            (case G.view graph variable of G.Variable _ => ()
              | _ => raise ERR "construct" "malformed operand FV metadata";
             if G.scope_visible graph scope (G.node_scope graph variable)
               then () else raise ERR "construct" "operand FV escapes owner"))
            free
        in free end
      val operand_frees = List.map operand_free operands
      val _ = List.app (check_type o G.type_of graph)
        (G.reachable graph operands)
      val _ = term_types check_type (template :: holes)
      val _ = Option.app check_type expected_result_type
      fun match ((hole,node),context) = Type.raw_match_type
        (Term.type_of hole) (G.type_of graph node) context
      val context = List.foldl match ([],[]) (ListPair.zip (holes,operands))
      val context = case expected_result_type of NONE => context
        | SOME expected => Type.raw_match_type
            (Term.type_of template) expected context
      val substitution = #1 context
      (* Only the admitted small template and its schematic holes enter
         type instantiation. Actual operand representatives stay retained. *)
      val instantiated = Term.inst substitution template
      val typed_holes = List.map (Term.inst substitution) holes
      val _ = case SmtReplayImport.bounded_raw_size template_limit
          instantiated of SOME _ => ()
        | NONE => refusal "instantiated template admission"
      val _ = term_types check_type (instantiated :: typed_holes)
      val _ = exact_holes instantiated typed_holes
      val _ = List.app (fn (hole,node) =>
        if Type.compare (Term.type_of hole,G.type_of graph node) = EQUAL
          then () else raise ERR "construct" "instantiated hole type differs")
        (ListPair.zip (typed_holes,operands))
      val tree = syntax instantiated typed_holes
      fun add left right =
        if left > output_limit orelse right > output_limit orelse
            left > output_limit-right then
          (refusal "whole recipe output";raise Fail "unreachable refusal")
        else left+right
      fun measure (Hole index) = add 0 (Vector.sub (sizes,index))
        | measure (Constant _) = add 0 1
        | measure (Bound _) = add 0 1
        | measure (Application (operator,operand)) =
            add 1 (add (measure operator) (measure operand))
        | measure (Abstraction (_,body)) =
            add (case metric of G.RawNodes => 1
                  | G.BinderInclusiveNodes => 2) (measure body)
      val expected_size = measure tree
      (* Exact graph IDs must not become one kernel free variable when
         different actual operands are assembled below the same binder. *)
      fun variable_key_compare ((left,lt),(right,rt)) =
        case String.compare (left,right) of EQUAL => Int.compare (lt,rt)
          | order => order
      val free_keys = ref (Redblackmap.mkDict variable_key_compare)
      fun free_identity node =
        let
          val key = (#1 (Term.dest_var (G.representative graph node)),
            G.type_id graph node)
          val id = G.node_id node
        in case Redblackmap.peek (!free_keys,key) of NONE =>
            free_keys := Redblackmap.insert (!free_keys,key,id)
          | SOME other => if other = id then () else
              raise ERR "construct" "distinct operand free IDs alias" end
      val _ = List.app (List.app free_identity) operand_frees
      (* Whole prospective output admission precedes every graph scope
         allocation or HOL binder construction carrying actual operands. *)
      val values = Vector.fromList operands
      val branches = ref []
      val closed_scopes = ref []
      fun build current bound (Hole index) = Vector.sub (values,index)
        | build current bound (Constant term) = G.constant graph current term
        | build current bound (Bound index) = List.nth (bound,index)
        | build current bound (Application (operator,operand)) =
            G.application graph current
              (build current bound operator,build current bound operand)
        | build current bound (Abstraction (variable,body)) =
            let
              val child = G.new_scope graph current []
              fun close () =
                (G.close_scope graph child;
                 closed_scopes := child :: !closed_scopes)
              fun work () =
                let
                  val _ = scope_opened child
                  val binder = G.fresh_bound_variable graph child variable
                  val body = build child (binder :: bound) body
                  val node = G.abstraction graph current output_limit
                    (binder,body)
                  val _ = branches := node :: !branches
                in node end
              val node = work () handle error => (close ();raise error)
              val _ = close ()
            in node end
      val node = build scope [] tree
      val _ = if Type.compare (G.type_of graph node,
          Term.type_of instantiated) = EQUAL then () else
        raise ERR "construct" "constructed result type differs"
      val _ = case G.unfolded_nodes graph metric output_limit node of
          SOME size => if size = expected_size then () else
            raise ERR "construct" "constructed metric differs from recipe"
        | NONE => raise ERR "construct" "constructed output is unknown"
    in {node = node,branches = List.rev (!branches),
      closed_scopes = List.rev (!closed_scopes)} end
end
