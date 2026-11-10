(* Pure current-core recipe admission; constructs no theorem or proof block. *)
structure CPC_GraphNativeAdmission :> CPC_GraphNativeAdmission =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure Rules = SmtReplayRules
  structure Parser = CPC_ProofParser
  exception Adapter
  datatype unsupported = ScopedCommandAdapter | UnsupportedCommand
  exception Defer of unsupported
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphNativeAdmission"
  datatype fact = Fact of
    {node : G.node,recipe : recipe,occurrence : int}
  and recipe = Original of int | Pending of int | Reflexive of G.node
    | Symmetric of fact
    | Contradiction of fact * fact | Conjunction of fact * fact
    | Selection of int * fact
  fun node (Fact {node,...}) = node
  fun recipe (Fact {recipe,...}) = recipe
  fun occurrence (Fact {occurrence,...}) = occurrence
  datatype plan = Plan of
    {graph : G.graph,scope : G.scope,proof : Parser.graph_proof,
     sources : S.sources,canonical : G.node list,root : fact,
     all : G.node list,obligations : (int * G.node) list,
     limit : int,check_type : Type.hol_type -> unit}
  fun prepare {graph,scope,proof : Parser.graph_proof,sources,
               template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 then () else raise Adapter
      val canonical = S.assumption_nodes sources @ [S.denied_goal_node sources]
      val falsehood = G.constant graph scope boolSyntax.F
      fun equality (left,right) =
        let val marker = Term.genvar (G.type_of graph left)
            val operator = G.constant graph scope (Term.rator (Term.rator
              (boolSyntax.mk_eq (marker,marker))))
        in G.application graph scope
          (G.application graph scope (operator,left),right) end
      val known = ref (Redblackmap.mkDict String.compare)
      val obligations = ref ([] : (int * G.node) list)
      val independent = ref ([] : G.node list)
      val last = ref (NONE : fact option)
      val captured = ref 0
      val fact_nodes = ref ([] : G.node list)
      fun new_fact {node,recipe} =
        let val serial = !captured
            val _ = captured := serial+1
            val _ = fact_nodes := node :: !fact_nodes
        in Fact {node = node,recipe = recipe,occurrence = serial} end
      fun add id fact =
        if Redblackmap.inDomain (!known,id) then
          raise Defer ScopedCommandAdapter
        else (known := Redblackmap.insert (!known,id,fact);last := SOME fact)
      fun find id = case Redblackmap.peek (!known,id) of SOME fact => fact
        | NONE => raise ERR "command" "unknown or expired premise ID"
      fun declared step target = case #conclusion
          (step : Parser.graph_rule_step) of NONE => () | SOME value =>
            if #node value = target then () else
              raise ERR "command" "declared native endpoint differs"
      fun original_index target =
        let fun loop [] _ = NONE
              | loop (source :: rest) index =
                  if source = target andalso Portable.pointer_eq
                      (G.representative graph source,
                       G.representative graph target) then SOME index
                  else loop rest (index+1)
        in loop canonical 0 end
      fun source_index target = case original_index target of
          SOME index => index
        | NONE => raise ERR "command"
            "assumption is not a canonical original Source"
      fun command (Parser.GraphAssume (id,value)) =
            add id (new_fact {node = #node value,
                         recipe = Original (source_index (#node value))})
        | command (Parser.GraphAssumePush _) = raise Defer ScopedCommandAdapter
        | command (Parser.GraphStep {step,pop}) =
            if pop then raise Defer ScopedCommandAdapter else
            let
              val name = #replay_handler (#rule step)
              val _ = if (name = "trust" orelse name = "refl") andalso
                  not (null (#premises step)) then
                raise Defer UnsupportedCommand else ()
              val fact = if name = "trust" then
                  (case #args step of [Parser.GraphTerm value] =>
                    let val target = #node value
                        val _ = declared step target
                        val index = length (!obligations)
                        val serial = !captured
                        (* Keep the command occurrence even when its exact
                           target already has canonical original authority. *)
                        val recipe = case original_index target of
                            SOME source => Original source
                          | NONE =>
                              Pending index
                        val _ = obligations := (serial,target) :: !obligations
                    in new_fact {node = target,recipe = recipe} end
                   | _ => raise Defer UnsupportedCommand)
                else if name = "refl" then
                  (case #args step of [Parser.GraphTerm value] =>
                    let val operand = #node value
                        val target = equality (operand,operand)
                        val _ = declared step target
                        val _ = independent := target :: !independent
                    in new_fact {node = target,recipe = Reflexive operand} end
                   | _ => raise Defer UnsupportedCommand)
                else if name = "symm" then
                  (case (List.map find (#premises step),#args step) of
                     ([premise],[]) =>
                       (case SmtReplayRules.equality graph (node premise) of
                          SOME (left,right) =>
                            let val target = equality (right,left)
                                val _ = declared step target
                            in new_fact {node = target,
                              recipe = Symmetric premise} end
                        | NONE => raise Defer UnsupportedCommand)
                   | _ => raise Defer UnsupportedCommand)
                else if name = "and_intro" then
                  (case (List.map find (#premises step),#args step) of
                     ([left,right],[]) =>
                       let val operator = G.constant graph scope
                             boolSyntax.conjunction
                           val target = G.application graph scope
                             (G.application graph scope
                               (operator,node left),node right)
                           val _ = declared step target
                       in new_fact {node = target,
                         recipe = Conjunction (left,right)} end
                   | _ => raise Defer UnsupportedCommand)
                else if name = "and_elim" then
                  (case (List.map find (#premises step),#args step) of
                     ([premise],[Parser.GraphIndex index]) =>
                       if index = 0 orelse index = 1 then
                         (case Rules.operands graph boolSyntax.conjunction 2
                             (node premise) of SOME operands =>
                           let val target = List.nth (operands,index)
                               val _ = declared step target
                           in new_fact {node = target,
                             recipe = Selection (index,premise)} end
                          | _ => raise ERR "command" "nonbinary conjunction")
                       else raise Defer UnsupportedCommand
                   | _ => raise Defer UnsupportedCommand)
                else if name = "contra" then
                  let val premises = List.map find (#premises step)
                      fun choose [] = raise ERR "command"
                            "native contra lacks exact opposite facts"
                        | choose (positive :: rest) =
                            case List.find (fn negative =>
                              case Rules.operands graph boolSyntax.negation 1
                                  (node negative) of
                                SOME [body] => body = node positive
                              | _ => false) premises of
                                SOME negative => (positive,negative)
                              | NONE => choose rest
                      val pair = choose premises
                      val _ = declared step falsehood
                  in new_fact {node = falsehood,
                    recipe = Contradiction pair} end
                else raise Defer UnsupportedCommand
            in add (#id step) fact end
      val _ = List.app command (#commands proof)
      val root = case !last of SOME root =>
          if node root = falsehood then root else
            raise ERR "command" "native packet does not end in contradiction"
        | NONE => raise ERR "command" "empty native packet"
      val obligations = List.rev (!obligations)
      val all = falsehood :: canonical @ List.map #2 obligations @
        !independent @
        List.rev (!fact_nodes)
      val nodes = G.block_reachable graph all
      val definitions = List.mapPartial (fn node => case G.view graph node of
          G.Constant _ => SOME (5 : IntInf.int)
        | G.Application _ => SOME 7 | _ => NONE) nodes
      val context = if null definitions then 1 else
        List.foldl (op +) 0 definitions +
        3 * IntInf.fromInt (length definitions-1)
      val required = context+4+3*IntInf.fromInt
        (length canonical+length obligations)
      val _ = if required <= IntInf.fromInt template_limit then () else
        raise Adapter
      val _ = List.app (check_type o G.type_of graph) nodes
    in Plan {graph = graph,scope = scope,proof = proof,sources = sources,
      canonical = canonical,root = root,all = all,
      obligations = obligations,limit = template_limit,
      check_type = check_type} end
    handle Defer _ => raise Adapter
  fun validate (Plan {graph,scope,canonical,sources,...}) =
    (G.validate_scope graph scope;
     if canonical = S.assumption_nodes sources @ [S.denied_goal_node sources]
     then () else raise ERR "validate" "original Source changed")
  fun bind (plan as Plan {graph = g,scope = s,proof = p,sources = old,
      limit,check_type = check,...})
      {graph,scope,proof,sources,template_limit,check_type} =
    (validate plan;
     if Portable.pointer_eq (g,graph) andalso s = scope andalso
        Portable.pointer_eq (p,proof) andalso
        Portable.pointer_eq (old,sources) andalso limit = template_limit
        andalso Portable.pointer_eq (check,check_type) then () else
       raise ERR "bind" "wrong packet owner or recipe")
  fun root (plan as Plan {root,...}) = (validate plan;root)
  fun roots (plan as Plan {all,...}) = (validate plan;all)
  fun obligations (plan as Plan {obligations,...}) =
    (validate plan;obligations)
end
