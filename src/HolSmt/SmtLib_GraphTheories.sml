(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphTheories :> SmtLib_GraphTheories =
struct
  open SmtLib_GraphBackend SmtLib_Parser SmtLib_Theories SmtLib_Logics
  structure B = SmtLib_GraphBackend
  structure P = SmtLib_Parser
  structure T = SmtLib_Theories
  structure L = SmtLib_Logics
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphTheories"
  datatype support = Recipe | Scoped of string | Shape of string
                   | Unregistered
  type limits =
    {template_limit : int, index_limit : int, operand_limit : int,
     token_limit : int}
  type entry =
    {theory : string, name : string, overload : int, support : support,
     metadata : T.symbol_metadata list}
  type 'a dictionaries =
    Type.hol_type P.dict * 'a P.construction_dict
  type callback = string -> Term.term list -> Term.term list -> Term.term
  type packet =
    {theory : string, dictionary : Term.term P.dict,
     metadata : T.symbol_metadata list, support : string -> support}

  fun recipe _ = Recipe
  fun word_support "@bbterm" =
        Shape "bit-selector/Boolean constructor recovery requires graph IDs"
    | word_support _ = Recipe
  fun sequence_support "seq.unit" =
        Shape "String selector provenance requires graph constructor roles"
    | sequence_support _ = Recipe
  fun set_support name =
    if List.exists (fn value => value = name)
        ["set.filter", "set.all", "set.some"] then
      Scoped "set predicate construction inserts actual operands below binder"
    else if name = "set.comprehension" then
      Shape "set comprehension must inspect admitted binder identities"
    else Recipe
  fun bag_support name =
    if List.exists (fn value => value = name)
        ["bag", "bag.difference_remove", "bag.some", "bag.partition"] then
      Scoped "bag construction inserts actual operands below binder"
    else Recipe

  (* These are audited constructor families: their admitted callbacks
     inspect types/indices or build constant/application syntax. Exceptions
     that inspect an operand's shape or introduce operand-bearing binders
     are classified above and never fed schematic stand-ins. *)
  val packets : packet list =
    [{theory = "Core", dictionary = T.Core.tmdict,
      metadata = T.Core.metadata, support = recipe},
     {theory = "Ints", dictionary = T.Ints.tmdict,
      metadata = T.Ints.metadata, support = recipe},
     {theory = "Reals", dictionary = T.Reals.tmdict,
      metadata = T.Reals.metadata, support = recipe},
     {theory = "Reals_Ints", dictionary = T.Reals_Ints.tmdict,
      metadata = T.Reals_Ints.metadata, support = recipe},
     {theory = "Fixed_Size_BitVectors",
      dictionary = T.Fixed_Size_BitVectors.tmdict,
      metadata = T.Fixed_Size_BitVectors.metadata, support = word_support},
     {theory = "FloatingPoint", dictionary = T.FloatingPoint.tmdict,
      metadata = T.FloatingPoint.metadata, support = recipe},
     {theory = "ArraysEx", dictionary = T.ArraysEx.tmdict,
      metadata = T.ArraysEx.metadata, support = recipe},
     {theory = "HO-Core", dictionary = T.HO_Core.tmdict,
      metadata = T.HO_Core.metadata, support = recipe},
     {theory = "UnicodeStrings", dictionary = T.UnicodeStrings.tmdict,
      metadata = T.UnicodeStrings.metadata, support = recipe},
     {theory = "Seq_Extensions", dictionary = T.Seq_Extensions.tmdict,
      metadata = T.Seq_Extensions.metadata, support = sequence_support},
     {theory = "CVC5_Seq", dictionary = T.CVC5_Seq.tmdict,
      metadata = T.CVC5_Seq.metadata, support = recipe},
     {theory = "Z3_Seq", dictionary = T.Z3_Seq.tmdict,
      metadata = T.Z3_Seq.metadata, support = recipe},
     {theory = "CVC5_Set", dictionary = T.CVC5_Set.tmdict,
      metadata = T.CVC5_Set.metadata, support = set_support},
     {theory = "CVC5_Bag", dictionary = T.CVC5_Bag.tmdict,
      metadata = T.CVC5_Bag.metadata, support = bag_support},
     {theory = "Z3_Set", dictionary = T.Z3_Set.tmdict,
      metadata = T.Z3_Set.metadata, support = recipe}]

  (* Dictionary unions retain callback objects. Matching those objects
     identifies the exact audited registry entry without reordering or
     selecting builders just by potentially overloaded spelling. *)
  fun registered name (parse : callback) =
    let
      fun matches ({dictionary, ...} : packet) =
        case Redblackmap.peek (dictionary, name) of
          NONE => false
        | SOME callbacks => List.exists
            (fn callback => Portable.pointer_eq (callback, parse)) callbacks
    in List.find matches packets end
  fun mixed_arithmetic name parse =
    List.exists (fn symbol => symbol = name)
      ["=", "-", "+", "*", "/", "<=", "<", ">=", ">"] andalso
    (case Redblackmap.peek (L.AUFLIRA.tmdict, name) of
       NONE => false
     | SOME callbacks => List.exists
         (fn callback => Portable.pointer_eq (callback, parse)) callbacks)
  fun word_alias name parse =
    List.exists (fn symbol => symbol = name)
      ["bvudiv_i", "bvurem_i", "bvsdiv_i", "bvsrem_i"] andalso
    (case Redblackmap.peek (L.QF_BV.tmdict, name) of
       NONE => false
     | SOME callbacks => List.exists
         (fn callback => Portable.pointer_eq (callback, parse)) callbacks)

  fun describe name overload parse : entry =
    case registered name parse of
      SOME {theory, metadata, support, ...} =>
        {theory = theory, name = name, overload = overload,
         support = support name,
         metadata = List.filter (fn (entry : T.symbol_metadata) =>
           #kind entry = "term" andalso #name entry = name) metadata}
    | NONE => if mixed_arithmetic name parse then
        {theory = "AUFLIRA", name = name, overload = overload,
         support = Recipe, metadata = []}
      else if word_alias name parse then
        {theory = "Z3_BV_alias", name = name, overload = overload,
         support = Recipe, metadata = []}
      else {theory = "unregistered", name = name, overload = overload,
        support = Unregistered, metadata = []}

  fun checked_limits ({template_limit, index_limit, operand_limit,
                       token_limit} : limits) =
    if template_limit > 0 andalso index_limit > 0 andalso
       operand_limit > 0 andalso token_limit > 0 then ()
    else raise ERR "limits" "nonpositive graph constructor contract"

  fun schema (limits : limits) (parse : callback) token
      {indices, operand_types, argument_offset} =
    let
      val _ = if String.size token <= #token_limit limits then () else
        raise ERR "schema" "constructor token exceeds bounded contract"
      val _ = if List.length operand_types <= #operand_limit limits then ()
        else raise ERR "schema" "constructor operand count exceeds contract"
      val _ = if argument_offset = 0 then () else
        raise ERR "schema" "semantic indices require an ID-aware constructor"
      fun index (P.RecipeLiteral term) =
            (case SmtReplayImport.bounded_raw_size (#index_limit limits)
                term of SOME _ => term
             | NONE => raise ERR "schema" "expanded literal index")
        | index (P.RecipeSymbol name) =
            if String.size name <= #token_limit limits then
              Term.mk_var (name, Type.mk_vartype "'smtlib_index")
            else raise ERR "schema" "symbol index exceeds bounded contract"
        | index (P.RecipeOperand _) =
            raise ERR "schema" "semantic indices require graph constructor"
      val holes = Lib.mapi (fn position => fn ty => Term.mk_var
        ("__smt_recipe_operand_" ^ Int.toString position, ty)) operand_types
      (* Native type instantiation occurs on this bounded schema before any
         actual graph operands are plugged. Declaration IDs stay intact. *)
      val template = parse token (List.map index indices) holes
    in B.compile_recipe {template = template, holes = holes,
      template_limit = #template_limit limits} end

  fun deferred ({theory, name, support, ...} : entry) _ _ _ _ =
    let val reason = case support of
        Scoped reason => reason | Shape reason => reason
      | Unregistered => "no audited graph constructor registered"
      | Recipe => "unexpected recipe refusal"
    in raise ERR "constructor"
      (theory ^ "." ^ name ^ ": " ^ reason) end

  fun select_with backend limits special {logic, solver} =
    let
      val _ = checked_limits limits
      fun dictionaries logic = case solver of
          NONE => L.parsedicts_of_logic logic
        | SOME solver => L.parsedicts_of_solver_logic solver logic
      (* Match translation parser selection for native datatype logics. *)
      val (tydict, dictionary) = dictionaries logic
        handle error as Feedback.HOL_ERR _ =>
          if String.isSubstring "DT" logic then dictionaries "ALL"
          else raise error
      val entries = Redblackmap.foldl (fn (name, callbacks, entries) =>
        entries @ Lib.mapi (fn overload => fn parse =>
          describe name overload parse) callbacks) [] dictionary
      fun adapt name overload parse =
        let val description = describe name overload parse in
          case special description of SOME parse => parse
          | NONE => case #support description of
              Recipe => P.construction_recipe_parsefn backend
                (schema limits parse)
            | _ => deferred description
        end
      val dictionary = Redblackmap.map (fn (name, callbacks) =>
        Lib.mapi (fn overload => adapt name overload) callbacks) dictionary
    in {dictionaries = (tydict, dictionary), entries = entries,
      metadata = L.metadata_of_logic logic} end
  fun recipe_parsefn backend limits parse =
    (checked_limits limits;
     P.construction_recipe_parsefn backend (schema limits parse))
  fun select backend limits options =
    select_with backend limits (fn _ => NONE) options

  fun bind_sources backend frame sources dictionary =
    List.foldl (fn ((key, original), dictionary) =>
      Library.extend_dict
        ((key, P.construction_value_parsefn backend
           (B.source backend frame original)), dictionary)) dictionary sources

  val integer_hole = Term.mk_var ("__smt_recipe_integer", intSyntax.int_ty)
  val integer_to_real = B.compile_recipe
    {template = intrealSyntax.mk_real_of_int integer_hole,
     holes = [integer_hole], template_limit = 32}
  fun coerce_arguments backend frame arguments =
    let
      fun coerce value =
        if Type.compare (B.type_of backend value, intSyntax.int_ty) = EQUAL
        then (B.construct backend frame integer_to_real [value], true)
        else (value, false)
      val coerced = List.map coerce arguments
    in (List.map #1 coerced, List.exists #2 coerced) end
  type policy_limits = SmtReplayResourcePolicy.recipe_policy
  fun policy_list_length pending =
    let fun count [] (n:IntInf.int) = n
          | count (_::rest) n = count rest (n+1)
    in count pending 0 end
  fun checked_policy_limits
      ({template_limit,index_limit,operand_limit,token_limit}:policy_limits) =
    if List.all SmtReplayResourcePolicy.positive
        [template_limit,index_limit,operand_limit,token_limit] then ()
    else raise ERR "limits" "nonpositive graph constructor contract"
  fun schema_with_policy (limits : policy_limits) (parse : callback) token
      {indices, operand_types, argument_offset} =
    let
      val _ = if SmtReplayResourcePolicy.allows (#token_limit limits)
          (IntInf.fromInt (String.size token)) then () else
        raise ERR "schema" "constructor token exceeds bounded contract"
      val _ = if SmtReplayResourcePolicy.allows (#operand_limit limits)
          (policy_list_length operand_types) then ()
        else raise ERR "schema" "constructor operand count exceeds contract"
      val _ = if argument_offset = 0 then () else
        raise ERR "schema" "semantic indices require an ID-aware constructor"
      fun index (P.RecipeLiteral term) =
            (case SmtReplayImport.raw_size_with_policy (#index_limit limits)
                term of SOME _ => term
             | NONE => raise ERR "schema" "expanded literal index")
        | index (P.RecipeSymbol name) =
            if SmtReplayResourcePolicy.allows (#token_limit limits)
                (IntInf.fromInt (String.size name)) then
              Term.mk_var (name, Type.mk_vartype "'smtlib_index")
            else raise ERR "schema" "symbol index exceeds bounded contract"
        | index (P.RecipeOperand _) =
            raise ERR "schema" "semantic indices require graph constructor"
      val holes = Lib.mapi (fn position => fn ty => Term.mk_var
        ("__smt_recipe_operand_" ^ Int.toString position, ty)) operand_types
      (* Native type instantiation occurs on this bounded schema before any
         actual graph operands are plugged. Declaration IDs stay intact. *)
      val template = parse token (List.map index indices) holes
    in B.compile_recipe_with_policy {template = template, holes = holes,
      template_limit = #template_limit limits} end

  fun construction_recipe_parsefn_with_policy backend build frame
      token indices arguments =
    let
      fun index (LiteralIndex term, (descriptions, values, next)) =
            (RecipeLiteral term :: descriptions, values, next)
        | index (SymbolIndex name, (descriptions, values, next)) =
            (RecipeSymbol name :: descriptions, values, next)
        | index (ValueIndex (value, _), (descriptions, values, next)) =
            (RecipeOperand {position = next,
                            hol_type = B.type_of backend value}
               :: descriptions,
             value :: values, next + 1)
      val (descriptions, values, offset) = List.foldl index ([], [], 0) indices
      val operands = List.rev values @ arguments
      val recipe = build token
        {indices = List.rev descriptions,
         operand_types = List.map (B.type_of backend) operands,
         argument_offset = offset}
    in B.construct_with_policy backend frame recipe operands end

  fun select_with_policy backend limits special {logic, solver} =
    let
      val _ = checked_policy_limits limits
      fun dictionaries logic = case solver of
          NONE => L.parsedicts_of_logic logic
        | SOME solver => L.parsedicts_of_solver_logic solver logic
      (* Match translation parser selection for native datatype logics. *)
      val (tydict, dictionary) = dictionaries logic
        handle error as Feedback.HOL_ERR _ =>
          if String.isSubstring "DT" logic then dictionaries "ALL"
          else raise error
      val entries = Redblackmap.foldl (fn (name, callbacks, entries) =>
        entries @ Lib.mapi (fn overload => fn parse =>
          describe name overload parse) callbacks) [] dictionary
      fun adapt name overload parse =
        let val description = describe name overload parse in
          case special description of SOME parse => parse
          | NONE => case #support description of
              Recipe => construction_recipe_parsefn_with_policy backend
                (schema_with_policy limits parse)
            | _ => deferred description
        end
      val dictionary = Redblackmap.map (fn (name, callbacks) =>
        Lib.mapi (fn overload => adapt name overload) callbacks) dictionary
    in {dictionaries = (tydict, dictionary), entries = entries,
      metadata = L.metadata_of_logic logic} end
  fun recipe_parsefn_with_policy backend limits parse =
    (checked_policy_limits limits;
     construction_recipe_parsefn_with_policy backend
       (schema_with_policy limits parse))
  fun select_with_policy_no_override backend limits options =
    select_with_policy backend limits (fn _ => NONE) options


end
