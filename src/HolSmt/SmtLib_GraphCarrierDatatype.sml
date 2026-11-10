structure SmtLib_GraphCarrierDatatype :> SmtLib_GraphCarrierDatatype =
struct
  structure Q = SmtLib_GraphQueryAnalysis

  type errors =
    {syntax_error : string -> string -> exn, is_mismatch : exn -> bool}
  type hooks =
    {parser_case : Q.carrier ->
       Q.carrier SmtLib.outbound_carrier_parser_case option,
     datatype_selector_term : Type.hol_type -> Term.term -> int ->
       Q.carrier -> Q.carrier,
     is_case : Q.carrier -> bool,
     case_view : Q.carrier ->
       {scrutinee:Q.carrier,clauses:(Q.carrier list * Q.carrier) list} option}

  datatype template_kind = Tester | Selector of int

  fun compare_scoped ((left_scope, left_node), (right_scope, right_node)) =
    case Int.compare (left_scope, right_scope) of
      EQUAL => Int.compare (left_node, right_node)
    | result => result

  fun compare_kind (Tester, Tester) = EQUAL
    | compare_kind (Tester, _) = LESS
    | compare_kind (_, Tester) = GREATER
    | compare_kind (Selector left, Selector right) = Int.compare (left, right)

  fun compare_template ((left_ty, left_head, left_kind),
      (right_ty, right_head, right_kind)) =
    case Type.compare (left_ty, right_ty) of
      EQUAL =>
        (case Term.compare (left_head, right_head) of
           EQUAL => compare_kind (left_kind, right_kind)
         | result => result)
    | result => result

  fun compare_recipe ((left_template, left_arg),
      (right_template, right_arg)) =
    case compare_template (left_template, right_template) of
      EQUAL => compare_scoped (left_arg, right_arg)
    | result => result

  fun make (context : Q.outbound_context)
      ({syntax_error, is_mismatch} : errors) : hooks =
    let
      val parser_cache = ref (Redblackmap.mkDict compare_scoped)
      val case_cache = ref (Redblackmap.mkDict compare_scoped)
      val view_cache = ref (Redblackmap.mkDict compare_scoped)
      val template_cache = ref (Redblackmap.mkDict compare_template)
      val recipe_cache = ref (Redblackmap.mkDict compare_recipe)

      fun guard current = ignore ((#key context) current)
      fun mismatch message = raise syntax_error "datatype_case" message
      (* No carrier callback executes inside this pure metadata boundary. *)
      fun metadata thunk = thunk ()
        handle Feedback.HOL_ERR detail =>
          raise syntax_error (Feedback.top_function_of detail)
            (Feedback.message_of detail)
      fun accepts observe current =
        (ignore (observe current); true)
        handle primary => if is_mismatch primary then false else raise primary
      fun application current =
        case (#view context) current of
          Q.ApplicationView operands => operands
        | _ => mismatch "application expected"
      fun abstraction current =
        case (#view context) current of
          Q.AbstractionView operands => operands
        | _ => mismatch "abstraction expected"
      fun same_constant current expected =
        case (#view context) current of
          Q.ConstantView atom => Term.same_const atom expected
        | _ => false

      (* Pmatch.dest_case first recognizes literal_case, then uses the
         datatype's generic case head and a strict constructor/branch zip.
         Peeling and matching the branch binder types retains its shape
         checks without manufacturing raw patterns from query variables. *)
      fun literal_case current =
        let
          val (prefix, argument) = application current
          val (head, function) = application prefix
          val _ = if same_constant head boolSyntax.literal_case then ()
            else mismatch "not literal_case"
        in (function, argument) end
      fun datatype_case current =
        let
          val (head, arguments) = (#strip_comb context) current
          val (scrutinee, branches) =
            case arguments of
              first :: rest => (first, rest)
            | [] => mismatch "case exp has too few args"
          val scrutinee_ty = (#type_of context) scrutinee
          val info = metadata (fn () =>
            let val {Thy, Tyop, ...} = Type.dest_thy_type scrutinee_ty in
              case TypeBase.read {Thy = Thy, Tyop = Tyop} of
                SOME info => info
              | NONE => mismatch "unable to destruct case expression"
            end)
          val case_head = metadata (fn () => TypeBasePure.case_const_of info)
          val _ = if same_constant head case_head then ()
            else mismatch "unable to destruct case expression"
          val constructors =
            metadata (fn () => TypeBasePure.constructors_of info)
          val _ = if List.length constructors = List.length branches then ()
            else mismatch "different constructor and branch counts"
          fun peel [] branch = ([], branch)
            | peel (_ :: domains) branch =
                let val (variable, body) = abstraction branch
                    val (variables, result) = peel domains body
                in (variable :: variables, result) end
          fun validate (constructor, branch) =
            let
              val domains = metadata (fn () =>
                #1 (boolSyntax.strip_fun (Term.type_of constructor)))
              val (variables, body) = peel domains branch
              val variable_types = List.map (#type_of context) variables
              val _ = metadata (fn () =>
                ignore (Term.inst
                  (Type.match_type (Term.type_of constructor)
                    (boolSyntax.list_mk_fun (variable_types, scrutinee_ty)))
                  constructor))
            in (variables,body) end
          val clauses = List.map validate
            (ListPair.zip (constructors,branches))
        in {scrutinee=scrutinee,clauses=clauses} end
      fun dest_case current =
        if accepts literal_case current then
          let val (function, scrutinee) = literal_case current
              val (_,body) = abstraction function
              (* Pmatch's literal_case pattern is a variable; strip_comb
                 consequently supplies no pattern arguments. *)
          in {scrutinee=scrutinee,clauses=[([],body)]} end
        else datatype_case current

      fun guard_case NONE = ()
        | guard_case (SOME {scrutinee,clauses}) =
            (guard scrutinee;List.app (fn (variables,body) =>
              (List.app guard variables;guard body)) clauses)
      fun case_view current =
        let val key = (#key context) current in
          case Redblackmap.peek (!view_cache,key) of
            SOME result => (guard_case result;result)
          | NONE =>
              let val result = SOME (dest_case current)
                    handle primary =>
                      if is_mismatch primary then NONE else raise primary
                  val _ = guard current val _ = guard_case result
                  val _ = view_cache :=
                    Redblackmap.insert (!view_cache,key,result)
              in result end
        end

      fun is_case current =
        let val key = (#key context) current in
          case Redblackmap.peek (!case_cache, key) of
            SOME result => result
          | NONE =>
              let val result = accepts dest_case current
                  val _ = guard current
                  val _ = case_cache :=
                    Redblackmap.insert (!case_cache, key, result)
              in result end
        end

      fun template key argument =
        let val _ = guard argument in
          case Redblackmap.peek (!template_cache, key) of
            SOME result => result
          | NONE =>
              let
                val (ty, constructor, kind) = key
                val result = metadata (fn () =>
                  let val hole = Term.genvar ty
                      val body = case kind of
                          Tester => SmtLib.parser_datatype_tester_template
                            ty constructor hole
                        | Selector index =>
                            SmtLib.parser_datatype_selector_template
                              ty constructor index hole
                  in (hole, body) end)
                val _ = guard argument
                val _ = template_cache :=
                  Redblackmap.insert (!template_cache, key, result)
              in result end
        end

      (* Inspect declaration syntax only. The hole is replaced immediately;
         its potentially large operand never enters a HOL constructor or
         metadata walker. Fresh template binders become outbound Bound-ID
         recipes, including when their bodies contain the original hole. *)
      fun lift (hole, body) argument =
        let
          fun visit environment current =
            let val _ = (#step context) () in
              if Term.is_var current then
                if Term.aconv current hole then argument
                else
                  (case List.find (fn (variable, _) =>
                      Term.aconv current variable) environment of
                     SOME (_, bound) => bound
                   | NONE => mismatch "unbound declaration-template variable")
              else if Term.is_const current then (#constant context) current
              else if Term.is_comb current then
                let val (function, operand) = Term.dest_comb current
                    val function = visit environment function
                    val operand = visit environment operand
                in (#mk_comb context) (function, operand) end
              else
                let val (variable, inner) = Term.dest_abs current
                    val variable_ty = metadata (fn () => Term.type_of variable)
                    val bound = (#genvar context) variable_ty
                    val inner = visit ((variable, bound) :: environment) inner
                in (#list_mk_abs context) ([bound], inner) end
            end
        in visit [] body end

      fun recipe kind ty constructor argument =
        let
          val argument_key = (#key context) argument
          val argument_ty = (#type_of context) argument
          val _ = if Type.compare (argument_ty, ty) = EQUAL then ()
            else mismatch "scrutinee type mismatch"
          val template_key = (ty, constructor, kind)
          val key = (template_key, argument_key)
        in
          case Redblackmap.peek (!recipe_cache, key) of
            SOME result => (guard result; result)
          | NONE =>
              let
                val result = lift (template template_key argument) argument
                val _ = guard argument
                val _ = guard result
                val _ = recipe_cache :=
                  Redblackmap.insert (!recipe_cache, key, result)
              in result end
        end

      fun datatype_selector_term ty constructor index argument =
        recipe (Selector index) ty constructor argument

      fun guard_descriptor NONE = ()
        | guard_descriptor (SOME (SmtLib.CarrierSelector {scrutinee, ...})) =
            guard scrutinee
        | guard_descriptor (SOME (SmtLib.CarrierTester {scrutinee, ...})) =
            guard scrutinee

      fun parser_case current =
        let val key = (#key context) current in
          case Redblackmap.peek (!parser_cache, key) of
            SOME result => (guard_descriptor result; result)
          | NONE =>
              let
                fun recognise () =
                  let
                    val scrutinee = #scrutinee (dest_case current)
                    val ty = (#type_of context) scrutinee
                    val constructors = metadata (fn () =>
                      case TypeBase.fetch ty of
                        SOME info => List.map (TypeBasePure.cinst ty)
                          (TypeBasePure.constructors_of info)
                      | NONE => mismatch "missing TypeBase entry")
                    fun selector constructor =
                      let
                        val domains = metadata (fn () =>
                          #1 (boolSyntax.strip_fun (Term.type_of constructor)))
                        fun find [] = NONE
                          | find (index :: indices) =
                              if (#same context) (current,
                                  datatype_selector_term ty constructor index
                                    scrutinee) then
                                SOME (SmtLib.CarrierSelector
                                  {constructor = constructor,
                                   selector_index = index,
                                   scrutinee = scrutinee})
                              else find indices
                      in find (List.tabulate (List.length domains, fn n => n))
                      end
                    fun tester constructor =
                      if (#same context)
                          (current, recipe Tester ty constructor scrutinee)
                      then
                        SOME (SmtLib.CarrierTester
                          {constructor = constructor, scrutinee = scrutinee})
                      else NONE
                    fun first observe [] = NONE
                      | first observe (constructor :: rest) =
                          case observe constructor of
                            SOME result => SOME result
                          | NONE => first observe rest
                  in
                    case first selector constructors of
                      SOME result => SOME result
                    | NONE => first tester constructors
                  end
                val result = recognise ()
                  handle primary =>
                    if is_mismatch primary then NONE else raise primary
                val _ = guard current
                val _ = guard_descriptor result
                val _ = parser_cache :=
                  Redblackmap.insert (!parser_cache, key, result)
              in result end
        end
    in
      {parser_case = parser_case,
       datatype_selector_term = datatype_selector_term,
       is_case = is_case,case_view=case_view}
    end
end
