(* Copyright (c) 2026 The HOL4 contributors. *)

(* SMT-LIB algebraic datatype elaboration scaffold. *)

structure SmtLib_Datatypes =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Datatypes"

  structure P = SmtLib_Parser
  structure PD = ParseDatatype_dtype

  type 'a located = 'a SmtLib_Parser.located
  type datatype_decl = SmtLib_Parser.datatype_decl_ast located
  type datatype_binding = SmtLib_Parser.datatype_binding_ast located
  type datatype_group = (string located * datatype_decl) list

  type name_pair = {smt : string, hol : string}

  datatype name_kind =
      TypeName
    | ConstructorName
    | SelectorName
    | TesterName

  type name_map = {
    types : name_pair list,
    constructors : name_pair list,
    selectors : name_pair list,
    testers : name_pair list
  }

  type selector_info = {
    selector_smt : string,
    selector_hol : string,
    constructor_smt : string,
    constructor_hol : string,
    field_index : int
  }

  type elaboration = {
    asts : Datatype.AST list,
    names : name_map,
    hol_types : Type.hol_type list,
    tyinfos : TypeBase.tyinfo list,
    selectors : selector_info list,
    constructors : name_pair list
  }

  type selector_case = {
    selector : string,
    constructor : string,
    scrutinee : Term.term
  }

  type tester_case = {
    constructor : string,
    scrutinee : Term.term
  }

  val empty_name_map = {
    types = [],
    constructors = [],
    selectors = [],
    testers = []
  }

  type cache_entry = {
    key : string,
    result : elaboration,
    selectors : selector_info list,
    constructors : name_pair list
  }

  val cache : cache_entry list ref = ref []
  val selector_table : selector_info list ref = ref []
  val constructor_table : name_pair list ref = ref []

  fun node (P.Located {node, ...}) = node

  fun option_get msg opt =
    case opt of
      SOME x => x
    | NONE => raise ERR "option_get" msg

  fun sanitize base =
    let
      val s = SmtLib_Theories.sanitize_name base
    in
      if s = "" then "anon" else s
    end

  fun member x xs = List.exists (fn y => x = y) xs

  fun first_existing used base n =
    let val candidate = if n = 0 then base else base ^ "_" ^ Int.toString n
    in
      if used candidate then first_existing used base (n + 1)
      else candidate
    end

  fun fresh_name used avoid base =
    first_existing (fn name => member name avoid orelse used name) base 0

  fun type_name_used name = not (List.null (Type.decls name))

  fun const_name_used name = not (List.null (Term.decls name))

  fun fresh_type_name avoid smt =
    fresh_name type_name_used avoid ("smtlib_dt_" ^ sanitize smt)

  fun fresh_const_name avoid prefix smt =
    fresh_name const_name_used avoid (prefix ^ sanitize smt)

  fun assoc_smt smt pairs =
    Option.map #hol (List.find (fn {smt = n, ...} => n = smt) pairs)

  fun assoc_hol hol pairs =
    Option.map #smt (List.find (fn {hol = n, ...} => n = hol) pairs)

  fun add_name kind ({types, constructors, selectors, testers} : name_map)
      pair =
    case kind of
      TypeName =>
        {types = pair :: types, constructors = constructors,
         selectors = selectors, testers = testers}
    | ConstructorName =>
        {types = types, constructors = pair :: constructors,
         selectors = selectors, testers = testers}
    | SelectorName =>
        {types = types, constructors = constructors,
         selectors = pair :: selectors, testers = testers}
    | TesterName =>
        {types = types, constructors = constructors,
         selectors = selectors, testers = pair :: testers}

  fun sort_key sort =
    case node sort of
      P.SortIdentifier name => name
    | P.SortIndexed (head, indices) =>
        "(_ " ^ node head ^ " " ^
        String.concatWith " " (List.map node indices) ^ ")"
    | P.SortApply (head, args) =>
        "(" ^ node head ^ " " ^
        String.concatWith " " (List.map sort_key args) ^ ")"

  fun selector_key selector =
    case node selector of
      P.DatatypeSelector (name, sort) => "(" ^ node name ^ " " ^
        sort_key sort ^ ")"

  fun constructor_key constructor =
    case node constructor of
      P.DatatypeConstructor (name, tester, selectors) =>
        "(" ^ node name ^ " " ^
        (case node tester of P.DatatypeTester t => node t) ^ " " ^
        String.concatWith " " (List.map selector_key selectors) ^ ")"

  fun decl_key (name, decl) =
    case node decl of
      P.DatatypeDecl (params, constructors) =>
        "(" ^ node name ^ " (par " ^
        String.concatWith " " (List.map node params) ^ ") " ^
        String.concatWith " " (List.map constructor_key constructors) ^ ")"

  fun group_key group =
    String.concatWith "\n" (List.map decl_key group)

  fun builtin_pretype name =
    case name of
      "Bool" => SOME (PD.dTyop {Tyop = "bool", Thy = SOME "min", Args = []})
    | "Int" => SOME (PD.dTyop {Tyop = "int", Thy = SOME "integer", Args = []})
    | "Real" => SOME (PD.dTyop {Tyop = "real", Thy = SOME "realax",
        Args = []})
    (* The same carrier the UnicodeStrings dictionary decodes 'String' to.
       HOL's ':string' is a char list and is no longer the SMT 'String'
       sort, so elaborating a field at that type would not survive
       re-emission. *)
    | "String" => SOME (PD.dAQ SmtLib_Theories.UnicodeStrings.string_ty)
    | _ => NONE

  fun fun_pretype (domain, range) =
    PD.dTyop {Tyop = "fun", Thy = SOME "min", Args = [domain, range]}

  fun list_mk_fun_pretype (domains, range) =
    List.foldr fun_pretype range domains

  fun bitvector_pretype indices =
    case indices of
      [idx] =>
        (case Int.fromString (node idx) of
           SOME n => PD.dAQ (wordsSyntax.mk_int_word_type n)
         | NONE => raise ERR "sort_to_pretype"
             ("invalid BitVec width '" ^ node idx ^ "'"))
    | _ => raise ERR "sort_to_pretype"
        "BitVec sort expects exactly one index"

  fun sort_to_pretype type_names params sort =
    let
      fun self s = sort_to_pretype type_names params s
      fun sort_name name args =
        case assoc_smt name params of
          SOME hol_param =>
            if List.null args then PD.dVartype hol_param
            else raise ERR "sort_to_pretype"
              ("type parameter '" ^ name ^ "' used with arguments")
        | NONE =>
            (case assoc_smt name type_names of
               SOME hol_ty =>
                 PD.dTyop {Tyop = hol_ty, Thy = NONE, Args = args}
             | NONE =>
                 (case (builtin_pretype name, args) of
                    (SOME pty, []) => pty
                  | _ => raise ERR "sort_to_pretype"
                      ("unknown datatype selector sort '" ^ name ^ "'")))
    in
      case node sort of
        P.SortIdentifier name => sort_name name []
      | P.SortIndexed (head, indices) =>
          if node head = "BitVec" then bitvector_pretype indices
          else raise ERR "sort_to_pretype"
            ("unknown indexed datatype selector sort '" ^ node head ^ "'")
      | P.SortApply (head, args) =>
          if node head = "Array" andalso List.length args = 2 then
            fun_pretype (self (List.nth (args, 0)), self (List.nth (args, 1)))
          else if node head = "->" then
            (case List.rev (List.map self args) of
               range :: rev_domains =>
                 list_mk_fun_pretype (List.rev rev_domains, range)
             | [] => raise ERR "sort_to_pretype"
                 "function sort expects at least one range sort")
          else sort_name (node head) (List.map self args)
    end

  fun constructor_args ty =
    case Lib.total Type.dom_rng ty of
      NONE => []
    | SOME (domain, range) => domain :: constructor_args range

  fun const_name tm =
    #Name (Term.dest_thy_const tm)
    handle Feedback.HOL_ERR _ => Lib.fst (Term.dest_const tm)

  fun constructors_of_type ty =
    List.map (TypeBasePure.cinst ty) (TypeBase.constructors_of ty)

  fun find_constructor ty name =
    List.find (fn ctor => const_name ctor = name) (constructors_of_type ty)

  fun mk_constructor_pattern ctor =
    let
      val arg_tys = constructor_args (Term.type_of ctor)
      val vars = List.tabulate (List.length arg_tys,
        fn i => Term.mk_var ("x" ^ Int.toString i, List.nth (arg_tys, i)))
    in
      (Term.list_mk_comb (ctor, vars), vars)
    end

  fun lookup_selector selector constructor =
    List.find
      (fn {selector_smt, selector_hol, constructor_smt, constructor_hol, ...} =>
        (selector = selector_smt orelse selector = selector_hol) andalso
        (constructor = constructor_smt orelse constructor = constructor_hol))
      (!selector_table)

  fun register_selectors selectors =
    selector_table := selectors @ !selector_table

  fun register_constructors constructors =
    constructor_table := constructors @ !constructor_table

  fun entries TypeName ({types, ...} : name_map) = types
    | entries ConstructorName {constructors, ...} = constructors
    | entries SelectorName {selectors, ...} = selectors
    | entries TesterName {testers, ...} = testers

  fun lookup_smt kind names smt =
    assoc_smt smt (entries kind names)

  fun lookup_hol kind names hol =
    assoc_hol hol (entries kind names)

  fun allocate_type_names group =
    let
      fun alloc ((name, _), (avoid, names)) =
        let
          val smt = node name
          val hol = fresh_type_name avoid smt
        in
          (hol :: avoid, {smt = smt, hol = hol} :: names)
        end
      val (_, names) = List.foldl alloc ([], []) group
    in
      List.rev names
    end

  fun allocate_params params =
    let
      fun alloc (param, (avoid, names)) =
        let
          val smt = node param
          val base = "'smtlib_dt_" ^ sanitize smt
          fun used name = member name avoid
          val hol = fresh_name used avoid base
        in
          (hol :: avoid, {smt = smt, hol = hol} :: names)
        end
      val (_, names) = List.foldl alloc ([], []) params
    in
      List.rev names
    end

  fun allocate_constructors group =
    let
      fun constructors_of_decl (_, decl) =
        case node decl of P.DatatypeDecl (_, constructors) => constructors
      fun alloc (constructor, (avoid, names)) =
        case node constructor of
          P.DatatypeConstructor (name, _, _) =>
            let
              val smt = node name
              val hol = fresh_const_name avoid "smtlib_dt_ctor_" smt
            in
              (hol :: avoid, {smt = smt, hol = hol} :: names)
            end
      val constructors = List.concat (List.map constructors_of_decl group)
      val (_, names) = List.foldl alloc ([], []) constructors
    in
      List.rev names
    end

  fun elaborate_decl type_names ctor_names decl =
    case node decl of
      P.DatatypeDecl (params, constructors) =>
        let
          val param_names = allocate_params params
          fun selector_pretype selector =
            case node selector of
              P.DatatypeSelector (_, sort) =>
                sort_to_pretype type_names param_names sort
          fun constructor constructor =
            case node constructor of
              P.DatatypeConstructor (name, _, selectors) =>
                (option_get ("missing constructor name map for " ^ node name)
                   (assoc_smt (node name) ctor_names),
                 List.map selector_pretype selectors)
        in
          (param_names, PD.Constructors (List.map constructor constructors))
        end

  fun cached_type_names () =
    List.concat (List.map (fn {result, ...} => #types (#names result)) (!cache))

  fun build_names_and_asts group =
    let
      val type_names = allocate_type_names group
      val available_type_names = type_names @ cached_type_names ()
      val ctor_names = allocate_constructors group
      val base_names =
        List.foldl (fn (pair, acc) => add_name TypeName acc pair)
          empty_name_map type_names
      val base_names =
        List.foldl (fn (pair, acc) => add_name ConstructorName acc pair)
          base_names ctor_names
      fun one ((name, decl), (names, asts, selector_infos, selector_avoid,
            tester_avoid)) =
        let
          val hol_ty = option_get ("missing type name map for " ^ node name)
            (assoc_smt (node name) type_names)
          val (param_names, form) =
            elaborate_decl available_type_names ctor_names decl
          fun constructor_data constructor =
            case node constructor of
              P.DatatypeConstructor (ctor_name, tester, selectors) =>
                let
                  val ctor_smt = node ctor_name
                  val ctor_hol = option_get
                    ("missing constructor name map for " ^ ctor_smt)
                    (assoc_smt ctor_smt ctor_names)
                  val tester_smt =
                    (case node tester of P.DatatypeTester t => "is " ^ node t)
                  val tester_hol = fresh_name const_name_used tester_avoid
                    ("smtlib_dt_is_" ^ sanitize ctor_smt)
                in
                  (ctor_smt, ctor_hol, tester_smt, tester_hol, selectors)
                end
          val constructor_datas =
            case node decl of
              P.DatatypeDecl (_, constructors) =>
                List.map constructor_data constructors
          fun add_tester ((_, _, tester_smt, tester_hol, _), (avoid, acc)) =
            (tester_hol :: avoid,
             add_name TesterName acc {smt = tester_smt, hol = tester_hol})
          val (tester_avoid, names) =
            List.foldl add_tester (tester_avoid, names) constructor_datas
          fun add_selector ((ctor_smt, ctor_hol, _, _, selectors),
                (avoid, names, infos)) =
            let
              fun one_selector (selector, (i, avoid, names, infos)) =
                case node selector of
                  P.DatatypeSelector (selector_name, _) =>
                    let
                      val smt = node selector_name
                      val hol = fresh_name const_name_used avoid
                        ("smtlib_dt_sel_" ^ sanitize smt)
                      val info = {
                        selector_smt = smt, selector_hol = hol,
                        constructor_smt = ctor_smt,
                        constructor_hol = ctor_hol, field_index = i}
                    in
                      (i + 1, hol :: avoid,
                       add_name SelectorName names {smt = smt, hol = hol},
                       info :: infos)
                    end
              val (_, avoid, names, infos) =
                List.foldl one_selector (0, avoid, names, infos) selectors
            in
              (avoid, names, infos)
            end
          val (selector_avoid, names, selector_infos) =
            List.foldl add_selector (selector_avoid, names, selector_infos)
              constructor_datas
        in
          (names, (hol_ty, form) :: asts, selector_infos,
           selector_avoid, tester_avoid)
        end
      val (names, asts, selectors, _, _) =
        List.foldl one (base_names, [], [],
          List.map #selector_hol (!selector_table), []) group
    in
      (List.rev asts, names, selectors, ctor_names)
    end

  fun hol_type_of_decl names (name, decl) =
    let
      val hol_name = option_get ("missing type name map for " ^ node name)
        (lookup_smt TypeName names (node name))
      val params =
        case node decl of P.DatatypeDecl (params, _) => allocate_params params
      val args = List.map (Type.mk_vartype o #hol) params
    in
      Type.mk_thy_type {Thy = Theory.current_theory(), Tyop = hol_name,
        Args = args}
    end

  fun fetch_tyinfo ty =
    case TypeBase.fetch ty of
      SOME tyi => tyi
    | NONE => raise ERR "define_datatype_group"
        ("datatype was not registered in TypeBase: " ^
         Hol_pp.type_to_string ty)

  fun define_new_group key group =
    let
      val first_name =
        case group of
          (name, _) :: _ => node name
        | [] => raise ERR "define_datatype_group" "empty datatype group"
      val (asts, names, selectors, constructors) = build_names_and_asts group
      val _ =
        Datatype.astHol_datatype asts
        handle Feedback.HOL_ERR holerr =>
          raise ERR "define_datatype_group"
            ("datatype declaration '" ^ first_name ^
             "' is not well-founded: " ^ Feedback.message_of holerr)
      val hol_types = List.map (hol_type_of_decl names) group
      val tyinfos = List.map fetch_tyinfo hol_types
      val result = {asts = asts, names = names, hol_types = hol_types,
        tyinfos = tyinfos, selectors = selectors, constructors = constructors}
      val entry = {key = key, result = result, selectors = selectors,
        constructors = constructors}
      val _ = cache := entry :: !cache
      val _ = register_selectors selectors
      val _ = register_constructors constructors
    in
      result
    end

  fun not_implemented function detail =
    raise ERR function ("datatype elaboration not implemented: " ^ detail)

  fun define_datatype_group (group : datatype_group) =
    let val key = group_key group
    in
      case List.find (fn {key = k, ...} => k = key) (!cache) of
        SOME {result, selectors, constructors, ...} =>
          (register_selectors selectors;
           register_constructors constructors;
           result)
      | NONE => define_new_group key group
    end

  fun define_datatype (name : string located, decl : datatype_decl) =
    define_datatype_group [(name, decl)]

  fun define_datatypes (bindings : datatype_binding list,
      decls : datatype_decl list) =
    let
      fun binding_name binding =
        case node binding of P.DatatypeBinding (name, _) => name
      val _ =
        if List.length bindings = List.length decls then ()
        else raise ERR "define_datatypes"
          "datatype binding count does not match declaration count"
    in
      define_datatype_group (ListPair.zip (List.map binding_name bindings,
        decls))
    end

  fun mk_selector_case ({selector, constructor, scrutinee} : selector_case) =
    let
      val info = option_get
        ("unknown datatype selector '" ^ selector ^ "' for constructor '" ^
         constructor ^ "'")
        (lookup_selector selector constructor)
      val ty = Term.type_of scrutinee
      val result_ty =
        (case find_constructor ty (#constructor_hol info) of
           SOME ctor =>
             List.nth (constructor_args (Term.type_of ctor),
               #field_index info)
         | NONE => raise ERR "mk_selector_case"
             ("constructor '" ^ constructor ^
              "' is not a constructor for the scrutinee type"))
      fun branch ctor =
        let
          val (pat, vars) = mk_constructor_pattern ctor
          val rhs =
            if const_name ctor = #constructor_hol info then
              List.nth (vars, #field_index info)
            else boolSyntax.mk_arb result_ty
        in
          (pat, rhs)
        end
    in
      TypeBase.mk_case (scrutinee,
        List.map branch (constructors_of_type ty))
    end

  fun mk_tester_case ({constructor, scrutinee} : tester_case) =
    let
      val ty = Term.type_of scrutinee
      val constructors = constructors_of_type ty
      val target =
        case List.find
          (fn ctor => const_name ctor = constructor orelse
             List.exists
               (fn {smt, hol} =>
                 constructor = smt andalso const_name ctor = hol)
               (!constructor_table))
          constructors of
          SOME ctor => const_name ctor
        | NONE => raise ERR "mk_tester_case"
            ("constructor '" ^ constructor ^
             "' is not a constructor for the scrutinee type")
      fun branch ctor =
        let val (pat, _) = mk_constructor_pattern ctor
        in
          (pat, if const_name ctor = target then boolSyntax.T else boolSyntax.F)
        end
    in
      TypeBase.mk_case (scrutinee, List.map branch constructors)
    end

  fun parser_result_of_group group
      ({hol_types, selectors, constructors, ...} : elaboration) =
    let
      fun type_entry ((name, _), hol_type) =
        {smt_name = node name, hol_type = hol_type}

      fun constructor_entry hol_type ctor =
        let
          val tm = TypeBasePure.cinst hol_type ctor
          val hol_name = const_name tm
          val smt_name =
            option_get ("missing SMT constructor name for " ^ hol_name)
              (assoc_hol hol_name constructors)
        in
          {smt_name = smt_name, hol_name = hol_name, term = tm}
        end

      fun constructor_entries hol_type =
        List.map (constructor_entry hol_type)
          (TypeBase.constructors_of hol_type)

      fun selector_entry
          ({selector_smt, constructor_smt, constructor_hol, field_index, ...}
             : selector_info) =
        let
          fun find_in_type hol_type =
            Option.map (fn ctor => (hol_type, ctor))
              (find_constructor hol_type constructor_hol)
          val (domain, ctor) =
            option_get
              ("missing constructor type for selector " ^ selector_smt)
              (Lib.get_first find_in_type hol_types)
          val range =
            List.nth (constructor_args (Term.type_of ctor), field_index)
        in
          {smt_name = selector_smt, constructor = constructor_smt,
           domain = domain, range = range}
        end
    in
      {types = ListPair.map type_entry (group, hol_types),
       constructors = List.concat (List.map constructor_entries hol_types),
       selectors = List.map selector_entry selectors,
       mk_selector_case = mk_selector_case,
       mk_tester_case = mk_tester_case}
    end

  fun define_datatype_for_parser (name, decl) =
    parser_result_of_group [(name, decl)] (define_datatype (name, decl))

  fun define_datatypes_for_parser (bindings, decls) =
    let
      fun binding_name binding =
        case node binding of P.DatatypeBinding (name, _) => name
      val group = ListPair.zip (List.map binding_name bindings, decls)
    in
      parser_result_of_group group (define_datatypes (bindings, decls))
    end

  val _ = P.install_datatype_elaborator {
    define_datatype = define_datatype_for_parser,
    define_datatypes = define_datatypes_for_parser
  }

end
