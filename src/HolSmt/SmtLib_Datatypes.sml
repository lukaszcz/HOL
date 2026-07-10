(* Copyright (c) 2026 The HOL4 contributors. *)

(* SMT-LIB algebraic datatype elaboration scaffold. *)

structure SmtLib_Datatypes =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Datatypes"

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

  type elaboration = {
    asts : Datatype.AST list,
    names : name_map
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

  fun entries TypeName ({types, ...} : name_map) = types
    | entries ConstructorName {constructors, ...} = constructors
    | entries SelectorName {selectors, ...} = selectors
    | entries TesterName {testers, ...} = testers

  fun lookup_smt kind names smt =
    Option.map #hol (List.find (fn {smt = n, ...} => n = smt)
      (entries kind names))

  fun lookup_hol kind names hol =
    Option.map #smt (List.find (fn {hol = n, ...} => n = hol)
      (entries kind names))

  fun not_implemented function detail =
    raise ERR function ("datatype elaboration not implemented: " ^ detail)

  fun define_datatype (_ : string located, _ : datatype_decl) =
    not_implemented "define_datatype" "declare-datatype"

  fun define_datatypes (_ : datatype_binding list, _ : datatype_decl list) =
    not_implemented "define_datatypes" "declare-datatypes"

  fun define_datatype_group (_ : datatype_group) =
    not_implemented "define_datatype_group" "mutual datatype group"

  fun mk_selector_case (_ : selector_case) =
    not_implemented "mk_selector_case" "selector case expression"

  fun mk_tester_case (_ : tester_case) =
    not_implemented "mk_tester_case" "tester case expression"

end
