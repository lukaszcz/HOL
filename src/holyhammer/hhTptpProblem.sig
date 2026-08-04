signature hhTptpProblem =
sig

  datatype tptp_type =
      TyCon of string * tptp_type list
    | TyVar of string
    | TyFun of tptp_type * tptp_type
    | TyPi of string list * tptp_type

  datatype tptp_term =
      Tm of (string * tptp_type list) * tptp_term list
    | TmAbs of (string * tptp_type) * tptp_term

  datatype conn = Not | And | Or | Implies | Iff | Equal

  datatype tptp_formula =
      Quant of bool * (string * tptp_type option) list * tptp_formula
    | TyQuant of bool * string list * tptp_formula
    | Conn of conn * tptp_formula list
    | Atom of tptp_term

  type syntax = {with_ite : bool, with_let : bool}
  datatype fool = NoFool | Fool of syntax
  datatype format =
      FOF
    | TFF of {poly : bool, fool : fool}
    | THF of {poly : bool, syntax : syntax, choice : bool}
  datatype role = Axiom | Hypothesis | Definition | Conjecture
  datatype line =
      TypeDecl of string * string * int
    | SymDecl of string * string * tptp_type
    | FormLine of string * role * tptp_formula
  type problem = (string * line list) list

  val string_of_problem : format -> string -> problem -> string

end
