(* Registry route and recorded indexed operand selection are syntax DATA. *)
signature CPC_SharedReplayPlan =
sig
  datatype route = Scoped | Resolved | Converted | Aligned | Simple | Bounded
  (* Scoped when [pop]; else by the handler: resolution, CNF, factoring
     and reordering have their own routes, the simple Boolean, equality
     and truth handlers are Simple, every other handler is Bounded. *)
  val route_of : {pop:bool,handler:CPC_Proof.replay_handler} -> route
  (* The handlers the arithmetic graph route admits (names starting "arith"
     or "int_tight_"). *)
  val arithmetic_handler : CPC_Proof.replay_handler -> bool
  val occurrence_provenance : 'a SmtLib_Parser.construction_occurrence ->
    CPC_Proof.term_provenance
  val occurrence_provenance_observed :
    ('a SmtLib_Parser.construction_occurrence -> unit) ->
    'a SmtLib_Parser.construction_occurrence -> CPC_Proof.term_provenance
  val recorded : (Term.term -> int -> 'node -> 'node list option) ->
    Term.term -> int -> 'node -> 'node list option
  val recorded_observed : (unit -> unit) ->
    (Term.term -> int -> 'node -> 'node list option) ->
    Term.term -> int -> 'node -> 'node list option
  val selected :
    {children:'provenance -> 'provenance list,
     recorded:Term.term -> int -> 'node -> 'node list option,
     length:'provenance list -> int,
     node_at:'node list * int -> 'node,
     provenance_at:'provenance list * int -> 'provenance,
     error:string -> exn} ->
    Term.term -> 'node -> 'provenance -> int -> 'node * 'provenance
  datatype simple_boolean = SimpleAndIntro | SimpleAndElim
    | SimpleNotNotElim
    | SimpleNotOrElim
    | SimpleNotImpliesElim1
    | SimpleNotImpliesElim2
    | SimpleImpliesElim
    | SimpleEquivElim1
    | SimpleEquivElim2
    | SimpleNotEquivElim1
    | SimpleNotEquivElim2
    | SimpleIteElim1
    | SimpleIteElim2
    | SimpleNotIteElim1
    | SimpleNotIteElim2
    | SimpleNotAnd
  val simple_boolean_of : CPC_Proof.replay_handler -> simple_boolean option
  val conjunction : {visit:unit -> unit,truth:unit -> 'node,
    binary:'node * 'node -> 'node} -> 'node list -> 'node
  val child_provenance :
    {equal:string * string -> bool,
     length:CPC_Proof.term_provenance list -> int,
     tabulate:int * (int -> CPC_Proof.term_provenance) ->
       CPC_Proof.term_provenance list} ->
    string -> int -> CPC_Proof.term_provenance ->
    CPC_Proof.term_provenance list
  val aggregate_entries :
    {children:CPC_Proof.term_provenance ->
       CPC_Proof.term_provenance list option,
     recorded:int -> 'node -> 'node list option,
     length:CPC_Proof.term_provenance list -> int,
     push:{node:'node,provenance:CPC_Proof.term_provenance} ->
       ('node * CPC_Proof.term_provenance) list ->
       ('node * CPC_Proof.term_provenance) list,
     reverse:('node * CPC_Proof.term_provenance) list ->
       ('node * CPC_Proof.term_provenance) list,
     start:'node list * CPC_Proof.term_provenance list *
       ('node * CPC_Proof.term_provenance) list ->
       ('node * CPC_Proof.term_provenance) list,
     initial:'node * CPC_Proof.term_provenance ->
       ('node * CPC_Proof.term_provenance) list,
     check:int -> unit,error:string -> exn} -> 'node ->
    CPC_Proof.term_provenance -> ('node * CPC_Proof.term_provenance) list
  val produced_conjunction :
    {run:(unit -> ('node * CPC_Proof.term_provenance) list option) ->
       ('node * CPC_Proof.term_provenance) list option,
     observe:unit -> unit,input:unit -> 'layout option,
     recorded:'layout -> {atom:'node,negative:bool} list,
     same:'node * 'node -> bool,children:'node -> 'node list option,
     validate:'node -> unit,check:int -> unit,
     pending:'node * 'node * 'node list -> 'node list,
     leaf:'node * CPC_Proof.term_provenance *
       ('node * CPC_Proof.term_provenance) list ->
       ('node * CPC_Proof.term_provenance) list,
     reverse:('node * CPC_Proof.term_provenance) list ->
       ('node * CPC_Proof.term_provenance) list,
     initial:'node -> 'node list} -> 'node ->
    ('node * CPC_Proof.term_provenance) list option
  val not_and :
    {negated:'node -> 'node option,one:unit -> 'node,
     one_provenance:unit -> CPC_Proof.term_provenance,
     negation_provenance:CPC_Proof.term_provenance ->
       CPC_Proof.term_provenance,
     operands:Term.term -> int -> 'node -> 'node list,
     is_false:'node -> bool,
     child_provenance:string -> int -> CPC_Proof.term_provenance ->
       CPC_Proof.term_provenance list,
     recorded_entries:'node -> CPC_Proof.term_provenance ->
       ('node * CPC_Proof.term_provenance) list,
     owned:'owner option,
     produced_entries:'owner -> 'node ->
       ('node * CPC_Proof.term_provenance) list option,
     map:(('node * CPC_Proof.term_provenance) -> 'output) ->
       ('node * CPC_Proof.term_provenance) list -> 'output list,
     negative:'node -> CPC_Proof.term_provenance -> 'output,
     disjoin:'output list -> 'fact,error:string -> exn} -> 'fact
  val cnf_literals :
    (Term.term -> 'entry * 'entry) ->
    (Term.term -> string -> 'entry) ->
    (Term.term -> string -> 'entry list) ->
    (unit -> 'entry * 'entry) ->
    (unit -> 'entry * 'entry * 'entry) ->
    ('entry -> 'literal) -> ('entry -> 'literal) ->
    (('entry -> 'literal) -> 'entry list -> 'literal list) ->
    (string -> string -> exn) -> string -> 'entry -> 'literal list
  val false_intro : ('observed -> 'node -> 'node option) ->
    'observed -> (unit -> 'node) -> ('node -> 'shape) ->
    ('graph -> 'scope -> Term.term -> 'shape) -> 'graph -> 'scope ->
    (CPC_Proof.term_provenance -> CPC_Proof.term_provenance) ->
    (unit -> CPC_Proof.term_provenance) ->
    ('shape -> 'shape -> CPC_Proof.term_provenance *
       CPC_Proof.term_provenance -> 'result) ->
    (string -> string -> exn) -> 'result
  val false_elim : ('node -> 'node * 'node) -> (unit -> 'node) ->
    (CPC_Proof.term_provenance -> CPC_Proof.term_provenance *
       CPC_Proof.term_provenance) ->
    (unit -> CPC_Proof.term_provenance) ->
    ('graph -> 'node -> Term.term -> bool) -> 'graph ->
    ('node -> CPC_Proof.term_provenance ->
       'shape * CPC_Proof.term_provenance) ->
    ('shape -> CPC_Proof.term_provenance -> 'result) ->
    (string -> string -> exn) -> 'result
  val true_intro : (unit -> 'node) -> ('node -> 'shape) ->
    ('graph -> 'scope -> Term.term -> 'shape) -> 'graph -> 'scope ->
    (unit -> CPC_Proof.term_provenance) ->
    ('shape -> 'shape -> CPC_Proof.term_provenance *
       CPC_Proof.term_provenance -> 'result) -> 'result
  val true_elim : ('node -> 'node * 'node) -> (unit -> 'node) ->
    (CPC_Proof.term_provenance -> CPC_Proof.term_provenance *
       CPC_Proof.term_provenance) ->
    (unit -> CPC_Proof.term_provenance) ->
    ('graph -> 'node -> Term.term -> bool) -> 'graph ->
    ('node -> 'shape) ->
    ('shape -> CPC_Proof.term_provenance -> 'result) ->
    (string -> string -> exn) -> 'result
  val no_metadata_copy : 'a -> unit
  val process_scope_entries : ('node -> unit) ->
    ('node * 'node -> bool) ->
    ('graph -> Term.term -> int -> 'node -> 'node list option) ->
    'graph ->
    (('node * CPC_Proof.term_provenance) list ->
       ('node * CPC_Proof.term_provenance) list) ->
    (int -> unit) -> 'node -> 'node -> CPC_Proof.term_provenance ->
    ('node * CPC_Proof.term_provenance) list ->
    ('node * CPC_Proof.term_provenance) list option
  val and_intro :
    {conjunction:'node list -> 'node,
     provenances:unit -> CPC_Proof.term_provenance list,
     current:'node -> CPC_Proof.term_provenance -> 'fact} ->
    'node list -> 'fact
  val not_not_elim :
    {negated:'node -> 'node option,one:unit -> 'node,
     one_provenance:unit -> CPC_Proof.term_provenance,
     negation_provenance:CPC_Proof.term_provenance ->
       CPC_Proof.term_provenance,
     current:'node -> CPC_Proof.term_provenance -> 'fact,
     error:string -> exn} -> 'fact
  datatype simple_equality = SimpleRefl | SimpleSymm | SimpleTrans
    | SimpleCong | SimpleHoCong | SimpleEqResolve | SimpleContra
  val simple_equality_of : CPC_Proof.replay_handler -> simple_equality option
  (* The simple handlers that are neither Boolean nor equality rules. *)
  datatype truth_family = DeclaredBoolean | FalseIntro | FalseElim
    | TrueIntro | TrueElim | ProcessScope
  val truth_family_of : CPC_Proof.replay_handler -> truth_family option
  val equality_provenance : CPC_Proof.term_provenance ->
    CPC_Proof.term_provenance * CPC_Proof.term_provenance
  val reflexive : {require_one:string -> 'node list -> 'node,
    relation:'node -> 'node -> 'fact} -> 'node list -> 'fact
  val positive_symmetry :
    {pair:'node -> 'node * 'node,one:unit -> 'node,
     one_provenance:unit -> CPC_Proof.term_provenance,
     relation_kind:'node -> 'kind,
     relation_with_kind:'kind -> 'node -> 'node ->
       (CPC_Proof.term_provenance * CPC_Proof.term_provenance) -> 'fact} ->
    'fact
  val higher_congruence :
    {map:('node -> 'node * 'node) -> 'node list -> ('node * 'node) list,
     pair:'node -> 'node * 'node,application:'node * 'node -> 'node,
     relation:'node -> 'node -> 'fact,error:string -> exn} ->
    'node list -> 'fact
  val equality_resolve :
    {node:'premise -> 'node,pair:'node -> 'node * 'node,
     provenance:'premise -> CPC_Proof.term_provenance,
     same:'node * 'node -> bool,
     current:'node -> CPC_Proof.term_provenance -> 'fact,
     retry:Feedback.hol_error -> bool,error:string -> exn} ->
    'premise list -> 'fact
  exception AliasCorrespondence of string
  val equality_resolve_with_aliases :
    ('node -> ('kind * ('node * 'node)) option) ->
    {node:'premise -> 'node,pair:'node -> 'node * 'node,
     provenance:'premise -> CPC_Proof.term_provenance,
     same:'node * 'node -> bool,
     current:'node -> CPC_Proof.term_provenance -> 'fact,
     retry:Feedback.hol_error -> bool,error:string -> exn} ->
    'premise list -> 'fact
  val relation_path :
    {visit:unit -> unit,relation:'node -> ('kind * ('node * 'node)) option,
     map_partial:('node -> ('node * 'node) option) -> 'node list ->
       ('node * 'node) list,
     same_kind:'kind * 'kind -> bool,same:'node * 'node -> bool,
     key:'node -> 'key,empty:unit -> 'seen,
     member:'seen * 'key -> bool,add:'seen * 'key -> 'seen,
     push:'node * 'node list -> 'node list,
     fold:(('node * 'node) * 'node list -> 'node list) -> 'node list ->
       ('node * 'node) list -> 'node list,error:string -> exn} ->
    'node -> 'node list -> bool
  val congruence_rewrite :
    {replacement:'node -> 'output option,lookup:'node -> 'output option,
     publish:'node * 'output -> unit,
     view:'node -> ('node * 'node) option,retained:'node -> 'output,
     same:'node * 'output -> bool,
     application:'output * 'output -> 'output} -> 'node -> 'output
  val disjoin :
    {visit:unit -> unit,falsity:unit -> 'node,atom:'node -> 'fact,
     current:'node -> CPC_Proof.term_provenance -> 'fact,
     binary:'node * 'node -> 'node,
     provenances:('node * CPC_Proof.term_provenance) list ->
       CPC_Proof.term_provenance list} ->
    ('node * CPC_Proof.term_provenance) list -> 'fact
  val not_or_elim :
    {require_one:string -> 'premise list -> 'premise,
     node:'premise -> 'node,negated:'node -> 'node option,
     provenance:'premise -> CPC_Proof.term_provenance,
     selected:Term.term -> 'node -> CPC_Proof.term_provenance -> int ->
       'node * CPC_Proof.term_provenance,index:unit -> int,
     negate:'node -> 'output,
     current:'output -> CPC_Proof.term_provenance -> 'fact,
     error:string -> string -> exn} -> 'premise list -> 'fact
  (* Operand selection of the eleven clausal-elimination rules
       ~(a ==> b)  not_implies_elim1 / 2   a (current) / ~b (finished)
       a ==> b     implies_elim            ~a \/ b
       a = b       equiv_elim1 / 2         ~a \/ b / a \/ ~b
       ~(a = b)    not_equiv_elim1 / 2     a \/ b / ~a \/ ~b
       if c then a else b      ite_elim1 / 2       ~c \/ a / c \/ b
       ~(if c then a else b)   not_ite_elim1 / 2   ~c \/ ~a / c \/ ~b
     with operands in source order: First, Second (and Third for the
     conditional, whose operands are c, a, b).  [reader] selects how the
     operands and their provenance are read: an implication with its
     constructor token and exactly two operands, an equation through the
     relation [pair] and [equality_provenance], a conditional with exactly
     three operands.  [strip_negation] reads the premise, and its
     provenance, below a negation.  [reduced_true] returns the premise as
     an atom, before any operand is inspected, when it has reduced to T. *)
  datatype clausal_reader = ClausalImplication | ClausalEquivalence
    | ClausalConditional
  datatype clausal_operand = ClausalFirst | ClausalSecond | ClausalThird
  datatype clausal_polarity = ClausalPositive | ClausalNegative
  type clausal_literal = clausal_operand * clausal_polarity
  datatype clausal_result = ClausalCurrent of clausal_operand
    | ClausalFinished of clausal_operand
    | ClausalDisjunction of clausal_literal * clausal_literal
  type clausal_descriptor =
    {reader:clausal_reader,strip_negation:bool,reduced_true:bool,
     result:clausal_result}
  (* NONE for the Boolean families that are not clausal eliminations. *)
  val clausal_descriptor : simple_boolean -> clausal_descriptor option
  (* The literals the descriptor derives, in order, over the operands of its
     reader (First, Second, Third are the list's first three elements). *)
  val clausal_literals : clausal_descriptor ->
    {positive:'a -> 'b,negative:'a -> 'b} -> 'a list -> 'b list
  (* Interprets the descriptor over a consumer's callbacks, in this order:
     [same_constant (one ())] and, when it holds, [atom (one ())] (only for
     [reduced_true]); [one ()] and [negated] (when stripping); the operand
     reader; [one_provenance]; [negation_provenance] (when stripping); the
     provenance reader; the literals in order.  A one-literal result goes
     to [current] (a positive operand) or [finish] (a [negative] literal);
     a clause goes to [disjoin].  [handler] names the rule in diagnostics. *)
  val clausal_elim :
    {negated:'node -> 'node option,one:unit -> 'node,
     operands:Term.term -> int -> 'node -> 'node list,
     child_provenance:string -> int -> CPC_Proof.term_provenance ->
       CPC_Proof.term_provenance list,
     negation_provenance:CPC_Proof.term_provenance ->
       CPC_Proof.term_provenance,
     one_provenance:unit -> CPC_Proof.term_provenance,
     pair:'node -> 'node * 'node,
     same_constant:'node -> Term.term -> bool,
     atom:'node -> 'fact,
     current:'node -> CPC_Proof.term_provenance -> 'fact,
     negative:'node -> CPC_Proof.term_provenance -> 'literal,
     positive:'node -> CPC_Proof.term_provenance -> 'literal,
     finish:'literal -> 'fact,
     disjoin:'literal list -> 'fact,
     error:string -> string -> exn} ->
    clausal_descriptor -> string -> 'fact
  val and_elim :
    {require_one:string -> 'premise list -> 'premise,
     node:'premise -> 'node,provenance:'premise -> 'provenance,
     selected:Term.term -> 'node -> 'provenance -> int ->
       'node * 'provenance,
     current:'node -> 'provenance -> 'fact,error:string -> exn} ->
    'premise list ->
    'syntax CPC_ProofParser.constructed_graph_argument list ->
    'fact
  val erase_present : ('literal -> 'literal -> bool) ->
    (('literal list -> 'literal list) -> 'literal list option ->
      'literal list option) ->
    ('literal -> 'literal list -> 'literal list option) ->
    'literal -> 'literal -> 'literal list -> 'literal list option
  val resolution_join :
    ('literal -> 'literal list -> 'literal list option) ->
    ('literal -> 'literal) ->
    ('literal list * 'literal list -> 'literal list) ->
    (string -> string -> exn) -> string ->
    'literal list -> 'literal list -> 'literal -> 'literal list
  val resolution_dynamic :
    (('literal -> bool) -> 'literal list -> 'literal option) ->
    (('literal -> bool) -> 'literal list -> bool) ->
    ('literal -> 'literal -> bool) -> ('literal -> 'literal) ->
    (string -> string -> exn) ->
    'literal list -> 'literal list -> 'literal
  val resolution_chain :
    ('literal list -> 'literal list -> 'literal -> 'literal list) ->
    ('literal list -> 'literal list -> 'literal) ->
    ('literal list -> 'literal list) ->
    ('literal list -> 'literal list list -> 'literal list ->
      'literal list -> 'literal list * 'literal list) ->
    (string -> string -> exn) ->
    'literal list -> 'literal list list -> 'literal list -> 'literal list ->
    'literal list * 'literal list
  val recorded_resolution_chain : (unit -> unit) ->
    ('literal list -> 'literal list -> 'literal -> 'literal list) ->
    ('literal list -> 'literal list list -> 'literal list -> 'literal list) ->
    (string -> string -> exn) ->
    'literal list -> 'literal list list -> 'literal list -> 'literal list
  val pivot_arguments :
    ('syntax CPC_ProofParser.constructed_graph_argument list -> int) ->
    ((('syntax CPC_ProofParser.constructed_graph_argument *
       'syntax CPC_ProofParser.constructed_graph_argument) ->
        {atom:'node,negative:bool}) ->
      'syntax CPC_ProofParser.constructed_graph_argument list *
      'syntax CPC_ProofParser.constructed_graph_argument list ->
      {atom:'node,negative:bool} list) ->
    ('environment -> 'syntax -> Term.term -> bool) -> 'environment ->
    ('syntax -> 'node) -> (string -> string -> exn) ->
    'syntax CPC_ProofParser.constructed_graph_argument list ->
    {atom:'node,negative:bool} list
  val recorded_pivot : (unit -> unit) ->
    ('environment -> 'syntax -> Term.term -> bool) ->
    ('environment -> 'syntax -> Type.hol_type) -> 'environment ->
    ('syntax -> 'node) -> ('environment -> 'node -> 'node option) ->
    (string -> string -> exn) ->
    'syntax CPC_ProofParser.constructed_graph_argument *
    'syntax CPC_ProofParser.constructed_graph_argument ->
    {atom:'node,negative:bool}
end
