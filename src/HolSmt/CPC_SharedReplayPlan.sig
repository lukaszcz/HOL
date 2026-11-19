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
  datatype clausal_rule = NotImpliesElim1 | NotImpliesElim2 | ImpliesElim
    | EquivElim1 | EquivElim2 | NotEquivElim1 | NotEquivElim2
    | IteElim1 | IteElim2 | NotIteElim1 | NotIteElim2
  datatype simple_boolean = SimpleAndIntro | SimpleAndElim
    | SimpleNotNotElim
    | SimpleNotOrElim
    | SimpleClausal of clausal_rule
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
       ~(a ==> b)  NotImpliesElim1 / 2   a (current) / ~b (finished)
       a ==> b     ImpliesElim           ~a \/ b
       a = b       EquivElim1 / 2        ~a \/ b / a \/ ~b
       ~(a = b)    NotEquivElim1 / 2     a \/ b / ~a \/ ~b
       if c then a else b      IteElim1 / 2       ~c \/ a / c \/ b
       ~(if c then a else b)   NotIteElim1 / 2    ~c \/ ~a / c \/ ~b
     The descriptor's constructor is the reader of the premise: an
     implication with its constructor token and exactly two operands, an
     equation through the relation [pair] and [equality_provenance], or a
     conditional with exactly three operands.  Each carries [negated] (the
     premise, and its provenance, are read below a negation) and a result
     whose operands are named for that reader, so a literal cannot name an
     operand its reader lacks.  The conditional rules keep a premise that has
     reduced to T (see [clausal_keeps_reduced_true]). *)
  datatype clausal_polarity = ClausalPositive | ClausalNegative
  datatype binary_operand = ClausalLeft | ClausalRight
  datatype ternary_operand = ClausalCondition | ClausalThen | ClausalElse
  type 'operand clausal_literal = 'operand * clausal_polarity
  datatype implication_result = ClausalCurrent of binary_operand
    | ClausalFinished of binary_operand
    | ClausalClause of binary_operand clausal_literal *
        binary_operand clausal_literal
  datatype clausal_descriptor =
      ClausalImplication of {negated:bool,result:implication_result}
    | ClausalEquivalence of {negated:bool,
        literals:binary_operand clausal_literal *
                 binary_operand clausal_literal}
    | ClausalConditional of {negated:bool,
        literals:ternary_operand clausal_literal *
                 ternary_operand clausal_literal}
  val clausal_descriptor : clausal_rule -> clausal_descriptor
  (* The handler of each clausal rule: the inverse of the clausal rows
     of [simple_class]. *)
  val clausal_handler : clausal_rule -> CPC_Proof.replay_handler
  (* Whether a premise that has reduced to T is kept as it is, before any
     operand is read (the conditional rules).  [clausal_elim] decides this
     before any reader runs; term replay calls the predicate itself;
     [clausal_literals] never does. *)
  val clausal_keeps_reduced_true : clausal_descriptor -> bool
  (* The literals the descriptor derives, in order.  The reader of the
     descriptor's kind is called once with the descriptor's [negated]; it
     returns the operands in source order. *)
  val clausal_literals : clausal_descriptor ->
    {positive:'a -> 'b,negative:'a -> 'b} ->
    {implication:bool -> 'a * 'a,equivalence:bool -> 'a * 'a,
     conditional:bool -> 'a * 'a * 'a} -> 'b list
  (* Interprets the descriptor over a consumer's callbacks, selecting the
     literals as [clausal_literals] does, over (node,provenance) pairs.
     Callback order: for a conditional, [same_constant (one ())] and, when
     it holds, [atom (one ())]; then [one ()] and [negated] (when
     stripping); the operand reader; [one_provenance]; [negation_provenance]
     (when stripping); the provenance reader; the literals in order.  A
     current result goes to [current]; a finished one is made by [negative]
     and goes to [finish]; a clause goes to [disjoin].  [handler] names the
     rule in diagnostics. *)
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
