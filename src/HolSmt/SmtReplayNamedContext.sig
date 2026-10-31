(* Compact named syntax, not original Source or realization authority. *)
signature SmtReplayNamedContext =
sig
  datatype boundary = Empty | Leaf of int | Split of boundary * boundary
  val make_tree : int -> int -> boundary
  val tree_term : Term.term vector -> boundary -> Term.term
  val project : boundary -> Thm.thm -> Thm.thm list
  val tree_proof : Thm.thm vector -> boundary -> Thm.thm

  datatype 'node view = Atom | Constant of Term.term
    | Application of 'node * 'node
  val constructor_rhs : ('node -> Term.term) -> 'node view ->
    Term.term option
  val spine : ('node -> 'node view) -> 'node ->
    (Term.term * 'node list) option
  val operands : ('node -> 'node view) -> Term.term -> int -> 'node ->
    'node list option
  val equality : ('node -> 'node view) -> 'node ->
    ('node * 'node) option
  type literal_substitution
  datatype 'node primitive = ReflexiveName of 'node
    | Symmetry | Transitivity | Congruence | EqualityMP
    | ApplyNamedArgument of 'node | ImplicationMP
    | SubstituteLiteral of literal_substitution
  (* Exact closed recipe inventory. Arity is checked before any rule call.
     The caller admits all compact operands and the prospective result.
     This worker grants no ownership, hypotheses or native admission. *)
  val primitive : ('node -> Term.term) -> 'node primitive ->
    Thm.thm list -> Thm.thm
  val primitive_using : (unit -> exn) -> ('node -> Term.term) ->
    'node primitive -> Thm.thm list -> Thm.thm
  type profile =
    {raw:IntInf.int,inc:IntInf.int,ann:IntInf.int,ty:IntInf.int}
  datatype shape = HeldSyntax of Term.term
    | EqualitySyntax of shape * shape | ApplicationSyntax of shape * shape
  (* Same native compact policy programme as the graph specialization.
     Supplied membership is syntax ownership only; the upper consumer
     retains the actual Work/native-contract association. *)
  type admission =
    {pay:IntInf.int -> unit,member:Term.term -> bool,guard:unit -> unit,
     template_limit:int,type_work_limit:int,error:string -> exn}
  type fixed_admission =
    {pay:IntInf.int -> unit,guard:unit -> unit,
     template_limit:int,type_work_limit:int,error:string -> exn}
  val type_weight : admission -> Type.hol_type -> IntInf.int
  val type_weight_using : (IntInf.int -> unit) -> (string -> exn) ->
    IntInf.int -> Type.hol_type -> IntInf.int
  val inspector : admission -> {profile:Term.term -> profile}
  (* Syntax metadata only. Each genuine owner keeps its store private;
     the admission payer must recheck that owner before every store access.
     A cache grants no native allowance, theorem, Source or scoped port. *)
  type profile_store
  val empty_profile_store_using : (IntInf.int -> unit) -> profile_store
  (* Owner-prepaid O(1) release only: no guard, debit or callback. *)
  val clear_profile_store : profile_store -> unit
  val inspector_with_store : admission -> profile_store ->
    {profile:Term.term -> profile}
  val prepare_fixed : admission -> ('node -> Term.term) ->
    'node primitive -> Thm.thm list ->
    {proofs:Thm.thm list,shape:shape,hypotheses:Term.term list}
  val prepare_fixed_using : fixed_admission -> (Term.term -> profile) ->
    ('node -> Term.term) -> 'node primitive -> Thm.thm list ->
    {proofs:Thm.thm list,shape:shape,hypotheses:Term.term list}
  (* SAME prospective fixed programme over syntax-only proof views.
     Result is DATA; it cannot enter the opaque edge constructor. Actual
     derive still reads genuine checked Thm.concl/Thm.hyp and runs the same
     native worker. Direct readers add no operation/context record. *)
  (* The actual metadata scans still use admission.pay. Only the final
     prospective native portfolio goes to quote. A syntax-only forecast
     is DATA, never an edge, native admission, or caller spending credit.
     The existing observed wrappers pass admission.pay unchanged. *)
  val prepare_fixed_quoted : (IntInf.int -> unit) ->
    ('proof -> Term.term) -> ('proof -> Term.term list) -> fixed_admission ->
    (Term.term -> profile) -> ('node -> Term.term) ->
    'node primitive -> 'proof list ->
    {proofs:'proof list,shape:shape,hypotheses:Term.term list}
  val prepare_fixed_observed : ('proof -> Term.term) ->
    ('proof -> Term.term list) -> fixed_admission ->
    (Term.term -> profile) -> ('node -> Term.term) ->
    'node primitive -> 'proof list ->
    {proofs:'proof list,shape:shape,hypotheses:Term.term list}
  val matches : shape -> Term.term -> bool
  (* Shared binder-free expression walker. Observe actual visits and
     construction setup, use genuine guarded profile/Type callbacks, then
     bound/quote the complete native portfolio BEFORE realize_shape.
     A caller-provided shape/observer grants no native or proof authority. *)
  val describe_shape : (shape -> unit) -> (Term.term -> profile) ->
    (Type.hol_type -> IntInf.int) ->
    (Type.hol_type -> Type.hol_type -> bool) ->
    shape -> profile * Type.hol_type
  val realize_shape : (shape -> unit) -> shape -> Term.term
  datatype 'node boolean_rule = PolicyImplicationMP | PolicyConjunction
    | PolicyConjunctLeft | PolicyConjunctRight | PolicyNotIntro
    | PolicyNotElim | PolicyEqTrueElim | PolicyEqFalseElim
    | PolicyContradiction of 'node
  datatype boolean_shape = PBHeld of Term.term | PBFalse
    | PBNegation of boolean_shape
    | PBImplication of boolean_shape * boolean_shape
    | PBConjunction of boolean_shape * boolean_shape
  val boolean_syntax : (boolean_shape -> unit) -> boolean_shape -> shape
  val prepare_boolean_using : fixed_admission -> (Term.term -> profile) ->
    ('node -> Term.term) -> 'node boolean_rule -> Thm.thm list ->
    {shape:boolean_shape,hypotheses:Term.term list}
  val prepare_boolean_quoted : (IntInf.int -> unit) ->
    ('proof -> Term.term) -> ('proof -> Term.term list) -> fixed_admission ->
    (Term.term -> profile) -> ('node -> Term.term) ->
    'node boolean_rule -> 'proof list ->
    {shape:boolean_shape,hypotheses:Term.term list}
  val prepare_boolean_observed : ('proof -> Term.term) ->
    ('proof -> Term.term list) -> fixed_admission ->
    (Term.term -> profile) -> ('node -> Term.term) ->
    'node boolean_rule -> 'proof list ->
    {shape:boolean_shape,hypotheses:Term.term list}
  val boolean_using : (unit -> exn) -> ('node -> Term.term) ->
    'node boolean_rule -> Thm.thm list -> Thm.thm
  val boolean_matches : boolean_shape -> Term.term -> bool

  type ('node,'proof) equality_operations =
    {key:'node -> int,same:'node * 'node -> bool,
     application:'node -> ('node * 'node) option,
     reflexive:'node -> 'proof,symmetry:'proof -> 'proof,
     transitivity:'proof -> 'proof -> 'proof,
     congruence:'proof * 'proof -> 'proof,definition:'node -> 'proof,
     error:string -> exn}
  val equality_programme : ('node,'proof) equality_operations ->
    {rule:string,left:'node,right:'node,
     premises:(('node * 'node) * 'proof) list} -> 'proof

  datatype named_inst_shape = NamedInstVariable of string * Type.hol_type
    | NamedInstConstant of Term.term * Type.hol_type
    | NamedInstApplication of named_inst_shape * named_inst_shape
  type named_inst_admission =
    {pay:IntInf.int -> unit,type_weight:Type.hol_type -> IntInf.int,
     member:Term.term -> bool,template_limit:int,type_work_limit:int,
     error:string -> string -> exn}
  val prepare_named_inst : named_inst_admission ->
    {substitution:(Term.term,Term.term) Lib.subst,theorem:Thm.thm} ->
    {shape:named_inst_shape,oracles:string list}
  val named_inst_matches : named_inst_shape -> Term.term -> bool

  type 'node operations =
    {guard:unit -> unit,spend:IntInf.int -> unit,key:'node -> int,
     type_of:'node -> Type.hol_type,view:'node -> 'node view,
     name:'node -> Term.term,check_type:Type.hol_type -> unit,
     native_limits:unit -> SmtReplayNativeContract.limits}
  type 'node block
  type edge
  (* All constructors run in the caller's existing action. Sources below
     are formal hypotheses ONLY. Original Source ports belong to the
     authentic upper consumer. Names must be distinct typed variables.
     Every retained operation rechecks the supplied lifetime guard. *)
  val freeze : 'node operations ->
    {nodes:'node list,sources:'node list,template_limit:int} -> 'node block
  val name : 'node block -> 'node -> Term.term
  val source : 'node block -> int -> edge
  val definition : 'node block -> 'node -> edge
  val constructor : 'node block -> 'node -> edge
  (* Same recursive constructor programme, not a new rule inventory.
     Static complete callbacks avoid a fresh operations box on old paths.
     Generic results have no Source, Scope or theorem authority. *)
  val constructor_using : ('context -> unit) ->
    ('node -> 'node view) ->
    ('context -> 'node -> 'proof) ->
    ('context -> 'node primitive -> 'proof list -> 'proof) ->
    'context -> 'node -> 'proof
  (* Actual existing tag predicate only; this boolean is not proof,
     Source, closure or native admission authority. *)
  val clean : Thm.thm -> bool
  val theorem : 'node block -> edge -> Thm.thm
  val needed_sources : 'node block -> edge -> int list
  val dependencies : 'node block -> edge -> int list
  val derive : 'node block -> 'node primitive -> edge list -> edge
  val derive_boolean : 'node block -> 'node boolean_rule -> edge list -> edge
  val compact_profile : 'node block -> Term.term -> profile
  val native_type_weight : 'node block -> Type.hol_type -> IntInf.int
  (* Only a clean closed proof over admitted compact names can enter.
     This is not original Source admission or a native operand conversion. *)
  val closed : 'node block -> Thm.thm -> edge
  val retire : 'node block -> unit
  (* Same closed input/owned-name admission and one actual INST as closed.
     Preparation is metadata-only; execution returns a genuine edge of
     the retained block once. The supplied owner guard remains active. *)
  type 'node closed_inst_plan
  val prepare_closed_inst : 'node block ->
    {substitution:(Term.term,Term.term)Lib.subst,theorem:Thm.thm} ->
    'node closed_inst_plan
  val execute_closed_inst : 'node closed_inst_plan -> edge
  (* Metadata-only preparation of the SAME sparse freeze programme.
     Operations callbacks still run as supplied; a sealed scoped caller
     must defer its external policy callbacks and settle the whole child
     programme first. This lower plan grants no Source/Scope authority.
     The real future ASSUME incidence is paid during preparation once;
     execution consumes the private retained programme once, not a caller
     amount, before minting ordinary formal named edges. *)
  type 'node freeze_plan
  (* Explicit additional formal hypotheses, not original Sources.
     Leaves are actual owned name variables or atomic constants only.
     The SAME prefix admits their complete bounded Boolean/Type geometry
     before any ASSUME. Original Source occurrence slots stay ordered;
     formals follow them and precede definitions in the immutable layout.
     A higher authentic owner must pair every selected actual native Hyp
     with its genuine witness. No original Source permission is issued.
     needed_sources is the old atom-name query; formal owners use actual
     native Hyp pointers, the layout and genuine edge dependencies. *)
  val prepare_freeze_with_formals : 'node operations ->
    {nodes:'node list,sources:'node list,formals:shape list,
     template_limit:int} -> 'node freeze_plan
  val freeze_with_formals : 'node operations ->
    {nodes:'node list,sources:'node list,formals:shape list,
     template_limit:int} -> 'node block
  val prepare_freeze : 'node operations ->
    {nodes:'node list,sources:'node list,template_limit:int} ->
    'node freeze_plan
  val execute_freeze : 'node freeze_plan -> 'node block
  (* Authenticated immutable syntax layout only. Its rows are the SAME
     individually bounded sparse ASSUME shapes; dictionary keys retain
     the original private guarded comparator. Reading this DATA cannot
     mint an edge, Source, scoped result or proof/native admission. *)
  val freeze_layout : 'node freeze_plan ->
    {shapes:shape list,definitions:(int,int) Redblackmap.dict,
     source_count:int}
  (* The SAME admitted sparse syntax is materialized once, privately.
     Native execute uses these exact immutable Term objects in ASSUME;
     forecasting does not rebuild a different hypothesis representative.
     The original macro construction quotation is consumed once, not
     charged again. No theorem or Source edge is produced by this read. *)
  val materialize_freeze : 'node freeze_plan -> Term.term list
  (* SAME caller-owned action; actual named input edges and the fixed
     recorded programme only. No caller open theorem enters this port. *)
  type 'node unit_resolution_plan
  val prepare_unit_resolution : 'node block ->
    {premises:{tree:'tree,edge:edge} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list,
     tree_view:'tree -> ('node,'tree) SmtReplayNamedClause.tree_view,
     metadata_template:SmtReplayResourcePolicy.limit} ->
    'node unit_resolution_plan
  val prepare_unit_resolution_with_atom_aliases :
    ('node * 'node) list -> 'node block ->
    {premises:{tree:'tree,edge:edge} list,target:'tree,
     target_expanded:'tree option,fallbacks:'tree list,
     tree_view:'tree -> ('node,'tree) SmtReplayNamedClause.tree_view,
     metadata_template:SmtReplayResourcePolicy.limit} ->
    'node unit_resolution_plan
  val execute_unit_resolution : 'node unit_resolution_plan -> edge
  (* SAME caller-owned action. Actual Block constructors, names and
     definition edges establish the equality; syntax aliases are DATA. *)
  type 'node atom_congruence_plan
  val prepare_atom_congruence : 'node block ->
    {left:'node,right:'node,
     metadata_template:SmtReplayResourcePolicy.limit} ->
    'node atom_congruence_plan
  val execute_atom_congruence : 'node atom_congruence_plan -> edge
  (* Fixed XOR is derived only from authentic Block geometry and
     the module's one closed Boolean definition. No caller theorem. *)
  datatype xor_clause = XorPositiveOne | XorPositiveTwo
    | XorNegativeOne | XorNegativeTwo
  type 'node fixed_xor_plan
  val prepare_fixed_xor : 'node block ->
    {node:'node,left:'node,right:'node,clause:xor_clause,
     metadata_template:SmtReplayResourcePolicy.limit} -> 'node fixed_xor_plan
  val execute_fixed_xor : 'node fixed_xor_plan -> edge
end
