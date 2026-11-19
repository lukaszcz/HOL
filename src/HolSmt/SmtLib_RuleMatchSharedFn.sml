(* Compile, prepare and instantiate steps shared by the rule matchers.  The
   closure-tree walk comes from SmtLib_RuleMatchTreeFn, applied here to the
   same owner.  Each matcher keeps its own owner, schema, match and instance
   datatypes, its validation, its result constructors and its diagnostic
   origin; this functor takes the owner's operations as arguments and runs
   every metered step in the order the matchers always ran it. *)
signature SmtLib_RuleMatchSharedOwner =
sig
  include SmtLib_RuleMatchOwner
  datatype terminal = Equality | Positive | Negative
end

signature SmtLib_RuleMatchShared =
sig
  type owner
  type terminal
  structure Walk : SmtLib_RuleMatchTree where type walk_owner = owner
  datatype operation = Specialize of SmtReplayGraph.node | Select of bool
    | Undisch
  (* One clause of a compiled rule: the routes peeled off its root. *)
  type leaf =
    {binders : SmtReplayGraph.node list,conditions : Walk.tree list,
     left : Walk.tree,right : Walk.tree option,terminal : terminal,
     operations : operation list}
  val same_owner : string -> Walk.walk_owner -> Walk.walk_owner -> unit
  val leaves : owner -> string -> Walk.tree -> leaf list
  (* Metered walk over a rule list: `per_rule` turns the closure tree of the
     index-th rule into the owner's schemas. *)
  val compile_rules : owner ->
    {caller : string,scope : SmtReplayGraph.scope,original_changed : string,
     length_mismatch : string,originals : Thm.thm list,
     facts : SmtReplayProof.closed_fact list,
     validate_fact : SmtReplayProof.closed_fact -> unit,
     per_rule : int -> Thm.thm -> Walk.tree -> 'a list} -> 'a list
end

functor SmtLib_RuleMatchSharedFn (A : SmtLib_RuleMatchSharedOwner) :
    SmtLib_RuleMatchShared where type owner = A.owner
                           where type terminal = A.terminal =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure Walk = SmtLib_RuleMatchTreeFn (A)
  open Walk
  type owner = A.owner
  type terminal = A.terminal
  datatype operation = Specialize of G.node | Select of bool | Undisch
  type leaf =
    {binders : G.node list,conditions : tree list,left : tree,
     right : tree option,terminal : terminal,operations : operation list}
  fun same_owner message owner other =
    if Portable.pointer_eq (owner,other) then () else
      raise A.err "same_owner" message

  (* Peel the forall, conjunction and implication routes off a rule root. *)
  fun leaves owner caller whole =
    let fun peel binders conditions operations value =
          case unary owner "bool" "!" value of
            SOME predicate => (case #shape (data predicate) of
              Lam {binder,body,...} =>
                peel (binders @ [binder]) conditions
                  (operations @ [Specialize binder]) body
            | _ => raise A.err caller "forall has no genuine lambda")
          | NONE => (case binary owner "bool" "/\\" value of
              SOME (l,r) =>
                peel binders conditions (operations @ [Select true]) l @
                peel binders conditions (operations @ [Select false]) r
            | NONE => (case binary owner "min" "==>" value of
                SOME (condition,body) =>
                  peel binders (conditions @ [condition])
                    (operations @ [Undisch]) body
              | NONE =>
                  let val (terminal,left,right) =
                    case binary owner "min" "=" value of
                      SOME (l,r) => (A.Equality,l,SOME r)
                    | NONE => (case unary owner "bool" "~" value of
                        SOME p => (A.Negative,p,NONE)
                      | NONE => (A.Positive,value,NONE))
                  in [{binders = binders,conditions = conditions,left = left,
                       right = right,terminal = terminal,
                       operations = operations}] end))
    in peel [] [] [] whole end

  fun compile_rules owner {caller,scope,original_changed,length_mismatch,
      originals,facts,validate_fact,per_rule} =
    let val graph = A.graph owner
        fun loop [] [] _ = []
          | loop (rule::rest) (fact::more) index =
            let val _ = A.tick owner
                val n = P.closed_node fact
                val _ = validate_fact fact
                val _ = if Portable.pointer_eq
                  (rule,P.closed_original fact) then () else
                  raise A.err caller original_changed
                val root = G.closure_root graph scope n
                val whole = tree owner scope scope root
            in per_rule index rule whole @ loop rest more (index+1) end
          | loop _ _ _ = raise A.err caller length_mismatch
    in loop originals facts 0 end
end
