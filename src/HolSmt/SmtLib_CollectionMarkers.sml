(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_CollectionMarkers :> SmtLib_CollectionMarkers =
struct
  datatype role = Membership | UnaryObservation | Insert | Delete | Update
                | BinaryConstruction | UnaryConstruction | Inclusion
                | Empty | Equality | Other

  type 'term operations =
    {strip_comb : 'term -> 'term * 'term list,
     dest_abs : 'term -> 'term * 'term,
     dest_comb : 'term -> 'term * 'term,
     condition : 'term -> ('term * 'term * 'term) option,
     bindings : 'term -> ('term * 'term) list,
     add : 'term -> 'term list -> 'term list,
     member : 'term -> 'term list -> bool,
     is_collection_type : 'term -> bool,
     classify : 'term * 'term -> role}

  type 'term closure_operations =
    {compare : 'term * 'term -> order,
     share_symbol : 'term -> bool,
     let_body : 'term -> 'term}

  type 'term memo_hooks =
    {walk : 'term -> 'term list -> (unit -> 'term list) -> 'term list,
     mark : 'term -> 'term list -> (unit -> 'term list) -> 'term list}

  fun collect_with_memo_and_syntax_errors (operations : 'term operations)
      is_syntax_error
      ({walk=memo_walk,mark=memo_mark} : 'term memo_hooks)
      {propagate_bindings, visit_prefix} =
    let
      fun mark term terms =
        memo_mark term terms (fn () =>
          case (#condition operations) term of
            SOME (_, then_term, else_term) =>
              mark else_term (mark then_term ((#add operations) term terms))
          | NONE => (#add operations) term terms)
      fun walk term terms =
        memo_walk term terms (fn () => let
          val (rator, rands) = (#strip_comb operations) term
          val terms =
            (let val (_, body) = (#dest_abs operations) term
             in walk body terms end
             handle primary => if is_syntax_error primary then
               List.foldl (fn (arg, acc) => walk arg acc) terms rands
             else raise primary)
          val terms =
            if propagate_bindings then
              (let val bindings = (#bindings operations) term
               in List.foldl (fn ((variable, value), acc) =>
                 if (#member operations) variable acc then mark value acc
                 else acc) terms bindings end
               handle primary => if is_syntax_error primary then terms
                 else raise primary)
            else terms
          val terms =
            if visit_prefix then
              (let val (immediate_rator, _) = (#dest_comb operations) term
               in walk immediate_rator terms end
               handle primary => if is_syntax_error primary then terms
                 else raise primary)
            else terms
        in
          case (#classify operations) (term, rator) of
            Membership =>
              (case rands of [_, collection] => mark collection terms
               | _ => terms)
          | UnaryObservation =>
              (case rands of [collection] => mark collection terms
               | _ => terms)
          | Insert =>
              (case rands of [_, collection] =>
                 mark term (mark collection terms)
               | _ => terms)
          | Delete =>
              (case rands of [collection, _] =>
                 mark term (mark collection terms)
               | _ => terms)
          | BinaryConstruction =>
              (case rands of [left, right] =>
                 mark term (mark left (mark right terms))
               | _ => terms)
          | UnaryConstruction =>
              (case rands of [collection] =>
                 mark term (mark collection terms)
               | _ => terms)
          | Inclusion =>
              (case rands of [left, right] => mark left (mark right terms)
               | _ => terms)
          | Empty => (#add operations) term terms
          | Equality =>
              (case rands of [left, right] =>
                 if (#is_collection_type operations) left andalso
                    (#is_collection_type operations) right then
                   mark left (mark right terms)
                 else terms
               | _ => terms)
          | Update => terms
          | Other => terms
        end)
    in walk end

  fun close (operations : 'term operations)
      (closure : 'term closure_operations) is_syntax_error inventory seeds =
    if List.null seeds then ([],[]) else
    let
      val compare = Lib.pair_compare (#compare closure, Int.compare)
      fun insert key term groups =
        let val previous = case Redblackmap.peek (groups,key) of
                SOME terms => terms | NONE => []
        in Redblackmap.insert (groups,key,term :: previous) end
      fun applications (term,(arguments,results)) =
        let val (head,args) = (#strip_comb operations) term
            fun argument (arg,(index,groups)) =
              (index + 1,insert (head,index) arg groups)
        in if (#share_symbol closure) head then
          (#2 (List.foldl argument (0,arguments) args),
           insert (head,List.length args) term results)
        else (arguments,results) end
      val (arguments,results) = List.foldl applications
        (Redblackmap.mkDict compare,Redblackmap.mkDict compare) inventory
      fun connect nodes terms =
        if List.exists (fn term => (#member operations) term terms) nodes then
          List.foldl (fn (term,acc) => (#add operations) term acc) terms nodes
        else terms
      fun propagate (term,terms) =
        let val terms = case (#condition operations) term of
                SOME (_,left,right) => connect [term,left,right] terms
              | NONE => terms
            val (head,args) = (#strip_comb operations) term
            val terms = case (#classify operations) (term,head) of
                Update => (case args of
                    [_,_,base] => connect [term,base] terms
                  | _ => terms)
              | _ => terms
        in (let val bindings = (#bindings operations) term
                val body = (#let_body closure) term
            in List.foldl (fn ((variable,value),acc) =>
              connect [variable,value] acc) (connect [term,body] terms)
                bindings end
            handle primary => if is_syntax_error primary then terms
              else raise primary) end
      fun spread groups terms = Redblackmap.foldl
        (fn (_,nodes,acc) => connect nodes acc) terms groups
      fun fixed terms =
        let val next = List.foldl propagate terms inventory
            val next = spread results (spread arguments next)
        in if List.length next = List.length terms then next
           else fixed next end
      val terms = fixed seeds
      val parameters = Redblackmap.foldl (fn ((head,index),args,acc) =>
        case List.find (fn arg => (#member operations) arg terms) args of
          SOME arg => (head,index,arg) :: acc | NONE => acc) [] arguments
    in (terms,parameters) end

  fun legacy_syntax_error (Feedback.HOL_ERR _) = true
    | legacy_syntax_error _ = false

  fun collect_with_memo operations hooks policy =
    collect_with_memo_and_syntax_errors operations legacy_syntax_error
      hooks policy

  fun collect operations policy =
    collect_with_memo operations
      {walk=fn _ => fn _ => fn compute => compute (),
       mark=fn _ => fn _ => fn compute => compute ()} policy
end
