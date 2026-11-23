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
      (* Marks what the application [term] = [rator rands] introduces. *)
      fun mark_application term rator rands terms =
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
      (* The application prefixes of [term], longest first, ending with its
         head. *)
      fun prefixes term =
        case (SOME ((#dest_comb operations) term)
              handle primary => if is_syntax_error primary then NONE
                else raise primary) of
          SOME (function, _) => function :: prefixes function
        | NONE => []
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
          (* Walking each prefix would walk its arguments again, so that
             applications nested in their first argument took arity^depth
             walks.  Walk the head once and mark each partial application
             from its own arguments, which were walked above. *)
          val terms =
            if visit_prefix then
              (case List.rev (prefixes term) of
                 [] => terms
               | head :: partials =>
                   let
                     val arity = List.length rands
                     (* Only unary and binary marker arguments are inspected. *)
                     fun prefix_arguments count =
                       if count <= 2 orelse count > arity then
                         List.take (rands, count)
                       else rands
                   in
                     #2 (List.foldl (fn (partial, (count, acc)) =>
                       (count + 1, mark_application partial rator
                          (prefix_arguments count) acc))
                       (1, walk head terms) partials)
                   end)
            else terms
        in
          mark_application term rator rands terms
        end)
    in walk end

  fun closure_groups (operations : 'term operations)
      (closure : 'term closure_operations) inventory =
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
    in List.foldl applications
      (Redblackmap.mkDict compare,Redblackmap.mkDict compare) inventory end

  fun propagate (operations : 'term operations)
      (closure : 'term closure_operations) is_syntax_error connect
      (term,terms) =
    let
      val terms = case (#condition operations) term of
          SOME (_,left,right) => connect [term,left,right] terms
        | NONE => terms
      val (head,args) = (#strip_comb operations) term
      val terms = case (#classify operations) (term,head) of
          Update => (case args of
              [_,_,base] => connect [term,base] terms
            | _ => terms)
        | _ => terms
    in
      (let val bindings = (#bindings operations) term
           val body = (#let_body closure) term
       in List.foldl (fn ((variable,value),acc) =>
         connect [variable,value] acc) (connect [term,body] terms)
           bindings end
       handle primary => if is_syntax_error primary then terms
         else raise primary)
    end

  fun parameters_for member arguments terms =
    Redblackmap.foldl (fn ((head,index),args,acc) =>
      case List.find (fn arg => member arg terms) args of
        SOME arg => (head,index,arg) :: acc | NONE => acc) [] arguments

  fun close (operations : 'term operations)
      (closure : 'term closure_operations) is_syntax_error inventory seeds =
    if List.null seeds then ([],[]) else
    let
      val (arguments,results) = closure_groups operations closure inventory
      fun connect nodes terms =
        if List.exists (fn term => (#member operations) term terms) nodes then
          List.foldl (fn (term,acc) => (#add operations) term acc) terms nodes
        else terms
      val propagate = propagate operations closure is_syntax_error connect
      fun spread groups terms = Redblackmap.foldl
        (fn (_,nodes,acc) => connect nodes acc) terms groups
      fun fixed terms =
        let val next = List.foldl propagate terms inventory
            val next = spread results (spread arguments next)
        in if List.length next = List.length terms then next
           else fixed next end
      val terms = fixed seeds
    in (terms,parameters_for (#member operations) arguments terms) end

  fun close_indexed (operations : 'term operations)
      (closure : 'term closure_operations) is_syntax_error inventory seeds =
    if List.null seeds then ([],[]) else
    let
      val (arguments,results) = closure_groups operations closure inventory
      fun connect nodes edges = nodes :: edges
      val edges = List.foldl
        (propagate operations closure is_syntax_error connect) [] inventory
      fun append (_,nodes,edges) = nodes :: edges
      val edges = Redblackmap.foldl append
        (Redblackmap.foldl append edges arguments) results
      fun collection_edge nodes =
        case List.filter (#is_collection_type operations) nodes of
          nodes as _ :: _ :: _ => SOME nodes
        | _ => NONE
      val edges = Vector.fromList (List.mapPartial collection_edge
        (List.rev edges))
      val incident = Vector.foldli (fn (index,nodes,table) =>
        List.foldl (fn (node,table) =>
          Redblackmap.insertWith (fn (saved,_) => index :: saved)
            (table,node,[index])) table nodes)
        (Redblackmap.mkDict (#compare closure)) edges
      val scheduled = Array.array (Vector.length edges,false)
      val pending = Redblackmap.mkDict Int.compare
      fun schedule index (node,(this,next)) =
        List.foldl (fn (edge,(this,next)) =>
          if Array.sub (scheduled,edge) then (this,next)
          else
            (Array.update (scheduled,edge,true);
             if edge > index then (Redblackmap.insert (this,edge,()),next)
             else (this,Redblackmap.insert (next,edge,()))))
          (this,next) (Option.getOpt (Redblackmap.peek (incident,node),[]))
      fun run (terms,marked,this,next) =
        case Redblackmap.firsti this of
          NONE =>
            if Redblackmap.isEmpty next then (terms,marked)
            else run (terms,marked,next,pending)
        | SOME (edge,()) =>
          let
            fun add (node,(terms,marked,this,next)) =
              if Redblackset.member (marked,node) then
                (terms,marked,this,next)
              else
                let val (this,next) = schedule edge (node,(this,next))
                in (node::terms,Redblackset.add (marked,node),this,next) end
          in run (List.foldl add
            (terms,marked,#1 (Redblackmap.remove (this,edge)),next)
            (Vector.sub (edges,edge))) end
      (* A newly marked node wakes later edges in this pass. Earlier edges
         wait until the next pass, as in the original ordered scan. *)
      val (this,next) = List.foldl (schedule ~1) (pending,pending) seeds
      val (terms,marked) = run (seeds,
        Redblackset.addList (Redblackset.empty (#compare closure),seeds),
        this,next)
    in
      (terms,parameters_for (fn arg => fn marked =>
        Redblackset.member (marked,arg)) arguments marked)
    end

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
