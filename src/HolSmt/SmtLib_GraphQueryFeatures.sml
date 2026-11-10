(* Shared sequence eligibility over an authenticated outbound query DAG. *)
structure SmtLib_GraphQueryFeatures =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure T = SmtLib_GraphTranslation

  type sequence_result =
    {eligible : bool, visits : int, totalized_visits : int}
  datatype visit = Enter of Q.carrier | Leave of Q.carrier

  fun compare_key ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of
      EQUAL => Int.compare (ln,rn)
    | order => order

  type string_presence_result =
    {has_hol_strings:bool,raw_visits:int,head_visits:int}

  (* Supply the actual emitted assumptions followed by the negated emitted
     conclusion, after any checked/backend transformations. The original GP
     roots need not be that syntax. This observer never chooses those roots.
     Library.subterms visits both App children and only an Abs body; no
     ALL_DISTINCT or literal-encoding pruning belongs to this inventory. *)
  fun string_presence (context:Q.outbound_context) roots :
      string_presence_result =
    let
      fun guard current = ignore ((#key context) current)
      val _ = guard (#goal context)
      val nodes = ref
        (Redblackmap.mkDict compare_key :
          (int * int,Q.carrier option) Redblackmap.dict)
      val ordered = ref ([]:Q.carrier list)
      fun inventory [] = ()
        | inventory (current::pending) =
            let val key = (#key context) current in
              case Redblackmap.peek (!nodes,key) of
                SOME _ => inventory pending
              | NONE =>
                  let
                    val _ = (#step context) ()
                    val (left,children) = case (#view context) current of
                        Q.ApplicationView (function,argument) =>
                          (SOME function,[function,argument])
                      | Q.AbstractionView (_,body) => (NONE,[body])
                      | _ => (NONE,[])
                    val _ = List.app guard children
                    val _ = guard current
                    val _ = nodes := Redblackmap.insert (!nodes,key,left)
                    val _ = ordered := current :: !ordered
                  in inventory (children @ pending) end
            end
      val _ = List.app guard roots
      val _ = inventory roots
      val ordered = List.rev (!ordered)
      val heads = ref
        (Redblackmap.mkDict compare_key :
          (int * int,Q.carrier) Redblackmap.dict)
      val head_visits = ref 0
      fun publish current head =
        let val key = (#key context) current
            val _ = guard head val _ = (#step context) ()
            val _ = guard current val _ = guard head
            val _ = heads := Redblackmap.insert (!heads,key,head)
            val _ = head_visits := !head_visits+1
        in () end
      (* Cache only the left-spine head, not a fresh argument list for every
         application prefix. Pending frames are explicit and successful-only.
         Every hit authenticates both the input and the returned carrier. *)
      fun head_of current =
        let
          fun finish head [] = (guard head;head)
            | finish head (current::pending) =
                (publish current head;finish head pending)
          fun walk current pending =
            let val key = (#key context) current in
              case Redblackmap.peek (!heads,key) of
                SOME head => (guard head;finish head pending)
              | NONE =>
                  (case Redblackmap.find (!nodes,key) of
                     SOME function => walk function (current::pending)
                   | NONE =>
                       (publish current current;finish current pending))
            end
        in walk current [] end
      fun test_constant predicate current = case (#view context) current of
          Q.ConstantView atom => predicate atom
        | _ => false
      val presence = SmtLib.outbound_string_presence
        {type_of= #type_of context,head_of=head_of,
         test_constant=test_constant} ordered
      val _ = List.app guard roots
      val _ = guard (#goal context)
    in {has_hol_strings=presence,raw_visits=length ordered,
      head_visits= !head_visits} end

  fun sequence_eligibility (context : Q.outbound_context) : sequence_result =
    let
      val builtin = T.outbound_builtin_operations context
      val recognizers = T.outbound_query_collection_recognizers context
        {sequence_emission=true}
      fun guard current = ignore ((#key context) current)
      fun accepts observe current =
        (ignore (observe current);true)
        handle primary =>
          if (#is_syntax_error builtin) primary then false else raise primary
      fun constant_name current = case (#view context) current of
          Q.ConstantView atom =>
            let val {Thy, Name, ...} = Term.dest_thy_const atom
            in SOME (Thy, Name) end
        | _ => NONE
      fun word_num current = case (#view context) current of
          Q.ApplicationView (function,_) =>
            (case (#view context) function of
               Q.ConstantView atom =>
                 Library.same_const wordsSyntax.w2n_tm atom
             | _ => false)
        | _ => false
      val operations : Q.carrier
          SmtLib.outbound_sequence_eligibility_operations =
        {constant_name=constant_name,type_of= #type_of context,
         is_extract=accepts (#seq_extract_shape recognizers),
         is_at=accepts (#seq_at_shape recognizers),is_word_num=word_num}
      val classifier = SmtLib.outbound_sequence_eligibility operations
      val nodes = ref
        (Redblackmap.mkDict compare_key :
          (int * int, Q.carrier list) Redblackmap.dict)
      val ordered = ref ([] : Q.carrier list)
      val postorder = ref ([] : Q.carrier list)
      (* Library.subterms visits an abstraction's body, not its binder. *)
      fun children current = case (#view context) current of
          Q.ApplicationView (function,argument) => [function,argument]
        | Q.AbstractionView (_,body) => [body]
        | _ => []
      fun inventory [] = ()
        | inventory (Leave current :: pending) =
            (guard current;postorder := current :: !postorder;
             inventory pending)
        | inventory (Enter current :: pending) =
            let val key = (#key context) current in
              case Redblackmap.peek (!nodes,key) of
                SOME _ => inventory pending
              | NONE =>
                  let
                    val _ = (#step context) ()
                    val next = children current
                    val _ = List.app guard next
                    val _ = nodes := Redblackmap.insert
                      (!nodes,key,next)
                    val _ = ordered := current :: !ordered
                  in inventory
                    (List.map Enter next @ (Leave current :: pending)) end
            end
      val roots = #goal context :: #assumptions context
      val _ = inventory (List.map Enter roots)
      val ordered = List.rev (!ordered)
      val postorder = List.rev (!postorder)
      fun saved_children current =
        let val key = (#key context) current
            val children = Redblackmap.find (!nodes,key)
            val _ = List.app guard children
        in children end
      val totalized_whole = ref (Redblackset.empty Int.compare)
      fun classify (current,roots) =
        let val _ = guard current val _ = (#step context) () in
          if (#totalized classifier) current then
            let val semantic = (#semantic_key context) current
                val _ = totalized_whole :=
                  Redblackset.add (!totalized_whole,semantic)
            in current :: roots end
          else roots
        end
      val totalized = List.rev (List.foldl classify [] ordered)
      (* One multi-source walk forms the union. Alpha membership is separate
         from the scoped keys used to visit and authenticate each position. *)
      val descendants = ref (Redblackset.empty compare_key)
      val totalized_parts = ref (Redblackset.empty Int.compare)
      val totalized_count = ref 0
      fun descend [] = ()
        | descend (current :: pending) =
            let val key = (#key context) current in
              if Redblackset.member (!descendants,key) then descend pending
              else
                let
                  val _ = (#step context) ()
                  val next = saved_children current
                  val semantic = (#semantic_key context) current
                  val _ = descendants := Redblackset.add (!descendants,key)
                  val _ = totalized_parts :=
                    Redblackset.add (!totalized_parts,semantic)
                  val _ = totalized_count := !totalized_count + 1
                in descend (next @ pending) end
            end
      val _ = descend totalized
      fun member table current =
        Redblackset.member (!table,(#semantic_key context) current)
      val native_parts = ref (Redblackmap.mkDict compare_key)
      fun native current =
        let val key = (#key context) current
        in Redblackmap.find (!native_parts,key) end
      fun compute_parts current =
        let
          val key = (#key context) current
          val _ = (#step context) ()
          val next = saved_children current
          val result = (#native_part classifier) current andalso
            List.all native next
          val _ = guard current
        in native_parts := Redblackmap.insert (!native_parts,key,result) end
      fun eligible () =
        List.all ((#supported classifier) (member totalized_parts)) ordered
        andalso not (List.exists (#is_word_num classifier) ordered) andalso
        (List.app compute_parts postorder;
         List.exists ((#selects_seq classifier)
           {native_parts=native,is_totalized_whole=member totalized_whole})
           ordered)
      val result = eligible ()
      val _ = List.app guard roots
    in
      {eligible=result,visits=length ordered,
       totalized_visits= !totalized_count}
    end

  fun native_sequence_goal context = #eligible (sequence_eligibility context)

  type feature_result =
    {features:SmtLib.logic_features,encoding_visits:int,
     quantifier_visits:int,bitvector_visits:int}

  (* The caller supplies the ACTUAL emitted assertion roots, declaration
     metadata and backend state. They can differ from the original GP roots
     after checked preprocessing. No parser or proof authority is inferred.
     Declaration arities/types are required even when no source node visits
     them; synthetic global definitions also contribute generated_forall. *)
  fun infer_features (context:Q.outbound_context)
      {operations:Q.carrier SmtLib.outbound_term_translation_operations,
       state:SmtLib.outbound_feature_state,regime,roots,
       types:(Type.hol_type,string) Redblackmap.dict,
       declarations:(Q.carrier * int) list} : feature_result =
    let
      val builtin = T.outbound_builtin_operations context
      val mismatch = #syntax_error builtin
      val is_mismatch = #is_syntax_error builtin
      fun guard current = ignore ((#key context) current)
      val _ = guard (#goal context)
      fun optional observe current = SOME (observe current)
        handle primary => if is_mismatch primary then NONE else raise primary
      fun dest_comb current = case (#view context) current of
          Q.ApplicationView pair => pair
        | _ => raise mismatch "feature_dest_comb" "application expected"
      fun dest_abs current = case (#view context) current of
          Q.AbstractionView pair => pair
        | _ => raise mismatch "feature_dest_abs" "abstraction expected"
      fun test_constant predicate current = case (#view context) current of
          Q.ConstantView atom => predicate atom
        | _ => false
      fun term_same_const current atom =
        test_constant (fn actual => Term.same_const actual atom) current
      fun constant_name current = case (#view context) current of
          Q.ConstantView atom =>
            let val {Thy,Name,...} = Term.dest_thy_const atom
            in (Thy,Name) end
        | _ => raise mismatch "feature_constant_name" "constant expected"
      fun dest_all_distinct current =
        let val (head,argument) = dest_comb current in
          if (#known_const_matches operations) listSyntax.all_distinct_tm head
          then argument
          else raise mismatch "feature_all_distinct" "ALL_DISTINCT expected"
        end
      fun is_all_distinct current =
        Option.isSome (optional dest_all_distinct current)
      fun memo () =
        let val answers = ref (Redblackmap.mkDict compare_key)
            val visits = ref 0
            fun apply current compute =
              let val key = (#key context) current in
                case Redblackmap.peek (!answers,key) of
                  SOME answer => (guard current;answer)
                | NONE =>
                    let val _ = (#step context) ()
                        val answer = compute ()
                        val _ = guard current
                        val _ = answers :=
                          Redblackmap.insert (!answers,key,answer)
                        val _ = visits := !visits + 1
                    in answer end
              end
        in (apply,visits) end
      (* BV and quantifier scans must not share encoding-inventory pruning:
         literal smtfp_bits fields prune BV only, and ALL_DISTINCT hides only
         its list encoding syntax. Every mode publishes returned bools only.
         The cache context (roots/backend/declarations/borrow) is fixed. *)
      val (memo_quantifier,quantifier_visits) = memo ()
      val (memo_bitvector,bitvector_visits) = memo ()
      val feature_operations : Q.carrier
          SmtLib.outbound_feature_operations =
        {type_of= #type_of operations,is_var= #is_var operations,
         is_comb=fn current => Option.isSome (optional dest_comb current),
         is_abs=fn current => Option.isSome (optional dest_abs current),
         dest_comb=dest_comb,dest_abs=dest_abs,
         strip_comb= #strip_comb operations,
         is_all_distinct=is_all_distinct,dest_all_distinct=dest_all_distinct,
         dest_list= #dest_list builtin,constant_name=constant_name,
         test_constant=test_constant,term_same_const=term_same_const,
         is_forall= #is_forall operations,is_exists= #is_exists operations,
         is_update_comb= #is_update_comb operations,
         is_injected_string= #is_injected_string operations,
         is_injected_float= #is_injected_float operations,
         is_word_literal= #is_word_literal builtin,
         is_shape_error=is_mismatch,is_optional_error=is_mismatch,
         metadata_error= #metadata_error operations,syntax_error=mismatch,
         memo_quantifier=memo_quantifier,memo_bitvector=memo_bitvector}
      val analysis = SmtLib.outbound_feature_analysis feature_operations
      val seen = ref (Redblackset.empty compare_key)
      val ordered = ref ([]:Q.carrier list)
      fun inventory [] = ()
        | inventory (current::pending) =
            let val key = (#key context) current in
              if Redblackset.member (!seen,key) then inventory pending
              else
                let val _ = (#step context) ()
                    val next = (#encoding_children analysis) current
                    val _ = List.app guard next
                    val _ = seen := Redblackset.add (!seen,key)
                    val _ = ordered := current :: !ordered
                in inventory (next @ pending) end
            end
      val _ = List.app guard roots
      val _ = List.app (guard o #1) declarations
      val _ = inventory roots
      val all_subterms = List.rev (!ordered)
      val features = (#infer analysis) state regime all_subterms roots
        (fn predicate => Redblackmap.foldl
          (fn (ty,_,found) => found orelse predicate ty) false types)
        (fn predicate => List.exists predicate declarations)
      val _ = List.app guard roots
      val _ = List.app (guard o #1) declarations
      val _ = guard (#goal context)
    in {features=features,encoding_visits=length all_subterms,
      quantifier_visits= !quantifier_visits,
      bitvector_visits= !bitvector_visits} end

end
