(* Copyright (c) 2026 The HOL4 contributors. *)

(* Sharing-preserving checked normalization for word-bearing Boolean graphs. *)

structure SmtWordGraph :> SmtWordGraph =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtWordGraph"
  val maximum = SmtResource.max_skeleton_replay_dag_nodes

  type metrics =
    {input_nodes : int,
     visited_nodes : int,
     generated_nodes : int,
     generated_edges : int,
     normalized_nodes : int,
     normalized_dag_nodes : int,
     projection_states : int,
     boolean_nodes : int,
     final_dag_nodes : int,
     type_nodes : int,
     type_tree_work : int,
     operator_calls : int,
     memo_hits : int}

  type proof_cache = (term, thm) Redblackmap.dict ref
  type indexed_proof_cache = (int, thm) Redblackmap.dict ref
  type context =
    {normalized : indexed_proof_cache, expanded : indexed_proof_cache,
     proof_normalized : indexed_proof_cache,
     proof_expanded : indexed_proof_cache,
     index : term -> int option, entries : int ref,
     word_schemas : proof_cache, bit_schemas : proof_cache,
     proof_schemas : proof_cache,
     frontier_programs :
       (term,((thm * metrics) option * (int * hol_type) list) option)
         Redblackmap.dict ref,
     schema_entries : int ref, local_law_reuse : bool,
     sat_context : SmtSkeletonProve.sat_context,
     cache_generation : unit ref ref,
     cache_live_check : term -> bool,
     refresh_caches : unit -> unit}

  fun new_context_with_local_laws local_law_reuse : context =
    let
      val signature_witness = ref (SmtSkeletonProve.cache_signature ())
      val cache_generation = ref (ref ())
      val live_hints = ref (NONE : SmtSkeletonProve.live_memo option)
      val normalized = ref (Redblackmap.mkDict Int.compare)
      val expanded = ref (Redblackmap.mkDict Int.compare)
      val proof_normalized = ref (Redblackmap.mkDict Int.compare)
      val proof_expanded = ref (Redblackmap.mkDict Int.compare)
      val index = ref (SmtResource.new_bounded_term_index maximum)
      val word_schemas = ref (Redblackmap.mkDict Term.compare)
      val bit_schemas = ref (Redblackmap.mkDict Term.compare)
      val proof_schemas = ref (Redblackmap.mkDict Term.compare)
      val frontier_programs = ref (Redblackmap.mkDict Term.compare)
      val entries = ref 0 and schema_entries = ref 0
      val sat_context = SmtSkeletonProve.new_sat_context ()
      fun refresh_caches () =
        if SmtSkeletonProve.cache_signature_matches (!signature_witness)
        then () else
          (cache_generation := ref ();
           live_hints := NONE;
           normalized := Redblackmap.mkDict Int.compare;
           expanded := Redblackmap.mkDict Int.compare;
           proof_normalized := Redblackmap.mkDict Int.compare;
           proof_expanded := Redblackmap.mkDict Int.compare;
           index := SmtResource.new_bounded_term_index maximum;
           word_schemas := Redblackmap.mkDict Term.compare;
           bit_schemas := Redblackmap.mkDict Term.compare;
           proof_schemas := Redblackmap.mkDict Term.compare;
           frontier_programs := Redblackmap.mkDict Term.compare;
           entries := 0; schema_entries := 0;
           #refresh_caches sat_context ();
           signature_witness := SmtSkeletonProve.cache_signature ())
      fun cache_live_check term =
        let
          val _ = refresh_caches ()
          val memo = case !live_hints of SOME memo => memo
            | NONE => let val memo = SmtSkeletonProve.new_live_memo ()
                      in live_hints := SOME memo; memo end
        in SmtSkeletonProve.live_check_with_hints
          (!signature_witness) memo term end
    in
      {normalized = normalized, expanded = expanded, entries = entries,
       proof_normalized = proof_normalized, proof_expanded = proof_expanded,
       index = fn term => (refresh_caches (); (!index) term),
       word_schemas = word_schemas, bit_schemas = bit_schemas,
       proof_schemas = proof_schemas, schema_entries = schema_entries,
       frontier_programs = frontier_programs,
       local_law_reuse = local_law_reuse, sat_context = sat_context,
       cache_generation = cache_generation,
       cache_live_check = cache_live_check, refresh_caches = refresh_caches}
    end

  fun new_context () = new_context_with_local_laws false

  (* Word normalization and proof-only reflexivity have distinct normal
     forms. Share checked operator/SAT schemas, not callback-sensitive node
     results; their aggregate entry limit is still the original bound. *)
  fun proof_context (context : context) : context =
    {normalized= #proof_normalized context,expanded= #proof_expanded context,
     proof_normalized= #proof_normalized context,
     proof_expanded= #proof_expanded context,index= #index context,
     entries= #entries context,word_schemas= #word_schemas context,
     bit_schemas= #bit_schemas context,proof_schemas= #proof_schemas context,
     schema_entries= #schema_entries context,
     frontier_programs= #frontier_programs context,
     local_law_reuse= #local_law_reuse context,
     sat_context= #sat_context context,
     cache_generation= #cache_generation context,
     cache_live_check= #cache_live_check context,
     refresh_caches= #refresh_caches context}

  fun schema_lookup (context : context) cache source =
    (#refresh_caches context ();
    case Redblackmap.peek (!cache, source) of
      NONE => NONE
    | SOME theorem =>
        SOME (SmtSkeletonProve.anchor_left source theorem, true))

  fun context_lookup (context : context) cache source =
    (#refresh_caches context ();
    case (#index context) source of
      NONE => NONE
    | SOME id =>
        (case Redblackmap.peek (!cache, id) of
           NONE => NONE
         | SOME theorem =>
             SOME (SmtSkeletonProve.anchor_left source theorem, true)))

  fun context_save (context : context) cache source (theorem, changed) =
    (#refresh_caches context ();
    if not changed orelse !(#entries context) >= maximum orelse
       not (#cache_live_check context (Thm.concl theorem)) then ()
    else
      case (#index context) source of NONE => () | SOME id =>
      if Option.isSome (Redblackmap.peek (!cache, id)) then () else let
        val _ = if List.null (Thm.hyp theorem) then ()
          else raise ERR "context_save" "normalization has hypotheses"
        val _ = Library.check_oracle_tags "SmtWordGraph" "context_save"
          theorem
      in
        cache := Redblackmap.insert (!cache, id, theorem);
        #entries context := !(#entries context) + 1
      end)

  (* Portable HOL does not expose a numeric physical-identity key.  Small
     operation-local caches use pointer lists; the potentially large generated
     graph uses shallow-hash buckets below.  Neither lookup unfolds equal
     shared terms through Term.compare. *)
  fun pointer_peek entries term =
    case List.find
        (fn (saved, _) => Portable.pointer_eq (term, saved)) entries of
      NONE => NONE
    | SOME (_, value) => SOME value

  fun eager_bits value = String.size (Arbnum.toBinString value)

  fun bounded_eager_product digit_limit left right =
    if digit_limit < 1 orelse eager_bits left > digit_limit orelse
       eager_bits right > digit_limit then NONE
    else if left = Arbnum.zero orelse right = Arbnum.zero then SOME Arbnum.zero
    else if left = Arbnum.one then SOME right
    else if right = Arbnum.one then SOME left
    else if eager_bits left + eager_bits right - 1 > digit_limit then NONE
    else
      (* The lower bit-length bound permits at most one additional digit of
         temporary product here.  Inspect that exact product before retaining
         it as an admitted eager intermediate. *)
      let val product = Arbnum.* (left, right)
      in if eager_bits product <= digit_limit then SOME product else NONE end

  fun eager_product_fits_for_test digit_limit left right =
    Option.isSome (bounded_eager_product digit_limit left right)

  datatype dimension = UnknownDimension | Within of Arbnum.num | TooLarge

  datatype eager_dimension =
      EagerUnknown
    | EagerWithin of Arbnum.num
    | EagerTooLarge

  datatype type_key =
      TypeVariableKey of string
    | TypeOperatorKey of KernelSig.kernelid * int list

  fun int_list_compare ([], []) = EQUAL
    | int_list_compare ([], _ :: _) = LESS
    | int_list_compare (_ :: _, []) = GREATER
    | int_list_compare (left :: lefts, right :: rights) =
        (case Int.compare (left, right) of
           EQUAL => int_list_compare (lefts, rights)
         | order => order)

  fun type_key_compare
      (TypeVariableKey left, TypeVariableKey right) =
        String.compare (left, right)
    | type_key_compare (TypeVariableKey _, TypeOperatorKey _) = LESS
    | type_key_compare (TypeOperatorKey _, TypeVariableKey _) = GREATER
    | type_key_compare
        (TypeOperatorKey (left, lefts), TypeOperatorKey (right, rights)) =
        (case KernelSig.id_compare (left, right) of
           EQUAL => int_list_compare (lefts, rights)
         | order => order)

  type type_info =
    {cardinality : dimension, eager : eager_dimension,
     tree_work : int, identity : int}

  type type_admission =
    {type_info : hol_type -> type_info,
     check_primitive_type : hol_type -> unit,
     bounded_word_width : hol_type -> dimension,
     type_nodes : int ref,
     type_tree_work : int ref}

  fun new_type_admission () =
    let
      val dimension_limit = Arbnum.fromInt maximum
      val type_work_limit = SmtResource.max_bv_replay_term_nodes
      val eager_digit_limit = Int.max (1, (type_work_limit - 3) div 2)
      val eager_digit_limit_num = Arbnum.fromInt eager_digit_limit
      val type_cache = ref ([] : (hol_type * type_info) list)
      val type_infos = ref
        (Redblackmap.mkDict type_key_compare :
          (type_key, type_info) Redblackmap.dict)
      val next_type_id = ref 0
      val type_nodes = ref 0
      val type_tree_work = ref 0
      fun operator_id ty = #Tyop (Type.dest_thy_typeid ty)
      val one_id = operator_id (fcpSyntax.mk_int_numeric_type 1)
      val bit0_id = operator_id (fcpSyntax.mk_int_numeric_type 2)
      val bit1_id = operator_id (fcpSyntax.mk_int_numeric_type 3)
      val sum_id = operator_id
        (Type.mk_thy_type
          {Thy = "sum", Tyop = "sum", Args = [Type.bool, Type.bool]})
      val prod_id = operator_id
        (Type.mk_thy_type
          {Thy = "pair", Tyop = "prod", Args = [Type.bool, Type.bool]})
      val fun_id = operator_id (Type.bool --> Type.bool)
      val cart_id = operator_id
        (fcpSyntax.mk_cart_type (Type.bool, Type.bool))
      fun same_operator left right =
        KernelSig.id_compare (left, right) = EQUAL

      fun bounded_count_add left right =
        if left > type_work_limit - Int.min (right, type_work_limit) then
          type_work_limit + 1
        else Int.min (type_work_limit + 1, left + right)

      fun bounded_plus (Within left) (Within right) =
            let val result = Arbnum.+ (left, right)
            in if Arbnum.<= (result, dimension_limit)
               then Within result else TooLarge end
        | bounded_plus TooLarge _ = TooLarge
        | bounded_plus _ TooLarge = TooLarge
        | bounded_plus _ _ = UnknownDimension

      fun bounded_times (Within left) right =
            if left = Arbnum.one then right
            else (case right of
                    Within value =>
                      let val result = Arbnum.* (left, value)
                      in if Arbnum.<= (result, dimension_limit)
                         then Within result else TooLarge end
                  | TooLarge => TooLarge
                  | UnknownDimension => UnknownDimension)
        | bounded_times left (Within right) =
            if right = Arbnum.one then left
            else (case left of TooLarge => TooLarge
                 | UnknownDimension => UnknownDimension
                 | Within _ => raise ERR "bounded_times" "impossible")
        | bounded_times TooLarge _ = TooLarge
        | bounded_times _ TooLarge = TooLarge
        | bounded_times _ _ = UnknownDimension

      fun bounded_power base exponent =
        if base = Arbnum.one then Within Arbnum.one
        else
          case exponent of
            Within power =>
              let
                fun loop n result =
                  if n = Arbnum.zero then Within result
                  else if Arbnum.>
                      (result, Arbnum.div (dimension_limit, base)) then
                    TooLarge
                  else loop (Arbnum.less1 n) (Arbnum.* (result, base))
              in loop power Arbnum.one end
          | TooLarge => TooLarge
          | UnknownDimension => UnknownDimension

      fun eager_plus (EagerWithin left) (EagerWithin right) =
            if Int.max (eager_bits left, eager_bits right) + 1 >
               eager_digit_limit then EagerTooLarge
            else EagerWithin (Arbnum.+ (left, right))
        | eager_plus EagerTooLarge _ = EagerTooLarge
        | eager_plus _ EagerTooLarge = EagerTooLarge
        | eager_plus _ _ = EagerUnknown

      fun eager_times (EagerWithin left) (EagerWithin right) =
            if left = Arbnum.zero orelse right = Arbnum.zero then
              EagerWithin Arbnum.zero
            else if left = Arbnum.one then EagerWithin right
            else if right = Arbnum.one then EagerWithin left
            else
              (case bounded_eager_product eager_digit_limit left right of
                 SOME product => EagerWithin product
               | NONE => EagerTooLarge)
        | eager_times EagerTooLarge _ = EagerTooLarge
        | eager_times _ EagerTooLarge = EagerTooLarge
        | eager_times _ _ = EagerUnknown

      fun eager_power (EagerWithin base) (EagerWithin exponent) =
            if exponent = Arbnum.zero then EagerWithin Arbnum.one
            else if base = Arbnum.zero then EagerWithin Arbnum.zero
            else if base = Arbnum.one then EagerWithin Arbnum.one
            else if Arbnum.> (exponent, eager_digit_limit_num) then
              EagerTooLarge
            else
              let
                val two = Arbnum.fromInt 2
                fun loop power factor result =
                  if power = Arbnum.zero then EagerWithin result
                  else
                    let
                      val result' =
                        if Arbnum.mod (power, two) = Arbnum.one then
                          eager_times (EagerWithin result)
                            (EagerWithin factor)
                        else EagerWithin result
                    in
                      case result' of
                        EagerWithin value =>
                          if power = Arbnum.one then EagerWithin value
                          else
                            (case eager_times (EagerWithin factor)
                                (EagerWithin factor) of
                               EagerWithin square => loop
                                 (Arbnum.div (power, two)) square value
                             | other => other)
                      | other => other
                    end
              in loop exponent base Arbnum.one end
        | eager_power EagerTooLarge _ = EagerTooLarge
        | eager_power _ EagerTooLarge = EagerTooLarge
        | eager_power _ _ = EagerUnknown

      fun type_info ty =
        case SmtResource.recent_pointer_lookup type_cache ty of
          SOME info => info
        | NONE =>
            let
              val arguments = if Type.is_vartype ty then []
                else Lib.snd (Type.dest_type ty)
              val children = List.map type_info arguments
              val key = if Type.is_vartype ty then
                  TypeVariableKey (Type.dest_vartype ty)
                else TypeOperatorKey
                  (operator_id ty, List.map #identity children)
              val info =
                case Redblackmap.peek (!type_infos, key) of
                  SOME saved => saved
                | NONE =>
                    let
                      val _ = type_nodes := !type_nodes + 1
                      val _ = SmtResource.check_dag_size_with_limit
                        "BitVector" "word-graph-type-dag" maximum
                        (!type_nodes)
                      val tree_work = List.foldl
                        (fn ({tree_work, ...}, total) =>
                          bounded_count_add total tree_work) 1 children
                      val id = if Type.is_vartype ty then NONE
                        else SOME (operator_id ty)
                      fun selected expected =
                        case id of SOME actual => same_operator actual expected
                         | NONE => false
                      val cardinality =
                        case children of
                          [] => if selected one_id then Within Arbnum.one
                            else UnknownDimension
                        | [child] =>
                            if selected bit0_id then bounded_times
                              (Within (Arbnum.fromInt 2)) (#cardinality child)
                            else if selected bit1_id then bounded_plus
                              (Within Arbnum.one)
                              (bounded_times (Within (Arbnum.fromInt 2))
                                (#cardinality child))
                            else UnknownDimension
                        | [left, right] =>
                            if selected sum_id then bounded_plus
                              (#cardinality left) (#cardinality right)
                            else if selected prod_id then bounded_times
                              (#cardinality left) (#cardinality right)
                            else if selected fun_id then
                              (case #cardinality right of
                                 Within base => bounded_power base
                                   (#cardinality left)
                               | TooLarge => TooLarge
                               | UnknownDimension => UnknownDimension)
                            else if selected cart_id then
                              (case #cardinality left of
                                 Within base => bounded_power base
                                   (#cardinality right)
                               | TooLarge => TooLarge
                               | UnknownDimension => UnknownDimension)
                            else UnknownDimension
                        | _ => UnknownDimension
                      val eager =
                        case children of
                          [] => if selected one_id then EagerWithin Arbnum.one
                            else EagerUnknown
                        | [child] =>
                            if selected bit0_id then eager_times
                              (EagerWithin (Arbnum.fromInt 2)) (#eager child)
                            else if selected bit1_id then eager_plus
                              (EagerWithin Arbnum.one)
                              (eager_times (EagerWithin (Arbnum.fromInt 2))
                                (#eager child))
                            else EagerUnknown
                        | [left, right] =>
                            if selected sum_id then eager_plus
                              (#eager left) (#eager right)
                            else if selected prod_id then eager_times
                              (#eager left) (#eager right)
                            else if selected fun_id then eager_power
                              (#eager right) (#eager left)
                            else if selected cart_id then eager_power
                              (#eager left) (#eager right)
                            else EagerUnknown
                        | _ => EagerUnknown
                      val created =
                        {cardinality = cardinality, eager = eager,
                         tree_work = tree_work, identity = !next_type_id}
                      val _ = next_type_id := !next_type_id + 1
                      val _ = type_infos :=
                        Redblackmap.insert (!type_infos, key, created)
                    in created end
              val _ = type_tree_work := Int.max (!type_tree_work,
                #tree_work info)
              val _ = type_cache := (ty, info) :: !type_cache
            in info end

      fun bounded_word_width ty =
        #cardinality (type_info (wordsSyntax.dest_word_type ty))

      fun check_primitive_type ty =
        let
          val {tree_work, ...} = type_info ty
          val seen = ref ([] : (hol_type * unit) list)
          fun check_width nested =
            case List.find (fn (saved, _) =>
                Portable.pointer_eq (nested, saved)) (!seen) of
              SOME (_, ()) => ()
            | NONE =>
                (seen := (nested, ()) :: !seen;
                 if wordsSyntax.is_word_type nested then
                   let val dimension = type_info
                     (wordsSyntax.dest_word_type nested)
                   in
                     (case #eager dimension of
                        EagerWithin _ => ()
                      | EagerUnknown => raise Conv.UNCHANGED
                      | EagerTooLarge =>
                          SmtResource.check_dag_size_with_limit "BitVector"
                            "word-graph-dimension-evaluation"
                            type_work_limit (type_work_limit + 1));
                     case #cardinality dimension of
                       Within _ => ()
                     | UnknownDimension => raise Conv.UNCHANGED
                     | TooLarge => SmtResource.check_dag_size_with_limit
                         "BitVector" "word-graph-width" maximum (maximum + 1)
                   end
                 else if Type.is_vartype nested then ()
                 else List.app check_width (Lib.snd (Type.dest_type nested)))
        in
          SmtResource.check_dag_size_with_limit "BitVector"
            "word-graph-primitive-type-tree" type_work_limit tree_work;
          check_width ty
        end
    in
      {type_info = type_info,
       check_primitive_type = check_primitive_type,
       bounded_word_width = bounded_word_width,
       type_nodes = type_nodes,
       type_tree_work = type_tree_work}
    end

  fun admit_primitive_type admission ty =
    #check_primitive_type admission ty

  fun primitive_type_id admission ty =
    (#check_primitive_type admission ty;
     #identity (#type_info admission ty))

  fun word_width admission ty =
    (#check_primitive_type admission ty;
     case #bounded_word_width admission ty of
       Within width => width
     | UnknownDimension => raise Conv.UNCHANGED
     | TooLarge => raise ERR "word_width" "admission invariant")

  fun unchanged_node _ = raise Conv.UNCHANGED

  (* Native matching/simplification can inspect annotations as well as
     terms. Bound their syntax WITHOUT evaluating word dimensions: a
     projection may discard an inadmissibly wide, unused producer. *)
  fun admit_callback_template (admission : type_admission) root =
    let
      val limit = SmtResource.max_bv_replay_term_nodes
      val _ = SmtResource.check_resource_goal
        "BitVector" "word-graph-schema" root
      val seen = ref ([] : term list)
      fun visit term =
        if List.exists (fn old => Portable.pointer_eq (old,term)) (!seen)
        then () else
          let
            val _ = seen := term :: !seen
            val {tree_work,...} = #type_info admission (Term.type_of term)
            val _ = SmtResource.check_dag_size_with_limit "BitVector"
              "word-graph-primitive-type-tree" limit tree_work
          in List.app visit (SmtResource.term_children term) end
    in visit root end

  fun admit_callback_dimensions (admission : type_admission) root =
    let
      val seen = ref ([] : term list)
      fun visit term =
        if List.exists (fn old => Portable.pointer_eq (old,term)) (!seen)
        then () else let
          val _ = seen := term :: !seen
          val (head,args) = boolSyntax.strip_comb term
          val selector = Term.is_const head andalso
            let val {Thy,Name,...} = Term.dest_thy_const head
            in Thy="pair" andalso (Name="FST" orelse Name="SND") end
          val full_word_operator = Term.is_const head andalso
            #Thy (Term.dest_thy_const head)="words" andalso
            length args=length (#1
              (boolSyntax.strip_fun (Term.type_of head)))
          val relation = boolSyntax.is_eq term andalso
            wordsSyntax.is_word_type (Term.type_of (boolSyntax.lhs term))
          val projection = wordsSyntax.is_index term andalso
            wordsSyntax.is_word_type
              (Term.type_of (#1 (wordsSyntax.dest_index term)))
          val _ = if full_word_operator orelse relation orelse projection then
            #check_primitive_type admission (Term.type_of head) else ()
        in
          (* Fixed field projections retain first refusal. Their schema
             keeps producer fields opaque and does not evaluate dimensions. *)
          if selector then ()
          else List.app visit (SmtResource.term_children term)
        end
    in visit root end

  fun checked_node_callback admission callback term =
    if Portable.pointer_eq (callback,unchanged_node) then callback term
    else (admit_callback_dimensions admission term; callback term)

  fun guarded_conversions {word_conversion,bit_conversion,node_conversion} =
    let
      (* Optional schema admission may fall back, but a primitive's first
         resource exception is terminal. Keep the exception itself intact
         for profiling/cleanup, and share this flag through binder discovery.
         Admission stays OUTSIDE the tracked raw callback. *)
      val callback_failed = ref false
      fun track conversion =
        if Portable.pointer_eq (conversion,unchanged_node) then conversion
        else fn term => conversion term
          handle exn as Feedback.HOL_ERR error =>
            (if SmtResource.is_resource_gate error then
               callback_failed := true else ();
             raise exn)
      val node_conversion = track node_conversion
    in
      {callback_failed=callback_failed,
       word_conversion=track word_conversion,
       bit_conversion=track bit_conversion,
       node_conversion=fn admission =>
         if Portable.pointer_eq (node_conversion,unchanged_node)
         then unchanged_node
         else checked_node_callback admission node_conversion}
    end

  (* Graph producers run this worker only on bounded operator templates:
     their INST residues are schema holes, never actual graph operands.
     The independent term-facing FP adapter below retains its old contract. *)
  fun normalize_template_stopping_using_in stop
      (context : context) reuse type_admission
      protect_callbacks
      {word_conversion, bit_conversion, node_conversion, callback_failed}
      root =
    let
      val _ = #refresh_caches context ()
      val signature_witness = SmtSkeletonProve.cache_signature ()
      (* After a callback changes signatures, discard local hints as well.
         Rebuild local DAG memoization rather than disabling it: even this
         fallback must not unfold shared graphs. Do not publish results from
         this invocation into the retained caches after such a change. *)
      val generation_witness = !(#cache_generation context)
      val local_signature = ref signature_witness
      val local_generation = ref generation_witness
      val reset_local = ref (fn () => ())
      fun reusable () =
        (#refresh_caches context ();
         if !local_generation = !(#cache_generation context) andalso
            SmtSkeletonProve.cache_signature_matches (!local_signature)
         then () else
           ((!reset_local) ();
            local_signature := SmtSkeletonProve.cache_signature ();
            local_generation := !(#cache_generation context));
         generation_witness = !(#cache_generation context) andalso
         SmtSkeletonProve.cache_signature_matches signature_witness)
      val input_nodes = SmtResource.dag_nodes_up_to maximum root
      val _ = SmtResource.check_dag_size_for
        "Skeleton" "word-graph-input" input_nodes
      val generated = ref 0
      val generated_edges = ref 0
      val operator_calls = ref 0
      val memo_hits = ref 0
      val normalized_nodes = ref 0
      val projection_states = ref 0
      val boolean_nodes = ref 0
      val bucket_count = 8191
      fun new_pointer_set () =
        Array.array (bucket_count, [] : term list)
      val pointer_hash = SmtResource.pointer_bucket bucket_count
      fun mark_pointer table term =
        let
          val index = pointer_hash term
          val bucket = Array.sub (table, index)
        in
          if List.exists (fn saved => Portable.pointer_eq (saved, term))
              bucket then false
          else
            (Array.update (table, index, term :: bucket); true)
        end
      fun pointer_lookup table term =
        pointer_peek (Array.sub (table, pointer_hash term)) term
      fun pointer_insert table term value =
        let val index = pointer_hash term in
          Array.update
            (table, index, (term, value) :: Array.sub (table, index))
        end
      val generated_seen = new_pointer_set ()
      val reserved = ref (HOLset.empty String.compare)
      fun mark_generated term = mark_pointer generated_seen term
      fun seed_source term =
        if mark_generated term then
          (if Term.is_var term then
             reserved := HOLset.add
               (!reserved, Lib.fst (Term.dest_var term))
           else ();
           List.app seed_source (SmtResource.term_children term))
        else ()
      fun count_nodes root =
        let
          val seen = new_pointer_set ()
          val count = ref 0
          fun visit term =
            if mark_pointer seen term then
              (count := !count + 1;
               List.app visit (SmtResource.term_children term))
            else ()
        in visit root; !count end
      (* Instantiating a small schema reconnects original operands.  Seed the
         generated-node set with the admitted source graph so those retained
         nodes are not charged again as allocations.  Reserve names from that
         same construction view.  This deliberately includes opened binder
         variables: schema freshness needs a conservative occupied-name set,
         not an independent free-variable oracle. Binder opening already has
         SmtResource's standing bounded-body contract. *)
      val _ = seed_source root
      val serial = ref 0

      fun fresh ty =
        let
          val name = "word_graph_operand_" ^ Int.toString (!serial)
          val _ = serial := !serial + 1
        in
          if HOLset.member (!reserved, name) then fresh ty
          else Term.mk_var (name, ty)
        end

      fun literal term =
        Term.is_const term orelse numSyntax.is_numeral term orelse
        wordsSyntax.is_word_literal term

      val node_conversion = node_conversion type_admission
      val type_info = #type_info type_admission
      val bounded_word_width = #bounded_word_width type_admission
      val check_primitive_type = #check_primitive_type type_admission
      val type_nodes = #type_nodes type_admission
      val type_tree_work = #type_tree_work type_admission

      fun is_word_projection term =
        wordsSyntax.is_index term andalso
        wordsSyntax.is_word_type
          (Term.type_of (Lib.fst (wordsSyntax.dest_index term)))

      datatype node_key =
          ConstantKey of int * int
        | ApplicationKey of int * int * int
        | AbstractionKey of int * int * int

      fun node_key_compare (left, right) =
        let
          fun fields (ConstantKey (constant, ty)) = [0, constant, ty]
            | fields (ApplicationKey (operator, operand, ty)) =
                [1, operator, operand, ty]
            | fields (AbstractionKey (variable, body, ty)) =
                [2, variable, body, ty]
        in int_list_compare (fields left, fields right) end

      val next_node_id = ref 0
      val node_pointer_cache = Array.array
        (bucket_count, [] : (term * int) list)
      val node_keys = ref (Redblackmap.mkDict node_key_compare)
      val node_representatives = ref (Redblackmap.mkDict Int.compare)
      val constant_identities = ref ([] : (term * int) list)
      val next_constant_id = ref 0

      fun new_node_id term =
        let val identity = !next_node_id
        in
          next_node_id := identity + 1;
          identity
        end

      fun constant_id term =
        case List.find (fn (saved, _) => Term.same_const term saved)
            (!constant_identities) of
          SOME (_, identity) => identity
        | NONE =>
            let val identity = !next_constant_id
            in
              next_constant_id := identity + 1;
              constant_identities := (term, identity) :: !constant_identities;
              identity
            end

      fun intern_node key term =
        case Redblackmap.peek (!node_keys, key) of
          SOME identity => identity
        | NONE =>
            let val identity = new_node_id term
            in
              node_keys := Redblackmap.insert (!node_keys, key, identity);
              identity
            end

      fun node_id term =
        case pointer_lookup node_pointer_cache term of
          SOME identity => identity
        | NONE =>
            let
              val tyid = #identity (type_info (Term.type_of term))
              val identity =
                if Term.is_var term then new_node_id term
                else if Term.is_const term then
                  intern_node (ConstantKey (constant_id term, tyid)) term
                else new_node_id term
              val _ = pointer_insert node_pointer_cache term identity
            in identity end

      fun canonicalize_key key theorem =
        let val right = boolSyntax.rhs (Thm.concl theorem)
        in
          case Redblackmap.peek (!node_keys, key) of
            NONE =>
              let val identity = new_node_id right
              in
                node_keys := Redblackmap.insert (!node_keys, key, identity);
                node_representatives := Redblackmap.insert
                  (!node_representatives, identity, right);
                (theorem, identity)
              end
          | SOME identity =>
              (case Redblackmap.peek (!node_representatives, identity) of
                 NONE => raise ERR "canonicalize_key"
                   "canonical node has no representative"
               | SOME representative =>
                   if Portable.pointer_eq (right, representative) then
                     (theorem, identity)
                   else
                     (SmtSkeletonProve.anchor_right representative theorem,
                      identity))
        end

      fun charge_generated term =
        if mark_generated term then
            let
              val children = SmtResource.term_children term
              val _ = generated := !generated + 1
              val _ = generated_edges := SmtResource.saturated_add
                (!generated_edges) (List.length children)
            in
              List.app charge_generated children
            end
        else ()

      fun full_words_operator term =
        if not (Term.is_comb term) then false
        else
          let
            val (head, arguments) = boolSyntax.strip_comb term
            val (argument_types, result_type) =
              boolSyntax.strip_fun (Term.type_of head)
          in
            Term.is_const head andalso
            #Thy (Term.dest_thy_const head) = "words" andalso
            List.length arguments = List.length argument_types andalso
            List.exists wordsSyntax.is_word_type
              (result_type :: argument_types)
          end

      fun full_projection_operator term =
        if not (Term.is_comb term) then false
        else
          let
            val (head, arguments) = boolSyntax.strip_comb term
            val (argument_types, result_type) =
              boolSyntax.strip_fun (Term.type_of head)
          in
            if not (Term.is_const head) then false
            else
              let val {Thy, Name, ...} = Term.dest_thy_const head
              in
                List.length arguments = List.length argument_types andalso
                wordsSyntax.is_word_type result_type andalso
                (Thy = "words" orelse Thy = "bitstring" orelse Thy = "fcp"
                 orelse Thy = "bool" andalso Name = "COND")
              end
          end

      fun word_relation term =
        wordsSyntax.is_word_lo term orelse
        (boolSyntax.is_eq term andalso
         wordsSyntax.is_word_type
           (Term.type_of (Lib.fst (boolSyntax.dest_eq term))))

      fun schematize head arguments rebuild =
        let
          val _ = check_primitive_type (Term.type_of head)
          (* Names need only be distinct within this schema and absent from
             the source.  Restarting gives identical operator/literal/alias
             shapes identical templates, independent of their operands. *)
          val _ = serial := 0
          val substitutions = ref ([] : (term * term) list)
          fun abstract argument =
            if literal argument then argument
            else
              case List.find
                  (fn (actual, _) => Portable.pointer_eq (argument, actual))
                  (!substitutions) of
                SOME (_, variable) => variable
              | NONE =>
                  let val variable = fresh (Term.type_of argument)
                  in
                    substitutions := (argument, variable) :: !substitutions;
                    variable
                  end
          val schematic = rebuild
            (Term.list_mk_comb (head, List.map abstract arguments))
          val _ = SmtResource.check_resource_goal
            "BitVector" "word-graph-schema" schematic
        in
          (schematic, !substitutions)
        end

      (* These tables contain checked operator schemas, not facts about the
         caller's values.  Word simplification and bit projection have separate
         normal forms.  Cache saturation affects reuse only, never admission. *)
      fun schema_conversion cache conversion schematic =
        let
          val cache_laws = reusable () andalso
            (reuse orelse #local_law_reuse context)
          val cached = if cache_laws then
              schema_lookup context cache schematic
            else NONE
          val theorem = case cached of SOME (theorem, _) =>
              (memo_hits := !memo_hits + 1; theorem)
            | NONE => Conv.QCONV conversion schematic
          val can_retain = reusable ()
          (* Validate EVERY callback result before INST, including disabled
             reuse and saturated caches. Hyp is also an INST input. *)
          val _ = if List.null (Thm.hyp theorem) then ()
            else raise ERR "schema_conversion" "operator schema has hypotheses"
          val _ = Library.check_oracle_tags "SmtWordGraph"
            "operator schema" theorem
          val theorem = SmtSkeletonProve.anchor_left schematic theorem
          val _ = if not can_retain orelse not cache_laws orelse
              Option.isSome cached orelse
              !(#schema_entries context) >= maximum orelse
              not (#cache_live_check context (Thm.concl theorem)) then ()
            else
              (cache := Redblackmap.insert (!cache, schematic, theorem);
               #schema_entries context := !(#schema_entries context) + 1)
        in theorem end

      fun instantiate_changed term schematic substitutions reduced =
        let
          val right = boolSyntax.rhs (Thm.concl reduced)
          val _ = SmtResource.check_resource_goal
            "BitVector" "word-graph-schema-output" right
        in
          if Term.aconv schematic right then (Thm.REFL term, false)
          else
            let
              val instantiated = Thm.INST
                (List.map (fn (actual, variable) =>
                  {redex = variable, residue = actual}) substitutions) reduced
              val result = SmtSkeletonProve.anchor_left term instantiated
              val _ = operator_calls := !operator_calls + 1
              val _ = charge_generated (boolSyntax.rhs (Thm.concl result))
            in (result, true) end
        end

      fun operator_conversion term =
        if not (full_words_operator term) then (Thm.REFL term, false)
        else
          let
            val (head, arguments) = boolSyntax.strip_comb term
            val (schematic, substitutions) = schematize head arguments I
            (* Word simplification alone can leave [word_bit n w] opaque
               when w is a variable.  Canonicalize its guarded projection
               as well, so it shares the same atom as an in-range FCP index.
               The guard is essential: an out-of-range word_bit is false,
               whereas a bare out-of-range FCP index is unspecified. *)
            val reduced =
              case Lib.total wordsSyntax.dest_word_bit schematic of
                SOME (index, word) =>
                  if numSyntax.is_numeral index then
                    (case bounded_word_width (Term.type_of word) of
                       Within width => simpLib.SIMP_CONV bossLib.std_ss
                         [wordsTheory.word_bit_def, fcpLib.DIMINDEX width]
                         schematic
                     | _ => schema_conversion (#word_schemas context)
                         word_conversion schematic)
                  else schema_conversion (#word_schemas context)
                    word_conversion schematic
              | NONE => schema_conversion (#word_schemas context)
                  word_conversion schematic
          in instantiate_changed term schematic substitutions reduced end
        handle Conv.UNCHANGED => (Thm.REFL term, false)

      val normalize_index = ref
        (SmtResource.new_bounded_term_index maximum)
      val normalize_cache = ref
        (Redblackmap.mkDict Int.compare :
          (int, thm * bool) Redblackmap.dict)
      val normalize_physical = Array.array
        (bucket_count, [] : (term * (thm * bool)) list)

      fun stopped term = case stop of
          NONE => false
        | SOME predicate => predicate term
      (* Lexical stops are occurrence-sensitive. Do not consult or populate
         structural memoization that could identify a stopped occurrence
         with an equal but non-stopped one. Physical memoization is local. *)
      fun normalization_id term =
        case stop of NONE => (!normalize_index) term | SOME _ => NONE

      fun cached_normalization term =
        let val _ = reusable () in
        case pointer_lookup normalize_physical term of
          SOME result => SOME result
        | NONE =>
            (case Option.mapPartial
                (fn id => Redblackmap.peek (!normalize_cache, id))
                (normalization_id term) of
               NONE => if reuse andalso reusable () then
                   context_lookup context (#normalized context) term
                 else NONE
             | SOME (theorem, changed) => SOME
                 (if changed then
                    (SmtSkeletonProve.anchor_left term theorem, true)
                  else (Thm.REFL term, false)))
        end

      fun external_conversion source =
        let
          val _ = if protect_callbacks andalso not
              (Portable.pointer_eq (node_conversion,unchanged_node)) then
              admit_callback_template type_admission source else ()
          val theorem = Conv.QCONV node_conversion source
            handle Conv.UNCHANGED => Thm.REFL source
          val _ = reusable ()
          val _ = if List.null (Thm.hyp theorem) then () else
            raise ERR "external_conversion" "operator schema has hypotheses"
          val _ = Library.check_oracle_tags "SmtWordGraph"
            "node schema" theorem
          val theorem = SmtSkeletonProve.anchor_left source theorem
          val right = boolSyntax.rhs (Thm.concl theorem)
        in (theorem, not (Term.aconv source right)) end

      fun normalize_source term =
        if stopped term then (Thm.REFL term, false)
        else case cached_normalization term of
          SOME result => (memo_hits := !memo_hits + 1; result)
        | NONE =>
            let
              val _ = normalized_nodes := !normalized_nodes + 1
              val (pre, pre_changed) = external_conversion term
              val result =
                if pre_changed then
                  let
                    (* A projection callback gets first refusal so it can
                       consume one field without normalizing the complete
                       tuple producer. *)
                    val right = boolSyntax.rhs (Thm.concl pre)
                    val (tail, _) = normalize_source right
                  in (Thm.TRANS pre tail, true) end
                else
                  let
                    val (children, children_changed) =
                      if Term.is_comb term andalso not (literal term) then
                        let
                          val (operator, operand) = Term.dest_comb term
                          val (operator_theorem, operator_changed) =
                            normalize_source operator
                          val (operand_theorem, operand_changed) =
                            normalize_source operand
                        in
                          if operator_changed orelse operand_changed then
                            (SmtSkeletonProve.anchor_left term
                               (Thm.MK_COMB
                                 (operator_theorem, operand_theorem)), true)
                          else (Thm.REFL term, false)
                        end
                      else if Term.is_abs term then
                        let
                          val (binder, body) = Term.dest_abs term
                          val (body_theorem, body_changed) =
                            normalize_source body
                        in
                          if body_changed then
                            let
                              val _ = SmtResource.check_resource_goal
                                "BitVector" "word-graph-binder-body" body
                              val _ = SmtResource.check_resource_goal
                                "BitVector" "word-graph-binder-result"
                                (boolSyntax.rhs (Thm.concl body_theorem))
                            in
                              (SmtSkeletonProve.anchor_left term
                                 (Thm.ABS binder body_theorem), true)
                            end
                          else (Thm.REFL term, false)
                        end
                      else (Thm.REFL term, false)
                    val residue = boolSyntax.rhs (Thm.concl children)
                    val (external, external_changed) =
                      external_conversion residue
                    val external_right =
                      boolSyntax.rhs (Thm.concl external)
                    val (local_theorem, local_changed) =
                      if external_changed then
                        (Thm.REFL external_right, false)
                      else operator_conversion residue
                    val first = if external_changed then external
                      else local_theorem
                    val first_changed = external_changed orelse local_changed
                    val (tail, tail_changed) =
                      if external_changed then normalize_source external_right
                      else
                        (Thm.REFL (boolSyntax.rhs (Thm.concl first)), false)
                  in
                    if first_changed orelse tail_changed then
                      (Thm.TRANS children (Thm.TRANS first tail), true)
                    else (children, children_changed)
                  end
              val _ = reusable ()
              val _ = case normalization_id term of NONE => ()
                | SOME id => normalize_cache :=
                    Redblackmap.insert (!normalize_cache, id, result)
              val _ = pointer_insert normalize_physical term result
              val _ = if reuse andalso reusable () then
                  context_save context (#normalized context) term result
                else ()
            in result end

      fun projection_closed schematic theorem =
        let
          val _ = SmtResource.check_resource_goal "BitVector"
            "word-graph-schema-output"
            (boolSyntax.rhs (Thm.concl theorem))
          val allowed = Term.free_vars schematic
          val seen = ref ([] : (term * unit) list)
          fun visit term =
            case pointer_peek (!seen) term of
              SOME () => true
            | NONE =>
                let
                  val _ = seen := (term, ()) :: !seen
                  val locally_closed =
                    if word_relation term then false
                    else if is_word_projection term then
                      let val word = Lib.fst (wordsSyntax.dest_index term)
                      in
                        if Term.is_var word andalso
                           List.exists (fn variable =>
                             Term.aconv variable word) allowed orelse
                          wordsSyntax.is_word_literal word then true
                        else false
                      end
                    else true
                in
                  locally_closed andalso
                  List.all visit (SmtResource.term_children term)
                end
        in visit (boolSyntax.rhs (Thm.concl theorem)) end

      fun relation_conversion term =
        if not (word_relation term) then (Thm.REFL term, false)
        else
          let
            val (head, arguments) = boolSyntax.strip_comb term
            val (schematic, substitutions) = schematize head arguments I
            val reduced = schema_conversion (#bit_schemas context)
              bit_conversion schematic
            val changed = not (Term.aconv schematic
              (boolSyntax.rhs (Thm.concl reduced)))
          in
            if not changed then (Thm.REFL term, false)
            else
              if projection_closed schematic reduced then
                instantiate_changed term schematic substitutions reduced
              else (Thm.REFL term, false)
          end
        handle Conv.UNCHANGED => (Thm.REFL term, false)

      fun projection_conversion term =
        let
          val (word, index) = wordsSyntax.dest_index term
          val numeric_index = numSyntax.dest_numeral index
        in
          case bounded_word_width (Term.type_of word) of
            UnknownDimension => (Thm.REFL term, false)
          | TooLarge =>
              (SmtResource.check_dag_size_with_limit
                 "Skeleton" "word-graph-width" maximum (maximum + 1);
               (Thm.REFL term, false))
          | Within width =>
              if not (Arbnum.< (numeric_index, width)) then
                (Thm.REFL term, false)
              else
                let val (head, arguments) = boolSyntax.strip_comb word
                in
                  if not (full_projection_operator word) then
                    (Thm.REFL term, false)
                  else
                    let
                      val (schematic, substitutions) = schematize
                        head arguments
                        (fn schematic_word =>
                          wordsSyntax.mk_index (schematic_word, index))
                      val reduced =
                        schema_conversion (#bit_schemas context)
                          bit_conversion schematic
                      val changed = not (Term.aconv schematic
                        (boolSyntax.rhs (Thm.concl reduced)))
                    in
                      if not changed then (Thm.REFL term, false)
                      else
                        if projection_closed schematic reduced then
                          instantiate_changed term schematic substitutions
                            reduced
                        else (Thm.REFL term, false)
                    end
                end
        end
        handle Conv.UNCHANGED => (Thm.REFL term, false)

      val expand_cache = Array.array
        (bucket_count, [] : (term * (thm * bool * int)) list)
      val bit_cache = ref
        (Redblackmap.mkDict (pair_compare (Int.compare, Arbnum.compare)))

      fun expand_uncached term =
        let
          val _ = reusable ()
          fun ordinary () =
            case pointer_lookup expand_cache term of
              SOME result => (memo_hits := !memo_hits + 1; result)
            | NONE =>
                let
                  val _ = boolean_nodes := !boolean_nodes + 1
                  val (initial, initial_changed) =
                    if is_word_projection term andalso
                            numSyntax.is_numeral
                              (Lib.snd (wordsSyntax.dest_index term)) then
                      (projection_states := !projection_states + 1;
                       projection_conversion term)
                    else relation_conversion term
                  val initial_right = boolSyntax.rhs (Thm.concl initial)
                  val (result, changed, identity) =
                    if initial_changed then
                      let
                        val (right_theorem, _, right_id) = expand initial_right
                        val combined = Thm.TRANS initial right_theorem
                      in (combined, true, right_id) end
                    else if Term.is_comb term andalso not (literal term) then
                      let
                        val (operator, operand) = Term.dest_comb term
                        val (operator_theorem, operator_changed, operator_id) =
                          expand operator
                        val (operand_theorem, operand_changed, operand_id) =
                          expand operand
                      in
                        if operator_changed orelse operand_changed then
                          let
                            val rebuilt = SmtSkeletonProve.anchor_left term
                              (Thm.MK_COMB
                                (operator_theorem, operand_theorem))
                            val tyid = #identity
                              (type_info (Term.type_of term))
                            val (canonical, identity) = canonicalize_key
                              (ApplicationKey
                                (operator_id, operand_id, tyid)) rebuilt
                          in (canonical, true, identity) end
                        else (Thm.REFL term, false, node_id term)
                      end
                    else if Term.is_abs term then
                      let
                        val (binder, body) = Term.dest_abs term
                        val (body_theorem, body_changed, body_id) = expand body
                      in
                        if body_changed then
                          let
                            val _ = SmtResource.check_resource_goal "BitVector"
                              "word-graph-binder-body" body
                            val _ = SmtResource.check_resource_goal "BitVector"
                              "word-graph-binder-result"
                              (boolSyntax.rhs (Thm.concl body_theorem))
                            val rebuilt = SmtSkeletonProve.anchor_left term
                              (Thm.ABS binder body_theorem)
                            val tyid = #identity
                              (type_info (Term.type_of term))
                            val (canonical, identity) = canonicalize_key
                              (AbstractionKey
                                (node_id binder, body_id, tyid)) rebuilt
                          in (canonical, true, identity) end
                        else (Thm.REFL term, false, node_id term)
                      end
                    else (Thm.REFL term, false, node_id term)
                  val _ = pointer_insert expand_cache term
                    (result, changed, identity)
                in (result, changed, identity) end
        in
          if is_word_projection term andalso
             numSyntax.is_numeral (Lib.snd (wordsSyntax.dest_index term)) then
            let
              val (word, index) = wordsSyntax.dest_index term
              val word_id = node_id word
              val numeric_index = numSyntax.dest_numeral index
            in
              case Redblackmap.peek (!bit_cache, (word_id, numeric_index)) of
                SOME (theorem, changed, identity) =>
                  (memo_hits := !memo_hits + 1;
                   (SmtSkeletonProve.anchor_left term theorem,
                    changed, identity))
              | NONE =>
                  let
                    val result as (theorem, changed, identity) = ordinary ()
                    val _ = bit_cache := Redblackmap.insert
                      (!bit_cache, (word_id, numeric_index), result)
                  in result end
            end
          else ordinary ()
        end

      and expand term =
        if stopped term then (Thm.REFL term, false, node_id term)
        else let val _ = reusable () in
        case pointer_lookup expand_cache term of
          SOME result => (memo_hits := !memo_hits + 1; result)
        | NONE =>
            (case (if reuse andalso reusable () then
                     context_lookup context (#expanded context) term
                   else NONE) of
               SOME (theorem, changed) =>
                 let val result = (theorem, changed,
                   node_id (boolSyntax.rhs (Thm.concl theorem)))
                 in memo_hits := !memo_hits + 1;
                    pointer_insert expand_cache term result; result end
             | NONE =>
                 let
                   val result as (theorem, changed, _) = expand_uncached term
                   val _ = if reuse andalso reusable () then
                       context_save context (#expanded context) term
                         (theorem, changed)
                     else ()
                 in result end)
        end

      val _ = reset_local := (fn () =>
        (normalize_index := SmtResource.new_bounded_term_index maximum;
         normalize_cache := Redblackmap.mkDict Int.compare;
         List.app (fn index =>
           (Array.update (normalize_physical, index, []);
            Array.update (expand_cache, index, [])))
           (List.tabulate (bucket_count, fn index => index));
         bit_cache := Redblackmap.mkDict
           (pair_compare (Int.compare, Arbnum.compare))))

      val (normalized, normalization_changed) =
        SmtResource.profile_phase "word-graph-normalize"
          normalize_source root
      val normalized_right = boolSyntax.rhs (Thm.concl normalized)
      val normalized_dag_nodes = SmtResource.profile_phase
        "word-graph-normalized-dag-count"
        count_nodes normalized_right
      val (expanded, expansion_changed, _) =
        SmtResource.profile_phase "word-graph-expand" expand normalized_right
      val theorem = SmtSkeletonProve.anchor_left root
        (Thm.TRANS normalized expanded)
      val changed = normalization_changed orelse expansion_changed
      val final_dag_nodes = SmtResource.profile_phase
        "word-graph-final-dag-count" count_nodes
        (boolSyntax.rhs (Thm.concl theorem))
      val _ = if changed then () else raise Conv.UNCHANGED
      val _ =
        if Portable.pointer_eq
             (Lib.fst (boolSyntax.dest_eq (Thm.concl theorem)), root) then ()
        else raise ERR "normalize" "normalization lost its exact left endpoint"
      val _ =
        if List.null (Thm.hyp theorem) then ()
        else raise ERR "normalize" "normalization introduced hypotheses"
      val _ = Library.check_oracle_tags
        "SmtWordGraph" "normalize" theorem
    in
      (theorem,
       {input_nodes = input_nodes,
        visited_nodes = !normalized_nodes + !boolean_nodes,
        generated_nodes = !generated,
        generated_edges = !generated_edges,
        normalized_nodes = !normalized_nodes,
        normalized_dag_nodes = normalized_dag_nodes,
        projection_states = !projection_states,
        boolean_nodes = !boolean_nodes,
        final_dag_nodes = final_dag_nodes,
        type_nodes = !type_nodes,
        type_tree_work = !type_tree_work,
        operator_calls = !operator_calls,
        memo_hits = !memo_hits})
    end

  (* Existing consumers have no lexical stops and retain their cache and
     callback policy verbatim. *)
  val normalize_template_using_in = normalize_template_stopping_using_in NONE

  structure G = SmtReplayGraph
  structure C = SmtReplayCanonGraph
  structure P = SmtReplayProof

  (* A completed word schema keeps uninterpreted operands opaque, even
     when one occurrence is nearer its root than another. In particular
     never expose an arbitrary UF spine merely to prove x + 0 = x. *)
  fun typed_frontier graph hole depth node =
    let
      val term = G.representative graph node
      fun spine node args = case G.view graph node of
          G.Application (f,x) => spine f (x::args)
        | _ => (node,args)
    in
      if Term.is_const term orelse numSyntax.is_numeral term orelse
          wordsSyntax.is_word_literal term then term
      else if depth < 0 then hole node
      else case G.view graph node of G.Application _ =>
        let
          val (head,args) = spine node []
          val operator = G.representative graph head
          val known = Term.is_const operator andalso
            List.exists (fn thy => #Thy (Term.dest_thy_const operator)=thy)
              ["words","bool","min","fcp","bitstring","pair",
               "arithmetic","num"]
        in if known then Term.list_mk_comb
          (operator,List.map (typed_frontier graph hole (depth-1)) args)
          else hole node end
      | _ => hole node
    end

  (* Keep the existing operator prover/cache, but run it on typed named
     frontiers. Successful proofs become graph recipes, not instantiated
     facts about actual operands. Revisit discovers generated projections
     and their successful dependencies BEFORE the one final freeze. *)
  fun discover_using_in canonical_frontiers (context : context) reuse
      admission conversions record graph scope source =
    let
      val _ = #refresh_caches context ()
      val limit = SmtResource.max_bv_replay_term_nodes
      val retain_scalars = Option.isSome record
      val cache_frontiers = canonical_frontiers orelse retain_scalars
      fun save item = case record of NONE => () | SOME record => record item
      val calls = ref 0 and hits = ref 0 and visits = ref 0
      val projections = ref 0
      (* Built-in graph adapters reuse checked frontier programs across
         calls in this context. Retained/custom adapters keep local tables.
         Persistent programs share the original schema entry allowance.
         Custom graph callbacks keep their occurrence-sensitive fresh holes.
         Canonical holes below preserve operand alias shape and all literal
         data. Signature changes discard both positive and declined hints. *)
      val frontier_programs = if canonical_frontiers then
          #frontier_programs context
        else ref (Redblackmap.mkDict Term.compare)
      val frontier_callbacks = ref (Redblackmap.mkDict Term.compare)
      val frontier_entries = if canonical_frontiers then
          #schema_entries context else ref 0
      val frontier_generation = ref (!(#cache_generation context))
      val frontier_signature = ref (SmtSkeletonProve.cache_signature ())
      fun refresh_frontiers () =
        (#refresh_caches context ();
         if !frontier_generation = !(#cache_generation context) andalso
             SmtSkeletonProve.cache_signature_matches (!frontier_signature)
         then () else
           (frontier_programs := Redblackmap.mkDict Term.compare;
            frontier_callbacks := Redblackmap.mkDict Term.compare;
            if canonical_frontiers then () else frontier_entries := 0;
            frontier_generation := !(#cache_generation context);
            frontier_signature := SmtSkeletonProve.cache_signature ()))
      (* Dictionary keys are optional small data. Do not compare a large
         Type before the ordinary producer's own admission boundary. *)
      fun cacheable_frontier template =
        let fun small_type ty =
              let val remaining = ref 64
                  fun visit ty = if !remaining=0 then false else
                    (remaining := !remaining-1;
                     Type.is_vartype ty orelse
                       List.all visit (#Args (Type.dest_thy_type ty)))
              in visit ty end
            fun small_term term = small_type (Term.type_of term) andalso
              not (Term.is_abs term) andalso
              List.all small_term (SmtResource.term_children term)
        in Option.isSome (SmtReplayImport.bounded_raw_size maximum template)
          andalso small_term template end
      fun frontier_cached on_hit admissible table conversion template =
        if not cache_frontiers orelse
            (canonical_frontiers andalso not (cacheable_frontier template))
          then conversion template else
        let
          val _ = refresh_frontiers ()
          fun result NONE = raise Conv.UNCHANGED
            | result (SOME value) = value
        in case Redblackmap.peek (!table,template) of
            SOME saved => (hits := !hits+1;
              (case saved of NONE => () | SOME value => on_hit value);
              result saved)
          | NONE =>
              let
                val generation = !(#cache_generation context)
                val signature_witness = SmtSkeletonProve.cache_signature ()
                val saved = SOME (conversion template)
                  handle Conv.UNCHANGED => NONE
                val _ = refresh_frontiers ()
                val _ = if generation = !(#cache_generation context) andalso
                    SmtSkeletonProve.cache_signature_matches
                      signature_witness andalso
                    !frontier_entries < maximum andalso
                    (not canonical_frontiers orelse
                     (case saved of NONE => true
                      | SOME value => admissible value)) then
                    (table := Redblackmap.insert (!table,template,saved);
                     frontier_entries := !frontier_entries+1)
                  else ()
              in result saved end
        end
      fun frontier_hole holes node =
        if not cache_frontiers then Term.genvar (G.type_of graph node)
        else Term.mk_var
          ("word_graph_frontier_" ^
             Int.toString (Redblackmap.numItems (!holes)),
           G.type_of graph node)
      val source_nodes = G.reachable graph [source]
      val node_callback = #node_conversion conversions admission
      val original = Redblackset.addList (Redblackset.empty Int.compare,
        List.map G.node_id source_nodes)
      fun observe () = visits := !visits + 1
      fun spine node args = case G.view graph node of
          G.Application (operator,argument) => spine operator (argument::args)
        | _ => (node,args)
      fun is_literal node =
        let val term = G.representative graph node
        in Term.is_const term orelse numSyntax.is_numeral term orelse
          wordsSyntax.is_word_literal term orelse
          (* The retained adapter must not replace a closed DIMINDEX count
             by a free schema hole. Keep only prospectively bounded scalar
             data; the existing callback Type admission precedes native FV. *)
          retain_scalars andalso Term.type_of term = numSyntax.num andalso
          Option.isSome (SmtReplayImport.bounded_raw_size 32 term) andalso
          (admit_callback_template admission term;
           List.null (Term.free_vars term)) end
      fun propose node =
        let
          val holes = ref (Redblackmap.mkDict Int.compare)
          fun hole node =
            case Redblackmap.peek (!holes,G.node_id node) of
              SOME (_,term) => term
            | NONE =>
                let val term = frontier_hole holes node
                in holes := Redblackmap.insert
                  (!holes,G.node_id node,(node,term)); term end
          (* Whole operator spines and literals are small. One further
             operator layer exposes a word beneath FCP/word_bit and the
             tuple selectors used by replay's projection callbacks. Equal
             operands retain one typed hole, irrespective of occurrence. *)
          fun frontier depth node =
            if is_literal node then G.representative graph node
            else if depth < 0 then hole node
            else case G.view graph node of
                G.Application _ =>
                  let val (head,args) = spine node []
                      val operator = case G.view graph head of
                          G.Constant _ => G.representative graph head
                        | _ => hole head
                  in Term.list_mk_comb
                    (operator,List.map (frontier (depth-1)) args) end
              | _ => hole node
          val shallow = frontier 0 node
          val projection = wordsSyntax.is_index shallow
          val template = if projection then frontier 1 node else shallow
          val {word_conversion,bit_conversion,node_conversion,
               callback_failed} = conversions
          (* The word child was normalized by graph postorder already.
             Projection discovery must not repeat that primitive call. *)
          val local_conversions =
            {callback_failed=callback_failed,
             word_conversion=if projection then
               (fn _ => raise Conv.UNCHANGED) else word_conversion,
             bit_conversion=bit_conversion,node_conversion=node_conversion}
          val _ = if retain_scalars then
              admit_callback_template admission template else ()
          (* A persistent program replays its Type requests into this
             call's cumulative admission, including unchanged programs. *)
          fun replay (_,requests) = List.app
            (fn (kind,ty) =>
              let
                fun request code = case code of
                    0 => ignore (#type_info admission ty)
                  | 1 => #check_primitive_type admission ty
                  | _ => ignore (#bounded_word_width admission ty)
              in
                if kind<3 then request kind
                else (request (kind-3) handle Conv.UNCHANGED => ())
              end) requests
          fun make template =
            let
              val requests = ref []
              fun record kind action ty =
                let
                  val outcome = Exn.capture action ty
                  (* Primitive admission may decline inside a successful
                     normalization. Repeat that request and its local catch. *)
                  val code = case outcome of
                      Exn.Exn Conv.UNCHANGED => kind+3 | _ => kind
                  val _ = if List.exists (fn (old,prior) => old=code andalso
                      Portable.pointer_eq (prior,ty)) (!requests) then ()
                    else requests := (code,ty) :: !requests
                in Exn.release outcome end
              val tracked =
                {type_info=record 0 (#type_info admission),
                 check_primitive_type=record 1
                   (#check_primitive_type admission),
                 bounded_word_width=record 2
                   (#bounded_word_width admission),
                 type_nodes= #type_nodes admission,
                 type_tree_work= #type_tree_work admission}
              val result = SOME (normalize_template_using_in context reuse
                (if canonical_frontiers then tracked else admission) true
                local_conversions template)
                handle Conv.UNCHANGED => NONE
            in (result,List.rev (!requests)) end
          fun bounded (result,requests) =
            length requests <= maximum andalso
            List.all (fn (_,ty) => cacheable_frontier
              (Term.mk_var ("word_graph_admitted_type",ty))) requests andalso
            (case result of NONE => true | SOME (theorem,_) =>
              cacheable_frontier (Thm.concl theorem))
          val outcome = Exn.capture (fn () =>
            case frontier_cached replay bounded frontier_programs make
                template of
              (NONE,_) => raise Conv.UNCHANGED
            | (SOME result,_) => result) ()
        in case outcome of
            Exn.Exn Conv.UNCHANGED => NONE
          | Exn.Exn exn => raise exn
          | Exn.Res (theorem,metrics) =>
              let
                val _ = calls := !calls + #operator_calls metrics
                val _ = hits := !hits + #memo_hits metrics
                val _ = projections :=
                  !projections + #projection_states metrics
                val pairs = List.map #2 (Redblackmap.listItems (!holes))
                val schema = C.checked_graph_schema graph scope
                  {theorem=theorem,holes=List.map #2 pairs,
                   operands=List.map #1 pairs,template_limit=limit}
                val _ = if C.graph_schema_source schema = node then () else
                  raise ERR "discover" "wrong operator schema endpoint"
                val _ = save (false,node,C.graph_schema_result schema,
                  fn () => case C.realize_typed_root_schema graph scope
                      limit (C.graph_schema_leaf graph scope
                        {schema=schema,observe=fn () => ()}) of
                    SOME proof => proof
                  | NONE => raise ERR "realize_local" "local Type frontier")
              in SOME schema end
        end
      fun pre_propose node =
        if Portable.pointer_eq (node_callback,unchanged_node)
        then NONE else let
          val holes = ref (Redblackmap.mkDict Int.compare)
          fun hole node = case Redblackmap.peek (!holes,G.node_id node) of
              SOME (_,term) => term
            | NONE =>
                let val term = frontier_hole holes node
                in holes := Redblackmap.insert
                  (!holes,G.node_id node,(node,term)); term end
          fun prefix depth node =
            if is_literal node then G.representative graph node
            else if depth < 0 then hole node
            else case G.view graph node of G.Application _ =>
              let
                val (head,args) = spine node []
                val operator = case G.view graph head of
                    G.Constant _ => G.representative graph head
                  | _ => hole head
                val selector = if Term.is_const operator then
                    let val {Thy,Name,...} = Term.dest_thy_const operator
                    in Thy="pair" andalso (Name="FST" orelse Name="SND") end
                  else false
                val tuple = Term.is_const operator andalso
                  let val {Thy,Name,...} = Term.dest_thy_const operator
                  in Thy="pair" andalso Name="," end
                val next = if selector then Int.max (1,depth-1)
                  else if tuple then ~1 else depth-1
              in Term.list_mk_comb (operator,List.map (prefix next) args) end
              | _ => hole node
          val shallow = prefix 0 node
          val template = if wordsSyntax.is_index shallow then prefix 1 node
            else shallow
          val _ = admit_callback_template admission template
          val theorem = frontier_cached (fn _ => ())
            (cacheable_frontier o Thm.concl) frontier_callbacks
            node_callback template
          val pairs = List.map #2 (Redblackmap.listItems (!holes))
          val schema = C.checked_graph_schema graph scope
            {theorem=theorem,holes=List.map #2 pairs,
             operands=List.map #1 pairs,template_limit=limit}
          val _ = if C.graph_schema_source schema=node then () else
            raise ERR "discover" "wrong projection schema endpoint"
        in if C.graph_schema_source schema=C.graph_schema_result schema then
            NONE else
              (save (true,node,C.graph_schema_result schema,
                 fn () => case C.realize_typed_root_schema graph scope
                     limit (C.graph_schema_leaf graph scope
                       {schema=schema,observe=fn () => ()}) of
                   SOME proof => proof
                 | NONE => raise ERR "realize_local" "local Type frontier");
               SOME schema) end
        handle Conv.UNCHANGED => NONE

      (* Binders are completed bounded local proofs, never schema templates.
         Close their local word normalization before the native ABS; both
         fully realized operands are admitted at the old binder boundary. *)
      fun local_conversion node =
        case G.view graph node of G.OpaqueRetained =>
          let val term = G.representative graph node
          in if not (Term.is_abs term) then NONE else
            let
              val _ = SmtResource.term_children term
              val (binder,body) = Term.dest_abs term
              val (proof,_) = normalize_using_in context reuse admission
                conversions body
              val _ = SmtResource.check_resource_goal
                "BitVector" "word-graph-binder-body" body
              val _ = SmtResource.check_resource_goal "BitVector"
                "word-graph-binder-result" (boolSyntax.rhs (Thm.concl proof))
              val theorem = SmtSkeletonProve.nodewise_exact_left term
                (Thm.ABS binder proof)
              val target = boolSyntax.rhs (Thm.concl theorem)
              val target_node = #node (G.import graph scope limit target)
              val theorem = SmtSkeletonProve.exact_equality term
                (G.representative graph target_node) theorem
              val source_view = G.record_opened_view graph scope limit node
              val target_view =
                G.record_opened_view graph scope limit target_node
              val converted = P.record_typed_conversion graph scope
                {source=node,source_view=source_view,target=target_node,
                 target_view=target_view,theorem=theorem,template_limit=limit,
                 check_type=fn _ => ()}
              val _ = save (false,node,target_node,fn () => theorem)
            in SOME converted end
            handle Conv.UNCHANGED => NONE
          end
        | _ => NONE
      val plan = C.graph_conversion_with_schema_leaves graph scope
        {revisit=true,template_limit=limit,propose=propose,
         pre_propose=pre_propose,
         local_conversion=local_conversion,observe=observe} source
      val roots = C.graph_roots plan
      val generated = List.filter (fn node => not
        (Redblackset.member (original,G.node_id node)))
        (G.reachable graph roots)
      val edges = List.foldl (fn (node,total) =>
        case G.view graph node of G.Application _ => total+2 | _ => total)
        0 generated
      val final_nodes = G.dag_nodes graph [C.graph_result plan]
      val _ = #refresh_caches context ()
    in (plan,
      {input_nodes=length source_nodes,visited_nodes= !visits,
       generated_nodes=length generated,generated_edges=edges,
       normalized_nodes= !visits,normalized_dag_nodes=final_nodes,
       projection_states= !projections,boolean_nodes=final_nodes,
       final_dag_nodes=final_nodes,type_nodes= !(#type_nodes admission),
       type_tree_work= !(#type_tree_work admission),
       operator_calls= !calls,memo_hits= !hits} : metrics) end

  and normalize_using_in context reuse admission conversions root =
    let
      val input_nodes = SmtResource.dag_nodes_up_to maximum root
      val _ = SmtResource.check_dag_size_for
        "Skeleton" "word-graph-input" input_nodes
      val graph = G.new ()
      val scope = G.root_scope graph
      val source = G.import graph scope maximum root
      fun completed_frontier () =
        let
          val holes = ref (Redblackmap.mkDict Int.compare)
          fun hole node = case Redblackmap.peek (!holes,G.node_id node) of
              SOME (_,term) => term
            | NONE =>
                let val term = Term.genvar (G.type_of graph node)
                in holes := Redblackmap.insert
                  (!holes,G.node_id node,(node,term)); term end
          val template = typed_frontier graph hole 1 (#node source)
          val pairs = List.map #2 (Redblackmap.listItems (!holes))
          fun atom (node,_) = case G.view graph node of
              G.Variable _ => true | G.Constant _ => true | _ => false
        in if not (List.all atom pairs) orelse not (Option.isSome
            (SmtReplayImport.bounded_raw_size
              SmtResource.max_bv_replay_term_nodes template)) then NONE else
          let
            (* Optional completed schemas cannot spend the mandatory
               discovery's Type budget before first-refusal pruning. *)
            val (theorem,metrics) = normalize_template_using_in context reuse
              (new_type_admission ()) true conversions template
            val schema = C.checked_graph_schema graph scope
              {theorem=theorem,holes=List.map #2 pairs,
               operands=List.map #1 pairs,
               template_limit=SmtResource.max_bv_replay_term_nodes}
            val _ = if C.graph_schema_source schema= #node source then () else
              raise ERR "normalize" "wrong completed word schema endpoint"
          in SOME (C.graph_schema_leaf graph scope
            {schema=schema,observe=fn () => ()},metrics) end
        end
      val ready = completed_frontier ()
        handle Feedback.HOL_ERR error =>
          if SmtResource.is_resource_gate error andalso
             not (!(#callback_failed conversions)) then NONE
          else raise Feedback.HOL_ERR error
      val (plan,metrics) = case ready of SOME ready => ready
        | NONE => discover_using_in false context reuse admission conversions
            NONE graph scope (#node source)
      val _ = if C.graph_source plan <> C.graph_result plan then ()
        else raise Conv.UNCHANGED
      val theorem = case C.realize_typed_root_schema graph scope
          SmtResource.max_bv_replay_term_nodes plan of SOME theorem => theorem
        | NONE =>
            let val block = P.prepare_needed_sources_with_conversions graph
              {scope=scope,roots=C.graph_roots plan,sources=[],closed_facts=[],
               conversions=C.graph_conversions plan,
               template_limit=SmtResource.max_bv_replay_term_nodes}
            in P.realize block (C.graph_equality plan)
              (C.graph_assemble_named graph block plan) end
      (* Retain exact unchanged source occurrences in the public normal
         form. This is a memoized syntax view, not an equality certificate;
         the checked nodewise anchor below still proves every incidence. *)
      val occurrences = ref (Redblackmap.mkDict Int.compare)
      fun occurrence node =
        case Redblackmap.peek (!occurrences,G.node_id node) of
          SOME term => term
        | NONE =>
            let val term = case G.source_anchor graph node of
                    SOME {original,...} => original
                  | NONE => (case G.view graph node of
                      G.Application (left,right) =>
                        Term.mk_comb (occurrence left,occurrence right)
                    | _ => G.representative graph node)
                val _ = occurrences := Redblackmap.insert
                  (!occurrences,G.node_id node,term)
            in term end
      val theorem = SmtSkeletonProve.exact_equality root
        (occurrence (C.graph_result plan)) theorem
      val _ = if null (Thm.hyp theorem) then () else
        raise ERR "normalize" "normalization introduced hypotheses"
      val _ = Library.check_oracle_tags "SmtWordGraph" "normalize" theorem
    in (theorem,metrics) end

  fun normalize_using_with_metrics conversions root =
    let val admission = new_type_admission ()
    in normalize_using_in (new_context ()) false admission
      (guarded_conversions conversions) root end

  (* Arithmetic normalization turns complement into a negation and adder.
     Keep its one-bit law available until projection expansion instead. *)
  fun builtin_word_conversion term =
    case Lib.total wordsSyntax.dest_word_1comp term of
      SOME word =>
        if wordsSyntax.is_word_literal word then
          Library.replay_word_simp_conv term
        else raise Conv.UNCHANGED
    | NONE => Library.replay_word_simp_conv term

  val projection_simp = simpLib.SIMP_CONV
    (simpLib.++ (simpLib.++ (simpLib.++ (boolSimps.bool_ss, fcpLib.FCP_ss),
      wordsLib.SIZES_ss), numSimps.REDUCE_ss))
    [combinTheory.o_THM, wordsTheory.word_and_def, wordsTheory.word_or_def,
     Rewrite.REWRITE_RULE [blastTheory.xor_thm] wordsTheory.word_xor_def,
     wordsTheory.word_1comp_def, wordsTheory.word_lsl_def,
     wordsTheory.word_lsr_def, wordsTheory.word_extract_def,
     wordsTheory.word_bits_def, wordsTheory.w2w,
     wordsTheory.word_concat_def, wordsTheory.word_join_index]

  fun literal_bit_conversion term =
    case Lib.total wordsSyntax.dest_index term of
      SOME (word, _) =>
        if wordsSyntax.is_word_literal word then wordsLib.WORD_EVAL_CONV term
        else raise Conv.UNCHANGED
    | NONE => raise Conv.UNCHANGED

  (* Project these operators before expanding a whole word into bits. *)
  fun builtin_bit_conversion term =
    let
      val direct =
        case Lib.total wordsSyntax.dest_index term of
          NONE => false
        | SOME (word, _) =>
            let val (head, arguments) = boolSyntax.strip_comb word in
              case Lib.total Term.dest_thy_const head of
                SOME {Thy="words", Name, ...} =>
                  List.exists (fn name => name = Name)
                    ["word_and", "word_or", "word_xor", "word_1comp",
                     "word_concat", "word_join", "w2w"]
                  orelse
                  (List.exists (fn name => name = Name)
                     ["word_lsl", "word_lsr"] andalso
                   case arguments of [_, amount] => numSyntax.is_numeral amount
                     | _ => false)
                  orelse
                  (List.exists (fn name => name = Name)
                     ["word_extract", "word_bits"] andalso
                   case arguments of [high, low, _] =>
                     numSyntax.is_numeral high andalso numSyntax.is_numeral low
                   | _ => false)
              | _ => false
            end
    in
      if direct then
        Conv.ORELSEC
          (Conv.THENC (projection_simp,
            Conv.THENC (Conv.DEPTH_CONV literal_bit_conversion,
              Rewrite.REWRITE_CONV [])), blastLib.BIT_BLAST_CONV) term
      else blastLib.BIT_BLAST_CONV term
    end

  (* Built-in operator laws are pure and reusable within this producer.
     Custom conversion probes above retain their uncached contract. *)
  fun normalize_with_metrics root =
    normalize_using_in (new_context_with_local_laws true) false
      (new_type_admission ())
      (guarded_conversions
        {word_conversion = builtin_word_conversion,
         bit_conversion = builtin_bit_conversion,
         node_conversion = unchanged_node}) root

  (* Independent term-facing FP field/LET/beta compatibility adapter.
     Preserve its existing local-binder and projection-first contract;
     graph word consumers retain the discovery recipe instead. *)
  fun normalize_with_node_conversion_and_metrics node_conversion root =
    normalize_template_using_in (new_context ()) false (new_type_admission ())
      false {callback_failed = ref false,
       word_conversion = builtin_word_conversion,
       bit_conversion = builtin_bit_conversion,
       node_conversion = fn _ => node_conversion} root

  fun normalize_with_node_conversion node_conversion =
    Lib.fst o normalize_with_node_conversion_and_metrics node_conversion

  fun normalize_with_node_conversion_stopping_and_metrics sources
      node_conversion root =
    normalize_template_stopping_using_in
      (SOME (fn term => List.exists
        (fn source => Portable.pointer_eq (source, term)) sources))
      (new_context ()) false (new_type_admission ())
      false {callback_failed = ref false,
       word_conversion = builtin_word_conversion,
       bit_conversion = builtin_bit_conversion,
       node_conversion = fn _ => node_conversion} root

  fun normalize_with_node_conversion_stopping sources node_conversion =
    Lib.fst o normalize_with_node_conversion_stopping_and_metrics
      sources node_conversion

  val normalize = Lib.fst o normalize_with_metrics

  fun graph_normalize_in context graph scope source =
    discover_using_in true context true (new_type_admission ())
      (guarded_conversions {word_conversion=builtin_word_conversion,
       bit_conversion=builtin_bit_conversion,node_conversion=unchanged_node})
      NONE graph scope source

  fun graph_normalize_using_with_metrics conversions graph scope source =
    let val admission = new_type_admission ()
    in discover_using_in false (new_context ()) false admission
      (guarded_conversions conversions) NONE graph scope source end

  (* Retained-source term boundary with the EXISTING graph admissions.
     Discover every bounded schema first. Then instantiate only those local
     laws, joining their exact endpoints with MK_COMB/TRANS. In particular,
     never substitute actual operands into a completed circuit theorem. *)
  fun normalize_retaining_sources_with_node_conversion sources
      node_conversion root =
    let
      val graph = G.new ()
      val scope = G.root_scope graph
      val _ = List.app (fn term => ignore (G.retain_source graph scope term))
        sources
      val source = #node (G.import graph scope maximum root)
      val early = ref (Redblackmap.mkDict Int.compare)
      val late = ref (Redblackmap.mkDict Int.compare)
      fun record (pre,node,result,proof) =
        let val table = if pre then early else late
        in table := Redblackmap.insert
          (!table,G.node_id node,(result,proof)) end
      val (plan,_) = discover_using_in false
        (new_context_with_local_laws true) false (new_type_admission ())
        (guarded_conversions
          {word_conversion=builtin_word_conversion,
           bit_conversion=builtin_bit_conversion,
           node_conversion=node_conversion}) (SOME record) graph scope source
      val _ = if C.graph_source plan=C.graph_result plan then
          raise Conv.UNCHANGED else ()
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun exact left right proof = SmtSkeletonProve.exact_equality
        (G.representative graph left) (G.representative graph right) proof
      fun reflexive node = Thm.REFL (G.representative graph node)
      fun realize node =
        case Redblackmap.peek (!memo,G.node_id node) of
          SOME result => result
        | NONE =>
            let
              val (current,prefix,rule) =
                case Redblackmap.peek (!early,G.node_id node) of
                  SOME rule => (node,reflexive node,SOME rule)
                | NONE =>
                    let
                      val (current,prefix) = case G.view graph node of
                          G.Application (operator,operand) =>
                            let
                              val (left,left_proof) = realize operator
                              val (right,right_proof) = realize operand
                              val current =
                                G.application graph scope (left,right)
                            in (current,
                              if current=node then reflexive node
                              else exact node current
                                (Thm.MK_COMB (left_proof,right_proof))) end
                        | _ => (node,reflexive node)
                    in (current,prefix,
                      Redblackmap.peek (!late,G.node_id current)) end
              val (result,proof) = case rule of
                  NONE => (current,prefix)
                | SOME (next,local_proof) =>
                    let
                      val step = exact current next (local_proof ())
                      val (result,tail) = if next=current then
                          (next,reflexive next) else realize next
                    in (result,exact node result
                      (Thm.TRANS prefix (Thm.TRANS step tail))) end
              val _ = memo := Redblackmap.insert
                (!memo,G.node_id node,(result,proof))
            in (result,proof) end
      val (result,theorem) = realize source
      val _ = if result=C.graph_result plan then () else
        raise ERR "realize_local" "discovered result differs"
      val theorem = SmtSkeletonProve.exact_equality root
        (G.representative graph result) theorem
      val _ = if List.null (Thm.hyp theorem) then () else
        raise ERR "realize_local" "local law has hypotheses"
      val _ = Library.check_oracle_tags "SmtWordGraph" "realize_local" theorem
    in theorem end

  (* SAT sees only Boolean constructors over compact block names. Word
     operands, their definitions and any realized Hyp never enter a matcher,
     simplifier or SAT-template substitution. Close SAT and word proofs
     together, THEN realize the original statement once. *)
  fun prove_discovered_in (context : context) graph scope plan =
    let
      fun phase name action = Profile.profile_with_exn_name
        ("word-graph/prove/" ^ name) action
      val _ = #refresh_caches context ()
      val source = C.graph_source plan
      val result = C.graph_result plan
      fun spine node args = case G.view graph node of
          G.Application (operator,argument) => spine operator (argument::args)
        | _ => (node,args)
      fun boolean node =
        let val (head,args) = spine node []
        in case G.view graph head of G.Constant _ =>
            let val term = G.representative graph head
                fun named constant n = length args=n andalso
                  Term.same_const term constant
            in named boolSyntax.T 0 orelse named boolSyntax.F 0 orelse
              named boolSyntax.negation 1 orelse
              named boolSyntax.conjunction 2 orelse
              named boolSyntax.disjunction 2 orelse
              named boolSyntax.implication 2 orelse
              (named boolSyntax.equality 2 andalso
               G.type_of graph (hd args)=Type.bool) orelse
              (named boolSyntax.conditional 3 andalso
               G.type_of graph node=Type.bool) end
          | _ => false
        end
      val gates = phase "gates"
        (fn () => List.filter boolean (G.reachable graph [result])) ()
      val block = phase "prepare" (fn () =>
        P.freeze_with_conversions graph
          {scope=scope,roots=C.graph_roots plan,sources=[],closed_facts=[],
           conversions=C.graph_conversions plan,
           template_limit=SmtResource.max_bv_replay_term_nodes}) ()
      val definitions = phase "constructors"
        (List.map (P.constructor block)) gates
      val equations = phase "equations"
        (List.map (Thm.concl o P.theorem block)) definitions
      fun original_sat () =
        let
          val antecedent = case equations of [] => boolSyntax.T
            | _ => boolSyntax.list_mk_conj equations
          val obligation = if null equations then P.name block result else
            boolSyntax.mk_imp (antecedent,P.name block result)
          val law = phase "sat" (SmtSkeletonProve.propositional_prove_in
            (#sat_context context)) obligation
        in phase "assemble-sat" (fn () =>
          if null equations then P.checked block law else
            P.compose block
              (fn proofs => Thm.MP law (Drule.LIST_CONJ proofs))
              definitions) () end
      fun circuit_sat () =
        let
          (* Fixed Boolean constructors over names: this optional inventory
             is bounded by the standing Skeleton cap. Larger circuits keep
             the original propositional producer and admissions. *)
          val equivalence = SmtCircuitSat.balanced_equivalences
            (List.map SmtCircuitSat.definition_cnf equations)
          val cnf = boolSyntax.rhs (Thm.concl equivalence)
          val output = P.name block result
          val target = boolSyntax.mk_imp (cnf,output)
          val measure = SmtResource.profile_phase
            "skeleton/sat-target-measure" SmtSkeletonProve.term_measure target
          val _ = SmtSkeletonProve.observe_sat_target target
          fun prove () = SmtSkeletonProve.cached_sat_proof
            (#sat_context context) target (#dag_nodes measure)
            (fn () => SmtCircuitSat.prove_cnf (cnf,output))
          fun timed () = SmtResource.profile_phase
            "skeleton/sat-search+checking" prove ()
          val law = phase "sat" (fn () =>
            case !SmtSkeletonProve.sat_completion_observer of
              NONE => timed ()
            | SOME observer =>
                let val started = Time.now ()
                    val theorem = timed ()
                    val _ = observer (target,Time.- (Time.now (),started))
                in theorem end) ()
        in phase "assemble-sat" (fn () => P.compose block
          (fn proofs => Thm.MP law (Thm.EQ_MP equivalence
            (SmtCircuitSat.balanced_conjunction proofs))) definitions) () end
      val proof = if length gates <=
          SmtResource.max_skeleton_replay_dag_nodes then circuit_sat ()
        else original_sat ()
      val conversion = phase "assemble-normalization" (fn () => P.compose block
        (fn [named,constructor] => Thm.EQ_MP constructor named
          | _ => raise Fail "word graph equality opening")
        [C.graph_assemble_named graph block plan,
         P.constructor block (C.graph_equality plan)]) ()
      val proof = phase "assemble-transport" (fn () => P.compose block
        (fn [conversion,proof] => Thm.EQ_MP (Thm.SYM conversion) proof
          | _ => raise Fail "word graph SAT transport") [conversion,proof]) ()
    in phase "realize" (P.realize block source) proof end

  fun prove_graph_using_in (context : context) node_conversion target =
    let
      val input = SmtResource.dag_nodes_up_to maximum target
      val _ = SmtResource.check_dag_size_for
        "BitVector" "word-circuit-replay" input
      val graph = G.new ()
      val scope = G.root_scope graph
      val source = #node (G.import graph scope maximum target)
      val admission = new_type_admission ()
      val conversions = guarded_conversions
        {word_conversion=builtin_word_conversion,
         bit_conversion=builtin_bit_conversion,
         node_conversion=node_conversion}
      fun reflexive admission =
        let val callback = #node_conversion conversions admission
        in fn term => if boolSyntax.is_eq term then
            (SmtReplayCanon.reflexive_equality_conv term
             handle Conv.UNCHANGED => callback term)
          else callback term end
      val (plan,_) = discover_using_in false context true admission
        {callback_failed= #callback_failed conversions,
         word_conversion= #word_conversion conversions,
         bit_conversion= #bit_conversion conversions,node_conversion=reflexive}
        NONE graph scope source
    in SmtSkeletonProve.exact_conclusion target
      (prove_discovered_in context graph scope plan) end

  (* Retain the cheap completed-schema route for shallow word identities.
     The whole schema proof (word lowering AND SAT) closes on holes. Its
     typed root law is itself the complete compact proof, so no unused
     operand-interior definitions need to be assembled. *)
  fun prove_using_in (context : context) node_conversion target =
    let
      val _ = #refresh_caches context ()
      val context = proof_context context
      val input = SmtResource.dag_nodes_up_to maximum target
      val _ = SmtResource.check_dag_size_for
        "BitVector" "word-circuit-replay" input
      exception WidePrefix
      fun root_schema () =
        let
          val graph = G.new ()
          val scope = G.root_scope graph
          val source = #node (G.import graph scope maximum target)
          val holes = ref ([] : (G.node * term) list)
          fun hole node = case List.find (fn (old,_) => old=node) (!holes) of
              SOME (_,term) => term
            | NONE =>
                let val term = Term.mk_var ("word_graph_proof_operand_" ^
                      Int.toString (length (!holes)),G.type_of graph node)
                in holes := !holes @ [(node,term)]; term end
          val template = typed_frontier graph hole 1 source
          val _ = case SmtReplayImport.bounded_raw_size
              SmtResource.max_bv_replay_term_nodes template of
              SOME _ => () | NONE => raise WidePrefix
          val admission = new_type_admission ()
          val _ = admit_callback_template admission template
            handle Feedback.HOL_ERR error =>
              if SmtResource.is_resource_gate error then raise WidePrefix
              else raise Feedback.HOL_ERR error
          val callback = checked_node_callback admission node_conversion
          fun reflexive term =
            if boolSyntax.is_eq term then
              (SmtReplayCanon.reflexive_equality_conv term
               handle Conv.UNCHANGED => callback term)
            else callback term
          val _ = #refresh_caches context ()
          val signature_witness = SmtSkeletonProve.cache_signature ()
          val generation_witness = !(#cache_generation context)
          val theorem = case Redblackmap.peek (!(#proof_schemas context),
              template) of SOME theorem => theorem
            | NONE =>
                let
                  val normalized = #1 (normalize_template_using_in context true
                    admission true
                    {callback_failed=ref false,
                     word_conversion=builtin_word_conversion,
                     bit_conversion=builtin_bit_conversion,
                     node_conversion=fn _ => reflexive} template)
                    handle Conv.UNCHANGED => Thm.REFL template
                  val residue = boolSyntax.rhs (Thm.concl normalized)
                  val law = SmtSkeletonProve.propositional_prove_in
                    (#sat_context context) residue
                  val theorem = Thm.EQ_MP (Thm.SYM normalized) law
                  val _ = #refresh_caches context ()
                  val _ = if generation_witness <>
                      !(#cache_generation context) orelse
                      not (SmtSkeletonProve.cache_signature_matches
                        signature_witness) orelse
                      !(#schema_entries context) >= maximum orelse
                      not (#cache_live_check context
                        (Thm.concl theorem)) then () else
                    (#proof_schemas context := Redblackmap.insert
                       (!(#proof_schemas context),template,theorem);
                     #schema_entries context := !(#schema_entries context)+1)
                in theorem end
          val schema = C.checked_graph_schema graph scope
            {theorem=Drule.EQT_INTRO theorem,holes=List.map #2 (!holes),
             operands=List.map #1 (!holes),
             template_limit=SmtResource.max_bv_replay_term_nodes}
          val _ = if C.graph_schema_source schema=source then () else
            raise ERR "prove" "wrong completed word schema endpoint"
          val plan = C.graph_schema_leaf graph scope
            {schema=schema,observe=fn () => ()}
        in Option.map
          (SmtSkeletonProve.exact_conclusion target o Drule.EQT_ELIM)
          (C.realize_typed_root_schema graph scope
            SmtResource.max_bv_replay_term_nodes plan) end
        handle HolSatLib.SAT_cex _ => NONE
             | HolSatLib.SAT_satisfiable _ => NONE
             | WidePrefix => NONE
    in case root_schema () of SOME theorem => theorem
      | NONE => prove_graph_using_in context node_conversion target end

  (* Normalize a shared finite-word circuit once, retaining shared operator
     projection proofs, then replay a checked SAT certificate for its Boolean
     graph.  No theory atom is assumed true by the propositional stage. *)
  fun prove_in (context : context) target =
    let
      val _ = #refresh_caches context ()
      val source_maximum = SmtResource.max_bv_replay_term_nodes
      val _ = SmtResource.check_dag_size_with_limit
        "BitVector" "word-circuit-source" source_maximum
        (SmtResource.dag_nodes_up_to source_maximum target)
      val share_thm = SmtReplayCanon.share_conv target
      val shared = boolSyntax.rhs (Thm.concl share_thm)
      val maximum = SmtResource.max_skeleton_replay_dag_nodes
      val observed = SmtResource.dag_nodes_up_to maximum shared
      val _ = SmtResource.check_dag_size_for
        "BitVector" "word-circuit-replay" observed
      (* Reflexivity belongs to this decision procedure, not to the word
         conversion's representation contract.  Check it both before word
         expansion and on reflexive equalities introduced by that expansion. *)
      fun full_circuit () = prove_using_in context unchanged_node shared
      val result =
        SmtResource.profile_phase "word-graph-Boolean-congruence"
          (SmtSkeletonProve.congruence_prove_in (#sat_context context)) shared
        handle Feedback.HOL_ERR holerr =>
          if SmtResource.is_resource_gate holerr then
            raise Feedback.HOL_ERR holerr
          else full_circuit ()
             | HolSatLib.SAT_cex _ => full_circuit ()
             | HolSatLib.SAT_satisfiable _ => full_circuit ()
    in
      Thm.EQ_MP (Thm.SYM share_thm) result
    end

  fun prove_with_node_conversion node_conversion target =
    let
      val input = SmtResource.dag_nodes_up_to maximum target
      val _ = SmtResource.check_dag_size_for
        "Skeleton" "word-graph-input" input
    in prove_using_in (new_context ()) node_conversion target end

  fun prove target = prove_in (new_context ()) target

end
