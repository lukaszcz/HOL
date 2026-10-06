(* Copyright (c) 2026 The HOL4 contributors. *)

(* Sharing-preserving checked normalization for word-bearing Boolean graphs. *)

structure SmtWordGraph :> SmtWordGraph =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtWordGraph"
  val maximum = SmtResource.max_skeleton_replay_dag_nodes

  type proof_cache = (term, thm) Redblackmap.dict ref
  type indexed_proof_cache = (int, thm) Redblackmap.dict ref
  type context =
    {normalized : indexed_proof_cache, expanded : indexed_proof_cache,
     index : term -> int option, entries : int ref,
     word_schemas : proof_cache, bit_schemas : proof_cache,
     schema_entries : int ref, sat_context : SmtSkeletonProve.sat_context}

  fun new_context () : context =
    {normalized = ref (Redblackmap.mkDict Int.compare),
     expanded = ref (Redblackmap.mkDict Int.compare), entries = ref 0,
     index = SmtResource.new_bounded_term_index maximum,
     word_schemas = ref (Redblackmap.mkDict Term.compare),
     bit_schemas = ref (Redblackmap.mkDict Term.compare),
     schema_entries = ref 0, sat_context = SmtSkeletonProve.new_sat_context ()}

  fun schema_lookup cache source =
    case Redblackmap.peek (!cache, source) of
      NONE => NONE
    | SOME theorem =>
        SOME (SmtSkeletonProve.anchor_left source theorem, true)

  fun context_lookup (context : context) cache source =
    case (#index context) source of
      NONE => NONE
    | SOME id =>
        (case Redblackmap.peek (!cache, id) of
           NONE => NONE
         | SOME theorem =>
             SOME (SmtSkeletonProve.anchor_left source theorem, true))

  fun context_save (context : context) cache source (theorem, changed) =
    if not changed orelse !(#entries context) >= maximum then ()
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
      end

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

  fun normalize_using_in (context : context) reuse
      {word_conversion, bit_conversion, node_conversion} root =
    let
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
      fun mark_generated term = mark_pointer generated_seen term
      fun seed_source term =
        if mark_generated term then
          List.app seed_source (SmtResource.term_children term)
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
         nodes are not charged again as allocations. *)
      val _ = seed_source root
      val reserved = ref (List.foldl
        (fn (variable, names) => HOLset.add
          (names, Lib.fst (Term.dest_var variable)))
        (HOLset.empty String.compare)
        (HOLset.listItems (Term.FVL_dag [root] Term.empty_tmset)))
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

      val type_admission = new_type_admission ()
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
        if not reuse then Conv.QCONV conversion schematic
        else
          case schema_lookup cache schematic of
            SOME (theorem, _) => theorem
          | NONE =>
              let
                val theorem = Conv.QCONV conversion schematic
                val _ = if !(#schema_entries context) >= maximum then ()
                  else
                    (if List.null (Thm.hyp theorem) then ()
                     else raise ERR "schema_conversion"
                       "operator schema has hypotheses";
                     Library.check_oracle_tags "SmtWordGraph"
                       "operator schema" theorem;
                     cache := Redblackmap.insert (!cache, schematic, theorem);
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

      val normalize_index = SmtResource.new_bounded_term_index maximum
      val normalize_cache = ref
        (Redblackmap.mkDict Int.compare :
          (int, thm * bool) Redblackmap.dict)
      val normalize_physical = Array.array
        (bucket_count, [] : (term * (thm * bool)) list)

      fun cached_normalization term =
        case pointer_lookup normalize_physical term of
          SOME result => SOME result
        | NONE =>
            (case Option.mapPartial
                (fn id => Redblackmap.peek (!normalize_cache, id))
                (normalize_index term) of
               NONE => if reuse then
                   context_lookup context (#normalized context) term
                 else NONE
             | SOME (theorem, changed) => SOME
                 (if changed then
                    (SmtSkeletonProve.anchor_left term theorem, true)
                  else (Thm.REFL term, false)))

      fun external_conversion source =
        let
          val theorem = Conv.QCONV node_conversion source
            handle Conv.UNCHANGED => Thm.REFL source
          val right = boolSyntax.rhs (Thm.concl theorem)
        in (theorem, not (Term.aconv source right)) end

      fun normalize_source term =
        case cached_normalization term of
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
              val _ = case normalize_index term of NONE => ()
                | SOME id => normalize_cache :=
                    Redblackmap.insert (!normalize_cache, id, result)
              val _ = pointer_insert normalize_physical term result
              val _ = if reuse then
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
        case pointer_lookup expand_cache term of
          SOME result => (memo_hits := !memo_hits + 1; result)
        | NONE =>
            (case (if reuse then
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
                   val _ = if reuse then
                       context_save context (#expanded context) term
                         (theorem, changed)
                     else ()
                 in result end)

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

  fun unchanged_node _ = raise Conv.UNCHANGED

  fun normalize_using_with_metrics conversions root =
    normalize_using_in (new_context ()) false conversions root

  val normalize_with_metrics = normalize_using_with_metrics
    {word_conversion = blastLib.WORD_SIMP_CONV,
     bit_conversion = blastLib.BIT_BLAST_CONV,
     node_conversion = unchanged_node}

  fun normalize_with_node_conversion_and_metrics node_conversion =
    normalize_using_with_metrics
      {word_conversion = blastLib.WORD_SIMP_CONV,
       bit_conversion = blastLib.BIT_BLAST_CONV,
       node_conversion = node_conversion}

  fun normalize_with_node_conversion node_conversion =
    Lib.fst o normalize_with_node_conversion_and_metrics node_conversion

  val normalize = Lib.fst o normalize_with_metrics

  (* Normalize a shared finite-word circuit once, retaining shared operator
     projection proofs, then replay a checked SAT certificate for its Boolean
     graph.  No theory atom is assumed true by the propositional stage. *)
  fun prove_in context target =
    let
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
      val reflexivity = SmtReplayCanon.dag_rewrite_conv
        SmtReplayCanon.reflexive_equality_conv
      val normalize = Lib.fst o normalize_using_in context true
        {word_conversion = blastLib.WORD_SIMP_CONV,
         bit_conversion = blastLib.BIT_BLAST_CONV,
         node_conversion = unchanged_node}
      fun full_circuit () =
        let
          val normalized = Conv.THENC
            (reflexivity, Conv.THENC (normalize, reflexivity)) shared
            handle Conv.UNCHANGED => Thm.REFL shared
          val residue = boolSyntax.rhs (Thm.concl normalized)
          val result = SmtSkeletonProve.propositional_prove_in
            (#sat_context context) residue
        in Thm.EQ_MP (Thm.SYM normalized) result end
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

  fun prove target = prove_in (new_context ()) target

end
