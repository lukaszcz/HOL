structure SmtSkeletonProve =
struct

  open HolKernel

  val ERR = Feedback.mk_HOL_ERR "SmtSkeletonProve"

  datatype expansion = Expanded of thm | Unable

  type atom_procedure =
    {name : string, expand : term -> expansion}

  datatype context = Context of
    {procedures : atom_procedure list,
     fallback : atom_procedure option,
     atom_index : term -> int option,
     atom_cache : (string * int * int, thm) Redblackmap.dict ref,
     cache_generation : unit ref ref,
     refresh_caches : unit -> unit}

  type metrics =
    {target_tree_nodes : int,
     target_dag_nodes : int,
     skeleton_dag_nodes : int,
     normalized_tree_nodes : int,
     normalized_dag_nodes : int,
     sat_tree_nodes : int,
     sat_dag_nodes : int,
     graph_nodes : int,
     graph_observations : int,
     graph_edges : int,
     graph_type_nodes : int,
     graph_type_observations : int,
     graph_type_edges : int,
     graph_leaf_transport_nodes : int,
     graph_leaf_transport_seconds : Time.time,
     distinct_atoms : int,
     atom_requests : int,
     atom_proofs : int,
     atom_cache_hits : int,
     node_cache_hits : int,
     node_cache_pointer_hits : int,
     node_cache_structural_reanchor_attempts : int,
     node_cache_structural_reanchor_successes : int,
     node_cache_structural_reanchor_fallbacks : int,
     node_cache_reanchor_seconds : Time.time,
     residual_atoms : int,
     atom_seconds : Time.time,
     sat_seconds : Time.time,
     total_seconds : Time.time,
     procedure_calls : (string * int) list}

  datatype node_cache_event =
      NodeCachePointerHit
    | NodeCacheStructuralReanchorAttempt
    | NodeCacheStructuralReanchorSuccess
    | NodeCacheStructuralReanchorFallback
    | NodeCacheReanchorTime of Time.time

  val node_cache_observer =
    ref (NONE : (node_cache_event -> unit) option)

  val sat_target_observer = ref (NONE : (term -> unit) option)
  val sat_completion_observer =
    ref (NONE : ((term * Time.time) -> unit) option)

  fun with_node_cache_observer observer action input =
    let
      val previous = !node_cache_observer
      fun restore () = node_cache_observer := previous
      fun run () = (node_cache_observer := observer; action input)
    in
      Portable.finally restore run ()
    end

  fun observe_node_cache event =
    case !node_cache_observer of
      NONE => ()
    | SOME observer => observer event

  fun with_sat_target_observer observer action input =
    let
      val previous = !sat_target_observer
      fun restore () = sat_target_observer := previous
      fun run () = (sat_target_observer := observer; action input)
    in
      Portable.finally restore run ()
    end

  fun observe_sat_target target =
    case !sat_target_observer of
      NONE => ()
    | SOME observer => observer target

  fun with_sat_observers target_observer completion_observer action input =
    let
      val previous_target = !sat_target_observer
      val previous_completion = !sat_completion_observer
      fun restore () =
        (sat_target_observer := previous_target;
         sat_completion_observer := previous_completion)
      fun run () =
        (sat_target_observer := target_observer;
         sat_completion_observer := completion_observer;
         action input)
    in
      Portable.finally restore run ()
    end

  (* Immutable signature-table witnesses also detect Context.restore, which
     need not advance retirement epochs. This only invalidates optional
     hints; it is neither term validation nor proof admission. *)
  fun cache_signature () =
    let val current = Context.snapshot () in
      (Context.typesig current, Context.termsig current)
    end

  fun cache_signature_matches (types, symbols) =
    let val (current_types, current_symbols) = cache_signature () in
      Portable.pointer_eq (types, current_types) andalso
      Portable.pointer_eq (symbols, current_symbols)
    end

  (* Small publication hints must not dominate fresh/zero-reuse contexts.
     Collision eviction affects retention only, never checked proving. *)
  val live_bucket_count = 127
  val live_term_bucket_count = 4093
  type 'a live_bucket = {values : 'a array, next : int ref}
  type 'a live_buckets =
    {peek:int -> 'a live_bucket option,put:int * 'a live_bucket -> unit}
  fun new_live_buckets count : 'a live_buckets =
    let
      val size = 32
      val blocks = Array.array ((count+size-1) div size,NONE)
      fun peek index =
        case Array.sub (blocks,index div size) of NONE => NONE
        | SOME block => Array.sub (block,index mod size)
      fun put (index,value) =
        let val slot = index div size
            val block = case Array.sub (blocks,slot) of SOME block => block
              | NONE => let val block = Array.array
                    (Int.min (size,count-slot*size),NONE)
                  in Array.update (blocks,slot,SOME block);block end
        in Array.update (block,index mod size,SOME value) end
    in {peek=peek,put=put} end
  type live_memo =
    {terms : Term.term live_buckets,types : Type.hol_type live_buckets}
  fun new_live_memo () : live_memo =
    {terms = new_live_buckets live_term_bucket_count,
     types = new_live_buckets live_bucket_count}

  (* Bounded positive hints are optional publication checks, not admission.
     Small pointer buckets avoid structural comparisons of shared Types. *)
  fun live_check_with_hints (typesig, termsig) ({terms, types} : live_memo) =
    let
      exception Unknown
      val remaining = ref SmtResource.max_bv_replay_term_nodes
      fun spend amount =
        if amount <= !remaining then remaining := !remaining - amount
        else raise Unknown
      fun known (buckets:'a live_buckets) bucket value =
        case #peek buckets bucket of NONE => false
        | SOME {values, ...} =>
            Array.exists (fn old => Portable.pointer_eq (value, old)) values
      fun remember (buckets:'a live_buckets) bucket value =
        case #peek buckets bucket of
          NONE =>
            (* Initial duplicates represent the same singleton set. After
               eight inserts the ring holds exactly the last eight values,
               just like the original newest-first list. *)
            #put buckets (bucket,
              {values = Array.array (8,value), next = ref 1})
        | SOME {values,next} =>
            (Array.update (values,!next,value);next := (!next+1) mod 8)
      fun live_type ty =
        let
          val _ = spend 1
          val bucket = if Type.is_vartype ty then 0 else
            KernelSig.epoch_of (#Tyop (Type.dest_thy_typeid ty))
              mod live_bucket_count
        in
          if known types bucket ty then true
          else
            let
              val live = Type.is_vartype ty orelse
                let val {Tyop, Args, ...} = Type.dest_thy_typeid ty in
                  KernelSig.uptodate_id typesig Tyop andalso
                  List.all live_type Args
                end
              val _ = if live then remember types bucket ty else ()
            in live end
        end
      (* Raw counting itself opens every nested binder. Standard count_body
         builds REFL/Beta at its range Type, whose native classification can
         unfold shared children exponentially. Liveness hints do not bound
         that work: admit an unfolded range before ANY such opening. This
         conservative optional check may only forgo retention. *)
      fun before_open ty =
        let
          val allowance = ref 8192
          val sizes = ref ([] : (hol_type * int) list)
          fun debit () =
            (if !allowance = 0 then raise Unknown else ();
             allowance := !allowance - 1; spend 1)
          fun find _ [] = NONE
            | find ty ((saved,size) :: rest) =
                (debit ();
                 if Portable.pointer_eq (ty,saved) then SOME size
                 else find ty rest)
          fun visit ty =
            (debit ();
             case find ty (!sizes) of
               SOME size => size
             | NONE =>
                 let
                   fun add (child,total) =
                     let val _ = debit ()
                         val sum = total + visit child
                     in if sum > 8192 then raise Unknown else sum end
                   val size = if Type.is_vartype ty then 1 else
                     List.foldl add 1 (#Args (Type.dest_thy_typeid ty))
                   val _ = sizes := (ty,size) :: !sizes
                 in size end)
          (* Pointer memoization saves guard work, not the native unfolded
             work. Reserve that too, across all openings in this check. *)
        in spend (visit (#2 (Type.dom_rng ty))) end
      fun live_term term =
        let
          val _ = spend 1
          (* Broad shared circuits need distinct routes beyond identical
             curried heads. Each bucket still has just eight positive hints;
             empty backing blocks stay unallocated in small fresh checks. *)
          val bucket = SmtResource.pointer_bucket live_term_bucket_count term
        in
          if known terms bucket term then true
          else
            let
              val live =
                if Term.is_comb term then
                  live_term (Term.rator term) andalso
                  live_term (Term.rand term)
                else if Term.is_var term then live_type (Term.type_of term)
                else if Term.is_const term then
                  let val {Name, Ty, ...} = Term.dest_thy_constid term in
                    KernelSig.uptodate_id termsig Name andalso live_type Ty
                  end
                else
                  (* Large binders are an optional miss. Never allow the
                     publication walk to open an unbounded legacy body. *)
                  (case SmtReplayImport.bounded_raw_size_with_type_check
                      before_open (Int.min (8192, !remaining)) term of
                     NONE => raise Unknown
                   | SOME nodes =>
                       let
                         val _ = spend nodes
                         val (variable, body) =
                           SmtReplayImport.dest_abs_preserving_names term
                       in live_term variable andalso live_term body end)
              val _ = if live then remember terms bucket term else ()
            in live end
        end
    in fn term => live_term term handle Unknown => false end

  fun new_cache_live_check () =
    live_check_with_hints (cache_signature ()) (new_live_memo ())

  fun cache_size (Context {atom_cache, refresh_caches, ...}) =
    (refresh_caches (); Redblackmap.numItems (!atom_cache))

  (* Admission and proof reconstruction share this exact DAG-aware metric.
     In particular, String dispatch must not reject a compact shared term by
     its exponentially larger unfolded tree before this engine sees it. *)
  val max_metric = SmtResource.max_metric
  val saturated_add = SmtResource.saturated_add
  val phase = SmtResource.profile_phase

  fun skeleton_children term =
    if Term.aconv term boolSyntax.T orelse
       Term.aconv term boolSyntax.F then SOME []
    else if boolSyntax.is_neg term then
      SOME [boolSyntax.dest_neg term]
    else if boolSyntax.is_conj term then
      let val (left, right) = boolSyntax.dest_conj term
      in SOME [left, right] end
    else if boolSyntax.is_disj term then
      let val (left, right) = boolSyntax.dest_disj term
      in SOME [left, right] end
    else if boolSyntax.is_imp term then
      let val (left, right) = boolSyntax.dest_imp term
      in SOME [left, right] end
    else if boolSyntax.is_cond term andalso Term.type_of term = Type.bool then
      let val (test, yes, no) = boolSyntax.dest_cond term
      in SOME [test, yes, no] end
    else if boolSyntax.is_eq term then
      let val (left, right) = boolSyntax.dest_eq term
      in
        if Term.type_of left = Type.bool then SOME [left, right]
        else NONE
      end
    else NONE

  fun connective_congruence term child_theorems =
    let
      val (head, arguments) = boolSyntax.strip_comb term
      val _ =
        if List.length arguments = List.length child_theorems then ()
        else raise ERR "connective_congruence"
          "propositional connective arity changed"
    in
      List.foldl
        (fn (child_theorem, theorem) =>
          Thm.MK_COMB (theorem, child_theorem))
        (Thm.REFL head) child_theorems
    end

  (* Congruence reconstructs an alpha-equal left side from its children.
     Anchor it to the caller's existing node immediately.  Because recursive
     results maintain the same invariant, the kernel comparison at each
     anchor sees the original child pointers and remains local to one node. *)
  fun anchor_left term theorem =
    Thm.TRANS (Thm.REFL term) theorem

  fun anchor_right term theorem =
    Thm.TRANS theorem (Thm.REFL term)

  (* Redblackmap keys are structural.  Keep separate entries for equal terms
     with different physical identities when a cached value embeds the exact
     occurrence. *)
  fun pointer_cache_peek dictionary term =
    case Redblackmap.peek (dictionary, term) of
      NONE => NONE
    | SOME bucket =>
        case List.find
            (fn (saved, _) => Portable.pointer_eq (term, saved)) bucket of
          NONE => NONE
        | SOME (_, value) => SOME value

  fun pointer_cache_insert dictionary term value =
    let
      val bucket = Option.getOpt (Redblackmap.peek (dictionary, term), [])
    in
      Redblackmap.insert (dictionary, term, (term, value) :: bucket)
    end

  exception REANCHOR_LIMIT

  datatype admission_type_key =
      AdmissionTypeVariable of string
    | AdmissionTypeOperator of KernelSig.kernelid * int list

  (* Metadata keys are not proof evidence. Meter comparisons themselves,
     including long names and argument lists, before inspecting each item. *)
  fun admission_type_key_compare reserve (left, right) =
    let
      fun strings (left, right) =
        let
          fun at index =
            (reserve 1;
             if index = String.size left then
               if index = String.size right then EQUAL else LESS
             else if index = String.size right then GREATER
             else case Char.compare
                 (String.sub (left, index), String.sub (right, index)) of
               EQUAL => at (index + 1)
             | order => order)
        in at 0 end
      fun arguments (left, right) =
        (reserve 1;
         case (left, right) of
           ([], []) => EQUAL
         | ([], _) => LESS
         | (_, []) => GREATER
         | (l :: ls, r :: rs) =>
             case Int.compare (l, r) of
               EQUAL => arguments (ls, rs)
             | order => order)
      fun declarations (left, right) =
        case strings (KernelSig.name_of left, KernelSig.name_of right) of
          EQUAL =>
            (case strings (KernelSig.seg_of left, KernelSig.seg_of right) of
               EQUAL => (reserve 1; Int.compare
                 (KernelSig.epoch_of left, KernelSig.epoch_of right))
             | order => order)
        | order => order
    in
      reserve 1;
      case (left, right) of
        (AdmissionTypeVariable l, AdmissionTypeVariable r) => strings (l, r)
      | (AdmissionTypeVariable _, AdmissionTypeOperator _) => LESS
      | (AdmissionTypeOperator _, AdmissionTypeVariable _) => GREATER
      | (AdmissionTypeOperator (l, ls), AdmissionTypeOperator (r, rs)) =>
          case declarations (l, r) of
            EQUAL => arguments (ls, rs)
          | order => order
    end

  datatype admission_type_node = AdmissionTypeNode of
    {id : int, tree_nodes : int, comparison_nodes : IntInf.int}

  fun new_type_admission_context () =
    let
      val maximum = SmtResource.max_bv_replay_term_nodes
      fun check work = SmtResource.check_term_size_for "BitVector"
        "skeleton-type-work" work
      exception MetadataLimit
      val remaining = ref (NONE : int option)
      fun reserve amount =
        case !remaining of
          NONE => ()
        | SOME fuel =>
            if amount <= fuel then remaining := SOME (fuel - amount)
            else raise MetadataLimit
      fun metered action input =
        let
          val previous = !remaining
          fun restore () = remaining := previous
          fun run () = (remaining := SOME maximum; action input)
        in Portable.finally restore run () end
      fun compare_required_keys (left,right) =
        let
          fun arguments ([],[]) = EQUAL
            | arguments ([],_) = LESS
            | arguments (_,[]) = GREATER
            | arguments (l::ls,r::rs) =
                (case Int.compare (l,r) of
                   EQUAL => arguments (ls,rs)
                 | order => order)
          fun declarations (left,right) =
            case String.compare
                (KernelSig.name_of left,KernelSig.name_of right) of
              EQUAL =>
                (case String.compare
                    (KernelSig.seg_of left,KernelSig.seg_of right) of
                   EQUAL => Int.compare
                     (KernelSig.epoch_of left,KernelSig.epoch_of right)
                 | order => order)
            | order => order
        in
          case (left,right) of
            (AdmissionTypeVariable l,AdmissionTypeVariable r) =>
              String.compare (l,r)
          | (AdmissionTypeVariable _,AdmissionTypeOperator _) => LESS
          | (AdmissionTypeOperator _,AdmissionTypeVariable _) => GREATER
          | (AdmissionTypeOperator (l,ls),AdmissionTypeOperator (r,rs)) =>
              (case declarations (l,r) of
                 EQUAL => arguments (ls,rs)
               | order => order)
        end
      val compare_metered_keys = admission_type_key_compare reserve
      val ids = ref (Redblackmap.mkDict
        (fn keys => case !remaining of
            NONE => compare_required_keys keys
          | SOME _ => compare_metered_keys keys))
      (* Only compact interning owns the original observation/edge stats.
         Speculative metadata must not add observations on a failed walk. *)
      (* Small Types only query the first eight observations. Keep that
         exact recent window, plus complete pointer retention for large
         Types. Older small misses cannot help any future lookup. *)
      val physical = ref ([] : (hol_type * admission_type_node) list)
      val large_physical = ref
        ([] : (hol_type * admission_type_node) list)
      (* Count every original compact miss even when its hint is retired. *)
      val observations = ref 0
      val optional_physical =
        ref ([] : (hol_type * admission_type_node) list)
      (* Persistent optional hints are bounded independently of cache age.
         Complete pointer memoization lives in each metadata call, below. *)
      fun recent ty =
        let
          fun seek 0 _ _ _ = NONE
            | seek fuel previous count entries =
                (reserve 1;
                 case entries of
                   [] => NONE
                 | (entry as (saved, node)) :: rest =>
                     if Portable.pointer_eq (ty, saved) then
                       (reserve (count + 1);
                        optional_physical :=
                          entry :: List.revAppend (previous, rest);
                        SOME node)
                     else seek (fuel - 1) (entry :: previous)
                       (count + 1) rest)
        in seek 8 [] 0 (!optional_physical) end
      val next_id = ref 0
      val nodes = ref 0
      val edges = ref 0
      (* Exact below the allowance; retain the first excessive subtree's
         lower bound above it, preserving the existing diagnostic. *)
      fun add_work left right =
        if left > maximum then left else if right > maximum then right
        else saturated_add left right
      (* Both paths use owned child IDs, never native Type comparison.
         The dictionary's comparator is metered only during optional work.
         Commit an ID/counter only after insertion has actually completed. *)
      fun canonical ty children =
        let
          fun node_id (AdmissionTypeNode {id, ...}) = id
          fun child_ids [] = (reserve 1; [])
            | child_ids (child :: rest) =
                (reserve 1; node_id child :: child_ids rest)
          val key = if Type.is_vartype ty then
              AdmissionTypeVariable (Type.dest_vartype ty)
            else AdmissionTypeOperator
              (#Tyop (Type.dest_thy_typeid ty), child_ids children)
          val _ = reserve 1
        in
          case Redblackmap.peek (!ids, key) of
            SOME node => node
          | NONE =>
              let
                val size = List.foldl
                  (fn (AdmissionTypeNode {tree_nodes, ...}, count) =>
                    (reserve 1; add_work count tree_nodes)) 1 children
                val comparison_nodes = List.foldl
                  (fn (AdmissionTypeNode {comparison_nodes, ...}, n) =>
                    (reserve 1; IntInf.min
                      (SmtReplayLeafProof.native_tree_switch + 1,
                       n + comparison_nodes))) 1 children
                val node = AdmissionTypeNode
                  {id = !next_id, tree_nodes = size,
                   comparison_nodes = comparison_nodes}
                val _ = reserve 1
                val updated = Redblackmap.insert (!ids, key, node)
              in
                ids := updated;
                next_id := !next_id + 1; nodes := !nodes + 1;
                node
              end
        end
      (* Optional full metadata charges every probe/comparison. Its private
         exhaustion is not the native unfolded Type-tree admission limit. *)
      fun metadata_walk root =
        let
          val local_physical = ref
            ([] : (hol_type * admission_type_node) list)
          fun local_lookup ty entries =
            (reserve 1;
             case entries of
               [] => NONE
             | (saved, node) :: rest =>
                 if Portable.pointer_eq (ty, saved) then SOME node
                 else local_lookup ty rest)
          fun remember ty node =
            (reserve 1;
             local_physical := (ty, node) :: !local_physical;
             node)
          fun lookup ty =
            case recent ty of
              SOME node => SOME (remember ty node)
            | NONE => local_lookup ty (!local_physical)
          fun visit ty =
        (reserve 1;
        case lookup ty of
          SOME node => node
        | NONE =>
            let
              val _ = reserve 1
              val arguments = if Type.is_vartype ty then []
                else #Args (Type.dest_thy_typeid ty)
              fun children_of arguments =
                (reserve 1;
                 case arguments of
                   [] => []
                 | ty :: rest =>
                     let
                       val child = visit ty
                     in child :: children_of rest end)
              val children = children_of arguments
              val node = canonical ty children
              val _ = reserve 1
              val _ = optional_physical :=
                (ty, node) :: !optional_physical
            in remember ty node end)
        in visit root end
      fun metadata ty = metered metadata_walk ty
        handle MetadataLimit => (check (maximum + 1); raise MetadataLimit)
      (* Required IDs and original stats have no bookkeeping allowance.
         Preserve the original small-Type cache policy: bounded probes for
         synthesized small Types, complete pointer memoization for shared
         large Types. All structural keys contain owned IDs, so falling
         back to this path cannot unfold a native Type comparison. *)
      fun prefix 0 _ = []
        | prefix _ [] = []
        | prefix n (first :: rest) = first :: prefix (n-1) rest
      fun remember_type_hint ty node =
        if (case !physical of
              (saved,_) :: _ => Portable.pointer_eq (ty,saved)
            | [] => false) then ()
        else physical := (ty,node) :: prefix 7
          (List.filter (fn (saved,_) =>
            not (Portable.pointer_eq (ty,saved))) (!physical))
      fun compact_type ty =
        let
          fun small 0 _ = NONE
            | small fuel ty =
                if Type.is_vartype ty then SOME (fuel - 1)
                else small_children (fuel - 1)
                  (#Args (Type.dest_thy_typeid ty))
          and small_children fuel [] = SOME fuel
            | small_children fuel (ty :: rest) =
                case small fuel ty of
                  NONE => NONE
                | SOME fuel => small_children fuel rest
          fun recent_small ty =
            let
              fun seek 0 _ _ = NONE
                | seek _ _ [] = NONE
                | seek fuel prior ((entry as (saved, node)) :: rest) =
                    if Portable.pointer_eq (ty, saved) then
                      (physical := entry :: List.revAppend (prior, rest);
                       SOME node)
                    else seek (fuel - 1) (entry :: prior) rest
            in seek 8 [] (!physical) end
          val is_small = Option.isSome (small 16 ty)
          val saved = if is_small then recent_small ty
            else SmtResource.recent_pointer_lookup large_physical ty
        in
          case saved of
            SOME node =>
              if is_small orelse (case !physical of
                  (saved,_) :: _ => Portable.pointer_eq (ty,saved)
                | [] => false) then node
              else (remember_type_hint ty node; node)
          | NONE =>
              let
                val arguments = if Type.is_vartype ty then []
                  else #Args (Type.dest_thy_typeid ty)
                val children = List.map compact_type arguments
                val node = canonical ty children
                val _ = edges := saturated_add (!edges)
                  (List.length children)
                val _ = observations := !observations + 1
                val _ = remember_type_hint ty node
                val _ = if is_small then () else
                  large_physical := (ty,node) :: !large_physical
              in node end
        end
      (* REFL only classifies the visited prefix. Never build metadata or
         even probe a cache for the unused suffix. Count exactly native
         classification visits, so this gate introduces no new refusal. *)
      fun intern root =
        let
          val memo = ref ([] : (hol_type * (bool * int)) list)
          val probes = ref maximum
          (* Optional probes stop when prepaid fuel is exhausted. The
             fallback still classifies the same visited prefix; it does
             not inspect an unused suffix or introduce a new refusal. *)
          fun find _ [] = NONE
            | find ty ((saved,result) :: rest) =
                if !probes = 0 then NONE else
                  (probes := !probes - 1;
                   if Portable.pointer_eq (ty,saved) then SOME result
                   else find ty rest)
          fun visit depth ty =
            (check depth;
             case find ty (!memo) of SOME result => result
             | NONE =>
               let
                 fun children [] n = (false,n)
                   | children (ty :: rest) n =
                       let val (poly,work) = visit (depth + 1) ty
                           val n = add_work n work
                           val _ = check n
                       in if poly then (true,n) else children rest n end
                 val result = if Type.is_vartype ty then (true,1)
                   else children (#Args (Type.dest_thy_typeid ty)) 1
                 val _ = if !probes = 0 then () else
                   memo := (ty,result) :: !memo
               in result end)
          val (_,work) = visit 1 root
        in check work end
      (* Opening/alpha comparison can inspect all annotation Types. Unlike
         REFL's classification, this is intentionally a full traversal. *)
      fun full_type ty =
        let
          fun native_admission () =
            let
              (* Metadata exhaustion must retain the first excessive
                 subtree, not a preorder prefix's maximum+1 diagnostic.
                 Stop at that subtree before visiting any further sibling. *)
              fun visit ty =
                let
                  fun children [] count = count
                    | children (ty :: rest) count =
                        let val work = add_work count (visit ty)
                            val _ = check work
                        in children rest work end
                in if Type.is_vartype ty then 1
                   else children (#Args (Type.dest_thy_typeid ty)) 1 end
            in check (visit ty) end
          val _ =
            (let
               val AdmissionTypeNode {tree_nodes, ...} =
                 metered metadata_walk ty
             in check tree_nodes end
             handle MetadataLimit => native_admission ())
        in compact_type ty end
      (* A cheap polymorphic prefix does not admit native comparison of the
         suffix. Required IDs nevertheless cover it, using only compact keys
         and exact pointer hits, with no optional-work refusal. *)
      fun type_id ty =
        let val AdmissionTypeNode {id, ...} = compact_type ty in id end
      fun raw_size limit term =
        (ignore (full_type (Term.type_of term));
         SmtReplayImport.bounded_raw_size_with_type_check
           (fn ty => if Thm.kernelid = "expknl" then ()
             else intern (#2 (Type.dom_rng ty))) limit term)
      fun admit_abstraction operation term =
        let
          val _ = case raw_size maximum term of
              SOME _ => ()
            | NONE => SmtResource.check_term_size_for "BitVector" operation
                (maximum + 1)
          fun atom_rank atom = if Term.is_var atom then 0 else 1
          fun compare_atoms (left, right) =
            case Int.compare (atom_rank left, atom_rank right) of
              EQUAL => if Term.is_var left then
                  pair_compare (String.compare, Int.compare)
                    ((Lib.fst (Term.dest_var left),
                      type_id (Term.type_of left)),
                     (Lib.fst (Term.dest_var right),
                      type_id (Term.type_of right)))
                else pair_compare (KernelSig.id_compare, Int.compare)
                  ((#Name (Term.dest_thy_constid left),
                    type_id (Term.type_of left)),
                   (#Name (Term.dest_thy_constid right),
                    type_id (Term.type_of right)))
            | order => order
          val atoms = HOLset.listItems
            (Term.all_atomsl [term] (HOLset.empty compare_atoms))
          val _ = List.app (ignore o full_type o Term.type_of) atoms
          (* The synthesized abstraction Type was admitted before raw_size
             opened anything. Nested count-only openings admit their actual
             range classification, not unused synthesized function Types. *)
        in () end
    in
      {intern = intern, metadata = metadata, type_id = type_id,
       compact_type = compact_type, full_type = full_type,
       admit_abstraction = admit_abstraction, raw_size = raw_size,
       nodes = nodes, edges = edges, physical = physical,
       observations = observations, large_physical = large_physical}
    end

  (* Canonical Type IDs may reject a mismatched pair, but cannot prove a
     matching pair equal. In particular, reject a late mismatch before TRANS
     unfolds a shared equal prefix. Successful transport still needs the
     stock kernel and retains both supplied endpoint occurrences. *)
  fun checked_leaf_transport classify_type metadata left right =
    let
      val left_type = Term.type_of left
      val right_type = Term.type_of right
      val _ = classify_type left_type
      val _ = classify_type right_type
      val same_atom = SmtReplayLeafProof.same_atom left right
      val _ = if (Term.is_var left orelse Term.is_const left) andalso
          not same_atom then raise Feedback.mk_HOL_ERR "Thm" "TRANS" ""
        else ()
      (* IDs are a negative/routing optimization, not required admission.
         In particular a cheap polymorphic prefix may hide a suffix too
         large even for a metered full DAG walk. Do not refuse its checked
         shared-variable/redex proof just because metadata is unavailable. *)
      fun summaries () =
        let
          val node as AdmissionTypeNode {id = left_id, ...} =
            metadata left_type
          val AdmissionTypeNode {id = right_id, ...} = metadata right_type
          val _ = if left_id = right_id then () else
            raise Feedback.mk_HOL_ERR "Thm" "TRANS" ""
        in SOME node end
        handle Feedback.HOL_ERR detail =>
          if SmtResource.is_resource_gate detail andalso
              String.isSubstring "skeleton-type-work"
                (Feedback.message_of detail) then NONE
          else raise Feedback.HOL_ERR detail
      val summary = summaries ()
      val large_shared = case summary of NONE => true
        | SOME (AdmissionTypeNode {tree_nodes, ...}) =>
            tree_nodes > SmtResource.max_bv_replay_term_nodes
      val large_comparison = case summary of NONE => true
        | SOME (AdmissionTypeNode {comparison_nodes, ...}) =>
            comparison_nodes > SmtReplayLeafProof.native_tree_switch
      (* Pair routing has its own bounded observations/probes. Exhaustion
         selects the checked redex route, never a semantic refusal. *)
      fun large_pair () =
        let
          exception RoutingLimit
          val remaining = ref (IntInf.fromInt
            SmtResource.max_bv_replay_term_nodes)
          fun debit amount =
            if amount <= !remaining then remaining := !remaining - amount
            else raise RoutingLimit
        in SmtReplayLeafProof.large_type_pair debit left_type right_type
          handle RoutingLimit => true
        end
    in
      if Thm.kernelid = "expknl" andalso large_shared andalso
         Portable.pointer_eq (left_type, right_type) andalso
         Term.is_var left andalso Term.is_var right andalso same_atom then
        SmtReplayLeafProof.shared_variable left right
      else if large_comparison andalso same_atom andalso
          (Thm.kernelid = "expknl" orelse large_pair ()) then
        SmtReplayLeafProof.redex_equality left right
      else Thm.TRANS (Thm.REFL left) (Thm.REFL right)
    end

  (* Optional-cache admission has no theorem/procedure side effects. Only
     these local transport gates become misses; actual proving exceptions
     and timeouts still escape unchanged. *)
  fun cache_admission_refusal detail =
    SmtResource.is_resource_gate detail andalso
    (String.isSubstring "skeleton-type-work" (Feedback.message_of detail)
     orelse String.isSubstring "skeleton-cache-abstraction"
       (Feedback.message_of detail))

  (* Preserve native destructor names: these children also define the
     original skeleton DAG metric, including sharing outside binders.
     Mandatory measurement/dispatch retains the binder-opening diagnostic;
     optional cache admission uses its separate abstraction gate below.
     Name-only clash handling avoids native annotation comparisons. *)
  fun admitted_dest_abs term =
    let
      val admission = new_type_admission_context ()
      (* Experimental count_body/dest_abs only returns the stored body;
         it does not run standard's range-Type classification. *)
      fun before_open ty = if Thm.kernelid = "expknl" then ()
        else #intern admission (#2 (Type.dom_rng ty))
      val maximum = SmtResource.max_bv_replay_term_nodes
      val _ = case SmtReplayImport.bounded_raw_size_with_type_check
          before_open maximum term of SOME _ => ()
        | NONE => SmtResource.check_term_size_for "BitVector"
            "binder-opening" (maximum + 1)
    in SmtReplayImport.dest_abs_preserving_names term end

  (* Semantic comparison is independent of optional cache reservations.
     Applications and Types are compared nodewise; only the public binder
     island uses native comparison, after BOTH operands have been admitted.
     Comparison results are lookup keys, never theorem evidence. *)
  fun new_semantic_order () =
    let
      val count = 4093
      (* A shallow structural hash sends every suffix of a homogeneous
         spine to one bucket. A flat list of term PAIRS there is quadratic
         even for lookup. Assign physical IDs in single-term buckets, then
         index the pair memo by integer pairs. IDs only route memo entries;
         the semantic order below still determines every returned result. *)
      val physical = Array.array (count, [] : (term * int) list)
      val next_physical = ref 0
      fun physical_id term =
        let val bucket = SmtResource.pointer_bucket count term in
          case List.find (fn (saved, _) =>
              Portable.pointer_eq (term, saved))
              (Array.sub (physical, bucket)) of
            SOME (_, id) => id
          | NONE =>
              let val id = !next_physical in
                next_physical := id + 1;
                Array.update (physical, bucket,
                  (term, id) :: Array.sub (physical, bucket));
                id
              end
        end
      val pairs = SmtResource.new_key_map
        (Lib.pair_compare (Int.compare,Int.compare))
        SmtResource.integer_pair_hash
      val pair_lookup = #peek pairs
      val pair_save = #insert pairs
      val type_pairs = Array.array
        (count, [] : (hol_type * hol_type * order) list)
      fun type_bucket ty =
        if Type.is_vartype ty then 0 else
          KernelSig.epoch_of (#Tyop (Type.dest_thy_typeid ty)) mod count
      (* Do not intern an entire annotation just to discover a different
         outer Tyop. No native Type comparison occurs in this programme. *)
      fun types (left, right) =
        if Portable.pointer_eq (left, right) then EQUAL
        else
          let
            val bucket = (type_bucket left + type_bucket right) mod count
          in
            case List.find (fn (l, r, _) =>
                Portable.pointer_eq (left, l) andalso
                Portable.pointer_eq (right, r))
                (Array.sub (type_pairs, bucket)) of
              SOME (_, _, result) => result
            | NONE =>
                let
                  val result =
                    if Type.is_vartype left then
                      if Type.is_vartype right then String.compare
                        (Type.dest_vartype left, Type.dest_vartype right)
                      else LESS
                    else if Type.is_vartype right then GREATER
                    else
                      (case KernelSig.id_compare
                          (#Tyop (Type.dest_thy_typeid left),
                           #Tyop (Type.dest_thy_typeid right)) of
                         EQUAL => list_compare types
                           (#2 (Type.dest_type left),
                            #2 (Type.dest_type right))
                       | result => result)
                  val _ = Array.update (type_pairs, bucket,
                    (left, right, result) :: Array.sub (type_pairs, bucket))
                in result end
          end
      fun bound _ [] _ = NONE
        | bound term (variable :: rest) index =
            if #1 (Term.dest_var term) = #1 (Term.dest_var variable) andalso
                types (Term.type_of term, Term.type_of variable) = EQUAL
            then SOME index else bound term rest (index + 1)
      fun rank env term = if Term.is_var term then
          (case bound term env 0 of NONE => 0 | SOME _ => 1)
        else if Term.is_const term then 2
        else if Term.is_comb term then 3 else 4
      fun compare_env left_env right_env (left, right) =
        if null left_env andalso null right_env andalso
            Portable.pointer_eq (left, right) then EQUAL
        else
          let
            val key = if null left_env andalso null right_env then
                SOME (physical_id left, physical_id right)
              else NONE
          in
            case Option.mapPartial
                pair_lookup key of
              SOME result => result
            | NONE =>
                let
                  val result = case Int.compare
                      (rank left_env left, rank right_env right) of
                      EQUAL =>
                        if Term.is_comb left then
                          (case compare_env left_env right_env
                              (Term.rator left, Term.rator right) of
                             EQUAL => compare_env left_env right_env
                               (Term.rand left, Term.rand right)
                           | result => result)
                        else if Term.is_var left then
                          (case (bound left left_env 0,
                                 bound right right_env 0) of
                             (SOME l, SOME r) => Int.compare (l, r)
                           | _ =>
                             case String.compare
                                 (#1 (Term.dest_var left),
                                  #1 (Term.dest_var right)) of
                               EQUAL => types
                                 (Term.type_of left, Term.type_of right)
                             | result => result)
                        else if Term.is_const left then
                          (case KernelSig.id_compare
                              (#Name (Term.dest_thy_constid left),
                               #Name (Term.dest_thy_constid right)) of
                             EQUAL => types
                               (Term.type_of left, Term.type_of right)
                           | result => result)
                        else
                          (case types
                              (#1 (Type.dom_rng (Term.type_of left)),
                               #1 (Type.dom_rng (Term.type_of right))) of
                             EQUAL =>
                               let
                                 val (lv, lb) = admitted_dest_abs left
                                 val (rv, rb) = admitted_dest_abs right
                               in compare_env (lv :: left_env)
                                 (rv :: right_env) (lb, rb) end
                           | result => result)
                    | result => result
                  val _ = case key of NONE => ()
                    | SOME key => pair_save (key,result)
                in result end
          end
    in compare_env [] [] end

  fun new_cache_index maximum =
    let
      val admission = new_type_admission_context ()
      fun binder term =
        (#admit_abstraction admission "skeleton-cache-abstraction" term;
         true)
        handle Feedback.HOL_ERR detail =>
          if cache_admission_refusal detail then false
          else raise Feedback.HOL_ERR detail
      fun type_id ty = (#intern admission ty; #type_id admission ty)
      val index = SmtResource.new_bounded_term_index_with_types
        {admit_binder = binder, intern_type = SOME type_id} maximum
    in fn term => index term handle Feedback.HOL_ERR detail =>
      if cache_admission_refusal detail then NONE
      else raise Feedback.HOL_ERR detail
    end

  fun new_cache_order _ = new_semantic_order ()

  fun term_children term =
    if Term.is_comb term then [Term.rator term, Term.rand term]
    else if Term.is_abs term then [#2 (admitted_dest_abs term)] else []

  fun term_measure root =
    let
      fun general () =
        let
          val saved = ref (Redblackmap.mkDict (new_semantic_order ()))
          fun visit term = case Redblackmap.peek (!saved, term) of
              SOME size => size
            | NONE =>
                let val size = List.foldl
                      (fn (child, n) => saturated_add n (visit child))
                      1 (term_children term)
                in saved:=Redblackmap.insert (!saved,term,size); size end
          val size = visit root
        in {tree_nodes=size,dag_nodes=Redblackmap.numItems (!saved)} end
      exception GeneralMeasure
      (* Positive hints only: bound probes even when every leaf has a fresh
         annotation. Eviction just repeats the bounded small-Type check. *)
      val types = Array.array (16, NONE : Type.hol_type option)
      val next_type = ref 0
      fun inspect term =
        if Term.is_abs term then raise GeneralMeasure
        else if Term.is_var term orelse Term.is_const term then
          let val ty=Term.type_of term
          in if Array.exists (fn SOME saved =>
                Portable.pointer_eq (saved,ty) | NONE => false) types then ()
            else let
              val remaining=ref 64
              fun small ty =
                (remaining:= !remaining-1;
                 if !remaining<0 then raise GeneralMeasure
                 else if Type.is_vartype ty then ()
                 else List.app small (#Args (Type.dest_thy_type ty)))
              val _ = small ty
            in
              Array.update (types, !next_type, SOME ty);
              next_type := (!next_type + 1) mod Array.length types
            end
          end
        else ()
      fun fast () =
        let
          (* For binder-free terms structural IDs give exactly the same
             equivalence classes and saturated sizes as the general order.
             Inspect before each native Type comparison, in the original
             physical DFS order. This only admits the optimization; binders,
             large annotations and the first node beyond the original bound
             still use the original general measurement. *)
          val observed = ref 0
          fun inspect_before term =
            (inspect term; observed := !observed+1;
             if !observed > SmtResource.max_bv_replay_term_nodes then
               raise GeneralMeasure else ())
        in SmtResource.term_measure_with_inspector inspect_before root end
    in fast () handle GeneralMeasure => general () end

  fun tree_nodes term = #tree_nodes (term_measure term)
  fun dag_nodes term = #dag_nodes (term_measure term)

  fun make_context_with_index_limit index_limit procedures fallback =
    let
      fun order ((name, role, id), (name', role', id')) =
        case String.compare (name, name') of
          EQUAL => (case Int.compare (role, role') of
              EQUAL => Int.compare (id, id') | result => result)
        | result => result
      fun fresh_index () =
        new_cache_index index_limit
      val signature_witness = ref (cache_signature ())
      val index = ref (fresh_index ())
      val cache_generation = ref (ref ())
      val atom_cache = ref (Redblackmap.mkDict order)
      fun refresh_caches () =
        if cache_signature_matches (!signature_witness) then () else
          (cache_generation := ref ();
           index := fresh_index ();
           atom_cache := Redblackmap.mkDict order;
           signature_witness := cache_signature ())
    in Context
      {procedures = procedures, fallback = fallback,
       atom_index = fn term => (refresh_caches (); (!index) term),
       atom_cache = atom_cache, cache_generation = cache_generation,
       refresh_caches = refresh_caches}
    end

  fun make_context procedures fallback = make_context_with_index_limit
    SmtResource.max_bv_replay_term_nodes procedures fallback

  fun new_context procedures = make_context procedures NONE

  fun new_context_with_index_limit maximum procedures =
    make_context_with_index_limit maximum procedures NONE

  fun new_dynamic_context procedures fallback =
    make_context procedures (SOME fallback)

  (* Build left = right one physical node at a time.  Both endpoint anchors
     compare only a newly built outer node whose children already have the
     requested endpoint pointers.  Structural cache collisions use separate
     pointer buckets. Optional cache transport additionally retains its
     caller's fixed DAG allowance. Required transport adds no new cutoff. *)
  fun nodewise_equality_with_limit allowance left right =
    let
      val type_admission = new_type_admission_context ()
      fun admit_type term =
        ignore (#intern type_admission (Term.type_of term))
      fun checked_refl term = (admit_type term; Thm.REFL term)
      fun inspect term =
        if Term.is_abs term then
          #admit_abstraction type_admission
            "skeleton-cache-abstraction" term
        else ()
      val _ = case allowance of
          NONE => ()
        | SOME maximum =>
            if SmtResource.dag_nodes_up_to_with_inspector
                inspect maximum left <= maximum then ()
            else raise REANCHOR_LIMIT
      val compared = ref 0
      val bucket_count = 4093
      (* Small exact transports need few buckets. Preserve the routes,
         allocating backing blocks only when an entry is inserted. *)
      val block_size = 256
      val cache = Array.array
        ((bucket_count+block_size-1) div block_size,
         NONE : (term * term * thm) list Array.array option)
      fun cached bucket =
        case Array.sub (cache,bucket div block_size) of
          NONE => []
        | SOME block => Array.sub (block,bucket mod block_size)
      fun hash_string string =
        CharVector.foldl (fn (character, hash) =>
          (hash * 33 + Char.ord character) mod bucket_count) 17 string
      fun shallow_hash 0 term =
            if Term.is_var term then hash_string (#1 (Term.dest_var term))
            else if Term.is_const term then
              hash_string (#Name (Term.dest_thy_const term))
            else if Term.is_abs term then 5 else 7
        | shallow_hash depth term =
            if Term.is_comb term then
              (41 * shallow_hash (depth - 1) (Term.rator term) +
               67 * shallow_hash (depth - 1) (Term.rand term) + 11) mod
                bucket_count
            (* Routing is not binder admission. In particular the right
               endpoint has not passed inspect yet. Keep both bodies opaque
               until compute admits the matching abstraction pair. *)
            else shallow_hash 0 term
      fun pair_bucket (left, right) =
        (97 * shallow_hash 3 left + shallow_hash 3 right) mod bucket_count
      fun visit (left, right) =
        (* A shared application needs only result-Type work, not the
           annotations of descendants that this shortcut never visits. *)
        if Portable.pointer_eq (left, right) then checked_refl left
        else
          let val bucket = pair_bucket (left, right) in
          case List.find
              (fn (saved_left, saved_right, _) =>
                Portable.pointer_eq (left, saved_left) andalso
                Portable.pointer_eq (right, saved_right))
              (cached bucket) of
            SOME (_, _, theorem) => theorem
          | NONE => compute (left, right)
          end
      and compute (left, right) =
        let
          val _ = compared := !compared + 1
          val _ = case allowance of NONE => ()
            | SOME maximum =>
                if !compared <= maximum then () else raise REANCHOR_LIMIT
          val theorem =
            if Term.is_comb left andalso Term.is_comb right then
              let
                val (left_operator, left_operand) = Term.dest_comb left
                val (right_operator, right_operand) = Term.dest_comb right
                val _ = admit_type left
                val _ = admit_type right
              in
                if Portable.pointer_eq (left_operator,right_operator)
                    andalso Portable.pointer_eq (left_operand,right_operand)
                then Thm.TRANS (checked_refl left) (checked_refl right)
                else anchor_right right (anchor_left left
                  (Thm.MK_COMB
                    (visit (left_operator, right_operator),
                     visit (left_operand, right_operand))))
              end
            else if Term.is_abs left andalso Term.is_abs right then
              let
                val _ = #admit_abstraction type_admission
                  "skeleton-cache-abstraction" left
                val _ = #admit_abstraction type_admission
                  "skeleton-cache-abstraction" right
              in Thm.TRANS (Thm.REFL left) (Thm.REFL right) end
            else if (Term.is_var left andalso Term.is_var right) orelse
                    (Term.is_const left andalso Term.is_const right) then
              checked_leaf_transport (#intern type_admission)
                (#metadata type_admission) left right
            else
              (* Different constructors cannot be alpha-equal. Preserve
                 TRANS's mismatch error without constructing unadmitted
                 reflexivity theorems for the right endpoint. *)
              raise Feedback.mk_HOL_ERR "Thm" "TRANS" ""
          val bucket = pair_bucket (left, right)
          val index = bucket div block_size
          val block = case Array.sub (cache,index) of
              SOME block => block
            | NONE =>
                let val block = Array.array
                      (Int.min (block_size,bucket_count-index*block_size),[])
                    val _ = Array.update (cache,index,SOME block)
                in block end
          val offset = bucket mod block_size
          val _ = Array.update
            (block,offset,(left,right,theorem)::Array.sub (block,offset))
        in
          theorem
        end
      val theorem = visit (left, right)
      val (actual_left, actual_right) =
        boolSyntax.dest_eq (Thm.concl theorem)
      val _ =
        if Portable.pointer_eq (left, actual_left) andalso
           Portable.pointer_eq (right, actual_right) then ()
        else raise ERR "bounded_nodewise_equality"
          "node-wise transport lost an endpoint occurrence"
    in
      theorem
    end

  fun bounded_nodewise_equality maximum =
    nodewise_equality_with_limit (SOME maximum)

  (* Required transport must not turn an optional cache allowance into a
     semantic refusal. Application work is nodewise; native binder/Type
     work retains its original admission in the common implementation. *)
  val nodewise_equality = nodewise_equality_with_limit NONE

  fun exact_conclusion target theorem =
    if Portable.pointer_eq (Thm.concl theorem, target) then theorem
    else Thm.EQ_MP (nodewise_equality (Thm.concl theorem) target) theorem

  fun nodewise_exact_left occurrence theorem =
    let val left = boolSyntax.lhs (Thm.concl theorem) in
      if Portable.pointer_eq (occurrence, left) then theorem
      else Thm.TRANS (nodewise_equality occurrence left) theorem
    end

  fun exact_equality left right theorem =
    let
      val theorem = nodewise_exact_left left theorem
      val endpoint = boolSyntax.rhs (Thm.concl theorem)
    in
      if Portable.pointer_eq (endpoint, right) then theorem
      else Thm.TRANS theorem (nodewise_equality endpoint right)
    end

  fun reanchor_cached_theorem occurrence theorem =
    let
      val (cached_left, _) = boolSyntax.dest_eq (Thm.concl theorem)
      val occurrence_equality = bounded_nodewise_equality
        SmtResource.max_skeleton_replay_dag_nodes occurrence cached_left
    in
      Thm.TRANS occurrence_equality theorem
    end

  fun exact_left occurrence theorem =
    let val (left, _) = boolSyntax.dest_eq (Thm.concl theorem)
    in
      if Portable.pointer_eq (occurrence, left) then theorem
      else reanchor_cached_theorem occurrence theorem
    end

  fun validate_theorem_with (_ : term -> int option)
      procedure atom theorem =
    let
      (* A cache index (including an exhausted one) grants no admission. *)
      val order = new_semantic_order ()
      fun same left right = order (left, right) = EQUAL
      val _ =
        if List.null (Thm.hyp theorem) then ()
        else raise ERR "validate_theorem"
          ("atom procedure " ^ procedure ^ " returned hypotheses")
      val (left, right) = boolSyntax.dest_eq (Thm.concl theorem)
        handle Feedback.HOL_ERR _ =>
          raise ERR "validate_theorem"
            ("atom procedure " ^ procedure ^
             " did not return an equality")
      val _ =
        if same left atom then ()
        else raise ERR "validate_theorem"
          ("atom procedure " ^ procedure ^ " returned the wrong left side")
      val _ =
        if Term.type_of right = Type.bool then ()
        else raise ERR "validate_theorem"
          ("atom procedure " ^ procedure ^ " returned a non-Boolean residue")
      val _ =
        if same left right then
          raise ERR "validate_theorem"
            ("atom procedure " ^ procedure ^ " made no progress")
        else ()
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" ("atom:" ^ procedure) theorem
    in
      theorem
    end

  fun validate_theorem procedure atom theorem =
    validate_theorem_with
      (new_cache_index SmtResource.max_bv_replay_term_nodes)
      procedure atom theorem

  fun procedure_names (Context {procedures, fallback, ...}) =
    List.map #name procedures @
      (case fallback of NONE => [] | SOME procedure => [#name procedure])

  fun procedure_named procedures name =
    case List.filter (fn procedure => #name procedure = name) procedures of
      [procedure] => procedure
    | [] => raise ERR "procedure_named"
        ("unknown classified atom owner: " ^ name)
    | _ => raise ERR "procedure_named"
        ("duplicate classified atom owner: " ^ name)

  (* Force HolSat's checked equality-to-T path; EQT_ELIM recovers the
     requested theorem by a kernel inference. *)
  fun checked_sat_prove sat_target =
    let
      val request = boolSyntax.mk_eq (sat_target, boolSyntax.T)
      val equality = HolSatLib.SAT_PROVE request
      val _ =
        if List.null (Thm.hyp equality) then ()
        else raise ERR "checked_sat_prove"
          "checked SAT equality has hypotheses"
      val equality = exact_conclusion request equality
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "checked-sat-equality" equality
      val theorem = Drule.EQT_ELIM equality
      val theorem = exact_conclusion sat_target theorem
    in
      theorem
    end

  val idempotent_variable = Term.mk_var ("p", Type.bool)
  val disj_idempotent = tautLib.TAUT_PROVE
    (boolSyntax.mk_eq
      (boolSyntax.mk_disj (idempotent_variable, idempotent_variable),
       idempotent_variable))
  val conj_idempotent = tautLib.TAUT_PROVE
    (boolSyntax.mk_eq
      (boolSyntax.mk_conj (idempotent_variable, idempotent_variable),
       idempotent_variable))

  val polarity_variable = idempotent_variable
  val polarity_negative = boolSyntax.mk_neg polarity_variable
  val polarity_rules = List.map tautLib.TAUT_PROVE
    [boolSyntax.mk_eq
       (boolSyntax.mk_conj (polarity_variable,polarity_negative),boolSyntax.F),
     boolSyntax.mk_eq
       (boolSyntax.mk_conj (polarity_negative,polarity_variable),boolSyntax.F),
     boolSyntax.mk_eq
       (boolSyntax.mk_disj (polarity_variable,polarity_negative),boolSyntax.T),
     boolSyntax.mk_eq
       (boolSyntax.mk_disj (polarity_negative,polarity_variable),boolSyntax.T),
     boolSyntax.mk_eq
       (boolSyntax.mk_eq (polarity_variable,polarity_negative),boolSyntax.F),
     boolSyntax.mk_eq
       (boolSyntax.mk_eq (polarity_negative,polarity_variable),boolSyntax.F)];

  val gate_reduction_conv = Conv.FIRST_CONV
    (List.map Conv.REWR_CONV
      (polarity_rules @ (boolTheory.REFL_CLAUSE :: boolTheory.COND_ID ::
       List.concat (List.map (Drule.CONJUNCTS o Drule.SPEC_ALL)
         [boolTheory.AND_CLAUSES, boolTheory.OR_CLAUSES,
          boolTheory.NOT_CLAUSES, boolTheory.IMP_CLAUSES,
          boolTheory.EQ_CLAUSES, boolTheory.COND_CLAUSES]))))

  datatype raw_key =
      RawVariable of string * int
    | RawConstant of KernelSig.kernelid * int
    | RawApplication of int * int

  fun raw_key_rank key =
    case key of RawVariable _ => 0 | RawConstant _ => 1 | RawApplication _ => 2

  fun raw_key_compare (left, right) =
    case Int.compare (raw_key_rank left, raw_key_rank right) of
      EQUAL =>
        (case (left, right) of
           (RawVariable (left_name, left_type),
            RawVariable (right_name, right_type)) =>
             (case String.compare (left_name, right_name) of
                EQUAL => Int.compare (left_type, right_type)
              | order => order)
         | (RawConstant (left_id, left_type),
            RawConstant (right_id, right_type)) =>
             (case KernelSig.id_compare (left_id, right_id) of
                EQUAL => Int.compare (left_type, right_type)
              | order => order)
         | (RawApplication (left_operator, left_operand),
            RawApplication (right_operator, right_operand)) =>
             pair_compare (Int.compare, Int.compare)
               ((left_operator, left_operand),
                (right_operator, right_operand))
         | _ => EQUAL)
    | order => order

  datatype graph_kind =
      GraphTrue
    | GraphFalse
    | GraphAtom of int
    | GraphNegation of int
    | GraphConjunction of int * int
    | GraphDisjunction of int * int
    | GraphImplication of int * int
    | GraphEquality of int * int
    | GraphConditional of int * int * int

  fun graph_kind_rank kind =
    case kind of
      GraphTrue => 0 | GraphFalse => 1 | GraphAtom _ => 2 |
      GraphNegation _ => 3 | GraphConjunction _ => 4 |
      GraphDisjunction _ => 5 | GraphImplication _ => 6 |
      GraphEquality _ => 7 | GraphConditional _ => 8

  fun graph_kind_compare (left, right) =
    case Int.compare (graph_kind_rank left, graph_kind_rank right) of
      EQUAL =>
        (case (left, right) of
           (GraphAtom left_id, GraphAtom right_id) =>
             Int.compare (left_id, right_id)
         | (GraphNegation left_id, GraphNegation right_id) =>
             Int.compare (left_id, right_id)
         | (GraphConjunction left_ids, GraphConjunction right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphDisjunction left_ids, GraphDisjunction right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphImplication left_ids, GraphImplication right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphEquality left_ids, GraphEquality right_ids) =>
             pair_compare (Int.compare, Int.compare) (left_ids, right_ids)
         | (GraphConditional (left_test, left_yes, left_no),
            GraphConditional (right_test, right_yes, right_no)) =>
             list_compare Int.compare
               ([left_test, left_yes, left_no],
                [right_test, right_yes, right_no])
         | _ => EQUAL)
    | order => order

  datatype raw_node = RawNode of
    {id : int, representative : term, equality : thm option ref,
     tree_nodes : int, ty : hol_type}

  datatype graph_node = GraphNode of
    {id : int, kind : graph_kind, representative : term,
     equality : thm, tree_nodes : int}

  (* The graph uses kernel declaration identities and canonical child IDs as
     lookup keys.  Terms remain the proof evidence: every reuse is justified
     by a checked equality with the current occurrence as its exact left
     endpoint.  Whole abstractions form the public-kernel boundary and are
     compared only after bounded raw and type-work admission. *)
  fun build_cnf_graph_mode reduce_gates skeleton =
    let
      val maximum = SmtResource.max_bv_replay_term_nodes
      val type_admission = new_type_admission_context ()
      val term_order = new_semantic_order ()
      fun intern_type ty =
        (#intern type_admission ty; #compact_type type_admission ty)
      fun type_id (AdmissionTypeNode {id, ...}) = id
      val admit_type = #intern type_admission
      val admit_abstraction = #admit_abstraction type_admission
      val type_nodes = #nodes type_admission
      val type_edges = #edges type_admission
      val type_observations = #observations type_admission
      fun raw_hash (RawVariable (_,ty)) = Word.fromInt ty
        | raw_hash (RawConstant (id,ty)) =
            SmtResource.integer_pair_hash (KernelSig.epoch_of id,ty)
        | raw_hash (RawApplication children) =
            SmtResource.integer_pair_hash children
      val raw_ids = SmtResource.new_key_map raw_key_compare raw_hash
      val physical_bucket_count = 4093
      val raw_physical = Array.array
        (physical_bucket_count, [] : (term * raw_node) list)
      val physical_bucket = SmtResource.pointer_bucket physical_bucket_count
      fun physical_find buckets term =
        List.find
          (fn (saved, _) => Portable.pointer_eq (term, saved))
          (Array.sub (buckets, physical_bucket term))
      fun physical_insert buckets term node =
        let val bucket = physical_bucket term in
          Array.update (buckets, bucket,
            (term, node) :: Array.sub (buckets, bucket))
        end
      val abstractions = ref ([] : raw_node list)
      val next_raw_id = ref 0
      val raw_nodes = ref 0
      val raw_edges = ref 0
      val transport_nodes = ref 0
      val transport_time = ref Time.zeroTime
      fun fresh_raw representative equality tree_nodes ty =
        let
          val result = RawNode
            {id = !next_raw_id, representative = representative,
             equality = ref equality, tree_nodes = tree_nodes, ty = ty}
        in
          next_raw_id := !next_raw_id + 1;
          raw_nodes := !raw_nodes + 1;
          result
        end
      fun raw_id (RawNode {id, ...}) = id
      fun raw_representative (RawNode {representative, ...}) = representative
      (* NONE is known reflexivity at an already admitted representative.
         Structural reanchoring remains eager, including all its guards. *)
      fun raw_equality (RawNode {equality,representative,...}) =
        case !equality of SOME theorem => theorem
        | NONE => let val theorem = Thm.REFL representative
                  in equality := SOME theorem; theorem end
      fun raw_tree_nodes (RawNode {tree_nodes, ...}) = tree_nodes
      fun raw_type (RawNode {ty, ...}) = ty
      fun checked_leaf_equality operation occurrence representative =
        let
          val timer = Timer.startRealTimer ()
          val theorem = checked_leaf_transport (#intern type_admission)
            (#metadata type_admission) occurrence representative
          val _ = transport_nodes := !transport_nodes + 1
          val _ = transport_time := Time.+
            (!transport_time, Timer.checkRealTimer timer)
        in
          theorem
        end
      fun canonical_raw key occurrence representative initial_equality
          tree_nodes ty make_equality =
        case #peek raw_ids key of
          SOME saved =>
            let
              val representative = raw_representative saved
              val equality = make_equality representative
            in
              RawNode {id = raw_id saved, representative = representative,
                equality = ref (SOME equality),
                tree_nodes = raw_tree_nodes saved,
                ty = raw_type saved}
            end
        | NONE =>
            let
              val saved = fresh_raw representative initial_equality
                tree_nodes ty
              val _ = #insert raw_ids (key,saved)
            in
              saved
            end
      fun intern_abstraction occurrence =
        let
          val size =
            case #raw_size type_admission maximum occurrence of
              SOME size => size
            | NONE =>
                (SmtResource.check_term_size_for "BitVector"
                   "skeleton-graph-abstraction" (maximum + 1); 0)
          val ty = Term.type_of occurrence
          val _ = admit_abstraction "skeleton-graph-abstraction" occurrence
          fun find [] = NONE
            | find (saved :: rest) =
                let val representative = raw_representative saved
                in
                  admit_abstraction
                    "skeleton-graph-abstraction" representative;
                  if Term.aconv occurrence representative then SOME saved
                  else find rest
                end
        in
          case find (!abstractions) of
            SOME saved =>
              RawNode
                {id = raw_id saved,
                 representative = raw_representative saved,
                 equality = ref (SOME (checked_leaf_equality
                   "skeleton-graph-abstraction" occurrence
                   (raw_representative saved))),
                 tree_nodes = raw_tree_nodes saved, ty = raw_type saved}
          | NONE =>
              let
                val (_, body) = Term.dest_abs occurrence
                val _ = ignore (intern_raw body)
                val _ = raw_edges := saturated_add (!raw_edges) 1
                val saved = fresh_raw occurrence NONE size ty
              in abstractions := saved :: !abstractions; saved end
        end
      and intern_raw occurrence =
        case physical_find raw_physical occurrence of
          SOME (_, saved) => saved
        | NONE =>
            let
              val saved =
                if Term.is_var occurrence then
                  let
                    val (name, ty) = Term.dest_var occurrence
                    val type_id = type_id (intern_type ty)
                  in
                    canonical_raw (RawVariable (name, type_id)) occurrence
                      occurrence NONE 1 ty
                      (checked_leaf_equality "skeleton-graph-variable"
                         occurrence)
                  end
                else if Term.is_const occurrence then
                  let
                    val ty = Term.type_of occurrence
                    val type_id = type_id (intern_type ty)
                    val key = RawConstant
                      (#Name (Term.dest_thy_constid occurrence), type_id)
                  in
                    canonical_raw key occurrence occurrence
                      NONE 1 ty
                      (checked_leaf_equality "skeleton-graph-constant"
                         occurrence)
                  end
                else if Term.is_comb occurrence then
                  let
                    val (operator, operand) = Term.dest_comb occurrence
                    val operator_node = intern_raw operator
                    val operand_node = intern_raw operand
                    val key = RawApplication
                      (raw_id operator_node, raw_id operand_node)
                    val tree_nodes = saturated_add 1
                      (saturated_add (raw_tree_nodes operator_node)
                        (raw_tree_nodes operand_node))
                    fun equality representative =
                      let
                        val _ = admit_type (raw_type operator_node)
                        val _ = admit_type (raw_type operand_node)
                        val congruence = anchor_left occurrence
                          (Thm.MK_COMB
                            (raw_equality operator_node,
                             raw_equality operand_node))
                      in
                        anchor_right representative congruence
                      end
                    val ty = Lib.snd (Type.dom_rng (raw_type operator_node))
                    (* An operator's polymorphic domain can hide a ground
                       range. Admit the actual result before any proof. *)
                    val _ = admit_type ty
                    val children_unchanged =
                      Portable.pointer_eq
                        (operator, raw_representative operator_node) andalso
                      Portable.pointer_eq
                        (operand, raw_representative operand_node)
                    val (candidate,candidate_equality) =
                      if children_unchanged then (occurrence,NONE)
                      else
                        let
                          val _ = admit_type (raw_type operator_node)
                          val _ = admit_type (raw_type operand_node)
                          val theorem = anchor_left occurrence
                            (Thm.MK_COMB
                              (raw_equality operator_node,
                               raw_equality operand_node))
                        in (boolSyntax.rhs (Thm.concl theorem),SOME theorem) end
                    val _ = raw_edges := saturated_add (!raw_edges) 2
                  in
                    canonical_raw key occurrence candidate candidate_equality
                      tree_nodes ty equality
                  end
                else if Term.is_abs occurrence then
                  intern_abstraction occurrence
                else raise ERR "build_cnf_graph"
                  "unknown raw term constructor"
              val _ = physical_insert raw_physical occurrence saved
            in
              saved
            end
      fun graph_hash kind =
        let
          val code = Word.fromInt (graph_kind_rank kind)
          fun add (hash,id) = Word.+ (Word.* (hash,0w37),Word.fromInt id)
          fun pair (left,right) = add (add (code,left),right)
        in case kind of
            GraphTrue => code | GraphFalse => code
          | GraphAtom id => add (code,id)
          | GraphNegation id => add (code,id)
          | GraphConjunction ids => pair ids
          | GraphDisjunction ids => pair ids
          | GraphImplication ids => pair ids
          | GraphEquality ids => pair ids
          | GraphConditional (test,yes,no) => add (pair (test,yes),no)
        end
      val graph_ids = SmtResource.new_key_map graph_kind_compare graph_hash
      val graph_physical = Array.array
        (physical_bucket_count, [] : (term * graph_node) list)
      val graph_observations = ref 0
      val graph_entries = ref ([] : graph_node list)
      val next_graph_id = ref 0
      val graph_edges = ref 0
      val residual_atoms = ref 0
      fun graph_id (GraphNode {id, ...}) = id
      fun graph_representative (GraphNode {representative, ...}) = representative
      fun graph_equality (GraphNode {equality, ...}) = equality
      fun graph_tree_nodes (GraphNode {tree_nodes, ...}) = tree_nodes
      fun add_graph kind representative equality tree_nodes =
        case #peek graph_ids kind of
          SOME saved =>
            GraphNode
              {id = graph_id saved, kind = kind,
               representative = graph_representative saved,
               equality = anchor_right (graph_representative saved) equality,
               tree_nodes = graph_tree_nodes saved}
        | NONE =>
            let
              val saved = GraphNode
                {id = !next_graph_id, kind = kind,
                 representative = representative, equality = equality,
                 tree_nodes = tree_nodes}
            in
              next_graph_id := !next_graph_id + 1;
              #insert graph_ids (kind,saved);
              graph_entries := saved :: !graph_entries;
              saved
            end
      fun connective_kind term ids =
        if boolSyntax.is_neg term then GraphNegation (hd ids)
        else if boolSyntax.is_conj term then
          GraphConjunction (List.nth (ids, 0), List.nth (ids, 1))
        else if boolSyntax.is_disj term then
          GraphDisjunction (List.nth (ids, 0), List.nth (ids, 1))
        else if boolSyntax.is_imp term then
          GraphImplication (List.nth (ids, 0), List.nth (ids, 1))
        else if boolSyntax.is_cond term then
          GraphConditional
            (List.nth (ids, 0), List.nth (ids, 1), List.nth (ids, 2))
        else GraphEquality (List.nth (ids, 0), List.nth (ids, 1))
      fun reduce_gate rebuilt children =
        let
          val variables = ref (Redblackmap.mkDict Int.compare)
          val substitution = ref []
          fun plain id representative =
            case Redblackmap.peek (!variables,id) of
                SOME variable => variable
              | NONE => let val variable=Term.genvar Type.bool
                in variables:=Redblackmap.insert (!variables,id,variable);
                   substitution:=(variable |-> representative):: !substitution;
                   variable end
          (* Preserve a child's literal polarity in this small schema.
             Underlying graph IDs retain aliases; actual operands enter only
             through the existing checked native substitution below. *)
          fun abstract (node as GraphNode {id,kind,representative,...}) =
            case kind of
                GraphTrue => boolSyntax.T
              | GraphFalse => boolSyntax.F
              | GraphNegation child => boolSyntax.mk_neg
                  (plain child (boolSyntax.dest_neg representative))
              | _ => plain id representative
          val head = #1 (boolSyntax.strip_comb rebuilt)
          val schematic = Term.list_mk_comb
            (head, List.map abstract children)
          val theorem = Conv.QCONV
            (Conv.TRY_CONV gate_reduction_conv) schematic
        in anchor_left rebuilt (Thm.INST (!substitution) theorem) end
      fun visit occurrence =
        case physical_find graph_physical occurrence of
          SOME (_, saved) => saved
        | NONE =>
            let
              val saved =
                if Term.aconv occurrence boolSyntax.T then
                  add_graph GraphTrue occurrence (Thm.REFL occurrence) 1
                else if Term.aconv occurrence boolSyntax.F then
                  add_graph GraphFalse occurrence (Thm.REFL occurrence) 1
                else
                  case skeleton_children occurrence of
                    NONE =>
                      let
                        val raw = intern_raw occurrence
                        val _ = residual_atoms := !residual_atoms + 1
                      in
                        add_graph (GraphAtom (raw_id raw))
                          (raw_representative raw) (raw_equality raw)
                          (raw_tree_nodes raw)
                      end
                  | SOME [] => raise ERR "build_cnf_graph"
                      "unexpected propositional leaf"
                  | SOME children =>
                      let
                        val child_nodes = List.map visit children
                        val child_ids = List.map graph_id child_nodes
                        val congruence = anchor_left occurrence
                          (connective_congruence occurrence
                            (List.map graph_equality child_nodes))
                        val rebuilt = boolSyntax.rhs (Thm.concl congruence)
                        val tree_nodes = saturated_add 1
                          (List.foldl
                            (fn (node, count) => saturated_add count
                              (graph_tree_nodes node)) 0 child_nodes)
                        val _ = graph_edges := saturated_add (!graph_edges)
                          (List.length child_nodes)
                      in
                        if (boolSyntax.is_conj rebuilt orelse
                            boolSyntax.is_disj rebuilt) andalso
                           graph_id (List.nth (child_nodes, 0)) =
                             graph_id (List.nth (child_nodes, 1)) then
                          let
                            val law = if boolSyntax.is_conj rebuilt then
                              conj_idempotent else disj_idempotent
                            val child = hd child_nodes
                            val GraphNode {kind, ...} = child
                            val instantiated = Thm.INST
                              [idempotent_variable |->
                                 graph_representative child] law
                            val theorem = Thm.TRANS congruence instantiated
                          in
                            GraphNode
                              {id = graph_id child,
                               kind = kind,
                               representative = graph_representative child,
                               equality = theorem,
                               tree_nodes = graph_tree_nodes child}
                          end
                        else if reduce_gates then
                          let
                            val reduction = reduce_gate rebuilt child_nodes
                            val residue = boolSyntax.rhs (Thm.concl reduction)
                          in
                            if term_order (rebuilt, residue) <> EQUAL then
                              let
                                val node = visit residue
                                val GraphNode {id, kind, representative,
                                  tree_nodes, ...} = node
                              in
                                GraphNode {id = id, kind = kind,
                                  representative = representative,
                                  tree_nodes = tree_nodes,
                                  equality = Thm.TRANS congruence
                                    (Thm.TRANS reduction
                                      (graph_equality node))}
                              end
                            else
                              let
                                val commutative = boolSyntax.is_conj rebuilt
                                  orelse boolSyntax.is_disj rebuilt
                                  orelse boolSyntax.is_eq rebuilt
                                val reverse = commutative andalso
                                  List.nth (child_ids, 0) >
                                  List.nth (child_ids, 1)
                                val oriented = if not reverse then congruence
                                  else Thm.TRANS congruence
                                    (Conv.REWR_CONV
                                      (if boolSyntax.is_conj rebuilt then
                                         boolTheory.CONJ_SYM
                                       else if boolSyntax.is_disj rebuilt then
                                         boolTheory.DISJ_SYM
                                       else boolTheory.EQ_SYM_EQ) rebuilt)
                                val ids = if reverse then List.rev child_ids
                                  else child_ids
                                val right = boolSyntax.rhs
                                  (Thm.concl oriented)
                              in add_graph (connective_kind right ids)
                                right oriented tree_nodes end
                          end
                        else add_graph (connective_kind rebuilt child_ids)
                          rebuilt congruence tree_nodes
                      end
              val _ = physical_insert graph_physical occurrence saved
              val _ = graph_observations := !graph_observations + 1
            in
              saved
            end
      val root = visit skeleton
      val normalized = graph_representative root
      val normalized_raw = intern_raw normalized
      val normalized_tree_nodes = raw_tree_nodes normalized_raw
      val normalized_dag_nodes = !raw_nodes
    in
      {root = root, entries = List.rev (!graph_entries),
       graph_nodes = !next_graph_id,
       graph_observations = !graph_observations,
       graph_edges = !graph_edges,
       raw_nodes = !raw_nodes, raw_edges = !raw_edges,
       normalized_tree_nodes = normalized_tree_nodes,
       normalized_dag_nodes = normalized_dag_nodes,
       type_nodes = !type_nodes,
       type_observations = !type_observations,
       type_edges = !type_edges,
       transport_nodes = !transport_nodes,
       transport_seconds = !transport_time,
       residual_atoms = List.length
         (List.filter
           (fn GraphNode {kind = GraphAtom _, ...} => true | _ => false)
           (!graph_entries))}
    end

  val build_cnf_graph = build_cnf_graph_mode false

  type sat_context =
    {proofs : (term * thm * int) list ref, nodes : int ref,
     refresh_caches : unit -> unit}

  fun new_sat_context () : sat_context =
    let
      val signature_witness = ref (cache_signature ())
      val proofs = ref []
      val nodes = ref 0
      fun refresh_caches () =
        if cache_signature_matches (!signature_witness) then () else
          (proofs := []; nodes := 0;
           signature_witness := cache_signature ())
    in {proofs = proofs, nodes = nodes,
        refresh_caches = refresh_caches} end

  local
  fun cached_sat_proof_using make_order
      (context : sat_context) target retained_cost prove =
    let
      val _ = #refresh_caches context ()
      val signature_witness = cache_signature ()
      val maximum = SmtResource.max_skeleton_replay_dag_nodes
      val term_order = make_order ()
      fun validate theorem =
        (#refresh_caches context ();
         if List.null (Thm.hyp theorem) then ()
         else raise ERR "cached_sat_proof" "SAT certificate has hypotheses";
         Library.check_oracle_tags "SmtSkeletonProve"
           "schematic SAT certificate" theorem;
         exact_conclusion target theorem)
      fun find [] _ = NONE
        | find ((entry as (saved, theorem, _)) :: rest) prior =
            if term_order (saved, target) = EQUAL then
              ( #proofs context := entry :: List.revAppend (prior, rest);
                SOME theorem)
            else find rest (entry :: prior)
      fun retain theorem =
        (#refresh_caches context ();
        (* Never publish a certificate captured across a signature change.
           Its checked result can still satisfy this request. *)
        if not (cache_signature_matches signature_witness) then ()
        else
          let
            val cost = retained_cost ()
            fun fit entries nodes =
              if nodes + cost <= maximum then (entries, nodes)
              else case entries of
                [] => ([], 0)
              | (_, _, old_cost) :: rest => fit rest (nodes - old_cost)
          in
            if cost > maximum orelse
                not (new_cache_live_check () (Thm.concl theorem)) then ()
            else
              let val (oldest_first,nodes) = fit
                    (List.rev (!(#proofs context))) (!(#nodes context))
              in
                #proofs context := (target,theorem,cost) ::
                  List.rev oldest_first;
                #nodes context := nodes+cost
              end
          end)
      val theorem = case find (!(#proofs context)) [] of
          SOME theorem => phase "skeleton/schematic-certificate-hit"
            validate theorem
        | NONE => let val theorem = validate (prove ())
                  in retain theorem; theorem end
    in theorem end

  in
  fun cached_sat_proof context target cost prove =
    cached_sat_proof_using new_semantic_order context target
      (fn () => cost) prove

  fun checked_graph_sat_prove_in (context : sat_context) entries root =
    let
      val _ = #refresh_caches context ()
      fun node_id (GraphNode {id, ...}) = id
      fun node_kind (GraphNode {kind, ...}) = kind
      fun node_representative (GraphNode {representative, ...}) =
        representative
      (* Reduction and interning may leave dead gates in the construction
         inventory.  Only dependencies of the observed output belong to the
         SAT problem; their checked definitions suffice for reconstruction. *)
      val inventory = List.foldl
        (fn (node, dictionary) => Redblackmap.insert
          (dictionary, node_id node, node))
        (Redblackmap.mkDict Int.compare) entries
      val live = ref (HOLset.empty Int.compare)
      fun mark id =
        if HOLset.member (!live, id) then ()
        else
          let
            val node = Redblackmap.find (inventory, id)
            val _ = live := HOLset.add (!live, id)
            val children = case node_kind node of
                GraphNegation child => [child]
              | GraphConjunction (left, right) => [left, right]
              | GraphDisjunction (left, right) => [left, right]
              | GraphImplication (left, right) => [left, right]
              | GraphEquality (left, right) => [left, right]
              | GraphConditional (test, yes, no) => [test, yes, no]
              | _ => []
          in List.app mark children end
      val _ = mark (node_id root)
      val entries = List.filter
        (fn node => HOLset.member (!live, node_id node)) entries
      fun generated kind =
        case kind of GraphTrue => false | GraphFalse => false | _ => true
      val variables = List.foldl
        (fn (node, dictionary) =>
          if generated (node_kind node) then
            Redblackmap.insert
              (dictionary, node_id node, Term.mk_var
                ("skeleton_node_" ^ Int.toString (node_id node), Type.bool))
          else dictionary)
        (Redblackmap.mkDict Int.compare) entries
      val kinds = List.foldl
        (fn (node, dictionary) => Redblackmap.insert
          (dictionary, node_id node, node_kind node))
        (Redblackmap.mkDict Int.compare) entries
      fun symbolic id =
        case Redblackmap.peek (kinds, id) of
          NONE => raise ERR "checked_graph_sat_prove" "unknown graph node ID"
        | SOME kind =>
            (case kind of
               GraphTrue => boolSyntax.T
             | GraphFalse => boolSyntax.F
             | _ => Redblackmap.find (variables, id))
      fun body kind =
        case kind of
          GraphNegation child => boolSyntax.mk_neg (symbolic child)
        | GraphConjunction (left, right) =>
            boolSyntax.mk_conj (symbolic left, symbolic right)
        | GraphDisjunction (left, right) =>
            boolSyntax.mk_disj (symbolic left, symbolic right)
        | GraphImplication (left, right) =>
            boolSyntax.mk_imp (symbolic left, symbolic right)
        | GraphEquality (left, right) =>
            boolSyntax.mk_eq (symbolic left, symbolic right)
        | GraphConditional (test, yes, no) =>
            boolSyntax.mk_cond
              (symbolic test, symbolic yes, symbolic no)
        | _ => raise ERR "checked_graph_sat_prove"
            "non-connective graph node has no definition"
      fun is_connective kind =
        case kind of
          GraphNegation _ => true | GraphConjunction _ => true |
          GraphDisjunction _ => true | GraphImplication _ => true |
          GraphEquality _ => true | GraphConditional _ => true | _ => false
      val connective_nodes = List.filter
        (is_connective o node_kind) entries
      val equations = List.map
        (fn node => boolSyntax.mk_eq
          (symbolic (node_id node), body (node_kind node)))
        connective_nodes
      val cnf_equivalence = phase "skeleton/gate-cnf"
        (SmtCircuitSat.balanced_equivalences o
         List.map SmtCircuitSat.definition_cnf) equations
      val antecedent = boolSyntax.lhs (Thm.concl cnf_equivalence)
      val cnf = boolSyntax.rhs (Thm.concl cnf_equivalence)
      val target = boolSyntax.mk_imp
        (antecedent, symbolic (node_id root))
      val sat_target = boolSyntax.mk_imp (cnf, symbolic (node_id root))
      val sat_measure = phase "skeleton/sat-target-measure"
        term_measure sat_target
      val substitution = List.map
        (fn node => Redblackmap.find (variables, node_id node) |->
          node_representative node)
        (List.filter (generated o node_kind) entries)
      val domains = HOLset.addList (HOLset.empty Term.compare,
        List.map #redex substitution)
      val _ =
        if HOLset.numItems domains = List.length substitution andalso
           List.all (Term.is_var o #redex) substitution then ()
        else raise ERR "checked_graph_sat_prove"
          "generated graph substitution domains overlap"
      val definition_theorem = phase "skeleton/reflexive-definitions"
        (SmtCircuitSat.balanced_conjunction o
         List.map (Thm.REFL o node_representative)) connective_nodes
      val _ = observe_sat_target sat_target
      (* This target contains only freshly named Boolean nodes and fixed
         Boolean heads. Its unfolded syntax is linear in the gate list,
         so native comparison cannot enter a large source annotation. *)
      fun prove () = cached_sat_proof_using (fn () => Term.compare)
        context sat_target
        (fn () => #dag_nodes sat_measure)
        (fn () => SmtCircuitSat.prove_cnf (cnf, symbolic (node_id root)))
      val cnf_theorem =
        case !sat_completion_observer of
          NONE => phase "skeleton/sat-search+checking"
            prove ()
        | SOME observer =>
            let
              val started = Time.now ()
              val theorem = phase "skeleton/sat-search+checking"
                prove ()
              val elapsed = Time.- (Time.now (), started)
              val _ = observer (sat_target, elapsed)
            in
              theorem
            end
      val target_theorem = phase "skeleton/circuit-implication"
        (fn () =>
          let val supplied_cnf = Thm.EQ_MP cnf_equivalence
            (Thm.ASSUME antecedent)
          in Thm.DISCH antecedent (Thm.MP cnf_theorem supplied_cnf) end) ()
      val target_theorem = exact_conclusion target target_theorem
      val instantiated = phase "skeleton/combined-instantiation"
        (fn substitution => Thm.INST substitution target_theorem)
        substitution
      val theorem = phase "skeleton/cnf-definitions"
        (fn definitions => Thm.MP instantiated definitions)
        definition_theorem
    in
      {theorem = theorem, sat_target = sat_target,
       sat_tree_nodes = #tree_nodes sat_measure,
       sat_dag_nodes = #dag_nodes sat_measure}
    end

  fun checked_graph_sat_prove entries root =
    checked_graph_sat_prove_in (new_sat_context ()) entries root

  exception PROCEDURE_UNABLE

  (* Pure propositional replay has no atom-reduction stage.  Construct its
     typed CNF graph directly, keeping all theory atoms opaque, and use the
     same checked circuit certificate and kernel transport as owned replay. *)
  (* A clause about a Boolean gate needs its immediate truth table, not the
     circuits computing its inputs.  Try an opaque clause first, then expose
     each literal's outer connective in turn.  Substitution of the opaque
     atoms into a checked tautology proves the exact original clause.  This
     is incomplete by design; callers retain the full graph procedure. *)
  local
  fun clause_frontier_prove_using_order make_order reuse_context limit target =
    let
      val term_order = make_order ()
      val empty_terms = HOLset.empty term_order
      val work = ref 0
      fun tick () =
        (work := !work + 1;
         if !work <= limit then ()
         else raise ERR "clause_frontier_prove" "Boolean frontier too large")
      fun clauses term =
        (tick ();
         if boolSyntax.is_disj term then
           let val (left, right) = boolSyntax.dest_disj term
           in clauses left @ clauses right end
         else [term])
      fun base term =
        if boolSyntax.is_neg term then base (boolSyntax.dest_neg term)
        else term
      val literals = clauses target
      val candidates = List.filter
        (fn term => case skeleton_children term of
           SOME (_ :: _) => true | _ => false) (List.map base literals)
      fun attempt exposed =
        let
          val _ = work := 0
          val atoms = ref (Redblackmap.mkDict term_order)
          val substitution = ref []
          (* A gate input may itself be a disjunction spread along the clause
             spine.  Preserve any occurrence of that complete input as one
             atom, rather than flattening it and losing the gate relation. *)
          val stops = HOLset.addList (empty_terms,
            List.concat (List.map
              (fn term => Option.getOpt (skeleton_children term, []))
              (HOLset.listItems exposed)) @
            (* The opaque attempt must also keep complete positive
               disjunctions named by negative literals. Flattening p \/ q
               in (p \/ q) \/ ~(p \/ q) loses its complementary occurrence.
               Later attempts still expose the original gate candidates. *)
            (if HOLset.isEmpty exposed then
               List.map boolSyntax.dest_neg
                 (List.filter boolSyntax.is_neg literals)
             else []))
          fun atom term =
            case Redblackmap.peek (!atoms, term) of
              SOME variable => variable
            | NONE =>
                let
                  (* Every source atom is replaced by a hole. Stable hole
                     names permit reuse of the closed Boolean law; source
                     variables never enter the schematic proof. *)
                  val variable = case reuse_context of NONE =>
                      Term.genvar Type.bool
                    | SOME _ => Term.mk_var ("clause_frontier_atom_" ^
                        Int.toString (Redblackmap.numItems (!atoms)),
                        Type.bool)
                in
                  atoms := Redblackmap.insert (!atoms, term, variable);
                  substitution := {redex = variable, residue = term} ::
                    !substitution;
                  variable
                end
          fun opaque term = (tick ();
            if Term.aconv term boolSyntax.T orelse
               Term.aconv term boolSyntax.F then term
            else if boolSyntax.is_neg term then
              boolSyntax.mk_neg (opaque (boolSyntax.dest_neg term))
            else atom term)
          fun literal term = (tick ();
            if boolSyntax.is_neg term then
              boolSyntax.mk_neg (literal (boolSyntax.dest_neg term))
            else if HOLset.member (exposed, term) then
              let
                val (head, children) = boolSyntax.strip_comb term
              in Term.list_mk_comb (head, List.map literal children) end
            else opaque term)
          fun clause term = (tick ();
            if HOLset.member (stops, base term) then opaque term
            else if boolSyntax.is_disj term then
              let val (left, right) = boolSyntax.dest_disj term
              in boolSyntax.mk_disj (clause left, clause right) end
            else literal term)
          val schematic = clause target
          val variables = List.map #2 (Redblackmap.listItems (!atoms))
          val valuations = List.foldl
            (fn (_, count) => if count > limit div 2 then limit + 1
                             else count * 2) 1 variables
          val _ = if valuations <= limit then ()
            else raise ERR "clause_frontier_prove"
              "Boolean truth table too large"
          fun prove () =
            let
              val valuation = Array.array (List.length variables, false)
              fun compile term =
                if Term.aconv term boolSyntax.T then (fn () => true)
                else if Term.aconv term boolSyntax.F then (fn () => false)
                else if Term.is_var term then
                  let val index = Lib.index (Term.aconv term) variables
                  in fn () => Array.sub (valuation, index) end
                else
                  let
                    val evaluations = List.map compile
                      (valOf (skeleton_children term))
                    fun first () = List.nth (evaluations, 0) ()
                    fun second () = List.nth (evaluations, 1) ()
                  in
                    if boolSyntax.is_neg term then (fn () => not (first ()))
                    else if boolSyntax.is_conj term then
                      (fn () => first () andalso second ())
                    else if boolSyntax.is_disj term then
                      (fn () => first () orelse second ())
                    else if boolSyntax.is_imp term then
                      (fn () => not (first ()) orelse second ())
                    else if boolSyntax.is_eq term then
                      (fn () => first () = second ())
                    else (fn () => if first () then second ()
                                  else List.nth (evaluations, 2) ())
                  end
              val evaluate = compile schematic
              fun all_valuations index =
                if index = Array.length valuation then evaluate ()
                else
                  (Array.update (valuation, index, false);
                   all_valuations (index + 1) andalso
                   (Array.update (valuation, index, true);
                    all_valuations (index + 1)))
              (* This unchecked search can only decline an attempt.  Acceptance
                 still requires the exhaustive kernel proof below. *)
              (* The finite truth table is checked in process.  Hundreds of
                 tiny gate clauses must not each launch a SAT subprocess. *)
            in
              (if all_valuations 0 then ()
               else raise ERR "clause_frontier_prove"
                 "Boolean frontier has a counterexample";
               Tactical.TAC_PROOF (([], schematic),
                 List.foldr (fn (variable, continuation) =>
                   Tactical.THEN (Tactic.BOOL_CASES_TAC variable, continuation))
                   (simpLib.ASM_SIMP_TAC boolSimps.bool_ss []) variables))
            end
          val theorem = case reuse_context of NONE => prove ()
            | SOME context =>
                (* Source atoms are holes of Type.bool, not operands of
                   this comparison. Count the actual retained native graph
                   only on a miss; the closed theorem shares its conclusion
                   with this key after validation. Keep the original 8192
                   allowance and the general cache API guarded. *)
                cached_sat_proof_using (fn () => Term.compare)
                  context schematic (fn () => SmtResource.dag_nodes_up_to
                    SmtResource.max_skeleton_replay_dag_nodes schematic) prove
          val instantiated = Thm.INST (!substitution) theorem
          val exact = exact_conclusion target instantiated
          val _ = Library.check_oracle_tags "SmtSkeletonProve"
            "clause-frontier" exact
        in exact end
      fun try [] = raise ERR "clause_frontier_prove"
            "no tautological Boolean frontier"
        | try (candidate :: rest) = attempt candidate
            handle Feedback.HOL_ERR _ => try rest
    in
      try (empty_terms ::
        List.map (fn term => HOLset.add (empty_terms, term)) candidates @
        [HOLset.addList (empty_terms, candidates)])
    end

  in
  val clause_frontier_prove_using =
    clause_frontier_prove_using_order new_semantic_order

  val clause_frontier_prove = clause_frontier_prove_using NONE
  fun clause_frontier_prove_in context =
    clause_frontier_prove_using (SOME context)

  (* Every key is an actual source subterm, never an arbitrary cache ID.
     Index only operands compared by the frontier. Any declined key or
     generation change restarts with the original semantic order inside
     the same caller step. The clause's native admission is independent. *)
  fun clause_frontier_prove_indexed context
      (Context {atom_index,cache_generation,...}) limit target =
    let
      exception DeclinedIndex
      val generation = !cache_generation
      fun key term = case atom_index term of
          SOME id => if generation = !cache_generation then id
                     else raise DeclinedIndex
        | NONE => raise DeclinedIndex
      fun order (left,right) =
        if Portable.pointer_eq (left,right) then EQUAL
        else Int.compare (key left,key right)
      fun run () = clause_frontier_prove_using_order (fn () => order)
        (SOME context) limit target
    in run () handle DeclinedIndex =>
      clause_frontier_prove_in context limit target end
  end
  end

  fun propositional_prove_in (context : sat_context) target =
    let
      val _ = #refresh_caches context ()
      val _ = Term.type_of target = Type.bool orelse
        raise ERR "propositional_prove" "target is not Boolean"
      val graph = phase "skeleton/propositional-cnf"
        (build_cnf_graph_mode true) target
      val GraphNode {kind, ...} = #root graph
      val actual = case kind of
          GraphTrue => boolTheory.TRUTH
        | _ => #theorem (phase "skeleton/propositional-sat"
            (checked_graph_sat_prove_in context (#entries graph)) (#root graph))
      val _ = List.null (Thm.hyp actual) orelse
        raise ERR "propositional_prove" "SAT theorem has hypotheses"
      val GraphNode {equality, ...} = #root graph
      val theorem = Thm.EQ_MP (Thm.SYM equality) actual
      val theorem = exact_conclusion target theorem
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "propositional-replay" theorem
    in theorem end

  fun propositional_prove target =
    propositional_prove_in (new_sat_context ()) target

  (* Expose only conditional control flow at equality observations.  Values
     of every type remain opaque; distributing equality over COND uses the
     polymorphic kernel-checked COND_RAND/COND_RATOR laws.  Memoization bounds
     the potentially quadratic product of two conditional value DAGs. *)
  fun conditional_equality_conv target =
    let
      val term_order = new_semantic_order ()
      val admission = new_type_admission_context ()
      val cache = ref (Redblackmap.mkDict term_order)
      val visited = ref 0
      (* Match the distribution law against a constant-size schematic
         frontier, never against its opaque value DAGs or binder bodies.
         Native Type matching is admitted before constructing that frontier.
         INST's source is small; values are substitution residues only. *)
      fun rewrite conversion term =
        let
          val substitution = ref []
          fun opaque value =
            let
              val ty = Term.type_of value
              val _ = ignore (#full_type admission ty)
              val variable = Term.genvar ty
              val _ = substitution := (variable |-> value) :: !substitution
            in variable end
          fun value term =
            if boolSyntax.is_cond term then
              let val (test, yes, no) = boolSyntax.dest_cond term in
                boolSyntax.mk_cond (opaque test, opaque yes, opaque no)
              end
            else opaque term
          val (left, right) = boolSyntax.dest_eq term
          val schematic = boolSyntax.mk_eq (value left, value right)
          val theorem = conversion schematic
        in nodewise_exact_left term (Thm.INST (!substitution) theorem) end
      fun visit term =
        case Redblackmap.peek (!cache, term) of
          SOME theorem => nodewise_exact_left term theorem
        | NONE =>
            let
              val _ = visited := !visited + 1
              val _ = !visited <=
                  SmtResource.max_skeleton_replay_dag_nodes orelse
                raise ERR "conditional_equality_conv"
                  "conditional equality frontier too large"
              fun equality () =
                let
                  val (left, right) = boolSyntax.dest_eq term
                  fun distribute conversion =
                    let val theorem = rewrite conversion term in
                      Thm.TRANS theorem
                        (visit (boolSyntax.rhs (Thm.concl theorem)))
                    end
                in
                  if term_order (left, right) = EQUAL then
                    nodewise_exact_left term
                      (Drule.EQT_INTRO (nodewise_equality left right))
                  else if boolSyntax.is_cond right then
                    distribute (Conv.REWR_CONV boolTheory.COND_RAND)
                  else if boolSyntax.is_cond left then
                    distribute (Conv.THENC
                      (Conv.RATOR_CONV
                         (Conv.REWR_CONV boolTheory.COND_RAND),
                       Conv.REWR_CONV boolTheory.COND_RATOR))
                  else if term_order (left, right) = GREATER then
                    rewrite (Conv.REWR_CONV boolTheory.EQ_SYM_EQ) term
                  else Thm.REFL term
                end
              val theorem =
                case skeleton_children term of
                  SOME children => anchor_left term
                    (connective_congruence term (List.map visit children))
                | NONE =>
                    if boolSyntax.is_eq term then equality ()
                    else Thm.REFL term
              val _ = cache := Redblackmap.insert (!cache, term, theorem)
            in theorem end
    in visit target end

  (* Lift checked Boolean equivalences through arbitrary typed applications.
     Theory operators stay uninterpreted: their arguments must be equal by
     congruence, not by an assumed theory identity.  Maximal Boolean islands
     are discharged once rather than lowering all surrounding word circuits. *)
  fun congruence_prove_in (context : sat_context) target =
    let
      val _ = #refresh_caches context ()
      val (left, right) = boolSyntax.dest_eq target
      val term_order = new_semantic_order ()
      val cache = ref (Redblackmap.mkDict
        (pair_compare (term_order, term_order)))
      val visited = ref 0
      fun boolean_island left right =
        Term.type_of left = Type.bool andalso
        (Option.isSome (skeleton_children left) orelse
         Option.isSome (skeleton_children right))
      fun visit (left, right) =
        if term_order (left, right) = EQUAL then
          nodewise_equality left right
        else
          case Redblackmap.peek (!cache, (left, right)) of
            SOME theorem => exact_equality left right theorem
          | NONE =>
              let
                val _ = visited := !visited + 1
                val _ = !visited <=
                    SmtResource.max_skeleton_replay_dag_nodes orelse
                  raise ERR "congruence_prove" "congruence frontier too large"
                fun structural () =
                  if Term.is_comb left andalso Term.is_comb right then
                    let
                      val (left_head, left_arg) = Term.dest_comb left
                      val (right_head, right_arg) = Term.dest_comb right
                    in
                      anchor_right right (anchor_left left
                        (Thm.MK_COMB (visit (left_head, right_head),
                          visit (left_arg, right_arg))))
                    end
                  else raise ERR "congruence_prove"
                    "opaque endpoints are not equal"
                fun boolean () =
                  let
                    val equality = boolSyntax.mk_eq (left, right)
                    val normalized = conditional_equality_conv equality
                    val residue = boolSyntax.rhs (Thm.concl normalized)
                  in Thm.EQ_MP (Thm.SYM normalized)
                    (propositional_prove_in context residue) end
                val theorem =
                  if boolean_island left right then
                    boolean ()
                  else structural ()
                val _ = cache := Redblackmap.insert
                  (!cache, (left, right), theorem)
              in theorem end
      val theorem = visit (left, right)
      val exact = exact_conclusion target theorem
      val _ = List.null (Thm.hyp exact) orelse
        raise ERR "congruence_prove" "congruence introduced hypotheses"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "Boolean congruence" exact
    in exact end

  fun congruence_prove target =
    congruence_prove_in (new_sat_context ()) target

  fun prove_with_owners
      (Context {procedures, fallback, atom_index, atom_cache,
                cache_generation, refresh_caches}) owners
      (target_measure : {tree_nodes : int, dag_nodes : int}) target =
    let
      val _ = refresh_caches ()
      val signature_witness = cache_signature ()
      val generation_witness = !cache_generation
      (* A callback may reset the index and then restore the signature.
         Neither old IDs nor working_cache belong to that new generation. *)
      fun reusable () =
        (refresh_caches ();
         generation_witness = !cache_generation andalso
         cache_signature_matches signature_witness)
      val live_check = ref (NONE : (term -> bool) option)
      fun live theorem =
        let
          val check = case !live_check of SOME check => check
            | NONE => let val check = new_cache_live_check ()
                      in live_check := SOME check; check end
        in check (Thm.concl theorem) end
      val _ =
        if Term.type_of target = Type.bool then ()
        else raise ERR "prove" "target is not Boolean"
      val _ =
        case skeleton_children target of
          NONE => raise ERR "prove"
            "whole obligation is a theory atom; local solve is forbidden"
        | SOME _ => ()
      val total_timer = Timer.startRealTimer ()
      (* Owner/node IDs are obligation-local, independent of any exhausted
         cross-obligation atom-cache index. Reindex legacy owner maps once. *)
      val node_index = ref (new_cache_index
        SmtResource.max_bv_replay_term_nodes)
      val term_order = new_semantic_order ()
      val owners = Redblackmap.foldl
        (fn (atom, owner, result) =>
          Redblackmap.insert (result, atom, owner))
        (Redblackmap.mkDict term_order) owners
      fun fresh_nodes () = SmtResource.new_key_map Int.compare Word.fromInt
      val nodes = ref (fresh_nodes ())
      (* Count semantic classes on the same admitted index as the local
         node cache. Metrics live for the whole obligation, so retain this
         original index across callback cache resets. A declined index uses
         the original semantic term set; it never becomes a proof refusal. *)
      val metric_index = ref (SOME (!node_index))
      val metric_ids = ref (SOME
        (SmtResource.new_key_map Int.compare Word.fromInt))
      val metric_terms = ref []
      val metric_count = ref 0
      val skeleton_nodes = ref NONE
      fun note_skeleton term cache_key =
        case !skeleton_nodes of SOME saved =>
            skeleton_nodes := SOME (HOLset.add (saved,term))
        | NONE =>
            let
              val index = valOf (!metric_index)
              val key = if Portable.pointer_eq (index,!node_index) then
                  cache_key else index term
            in case key of SOME id =>
                let val saved = valOf (!metric_ids) in
                  case #peek saved id of SOME () => ()
                  | NONE =>
                      (#insert saved (id,());
                       metric_terms := term :: !metric_terms;
                       metric_count := !metric_count+1)
                end
              | NONE =>
                  let
                    val saved = List.foldl (fn (term,saved) =>
                      HOLset.add (saved,term)) (HOLset.empty term_order)
                      (List.rev (!metric_terms))
                  in
                    skeleton_nodes := SOME (HOLset.add (saved,term));
                    metric_index := NONE; metric_ids := NONE;
                    metric_terms := []
                  end
            end
      fun skeleton_node_count () = case !skeleton_nodes of
          NONE => !metric_count | SOME saved => HOLset.numItems saved
      val distinct_atoms = ref (HOLset.empty term_order)
      val calls = ref (Redblackmap.mkDict String.compare)
      val working_cache = ref (!atom_cache)
      val local_signature = ref (cache_signature ())
      val local_generation = ref (!cache_generation)
      fun refresh_local () =
        (refresh_caches ();
         if !local_generation = !cache_generation andalso
            cache_signature_matches (!local_signature) then () else
           (working_cache := !atom_cache;
            node_index := new_cache_index
              SmtResource.max_bv_replay_term_nodes;
            nodes := fresh_nodes ();
            local_signature := cache_signature ();
            local_generation := !cache_generation))
      val node_hits = ref 0
      val node_pointer_hits = ref 0
      val node_reanchor_attempts = ref 0
      val node_reanchor_successes = ref 0
      val node_reanchor_fallbacks = ref 0
      val node_reanchor_time = ref Time.zeroTime
      val atom_requests = ref 0
      val atom_proofs = ref 0
      val atom_hits = ref 0
      val atom_time = ref Time.zeroTime
      val owned_atoms = ref 0
      fun add_call name =
        let
          val count = Option.getOpt (Redblackmap.peek (!calls, name), 0)
        in
          calls := Redblackmap.insert (!calls, name, count + 1)
        end
      fun raw_expand atom =
        case (case Redblackmap.peek (owners, atom) of
                SOME name =>
                  SOME (name, procedure_named procedures name, true)
              | NONE => Option.map (fn procedure =>
                  (#name procedure, procedure, false)) fallback) of
          NONE => (Thm.REFL atom, false)
        | SOME (name, procedure, required) =>
            let
              val {expand, ...} = procedure
              val _ = atom_requests := !atom_requests + 1
              val _ = distinct_atoms := HOLset.add (!distinct_atoms, atom)
              (* Explicit owners and fallback are distinct even if named
                 alike. An atom ID alone does not identify its expansion. *)
              val cache_key = if reusable () then Option.map
                (fn id => (name, if required then 0 else 1, id))
                (atom_index atom) else NONE
              fun prove () =
                let
                  val timer = Timer.startRealTimer ()
                  val _ = add_call name
                  val expansion = Profile.profile_with_exn_name
                    ("th_lemma[general](atom:" ^ name ^ ")")
                    expand atom
                  val _ = refresh_local ()
                  val can_retain = reusable ()
                  val elapsed = Timer.checkRealTimer timer
                  val _ = atom_time := Time.+ (!atom_time, elapsed)
                in
                  case expansion of
                    Unable =>
                      if required then raise PROCEDURE_UNABLE
                      else (Thm.REFL atom, false)
                  | Expanded theorem =>
                      let
                        val theorem = nodewise_exact_left atom
                          (validate_theorem_with atom_index name atom theorem)
                        val _ = owned_atoms := !owned_atoms + 1
                        val _ = case cache_key of NONE => ()
                          | SOME id =>
                              if not can_retain orelse not (live theorem)
                              then () else working_cache :=
                              Redblackmap.insert (!working_cache, id, theorem)
                        val _ = atom_proofs := !atom_proofs + 1
                      in
                        (theorem, true)
                      end
                end
            in
              case Option.mapPartial
                  (fn id => Redblackmap.peek (!working_cache, id)) cache_key of
                SOME theorem =>
                  (let
                     val theorem = reanchor_cached_theorem atom theorem
                   in
                     atom_hits := !atom_hits + 1;
                     (theorem, true)
                   end handle REANCHOR_LIMIT => prove ()
                     | Feedback.HOL_ERR detail =>
                         if cache_admission_refusal detail then prove ()
                         else raise Feedback.HOL_ERR detail)
              | NONE => prove ()
            end
      fun visit term =
        let
          val _ = refresh_local ()
          val cache_key = (!node_index) term
          val _ = note_skeleton term cache_key
          fun compute children =
            let
              val child_results = List.map visit children
              val changed = List.exists Lib.snd child_results
              val theorem =
                if changed then
                  anchor_left term
                    (connective_congruence term
                      (List.map Lib.fst child_results))
                else Thm.REFL term
              val result = (theorem, changed)
              (* Reindex after recursive callbacks; cache_key may belong
                 to an index that refresh_local has discarded. *)
              val _ = refresh_local ()
              val _ = case (!node_index) term of NONE => ()
                | SOME id => #insert (!nodes) (id,(term,result))
            in
              result
            end
        in
          case skeleton_children term of
            NONE =>
              (case fallback of
                 NONE => raw_expand term
               | SOME _ =>
                   let
                     val (first, changed) = raw_expand term
                   in
                     if changed then
                       let
                         val residue = boolSyntax.rhs (Thm.concl first)
                         val (rest, rest_changed) = visit residue
                       in
                         (Thm.TRANS first rest,
                          changed orelse rest_changed)
                       end
                     else (first, changed)
                   end)
          | SOME children =>
              (case Option.mapPartial
                  (#peek (!nodes)) cache_key of
                 SOME (saved, (theorem, changed)) =>
                   (node_hits := !node_hits + 1;
                    if Portable.pointer_eq (term, saved) then
                      (node_pointer_hits := !node_pointer_hits + 1;
                       observe_node_cache NodeCachePointerHit;
                       (theorem, changed))
                    else
                      let
                        val _ = node_reanchor_attempts :=
                          !node_reanchor_attempts + 1
                        val _ = observe_node_cache
                          NodeCacheStructuralReanchorAttempt
                        val timer =
                          if SmtResource.e0_enabled () then
                            SOME (Timer.startRealTimer ())
                          else NONE
                        fun finish () =
                          case timer of
                            NONE => ()
                          | SOME timer =>
                              let
                                val elapsed = Timer.checkRealTimer timer
                                val _ = node_reanchor_time := Time.+
                                  (!node_reanchor_time, elapsed)
                              in
                                observe_node_cache
                                  (NodeCacheReanchorTime elapsed)
                              end
                        fun fallback () =
                          (node_reanchor_fallbacks :=
                             !node_reanchor_fallbacks + 1;
                           observe_node_cache
                             NodeCacheStructuralReanchorFallback;
                           compute children)
                        fun reanchor () =
                          let val result = (exact_left term theorem, changed)
                          in
                            node_reanchor_successes :=
                              !node_reanchor_successes + 1;
                            observe_node_cache
                              NodeCacheStructuralReanchorSuccess;
                            result
                          end
                      in
                        (Portable.finally finish reanchor ()
                         handle REANCHOR_LIMIT => fallback ()
                              | Feedback.HOL_ERR detail =>
                                  if cache_admission_refusal detail then
                                    fallback ()
                                  else raise Feedback.HOL_ERR detail)
                      end)
               | NONE => compute children)
        end
      val normalization = Lib.fst
        (phase "skeleton/conversion" visit target)
      val normalized = boolSyntax.rhs (Thm.concl normalization)
      val _ =
        if !owned_atoms > 0 andalso
            term_order (normalized, target) = EQUAL then
          raise ERR "prove" "atom expansion made no progress"
        else ()
      val graph = phase "skeleton/cnf-normalization"
        build_cnf_graph normalized
      val _ = SmtResource.emit_e0
        ("skeleton-graph nodes=" ^ Int.toString (#graph_nodes graph) ^
         " observations=" ^ Int.toString (#graph_observations graph) ^
         " edges=" ^ Int.toString (#graph_edges graph) ^
         " raw_nodes=" ^ Int.toString (#raw_nodes graph) ^
         " raw_edges=" ^ Int.toString (#raw_edges graph) ^
         " type_nodes=" ^ Int.toString (#type_nodes graph) ^
         " type_observations=" ^
           Int.toString (#type_observations graph) ^
         " type_edges=" ^ Int.toString (#type_edges graph) ^
         " leaf_transport_nodes=" ^ Int.toString (#transport_nodes graph) ^
         " leaf_transport_wall=" ^ Time.toString (#transport_seconds graph))
      val GraphNode
        {representative = normalized, equality = idempotence,
         ...} = #root graph
      val sat_timer = Timer.startRealTimer ()
      val {theorem = actual_theorem, sat_target, sat_tree_nodes,
           sat_dag_nodes} =
        (phase "skeleton/cnf+sat" checked_graph_sat_prove
          (#entries graph) (#root graph)
         handle HolSatLib.SAT_cex theorem =>
           let
             fun label (GraphNode {kind = GraphAtom _, representative, ...}) =
                   let val (head, _) = boolSyntax.strip_comb representative in
                     if Term.is_const head then
                       let
                         val {Thy, Name, ...} = Term.dest_thy_const head
                         fun head_name argument =
                           let val (argument_head, _) =
                             boolSyntax.strip_comb argument
                           in
                             if Term.is_const argument_head then
                               let val {Thy, Name, ...} =
                                 Term.dest_thy_const argument_head
                               in Thy ^ "$" ^ Name end
                             else if Term.is_var argument_head then "variable"
                             else "other"
                           end
                         val (_, arguments) =
                           boolSyntax.strip_comb representative
                         val suffix = if Thy = "fcp" then
                             "[" ^ String.concatWith ","
                               (List.map head_name arguments) ^ "]"
                           else ""
                       in SOME (Thy ^ "$" ^ Name ^ suffix) end
                     else SOME "non-constant"
                   end
               | label _ = NONE
             val labels = List.mapPartial label (#entries graph)
             fun unique [] = []
               | unique (item :: rest) =
                   item :: unique (List.filter (fn other => other <> item) rest)
             val message = "SKELETON_CEX residual_atoms=" ^
               Int.toString (#residual_atoms graph) ^
               " owned_atoms=" ^ Int.toString (!owned_atoms) ^
               " labels=" ^ String.concatWith "," (unique labels)
             val _ = Feedback.HOL_MESG message
           in raise HolSatLib.SAT_cex theorem end)
      val _ =
        if List.null (Thm.hyp actual_theorem) then ()
        else raise ERR "prove" "checked SAT theorem has hypotheses"
      val actual_theorem =
        let val conclusion = Thm.concl actual_theorem in
          if Portable.pointer_eq (conclusion, normalized) then
            actual_theorem
          else
            let
              val equality = phase "skeleton/sat-conclusion-transport"
                (fn () => bounded_nodewise_equality
                  SmtResource.max_skeleton_replay_dag_nodes
                  conclusion normalized) ()
            in Thm.EQ_MP equality actual_theorem end
        end
        handle REANCHOR_LIMIT => raise ERR "prove"
          "checked SAT theorem exceeds the skeleton transport DAG bound"
      val _ = Library.check_oracle_tags
        "SmtSkeletonProve" "checked-sat" actual_theorem
      val sat_time = Timer.checkRealTimer sat_timer
      val idempotence_sym = phase "skeleton/idempotence-sym"
        Thm.SYM idempotence
      val converted_theorem = phase "skeleton/idempotence-eq-mp"
        (fn equality => Thm.EQ_MP equality actual_theorem)
        idempotence_sym
      val normalization_sym = phase "skeleton/normalization-sym"
        Thm.SYM normalization
      val theorem = phase "skeleton/normalization-eq-mp"
        (fn equality => Thm.EQ_MP equality converted_theorem)
        normalization_sym
      val _ = phase "skeleton/final-hypothesis-check"
        (fn () =>
          if List.null (Thm.hyp theorem) then ()
          else raise ERR "prove" "result theorem has hypotheses") ()
      val _ = phase "skeleton/final-conclusion-check"
        (fn () =>
          if Portable.pointer_eq (Thm.concl theorem, target) then ()
          else ignore (bounded_nodewise_equality
            SmtResource.max_skeleton_replay_dag_nodes
            (Thm.concl theorem) target)) ()
      val _ = phase "skeleton/final-oracle-check"
        (fn () => Library.check_oracle_tags
          "SmtSkeletonProve" "result" theorem) ()
      val total_time = Timer.checkRealTimer total_timer
      val procedure_calls = Redblackmap.foldl
        (fn (name, count, result) => (name, count) :: result) [] (!calls)
      val metrics =
        {target_tree_nodes = #tree_nodes target_measure,
         target_dag_nodes = #dag_nodes target_measure,
         skeleton_dag_nodes = skeleton_node_count (),
         normalized_tree_nodes = #normalized_tree_nodes graph,
         normalized_dag_nodes = #normalized_dag_nodes graph,
         sat_tree_nodes = sat_tree_nodes,
         sat_dag_nodes = sat_dag_nodes,
         graph_nodes = #graph_nodes graph,
         graph_observations = #graph_observations graph,
         graph_edges = #graph_edges graph,
         graph_type_nodes = #type_nodes graph,
         graph_type_observations = #type_observations graph,
         graph_type_edges = #type_edges graph,
         graph_leaf_transport_nodes = #transport_nodes graph,
         graph_leaf_transport_seconds = #transport_seconds graph,
         distinct_atoms = HOLset.numItems (!distinct_atoms),
         atom_requests = !atom_requests,
         atom_proofs = !atom_proofs,
         atom_cache_hits = !atom_hits,
         node_cache_hits = !node_hits,
         node_cache_pointer_hits = !node_pointer_hits,
         node_cache_structural_reanchor_attempts = !node_reanchor_attempts,
         node_cache_structural_reanchor_successes = !node_reanchor_successes,
         node_cache_structural_reanchor_fallbacks = !node_reanchor_fallbacks,
         node_cache_reanchor_seconds = !node_reanchor_time,
         residual_atoms = #residual_atoms graph,
         atom_seconds = !atom_time,
         sat_seconds = sat_time,
         total_seconds = total_time,
         procedure_calls = procedure_calls}
      val _ = if reusable () then atom_cache := !working_cache else ()
    in
      {theorem = theorem, metrics = metrics}
    end

  datatype attempt =
      Proved of {theorem : thm, metrics : metrics}
    | Declined

  fun attempt_with_owners context owners target_measure target =
    Proved (prove_with_owners context owners target_measure target)
    handle PROCEDURE_UNABLE =>
             (Feedback.HOL_MESG "SKELETON PROCEDURE_UNABLE"; Declined)
         | HolSatLib.SAT_cex _ =>
             (Feedback.HOL_MESG "SKELETON SAT_CEX"; Declined)
         | HolSatLib.SAT_satisfiable _ =>
             (Feedback.HOL_MESG "SKELETON SAT"; Declined)

end
