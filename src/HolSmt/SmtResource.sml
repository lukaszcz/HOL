(* Copyright (c) 2026 The HOL4 contributors. *)

(* Fixed resource budgets for checked theory replay. *)

structure SmtResource =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtResource"

  (* P5.3: these are the single source of truth for the D12 budget. *)
  (* Complete CPC certificates for the Float8 Sterbenz regression produced
     by cvc5 1.3.4 are about 22 MiB.  Keep the admission boundary tied to the
     ordinary release proof format and retain a fixed, cheaply checked
     power-of-two cap. *)
  val max_proof_bytes = 32 * 1024 * 1024
  (* Compatibility name retained for callers and diagnostics tests that
     predate the CPC proof-text gate. *)
  val max_z3_proof_bytes = max_proof_bytes
  val max_bitblast_step_time = Time.fromSeconds 10
  val max_bitblast_term_nodes = 200000
  (* TASK_17 measurement, commit 1f0a12403, Poly/ML 5.9.2: the authentic
     word8 COND_BBLAST bridge clause has 1,695,351 tree nodes and completed
     in 40.158 s (the prior independent measurement was 40.318 s).  Small
     word8 word_decide/rewrite/BV-th-lemma cases took 0.038/0.083/0.006 s.
     Two million nodes admits that legitimate clause; 90 seconds gives more
     than 2x time headroom.  TASK_15's owned-fragment precondition is the
     primary defense; these limits are the heap-pressure backstop. *)
  val max_bv_replay_step_time = Time.fromSeconds 90
  val max_bv_replay_term_nodes = 2000000
  (* This replay class is measured as a DAG, not an unfolded tree.  The
     authentic word32 midpoint proof contains a 4,332-node shared skeleton;
     8,192 is the next fixed power-of-two capacity.  Each admitted attempt
     still has its independent 30-second kernel-replay boundary. *)
  val max_skeleton_replay_step_time = Time.fromSeconds 30
  val max_skeleton_replay_dag_nodes = 8192
  (* Discharging a deferred proof hypothesis runs a general first-order
     search, so bound it: an undischargeable hypothesis must fail with a
     diagnostic rather than hang the replay. *)
  val max_hypothesis_entailment_time = Time.fromSeconds 10

  (* E0 profiling is opt-in and bounded.  Profile's in-memory counters retain
     successful and exceptional timings; these compact messages additionally
     survive an enclosing timeout when the caller retains stdout.  Never put
     terms in this channel. *)
  val max_e0_messages = 1024

  type e0_invocation =
    {messages : int ref,
     replay_snapshot_emitted : bool ref,
     replay_snapshot_message : string option ref,
     profile_baseline : (string * Profile.call_info) list}

  val current_e0_invocation = ref (NONE : e0_invocation option)
  val last_e0_message_count = ref 0
  val last_e0_profile_names = ref ([] : string list)
  val last_e0_replay_snapshot = ref (NONE : string option)
  val last_e0_replay_snapshot_count = ref 0

  fun e0_enabled () = Option.isSome (!current_e0_invocation)

  fun is_resource_gate holerr =
    Feedback.top_structure_of holerr = "SmtResource" andalso
    String.isPrefix "resource-gated: " (Feedback.message_of holerr)

  fun terminal_diagnostic_exception exn =
    case exn of
      Interrupt => true
    | Timeout.TIMEOUT _ => true
    | Feedback.HOL_ERR holerr => is_resource_gate holerr
    | _ => false

  (* Diagnostic work is secondary to the proof action.  A terminal primary
     exception keeps precedence; otherwise a terminal secondary exception
     remains visible.  The final continuation either preserves a nonterminal
     primary exception or discards a nonterminal diagnostic failure. *)
  fun resolve_diagnostic_exception original diagnostic nonterminal =
    if terminal_diagnostic_exception original then
      (ignore (Exn.capture diagnostic ()); raise original)
    else
      case Exn.capture diagnostic () of
        Exn.Res _ => nonterminal original
      | Exn.Exn exn =>
          if terminal_diagnostic_exception exn then raise exn
          else nonterminal original

  val e0_diagnostic_hook = ref (NONE : (string -> unit) option)

  fun invoke_e0_diagnostic_hook site =
    case !e0_diagnostic_hook of NONE => () | SOME hook => hook site

  fun with_e0_diagnostic_hook_for_test hook action input =
    let
      val previous = !e0_diagnostic_hook
      fun restore () = e0_diagnostic_hook := previous
      fun work () = (e0_diagnostic_hook := SOME hook; action input)
    in
      Portable.finally restore work ()
    end

  fun start_e0_invocation action input =
    let
      val invocation =
        {messages = ref 0,
         replay_snapshot_emitted = ref false,
         replay_snapshot_message = ref NONE,
         profile_baseline = Profile.results ()}
      fun restore () =
        (last_e0_message_count := !(#messages invocation);
         last_e0_replay_snapshot :=
           !(#replay_snapshot_message invocation);
         last_e0_replay_snapshot_count :=
           (if !(#replay_snapshot_emitted invocation) then 1 else 0);
         current_e0_invocation := NONE)
      fun work () =
        (last_e0_profile_names := [];
         last_e0_replay_snapshot := NONE;
         last_e0_replay_snapshot_count := 0;
         current_e0_invocation := SOME invocation;
         action input)
    in
      Portable.finally restore work ()
    end

  fun with_e0_invocation action input =
    case !current_e0_invocation of
      SOME _ => action input
    | NONE =>
        if OS.Process.getEnv "HOL4_SMT_E0_PROFILE" <> SOME "1" then
          action input
        else start_e0_invocation action input

  (* Deterministic diagnostics fixtures use the same invocation lifecycle
     without changing the process environment. *)
  fun with_e0_invocation_for_test action input =
    case !current_e0_invocation of
      SOME _ => action input
    | NONE => start_e0_invocation action input

  fun bounded_text maximum text =
    if String.size text <= maximum then text
    else if maximum <= 0 then ""
    else if maximum <= 3 then String.substring (text, 0, maximum)
    else String.substring (text, 0, maximum - 3) ^ "..."

  fun emit_e0 message =
    (case !current_e0_invocation of
       NONE => ()
     | SOME {messages, ...} =>
         if !messages < max_e0_messages then
           (messages := !messages + 1;
            Feedback.HOL_MESG ("HOLSMT_E0 " ^ message);
            TextIO.flushOut TextIO.stdOut)
         else if !messages = max_e0_messages then
           (messages := !messages + 1;
            Feedback.HOL_MESG "HOLSMT_E0 messages=suppressed";
            TextIO.flushOut TextIO.stdOut)
         else ())
    handle exn =>
      if terminal_diagnostic_exception exn then raise exn else ()

  (* The replay boundary gets one compact message outside the ordinary phase
     quota.  Set the latch before attempting output, so an output failure
     cannot cause a duplicate snapshot or replace the replay exception. *)
  fun emit_e0_replay_snapshot message =
    (let
       val message_open = "<<HOL message: "
       val prefix = "HOLSMT_E0 "
       val message_close = ">>"
       (* Feedback.format_MESG appends one LF to the rendered message. *)
       val snapshot = bounded_text
         (4096 - String.size message_open - String.size prefix -
          String.size message_close - String.size "\n") message
     in
       case !current_e0_invocation of
         NONE => ()
       | SOME {replay_snapshot_emitted, replay_snapshot_message, ...} =>
           if !replay_snapshot_emitted then ()
           else
             (replay_snapshot_emitted := true;
              replay_snapshot_message := SOME snapshot;
              invoke_e0_diagnostic_hook "replay-snapshot";
              Feedback.HOL_MESG (prefix ^ snapshot);
              TextIO.flushOut TextIO.stdOut)
     end)
    handle exn =>
      if terminal_diagnostic_exception exn then raise exn else ()

  fun exception_class exn =
    case exn of
      Feedback.HOL_ERR holerr =>
        Feedback.top_structure_of holerr ^ "." ^
        Feedback.top_function_of holerr ^ ":" ^
        bounded_text 240 (Feedback.message_of holerr)
    | _ => General.exnName exn

  fun profile_phase name f x =
    if not (e0_enabled ()) then f x
    else
      Profile.profile_with_exn_name ("E0(" ^ name ^ ")")
        (fn x =>
        let
          val real_timer = Timer.startRealTimer ()
          val cpu_timer = Timer.startCPUTimer ()
          val _ = emit_e0 ("phase=start name=" ^ name)
          fun finish status =
            (let
               val _ = invoke_e0_diagnostic_hook "profile-finish"
               val {nongc, gc} = Timer.checkCPUTimes cpu_timer
               val real = Timer.checkRealTimer real_timer
               val gc_time = Time.+ (#usr gc, #sys gc)
             in
               emit_e0 ("phase=" ^ status ^ " name=" ^ name ^
                 " wall=" ^ Time.toString real ^
                 " usr=" ^ Time.toString (#usr nongc) ^
                 " sys=" ^ Time.toString (#sys nongc) ^
                 " gc=" ^ Time.toString gc_time)
             end handle exn =>
               if terminal_diagnostic_exception exn then raise exn else ())
          val result = f x
            handle exn => resolve_diagnostic_exception exn
              (fn () => finish
                ("failure exception=" ^ exception_class exn))
              (fn original => raise original)
          val _ = finish "end"
        in
          result
        end) x

  fun emit_profile_summary () =
    case !current_e0_invocation of
      NONE => ()
    | SOME {profile_baseline, ...} =>
      let
        fun previous name =
          case List.find (fn (old_name, _) => old_name = name)
              profile_baseline of
            SOME (_, info) => SOME info
          | NONE => NONE
        fun time_delta current old =
          if Time.compare (current, old) = LESS then Time.zeroTime
          else Time.- (current, old)
        fun delta (name, current : Profile.call_info) =
          case previous name of
            NONE => (name, current)
          | SOME old =>
              (name,
               {usr = time_delta (#usr current) (#usr old),
                sys = time_delta (#sys current) (#sys old),
                gc = time_delta (#gc current) (#gc old),
                real = time_delta (#real current) (#real old),
                n = Int.max (0, #n current - #n old)})
        fun observed (_, {usr, sys, gc, real, n} : Profile.call_info) =
          n > 0 orelse
          List.exists (fn time => Time.compare (time, Time.zeroTime) <> EQUAL)
            [usr, sys, gc, real]
        val results = List.filter observed (List.map delta (Profile.results ()))
        val _ = last_e0_profile_names := List.map Lib.fst results
        val sorted = Listsort.sort
          (fn ((_, left), (_, right)) =>
            Time.compare (#real right, #real left)) results
        fun take 0 _ = []
          | take _ [] = []
          | take n (item :: rest) = item :: take (n - 1) rest
        fun one (name, {usr, sys, gc, real, n}) =
          bounded_text 64 name ^ ":n=" ^ Int.toString n ^
          ",wall=" ^ Time.toString real ^
          ",usr=" ^ Time.toString usr ^
          ",sys=" ^ Time.toString sys ^
          ",gc=" ^ Time.toString gc
        val summary = String.concatWith " | " (List.map one (take 16 sorted))
      in
        emit_e0 ("profile entries=" ^ Int.toString (List.length results) ^
          " top16=" ^ bounded_text 3500 summary)
      end handle exn =>
        if terminal_diagnostic_exception exn then raise exn else ()

  fun last_e0_message_count_for_test () = !last_e0_message_count

  fun last_e0_profile_names_for_test () = !last_e0_profile_names

  fun last_e0_replay_snapshot_for_test () = !last_e0_replay_snapshot

  fun last_e0_replay_snapshot_count_for_test () =
    !last_e0_replay_snapshot_count

  fun exhaust_e0_message_quota_for_test () =
    case !current_e0_invocation of
      NONE => ()
    | SOME {messages, ...} => messages := max_e0_messages

  val diagnostic_prefix = "resource-gated: fp-bitblast; "
  val feature_prefix = "resource-gate:FloatingPoint:"

  fun resource_diagnostic_prefix category =
    if category = "FloatingPoint" then diagnostic_prefix
    else "resource-gated: " ^ String.map Char.toLower category ^ "-replay; "

  fun resource_feature category case_id =
    "resource-gate:" ^ category ^ ":" ^ case_id

  fun max_step_time_for category =
    if category = "BitVector" then max_bv_replay_step_time
    else if category = "Skeleton" then max_skeleton_replay_step_time
    else max_bitblast_step_time

  fun max_term_nodes_for category =
    if category = "BitVector" then max_bv_replay_term_nodes
    else max_bitblast_term_nodes

  fun feature case_id = resource_feature "FloatingPoint" case_id

  fun proof_size_diagnostic_for category case_id observed =
    resource_diagnostic_prefix category ^
    "limit=proof-size; observed=" ^ Int.toString observed ^
    " bytes; maximum=" ^ Int.toString max_proof_bytes ^
    " bytes; feature=" ^ resource_feature category case_id

  fun step_time_diagnostic_for category case_id =
    resource_diagnostic_prefix category ^
    "limit=step-time; maximum=" ^
    LargeInt.toString (Time.toSeconds (max_step_time_for category)) ^
    " s; feature=" ^ resource_feature category case_id

  fun term_size_diagnostic_for category case_id observed =
    resource_diagnostic_prefix category ^
    "limit=term-size; observed=" ^ Int.toString observed ^
    " nodes; maximum=" ^ Int.toString (max_term_nodes_for category) ^
    " nodes; feature=" ^ resource_feature category case_id

  fun dag_size_diagnostic_with_limit category case_id maximum observed =
    resource_diagnostic_prefix category ^
    "limit=dag-size; observed=" ^ Int.toString observed ^
    " nodes; maximum=" ^ Int.toString maximum ^
    " nodes; feature=" ^ resource_feature category case_id

  fun dag_size_diagnostic_for category case_id observed =
    dag_size_diagnostic_with_limit category case_id
      max_skeleton_replay_dag_nodes observed

  fun proof_size_diagnostic case_id observed =
    proof_size_diagnostic_for "FloatingPoint" case_id observed

  fun step_time_diagnostic case_id =
    step_time_diagnostic_for "FloatingPoint" case_id

  fun term_size_diagnostic case_id observed =
    term_size_diagnostic_for "FloatingPoint" case_id observed

  fun raise_gate function_name diagnostic =
    raise ERR function_name diagnostic

  fun check_proof_size case_id observed =
    if observed <= max_z3_proof_bytes then
      ()
    else
      raise_gate "check_proof_size"
        (proof_size_diagnostic case_id observed)

  fun position_to_int_or_over_cap position =
    Position.toInt position
    handle Overflow => max_proof_bytes + 1

  (* 'proof_start' is the byte count consumed while reading solver status.
     Checking the remaining file size does no parsing and allocates no
     proof-sized string, so even very large outputs are rejected cheaply. *)
  fun remaining_file_bytes path proof_start =
    let val total = position_to_int_or_over_cap (OS.FileSys.fileSize path)
    in Int.max (0, total - proof_start) end

  fun with_proof_size_gate case_id path proof_start instream parse =
    let
      val observed = remaining_file_bytes path proof_start
      val () = check_proof_size case_id observed
    in
      parse instream
    end

  val with_z3_proof_size_gate = with_proof_size_gate

  fun check_term_size_for category case_id observed =
    if observed <= max_term_nodes_for category then
      ()
    else
      raise_gate "check_term_size"
        (term_size_diagnostic_for category case_id observed)

  fun check_term_size case_id observed =
    check_term_size_for "FloatingPoint" case_id observed

  (* Pointer-cache indexing must distinguish broad, homogeneous application
     DAGs without unfolding their trees.  Two bounded operand paths reach
     beyond the identical operator prefixes of curried applications.  This
     is only an index hint: every hit is resolved by exact pointer equality. *)
  val pointer_bucket = Term.pointer_bucket 16

  (* Repeated primitive types should not migrate to the cold end of a
     type-admission cache as independently allocated types are discovered.
     Move a physical hit to the front; retain every entry and use no
     structural equality or context-dependent classifier as a cache key. *)
  fun recent_pointer_lookup cache key =
    let
      fun seek _ [] = NONE
        | seek previous ((entry as (saved, value)) :: rest) =
            if Portable.pointer_eq (key, saved) then
              (if List.null previous then ()
               else cache := entry :: List.revAppend (previous, rest);
               SOME value)
            else seek (entry :: previous) rest
    in seek [] (!cache) end

  (* Preserve the binder-inclusive unfolded-tree metric, but compute each
     shared compound node's size once.  Summaries saturate at limit + 1;
     neither sharing nor memoization changes admission.  Keep the raw-size
     preflight before opening a binder, since dest_abs may normalize its
     entire body.  An ordinary tree visitor advances at every lookup and
     pointer comparison, so collision-heavy or unshared inputs can finish
     without waiting for the memoized traversal.  Cache hints only index
     exact physical-identity checks. *)
  fun term_nodes_up_to limit root =
    if limit < 1 then 1
    else
    let
      exception Exceeded
      exception TreeComplete of int
      datatype action = Visit of Term.term
        | Finish of Term.term * int * Term.term * Term.term
      val maximum_buckets = 4093
      val buckets = ref (Array.array
        (32, [] : (Term.term * int * int) list))
      val entries = ref 0
      val observed = ref 0
      val tree_pending = ref [root]
      val tree_count = ref 0
      fun tree_step () =
        case !tree_pending of
          [] => raise TreeComplete (!tree_count)
        | term :: rest =>
            let
              val count = !tree_count + 1
              val _ = if count <= limit then () else raise Exceeded
              val children =
                if Term.is_comb term then
                  let val (left, right) = Term.dest_comb term
                  in [left, right] end
                else if Term.is_abs term then
                  (case Term.term_size_bounded (limit - count + 1) term of
                     NONE => raise Exceeded
                   | SOME _ =>
                       let val (binder, body) = Term.dest_abs term
                       in [binder, body] end)
                else []
            in tree_pending := children @ rest; tree_count := count end
      val hint = pointer_bucket maximum_buckets
      fun find term code =
        (tree_step ();
         case List.find
            (fn (prior, _, _) =>
              (tree_step (); Portable.pointer_eq (term, prior)))
            (Array.sub (!buckets, code mod Array.length (!buckets))) of
          SOME (_, _, size) => SOME size
        | NONE => NONE)
      fun save term code size =
        let
          val current = !buckets
          val capacity = Array.length current
          val grown =
            if capacity < maximum_buckets andalso
               !entries >= 2 * capacity then
              let
                val target = Array.array
                  (Int.min (maximum_buckets, 2 * capacity), [])
                fun reindex (entry as (_, code, _)) =
                  let val slot = code mod Array.length target in
                    Array.update (target, slot,
                      entry :: Array.sub (target, slot))
                  end
                val _ = Array.app (List.app reindex) current
              in target end
            else current
          val slot = code mod Array.length grown
          val _ = Array.update (grown, slot,
            (term, code, size) :: Array.sub (grown, slot))
        in buckets := grown; entries := !entries + 1 end
      fun compound term = Term.is_comb term orelse Term.is_abs term
      fun completed term =
        if not (compound term) then 1
        else case find term (hint term) of
          SOME size => size
        | NONE => raise ERR "term_nodes_up_to" "incomplete size traversal"
      fun loop [] = completed root
        | loop (Visit term :: pending) =
            if not (compound term) then loop pending
            else
              let val code = hint term in
                case find term code of
                  SOME _ => loop pending
                | NONE =>
                    let
                      val _ = observed := !observed + 1
                      val _ = if !observed <= limit then ()
                        else raise Exceeded
                      val (left, right) =
                        if Term.is_comb term then Term.dest_comb term
                        else case Term.term_size_bounded limit term of
                          NONE => raise Exceeded
                        | SOME _ => Term.dest_abs term
                    in loop (Visit left :: Visit right ::
                      Finish (term, code, left, right) :: pending) end
              end
        | loop (Finish (term, code, left, right) :: pending) =
            let
              val left_size = completed left
              val right_size = completed right
              val _ = if left_size < limit andalso
                         right_size <= limit - left_size - 1 then ()
                else raise Exceeded
              val _ = save term code (1 + left_size + right_size)
            in loop pending end
    in
      loop [Visit root] handle Exceeded => limit + 1
        | TreeComplete size => size
    end

  fun check_resource_goal category case_id goal =
    let val limit = max_term_nodes_for category in
      check_term_size_for category case_id (term_nodes_up_to limit goal)
    end

  (* Exact structural keys for bounded replay caches.  Compound keys compare
     canonical child IDs instead of repeatedly comparing entire term DAGs.
     Types and declaration identities are part of leaf keys; abstractions
     retain the public kernel's alpha-equivalence boundary.  Exhaustion is a
     cache miss, not a replay refusal, and reservations bound pending work as
     well as retained physical nodes. *)
  fun new_bounded_term_index maximum =
    let
      datatype key = Variable of string * int
        | Constant of KernelSig.kernelid * int
        | Application of int * int
      fun compare (Variable fields, Variable fields') =
            Lib.pair_compare (String.compare, Int.compare) (fields, fields')
        | compare (Variable _, _) = LESS
        | compare (_, Variable _) = GREATER
        | compare (Constant fields, Constant fields') =
            Lib.pair_compare (KernelSig.id_compare, Int.compare)
              (fields, fields')
        | compare (Constant _, _) = LESS
        | compare (_, Constant _) = GREATER
        | compare (Application fields, Application fields') =
            Lib.pair_compare (Int.compare, Int.compare) (fields, fields')
      val nodes = ref (Redblackmap.mkDict compare)
      val abstractions = ref (Redblackmap.mkDict Term.compare)
      val types = ref (Redblackmap.mkDict Type.compare)
      val next = ref 0
      val reserved = ref 0
      val count = 4093
      val physical = Array.array
        (count, [] : (Term.term * int) list)
      fun type_id ty =
        case Redblackmap.peek (!types, ty) of
          SOME id => id
        | NONE =>
            let val id = Redblackmap.numItems (!types)
            in types := Redblackmap.insert (!types, ty, id); id end
      fun fresh () = let val id = !next in next := id + 1; id end
      fun intern key =
        case Redblackmap.peek (!nodes, key) of
          SOME id => id
        | NONE =>
            let val id = fresh ()
            in nodes := Redblackmap.insert (!nodes, key, id); id end
      fun visit term =
        let
          val bucket = pointer_bucket count term
          val found = List.find
            (fn (prior, _) => Portable.pointer_eq (term, prior))
            (Array.sub (physical, bucket))
        in
          case found of
            SOME (_, id) => SOME id
          | NONE =>
              if !reserved >= maximum then NONE
              else
                let
                  val _ = reserved := !reserved + 1
                  val result =
                    if Term.is_var term then SOME (intern
                      (Variable (#1 (Term.dest_var term),
                        type_id (Term.type_of term))))
                    else if Term.is_const term then
                      let val {Name, Ty, ...} = Term.dest_thy_constid term in
                        SOME (intern (Constant (Name, type_id Ty)))
                      end
                    else if Term.is_comb term then
                      let val (left, right) = Term.dest_comb term in
                        case (visit left, visit right) of
                          (SOME left_id, SOME right_id) =>
                            SOME (intern (Application (left_id, right_id)))
                        | _ => NONE
                      end
                    else
                      (case Redblackmap.peek (!abstractions, term) of
                         SOME id => SOME id
                       | NONE =>
                           let val id = fresh () in
                             abstractions := Redblackmap.insert
                               (!abstractions, term, id);
                             SOME id
                           end)
                  val _ = case result of
                      NONE => ()
                    | SOME id => Array.update (physical, bucket,
                        (term, id) :: Array.sub (physical, bucket))
                in result end
        end
    in visit end

  (* Replay terms are DAGs.  Count each node once while retaining the
     saturated unfolded-tree metric used by the skeleton profiler.  Keeping
     this measurement here gives admission gates and the skeleton engine one
     structural cost model instead of two subtly different traversals. *)
  val max_metric =
    case Int.maxInt of
      SOME maximum => maximum
    | NONE => 1073741823

  fun saturated_add left right =
    if left >= max_metric - right then max_metric else left + right

  fun term_children term =
    if Term.is_comb term then
      let val (operator, operand) = Term.dest_comb term
      in [operator, operand] end
    else if Term.is_abs term then
      (case Term.term_size_bounded max_bv_replay_term_nodes term of
         NONE =>
           (check_term_size_for "BitVector" "binder-opening"
              (max_bv_replay_term_nodes + 1);
            [])
       | SOME _ =>
           let val (_, body) = Term.dest_abs term in [body] end)
    else []

  type bounded_structure = {
    dag_nodes : int,
    edges : int,
    max_binder_depth : int,
    max_identifier_bytes : int,
    complete : bool
  }

  (* A compact diagnostic scan with a hard distinct-node bound.  Edges count
     children of each admitted DAG node once; identifier sizes come only from
     variable and constant metadata and never render a term. *)
  fun bounded_structure_with_children children_of inspect limit root
      : bounded_structure =
    let
      val bucket_count = 4093
      val seen_buckets =
        Array.array (bucket_count, [] : Term.term list)
      val pointer_hash = pointer_bucket bucket_count
      fun seen term =
        let
          val index = pointer_hash term
          val bucket = Array.sub (seen_buckets, index)
        in
          if List.exists
               (fn seen_term => Portable.pointer_eq (term, seen_term)) bucket
          then true
          else
            (Array.update (seen_buckets, index, term :: bucket); false)
        end
      fun identifier_bytes term =
        String.size (Lib.fst (Term.dest_var term))
        handle Feedback.HOL_ERR _ =>
          String.size (#Name (Term.dest_thy_const term))
          handle Feedback.HOL_ERR _ => 0
      fun loop ([], nodes, edges, depth, identifier) =
            {dag_nodes = nodes, edges = edges, max_binder_depth = depth,
             max_identifier_bytes = identifier, complete = true}
        | loop ((term, binder_depth) :: pending, nodes, edges,
            depth, identifier) =
            if seen term then
              loop (pending, nodes, edges, depth, identifier)
            else
              let
                val _ = inspect term
                val nodes = nodes + 1
                val children = children_of term
                val edges = saturated_add edges (List.length children)
                val depth = Int.max (depth, binder_depth)
                val identifier = Int.max
                  (identifier, identifier_bytes term)
                val next_depth =
                  if Term.is_abs term then binder_depth + 1
                  else binder_depth
                val pending = List.map
                  (fn child => (child, next_depth)) children @ pending
              in
                if nodes > limit then
                  {dag_nodes = nodes, edges = edges,
                   max_binder_depth = depth,
                   max_identifier_bytes = identifier, complete = false}
                else
                  loop (pending, nodes, edges, depth, identifier)
              end
    in
      loop ([(root, 0)], 0, 0, 0, 0)
  end

  val bounded_structure_with_inspector =
    bounded_structure_with_children term_children

  fun bounded_structure limit root =
    bounded_structure_with_inspector (fn _ => ()) limit root

  (* A bounded graph serialization for diagnostics and extracted fixtures.
     It records applications, abstractions, and identifier metadata with
     explicit node references, so repeated subterms stay shared.  Identifier
     labels are truncated independently; this digest is attribution metadata,
     never proof evidence or a replay key. *)
  fun bounded_graph_digest limit root =
    let
      val ids = ref ([] : (Term.term * int) list)
      val next_id = ref 0
      val entries = ref ([] : string list)
      fun label term =
        if Term.is_var term then
          "v:" ^ bounded_text 96 (Lib.fst (Term.dest_var term))
        else if Term.is_const term then
          let val {Thy, Name, ...} = Term.dest_thy_const term
          in "c:" ^ bounded_text 96 (Thy ^ "$" ^ Name) end
        else if Term.is_abs term then "lambda"
        else if Term.is_comb term then "apply"
        else "term"
      fun visit term =
        case List.find
            (fn (seen_term, _) => Portable.pointer_eq (term, seen_term))
            (!ids) of
          SOME (_, id) => id
        | NONE =>
            let
              val id = !next_id
              val _ = next_id := id + 1
              val _ = id < limit orelse
                raise ERR "bounded_graph_digest"
                  "diagnostic graph exceeds its bound"
              val _ = ids := (term, id) :: !ids
              val child_ids = List.map visit (term_children term)
              val entry = Int.toString id ^ ":" ^ label term ^ "(" ^
                String.concatWith "," (List.map Int.toString child_ids) ^ ");"
              val _ = entries := entry :: !entries
            in
              id
            end
      val _ = visit root
      val serialization = String.concat (List.rev (!entries))
    in
      {digest = MLSYSPortable.md5sum serialization,
       serialization = bounded_text 2048 serialization,
       serialization_bytes = String.size serialization,
       nodes = !next_id}
    end

  fun term_measure term =
    let
      datatype key = Variable of string * int
        | Constant of KernelSig.kernelid * int
        | Application of int * int
      fun key_compare (Variable (name, ty), Variable (name', ty')) =
            Lib.pair_compare (String.compare, Int.compare)
              ((name, ty), (name', ty'))
        | key_compare (Variable _, _) = LESS
        | key_compare (_, Variable _) = GREATER
        | key_compare (Constant (id, ty), Constant (id', ty')) =
            Lib.pair_compare (KernelSig.id_compare, Int.compare)
              ((id, ty), (id', ty'))
        | key_compare (Constant _, _) = LESS
        | key_compare (_, Constant _) = GREATER
        | key_compare (Application children, Application children') =
            Lib.pair_compare (Int.compare, Int.compare) (children, children')
      val nodes = ref (Redblackmap.mkDict key_compare)
      val abstractions = ref (Redblackmap.mkDict Term.compare)
      val types = ref (Redblackmap.mkDict Type.compare)
      val next = ref 0
      val buckets = 4093
      val physical = Array.array (buckets, [] : (Term.term * (int * int)) list)
      fun type_id ty =
        case Redblackmap.peek (!types, ty) of
          SOME id => id
        | NONE =>
            let val id = Redblackmap.numItems (!types)
            in types := Redblackmap.insert (!types, ty, id); id end
      fun fresh size =
        let val id = !next in next := id + 1; (id, size) end
      fun intern key size =
        case Redblackmap.peek (!nodes, key) of
          SOME result => result
        | NONE =>
            let val result = fresh size
            in nodes := Redblackmap.insert (!nodes, key, result); result end
      fun visit term =
        let
          val bucket = pointer_bucket buckets term
        in
          case List.find (fn (saved, _) => Portable.pointer_eq (term, saved))
              (Array.sub (physical, bucket)) of
            SOME (_, result) => result
          | NONE =>
              let
                val result =
                  if Term.is_var term then intern
                    (Variable (#1 (Term.dest_var term),
                       type_id (Term.type_of term))) 1
                  else if Term.is_const term then
                    let val {Name, Ty, ...} = Term.dest_thy_constid term in
                      intern (Constant (Name, type_id Ty)) 1
                    end
                  else if Term.is_comb term then
                    let
                      val (left, right) = Term.dest_comb term
                      val (left_id, left_size) = visit left
                      val (right_id, right_size) = visit right
                    in intern (Application (left_id, right_id))
                      (saturated_add 1 (saturated_add left_size right_size)) end
                  else
                    (* Alpha-equivalence of abstractions is a public-kernel
                       boundary.  Retain the old structural key and bounded
                       opening here; all surrounding applications use IDs. *)
                    (case Redblackmap.peek (!abstractions, term) of
                       SOME result => result
                     | NONE =>
                         let val result = fresh (List.foldl
                           (fn (child, size) => saturated_add size
                             (#2 (visit child))) 1 (term_children term))
                         in abstractions := Redblackmap.insert
                           (!abstractions, term, result); result end)
                val _ = Array.update (physical, bucket,
                  (term, result) :: Array.sub (physical, bucket))
              in result end
        end
    in
      {tree_nodes = #2 (visit term), dag_nodes = !next}
    end

  fun tree_nodes term = #tree_nodes (term_measure term)

  fun dag_nodes term = #dag_nodes (term_measure term)

  (* Admission needs only to distinguish an in-budget physical DAG from an
     oversized one.  [bounded_structure] uses pointer identity, so equal but
     independently rebuilt subgraphs remain distinct and the scan stops at
     the first node beyond the limit without computing an unfolded-tree
     metric. *)
  fun dag_nodes_up_to limit root =
    #dag_nodes (bounded_structure limit root)

  fun dag_nodes_up_to_with_inspector inspect limit root =
    #dag_nodes (bounded_structure_with_inspector inspect limit root)

  fun check_dag_size_for category case_id observed =
    if observed <= max_skeleton_replay_dag_nodes then ()
    else raise_gate "check_dag_size_for"
      (dag_size_diagnostic_for category case_id observed)

  fun check_dag_size_with_limit category case_id maximum observed =
    if observed <= maximum then ()
    else raise_gate "check_dag_size_with_limit"
      (dag_size_diagnostic_with_limit category case_id maximum observed)

  (* Classification must certify absence over the stored DAG, not enumerate
     every path through its unfolded tree.  Finding a witness ends the scan;
     an incomplete bounded scan is a resource refusal, never false absence. *)
  fun contains_with_pruning prune predicate root =
    let
      exception Found
      val maximum = max_bv_replay_term_nodes
      fun inspect node =
        if not (prune node) andalso predicate node then raise Found else ()
      fun children node = if prune node then [] else term_children node
    in
      (let
         val summary = bounded_structure_with_children
           children inspect maximum root
         val _ = if #complete summary then () else
           check_dag_size_with_limit "Skeleton" "theory-classification"
             maximum (#dag_nodes summary)
       in false end)
      handle Found => true
    end

  val contains = contains_with_pruning (fn _ => false)

  fun check_bitblast_goal case_id goal =
    check_resource_goal "FloatingPoint" case_id goal

  fun with_resource_step_time category case_id f x =
    Timeout.apply (max_step_time_for category) f x
    handle Timeout.TIMEOUT _ =>
      raise_gate "with_bitblast_step_time"
        (step_time_diagnostic_for category case_id)

  fun with_bitblast_step_time case_id f x =
    with_resource_step_time "FloatingPoint" case_id f x

end
