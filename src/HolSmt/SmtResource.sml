(* Copyright (c) 2026 The HOL4 contributors. *)

(* Fixed resource budget for checked FloatingPoint bit-blast replay. *)

structure SmtResource =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtResource"

  (* P5.3: these are the single source of truth for the D12 budget. *)
  val max_proof_bytes = 16 * 1024 * 1024
  (* Compatibility name retained for callers and diagnostics tests that
     predate the CPC proof-text gate. *)
  val max_z3_proof_bytes = max_proof_bytes
  val max_bitblast_step_time = Time.fromSeconds 10
  val max_bitblast_term_nodes = 200000

  val diagnostic_prefix = "resource-gated: fp-bitblast; "
  val feature_prefix = "resource-gate:FloatingPoint:"

  fun resource_diagnostic_prefix category =
    if category = "FloatingPoint" then diagnostic_prefix
    else "resource-gated: " ^ String.map Char.toLower category ^ "-replay; "

  fun resource_feature category case_id =
    "resource-gate:" ^ category ^ ":" ^ case_id

  fun feature case_id = resource_feature "FloatingPoint" case_id

  fun proof_size_diagnostic_for category case_id observed =
    resource_diagnostic_prefix category ^
    "limit=proof-size; observed=" ^ Int.toString observed ^
    " bytes; maximum=" ^ Int.toString max_proof_bytes ^
    " bytes; feature=" ^ resource_feature category case_id

  fun step_time_diagnostic_for category case_id =
    resource_diagnostic_prefix category ^
    "limit=step-time; maximum=" ^
    LargeInt.toString (Time.toSeconds max_bitblast_step_time) ^
    " s; feature=" ^ resource_feature category case_id

  fun term_size_diagnostic_for category case_id observed =
    resource_diagnostic_prefix category ^
    "limit=term-size; observed=" ^ Int.toString observed ^
    " nodes; maximum=" ^ Int.toString max_bitblast_term_nodes ^
    " nodes; feature=" ^ resource_feature category case_id

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

  (* 'proof_start' is the byte count consumed while reading Z3's status.
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
    if observed <= max_bitblast_term_nodes then
      ()
    else
      raise_gate "check_term_size"
        (term_size_diagnostic_for category case_id observed)

  fun check_term_size case_id observed =
    check_term_size_for "FloatingPoint" case_id observed

  (* Proof-parser terms are DAGs with extensive let-sharing.  [term_size]
     unfolds that sharing and turned a 100 KB comparison into 335 million
     visits before the cap could fire.  Preserve its tree-node semantics but
     stop as soon as the fixed limit is exceeded. *)
  fun term_nodes_up_to limit root =
    let
      fun loop ([], count) = count
        | loop (tm :: pending, count) =
            let val count = count + 1
            in
              if count > limit then count
              else if Term.is_comb tm then
                let val (rator, rand) = Term.dest_comb tm
                in loop (rator :: rand :: pending, count) end
              else if Term.is_abs tm then
                let val (binder, body) = Term.dest_abs tm
                in loop (binder :: body :: pending, count) end
              else
                loop (pending, count)
            end
    in
      loop ([root], 0)
    end

  fun check_resource_goal category case_id goal =
    check_term_size_for category case_id
      (term_nodes_up_to max_bitblast_term_nodes goal)

  fun check_bitblast_goal case_id goal =
    check_resource_goal "FloatingPoint" case_id goal

  fun with_resource_step_time category case_id f x =
    Timeout.apply max_bitblast_step_time f x
    handle Timeout.TIMEOUT _ =>
      raise_gate "with_bitblast_step_time"
        (step_time_diagnostic_for category case_id)

  fun with_bitblast_step_time case_id f x =
    with_resource_step_time "FloatingPoint" case_id f x

  fun is_resource_gate holerr =
    Feedback.top_structure_of holerr = "SmtResource" andalso
    String.isPrefix "resource-gated: " (Feedback.message_of holerr)

end
