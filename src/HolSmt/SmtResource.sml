(* Copyright (c) 2026 The HOL4 contributors. *)

(* Fixed resource budget for checked FloatingPoint bit-blast replay. *)

structure SmtResource =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtResource"

  (* P5.3: these are the single source of truth for the D12 budget. *)
  val max_z3_proof_bytes = 16 * 1024 * 1024
  val max_bitblast_step_time = Time.fromSeconds 10
  val max_bitblast_term_nodes = 200000

  val diagnostic_prefix = "resource-gated: fp-bitblast; "
  val feature_prefix = "resource-gate:FloatingPoint:"

  fun feature case_id = feature_prefix ^ case_id

  fun proof_size_diagnostic case_id observed =
    diagnostic_prefix ^
    "limit=proof-size; observed=" ^ Int.toString observed ^
    " bytes; maximum=" ^ Int.toString max_z3_proof_bytes ^
    " bytes; feature=" ^ feature case_id

  fun step_time_diagnostic case_id =
    diagnostic_prefix ^
    "limit=step-time; maximum=" ^
    LargeInt.toString (Time.toSeconds max_bitblast_step_time) ^
    " s; feature=" ^ feature case_id

  fun term_size_diagnostic case_id observed =
    diagnostic_prefix ^
    "limit=term-size; observed=" ^ Int.toString observed ^
    " nodes; maximum=" ^ Int.toString max_bitblast_term_nodes ^
    " nodes; feature=" ^ feature case_id

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
    handle Overflow => max_z3_proof_bytes + 1

  (* 'proof_start' is the byte count consumed while reading Z3's status.
     Checking the remaining file size does no parsing and allocates no
     proof-sized string, so even very large outputs are rejected cheaply. *)
  fun remaining_file_bytes path proof_start =
    let val total = position_to_int_or_over_cap (OS.FileSys.fileSize path)
    in Int.max (0, total - proof_start) end

  fun with_z3_proof_size_gate case_id path proof_start instream parse =
    let
      val observed = remaining_file_bytes path proof_start
      val () = check_proof_size case_id observed
    in
      parse instream
    end

  fun check_term_size case_id observed =
    if observed <= max_bitblast_term_nodes then
      ()
    else
      raise_gate "check_term_size" (term_size_diagnostic case_id observed)

  fun check_bitblast_goal case_id goal =
    check_term_size case_id (Term.term_size goal)

  fun with_bitblast_step_time case_id f x =
    Timeout.apply max_bitblast_step_time f x
    handle Timeout.TIMEOUT _ =>
      raise_gate "with_bitblast_step_time" (step_time_diagnostic case_id)

  fun is_resource_gate holerr =
    Feedback.top_structure_of holerr = "SmtResource" andalso
    String.isPrefix diagnostic_prefix (Feedback.message_of holerr)

end
