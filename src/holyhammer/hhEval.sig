signature hhEval =
sig
  datatype regime = Bushy | Chainy
  datatype selector =
      Deps
    | Knn of int
    | Mepo of int
    | Mash of int
    | Mesh of int
    | PerSlice
  datatype engine =
      Prover of string
    | Sched of {provers : string list, slices : int,
                cores : int, max_proofs : int}

  type condition =
    {cond_id : string, regime : regime, selector : selector,
     engine : engine, timeout : int, reconstruct : bool}

  type journal_slice =
    {slice : hhProver.slice, szs : string, time : real, cached : bool}

  type journal_entry =
    {run : string, thy : string, thm : string, goal_id : string,
     cond : string, regime : regime, selector : selector,
     engine : engine, ho : bool option, fresh : bool option, prover : string,
     prover_version : string option, nfacts : int,
     timeout : int, szs : string, t_prover : real,
     axioms_used : string list option, recon_ok : bool option,
     recon_method : string option, t_recon : real option,
     stac : string option, error : string option, stop : string option,
     t_total : real option, winner : hhProver.slice option,
     slices : journal_slice list}

  type corpus_coverage =
    {srcfiles : string list, dat_theories : string list,
     added_from_dat : string list}

  type corpus_entry =
    {thy : string, theorem_count : int, dep_stamp : string}

  type prover_identity =
    {name : string, path : string option, version : string option,
     sha256 : string option}

  type run_header =
    {expname : string, date : string, host : string, hol_commit : string,
     provers : prover_identity list, corpus : corpus_entry list,
     added_from_dat : string list, conditions : condition list, sample : int}

  type completed

  type anchor_row =
    {goal_id : string, slice_index : int, prover : string, filter : string,
     format : string, type_enc : string, lam_trans : string, nfacts : int,
     extra_opts : string list, slice_size : int, premise_digest : string,
     normalized_command : string list option, request_key : string}

  type anchor_goal_binding =
    {goal_id : string, goal_sha1 : string, ancestry_sha1 : string,
     fact_inventory_sha1 : string, selected_premises_sha1 : string,
     selected_premise_count : int}

  type anchor_manifest_header =
    {behavior_source_commit : string, gate_run_source_commit : string,
     task13_key_source : string, accepted_run_header : string,
     accepted_run_header_sha256 : string, accepted_journal : string,
     accepted_journal_sha256 : string, input_run_header_sha256 : string,
     input_journal : string, input_journal_sha256 : string,
     task13_paired_rows_sha256 : string,
     task13_command_rows_sha256 : string,
     task13_paired_driver_sha256 : string,
     task13_paired_controller_sha256 : string, task13_rows_checked : int,
     baseline_provenance_sha256 : string,
     invocation_provenance_sha256 : string,
     task13_internal_key_pair_mismatches : int,
     task13_premise_mismatches : int,
     task13_request_key_mismatches : int, model_current_theory : string,
     model_ancestry : string list, model_feature_rows : int,
     model_namespace_count : int, task13_execution_goals : int,
     goals : int, profiles : int,
     profile_start : int, profile_length : int, profile_set_sha1 : string,
     goal_digest_schema : string, goal_bindings : anchor_goal_binding list,
     row_count : int, prover_spawns : int}

  type anchor_manifest =
    {header : anchor_manifest_header, rows : anchor_row list}

  type anchor_certificate_entry =
    {theory : string, path : string, sha256 : string}

  type anchor_mismatch =
    {goal_id : string, slice_index : int, field : string,
     expected : string, actual : string}

  type anchor_model_binding =
    {inventory_sha1 : string, features_sha1 : string,
     weights_sha1 : string, feature_rows : int}

  type anchor_ranking =
    {goal_id : string, goal_sha1 : string, ancestry_sha1 : string,
     fact_inventory_sha1 : string, pool_count : int,
     selected_premises_sha1 : string, selected_premises : string list,
     maximum : int}

  type anchor_derivation =
    {current : anchor_row list, goal_bindings : anchor_goal_binding list,
     rankings : anchor_ranking list, model_binding : anchor_model_binding,
     prover_spawns : int}

  val string_of_regime : regime -> string
  val string_of_selector : selector -> string
  val is_higher_order_goal : Term.term -> bool
  val is_fresh_goal : string -> Term.term -> bool
  val validate_condition : condition -> unit
  val encode_condition : condition -> string
  val parse_condition : string -> condition

  val theories_from_srcfile_lines : string list -> string list
  val theories_from_srcfiles : string -> string list
  val coverage_check :
    {srcfiles : string list, dat_theories : string list} -> string list
  val stdlib_coverage : unit -> corpus_coverage
  val stdlib_theories : unit -> string list

  val eval_dir : unit -> string
  val experiment_dir : string -> string
  val journal_path : string -> string -> string

  val encode_journal_line : journal_entry -> string
  val parse_journal_line : string -> journal_entry
  val append_journal : string -> journal_entry -> unit
  val read_journal : string -> journal_entry list

  val read_completed : string -> completed
  val cell_completed : completed -> string * string -> bool
  val journal_complete : string -> (string * string) list -> bool

  val report : string -> unit

  val restrict_features_to_pool :
    string list -> (string * 'a) list -> (string * 'a) list
  val encode_anchor_row : anchor_row -> string
  val parse_anchor_row : string -> anchor_row
  val read_anchor_manifest : string -> anchor_manifest
  val parse_anchor_certificate_lines : string list ->
    anchor_certificate_entry list
  val read_anchor_certificate : string -> anchor_certificate_entry list
  val compare_anchor_rows :
    anchor_row list -> anchor_row list -> anchor_mismatch list
  val anchor_goal_digest_schema : string
  val anchor_goal_sha1 : Term.term list * Term.term -> string
  val anchor_model_binding : mlThmData.thmdata -> anchor_model_binding
  val derive_anchor_rows :
    {thy : string, theorem_names : string list, timeout : int,
     prover_versions : (string * string option) list} -> anchor_derivation
  val derive_anchor_rows_part :
    {thy : string, theorem_names : string list, timeout : int,
     prover_versions : (string * string option) list,
     profile_start : int, profile_length : int, replay_theory : bool} ->
    anchor_derivation
  val derive_anchor_rows_part_with_model :
    {thy : string, theorem_names : string list, timeout : int,
     prover_versions : (string * string option) list,
     profile_start : int, profile_length : int, replay_theory : bool,
     model_thmdata : mlThmData.thmdata,
     model_binding : anchor_model_binding} -> anchor_derivation
  val derive_anchor_rows_part_with_rankings :
    {thy : string, theorem_names : string list, timeout : int,
     prover_versions : (string * string option) list,
     profile_start : int, profile_length : int,
     rankings : anchor_ranking list,
     model_binding : anchor_model_binding} -> anchor_derivation
  val run_anchor_derivation :
    {thy : string, baseline_manifest : string,
     output_tsv : string, mismatch_report : string, timeout : int,
     theorem_names : string list option,
     prover_versions : (string * string option) list} ->
    {rows : int, mismatches : int, prover_spawns : int}

  val loaded_corpus_entry : string -> corpus_entry
  val current_prover_identities : condition list -> prover_identity list
  val new_run_header :
    {expname : string, corpus : corpus_entry list,
     added_from_dat : string list, conditions : condition list,
     sample : int} -> run_header
  val write_run_header : string -> run_header -> unit

  val sample_goal : int -> string -> bool

  val set_worker_settings : {conditions : condition list, sample : int} -> unit
  val write_evalscript : string -> string -> condition list -> int -> string
  val journal_theory_error : string -> string -> string -> unit
  val eval_thy : string -> string -> unit
  val run_eval :
    {expname : string, ncore : int, thyl : string list,
     conditions : condition list} -> unit

  val smoke_goals : (string * string * string) list
  val run_smoke : {expdir : string, timeout : int} -> journal_entry list
end
