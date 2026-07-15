signature hhProver =
sig
  datatype szs =
      SzsTheorem
    | SzsCounterSat
    | SzsSatisfiable
    | SzsGaveUp
    | SzsTimeout
    | SzsResourceOut
    | SzsInappropriate
    | SzsUnknown of string
    | RunFailure of string

  type slice =
    {prover : string, format : string, type_enc : string,
     lam_trans : string, nfacts : int, filter : string,
     extra_opts : string list, slice_size : int}

  type run_request =
    {timeout : int, problem : string, extra : string list,
     debug_dir : string option}

  type run_result =
    {szs : szs, used_axioms : string list option, time : real,
     version : string option, output_file : string}

  type prover_config =
    {name : string,
     exec_names : string list,
     env_var : string,
     version_args : string list,
     parse_version : string -> string option,
     tested_versions : string list,
     formats : string list,
     mk_command : string -> run_request -> string * string list,
     parse_output : string list -> szs * string list option,
     default_nfacts : int,
     slices : unit -> slice list,
     legacy : bool}

  val all : unit -> prover_config list
  val lookup : string -> prover_config option
  val register : prover_config -> unit
  val default_provers : unit -> string list

  val szs_of_line : string -> szs option
  val axioms_from_tstp : string list -> string list

  (* Process execution and probing are implemented by TASK_04. *)
  val find_exec : prover_config -> string option
  val probe : prover_config ->
    {path : string, version : string option, tested : bool} option
  val run : prover_config -> run_request -> run_result
end
