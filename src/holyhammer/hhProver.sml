(* ========================================================================= *)
(* FILE          : hhProver.sml                                              *)
(* DESCRIPTION   : HolyHammer prover registry and output parsers             *)
(* ========================================================================= *)

structure hhProver :> hhProver =
struct

open aiLib

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

fun trim_left s =
  let
    fun loop i =
      if i < String.size s andalso Char.isSpace (String.sub (s, i)) then
        loop (i + 1)
      else i
  in
    String.extract (s, loop 0, NONE)
  end

fun trim_right s =
  let
    fun loop i =
      if i > 0 andalso Char.isSpace (String.sub (s, i - 1)) then
        loop (i - 1)
      else i
  in
    String.substring (s, 0, loop (String.size s))
  end

fun trim s = trim_right (trim_left s)

fun first_word s =
  case String.tokens Char.isSpace s of
      [] => ""
    | word :: _ => word

fun status_of_word word =
  case word of
      "Theorem" => SzsTheorem
    | "Unsatisfiable" => SzsTheorem
    | "CounterSatisfiable" => SzsCounterSat
    | "Satisfiable" => SzsSatisfiable
    | "GaveUp" => SzsGaveUp
    | "Unknown" => SzsGaveUp
    | "Incomplete" => SzsGaveUp
    | "Timeout" => SzsTimeout
    | "ResourceOut" => SzsResourceOut
    | "MemoryOut" => SzsResourceOut
    | "Inappropriate" => SzsInappropriate
    | other => SzsUnknown other

fun szs_of_line line =
  let
    val marker = "SZS status "
    val n = String.size marker
    fun seek i =
      if i + n > String.size line then NONE
      else if String.substring (line, i, n) = marker then
        let val word = first_word (String.extract (line, i + n, NONE)) in
          if word = "" then NONE else SOME (status_of_word word)
        end
      else seek (i + 1)
  in
    seek 0
  end

fun is_comment line =
  let val line' = trim_left line in
    String.isPrefix "#" line' orelse String.isPrefix "%" line'
  end

fun unescape_axiom raw =
  let
    val bare = trim raw
    val unquoted =
      if String.size bare >= 2 andalso String.sub (bare, 0) = #"'" andalso
         String.sub (bare, String.size bare - 1) = #"'" then
        String.substring (bare, 1, String.size bare - 2)
      else bare
    val name = unescape unquoted handle _ => unquoted
  in
    if String.isPrefix "thm." name then
      SOME (String.extract (name, String.size "thm.", NONE))
    else NONE
  end

fun comma_at_top s =
  let
    fun loop i depth quoted =
      if i = String.size s then NONE
      else
        let val c = String.sub (s, i) in
          if quoted then
            if c = #"'" then
              if i + 1 < String.size s andalso String.sub (s, i + 1) = #"'"
              then loop (i + 2) depth true
              else loop (i + 1) depth false
            else loop (i + 1) depth true
          else if c = #"'" then loop (i + 1) depth true
          else if c = #"(" then loop (i + 1) (depth + 1) false
          else if c = #")" then loop (i + 1) (depth - 1) false
          else if c = #"," andalso depth = 0 then SOME i
          else loop (i + 1) depth false
        end
  in
    loop 0 0 false
  end

fun closing_paren s start =
  let
    fun loop i depth quoted =
      if i = String.size s then NONE
      else
        let val c = String.sub (s, i) in
          if quoted then
            if c = #"'" then
              if i + 1 < String.size s andalso String.sub (s, i + 1) = #"'"
              then loop (i + 2) depth true
              else loop (i + 1) depth false
            else loop (i + 1) depth true
          else if c = #"'" then loop (i + 1) depth true
          else if c = #"(" then loop (i + 1) (depth + 1) false
          else if c = #")" then
            if depth = 1 then SOME i else loop (i + 1) (depth - 1) false
          else loop (i + 1) depth false
        end
  in
    loop start 1 false
  end

fun file_names line =
  let
    val marker = "file("
    val marker_size = String.size marker
    fun find i names =
      if i + marker_size > String.size line then List.rev names
      else if String.substring (line, i, marker_size) = marker then
        let
          val start = i + marker_size
        in
          case closing_paren line start of
              NONE => List.rev names
            | SOME finish =>
              let
                val args = String.substring (line, start, finish - start)
                val name =
                  case comma_at_top args of
                      NONE => NONE
                    | SOME comma =>
                      unescape_axiom
                        (String.extract (args, comma + 1, NONE))
                val names' =
                  case name of NONE => names | SOME item => item :: names
              in
                find (finish + 1) names'
              end
        end
      else find (i + 1) names
  in
    find 0 []
  end

fun axiom_name line =
  let
    val open_paren = String.fields (fn c => c = #"(") line
  in
    case open_paren of
        _ :: rest =>
          (case String.fields (fn c => c = #",") (String.concat rest) of
               first :: second :: _ =>
                 if trim second = "axiom" then unescape_axiom first else NONE
             | _ => NONE)
      | [] => NONE
  end

fun distinct names =
  let
    fun loop seen [] = List.rev seen
      | loop seen (name :: rest) =
          if List.exists (fn seen_name => seen_name = name) seen then
            loop seen rest
          else loop (name :: seen) rest
  in
    loop [] names
  end

fun axioms_from_tstp lines =
  let
    val proof_lines = List.filter (not o is_comment) lines
    val from_files = distinct (List.concat (map file_names proof_lines))
    val from_axioms =
      distinct (List.mapPartial axiom_name proof_lines)
  in
    if null from_files then from_axioms else from_files
  end

fun first_some f [] = NONE
  | first_some f (x :: xs) =
      case f x of NONE => first_some f xs | found => found

fun parse_tstp lines =
  let
    val status =
      case first_some szs_of_line lines of
          SOME result => result
        | NONE => RunFailure "no SZS status"
    val axioms = axioms_from_tstp lines
  in
    case status of
        SzsTheorem => (status, SOME axioms)
      | _ => (status, NONE)
  end

fun core_axioms lines =
  let
    fun from_line line =
      case String.fields (fn c => c = #"[") line of
          _ :: tail =>
            (case String.fields (fn c => c = #"]") (String.concat tail) of
                 names :: _ =>
                   List.mapPartial unescape_axiom
                     (String.fields (fn c => c = #",") names)
               | [] => [])
        | [] => []
  in
    distinct (List.concat (map from_line (List.filter
      (String.isPrefix "core" o trim_left) lines)))
  end

fun parse_z3 lines =
  let
    val status =
      case first_some szs_of_line lines of
          SOME result => result
        | NONE => RunFailure "no SZS status"
  in
    case status of
        SzsTheorem => (status, SOME (core_axioms lines))
      | _ => (status, NONE)
  end

fun version_after marker text =
  let
    val n = String.size marker
    fun find i =
      if i + n > String.size text then NONE
      else if String.substring (text, i, n) = marker then
        let val version = first_word (String.extract (text, i + n, NONE)) in
          if version = "" then NONE else SOME version
        end
      else find (i + 1)
  in
    find 0
  end

fun e_version output = version_after "E " output
fun vampire_version output = version_after "Vampire " output
fun zipperposition_version output = version_after "zipperposition " output
fun z3_version output = version_after "Z3 version " output

fun one_slice name nfacts extra_opts () =
  [{prover = name, format = "fof", type_enc = "", lam_trans = "",
    nfacts = nfacts, filter = "knn", extra_opts = extra_opts,
    slice_size = 1}]

fun e_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--auto-schedule", "--tstp-in", "--tstp-out", "-s",
    "--cpu-limit=" ^ Int.toString timeout, "--proof-object=1"] @
   extra @ [problem])

fun vampire_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--mode", "portfolio", "--schedule", "casc", "--input_syntax",
    "tptp", "--proof", "tptp", "--output_axiom_names", "on", "-t",
    Int.toString timeout, "--input_file"] @ extra @ [problem])

fun zipperposition_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--input", "tptp", "--output", "tptp", "--timeout",
    Int.toString timeout] @ extra @ [problem])

fun z3_command executable {timeout, problem, extra, ...} =
  (executable,
   ["-tptp", "DISPLAY_UNSAT_CORE=true", "ELIM_QUANTIFIERS=true",
    "PULL_NESTED_QUANTIFIERS=true", "-T:" ^ Int.toString timeout] @
   extra @ [problem])

fun e_legacy_command executable {timeout, problem, extra, ...} =
  (executable,
   ["-s", "--cpu-limit=" ^ Int.toString timeout, "--auto-schedule",
    "--tstp-in", "-R", "--print-statistics", "-p", "--tstp-format"] @
   extra @ [problem])

fun vampire_legacy_command executable {timeout, problem, extra, ...} =
  (executable,
   ["--time_limit", Int.toString timeout, "--proof", "tptp",
    "--output_axiom_names", "on"] @ extra @ [problem])

val e_config : prover_config =
  {name = "e", exec_names = ["eprover-ho", "eprover"],
   env_var = "HOL4_EPROVER_EXECUTABLE", version_args = ["--version"],
   parse_version = e_version, tested_versions = ["3.2.5"],
   formats = ["fof"], mk_command = e_command, parse_output = parse_tstp,
   default_nfacts = 128, slices = one_slice "e" 128 [], legacy = false}

val vampire_config : prover_config =
  {name = "vampire", exec_names = ["vampire"],
   env_var = "HOL4_VAMPIRE_EXECUTABLE", version_args = ["--version"],
   parse_version = vampire_version, tested_versions = ["5.0.1"],
   formats = ["fof"], mk_command = vampire_command, parse_output = parse_tstp,
   default_nfacts = 96, slices = one_slice "vampire" 96 [], legacy = false}

val zipperposition_config : prover_config =
  {name = "zipperposition", exec_names = ["zipperposition"],
   env_var = "HOL4_ZIPPERPOSITION_EXECUTABLE", version_args = ["--version"],
   parse_version = zipperposition_version, tested_versions = ["2.1"],
   formats = ["fof"], mk_command = zipperposition_command,
   parse_output = parse_tstp, default_nfacts = 128,
   slices = one_slice "zipperposition" 128 [], legacy = false}

val z3_config : prover_config =
  {name = "z3", exec_names = ["z3"], env_var = "HOL4_Z3_EXECUTABLE",
   version_args = ["--version"], parse_version = z3_version,
   tested_versions = ["4.16.0"], formats = ["fof"], mk_command = z3_command,
   parse_output = parse_z3, default_nfacts = 32,
   slices = one_slice "z3" 32 [], legacy = true}

val e_legacy_config : prover_config =
  {name = "e-legacy", exec_names = ["eprover-ho", "eprover"],
   env_var = "HOL4_EPROVER_EXECUTABLE", version_args = ["--version"],
   parse_version = e_version, tested_versions = ["3.2.5"],
   formats = ["fof"], mk_command = e_legacy_command, parse_output = parse_tstp,
   default_nfacts = 128, slices = one_slice "e-legacy" 128 [], legacy = true}

val vampire_legacy_config : prover_config =
  {name = "vampire-legacy", exec_names = ["vampire"],
   env_var = "HOL4_VAMPIRE_EXECUTABLE", version_args = ["--version"],
   parse_version = vampire_version, tested_versions = ["5.0.1"],
   formats = ["fof"], mk_command = vampire_legacy_command,
   parse_output = parse_tstp, default_nfacts = 96,
   slices = one_slice "vampire-legacy" 96 [], legacy = true}

val registry = ref
  [e_config, vampire_config, zipperposition_config, z3_config,
   e_legacy_config, vampire_legacy_config]

fun all () = !registry

fun lookup name =
  List.find (fn ({name = other, ...} : prover_config) => name = other)
    (!registry)

fun register (config : prover_config) =
  let val name = #name config in
    case lookup name of
        SOME _ => raise Fail ("duplicate HolyHammer prover: " ^ name)
      | NONE => registry := !registry @ [config]
  end

(* TASK_04 adds version probing; executable discovery is deliberately kept
   here as the small hook needed to make the default portfolio useful. *)
fun is_found ({name, exec_names, ...} : prover_config) =
  Option.isSome (hhConfig.find_exec name exec_names)

fun default_provers () =
  map #name (List.filter (fn config =>
    not (#legacy config) andalso is_found config) (!registry))

fun unavailable what =
  raise Fail ("hhProver." ^ what ^ " is implemented by TASK_04")

fun find_exec _ = unavailable "find_exec"
fun probe _ = unavailable "probe"
fun run _ _ = unavailable "run"

end
