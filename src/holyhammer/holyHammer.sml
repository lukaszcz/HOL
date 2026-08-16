(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Premise selection and external provers                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib Thread aiLib smlRedirect mlFeature mlThmData
  mlNearestNeighbor

val ERR = mk_HOL_ERR "holyHammer"

fun set_timeout n = hhConfig.hh_set ("timeout", Int.toString n)

fun known_atps () = map #name (hhProver.all ())

fun config_of caller name =
  case hhProver.lookup name of
      SOME config => config
    | NONE =>
        raise ERR caller
          ("unknown HolyHammer prover '" ^ name ^ "'; known provers: " ^
           String.concatWith ", " (known_atps ()))

fun configs_of caller names = map (config_of caller) names

fun no_prover caller =
  let
    val message =
      "no prover binary found; run tools/download-provers or put a " ^
      "supported prover binary on PATH"
    val _ = print_endline ("HolyHammer: " ^ message)
  in
    raise ERR caller message
  end

fun available_configs caller configs =
  let
    fun available (config : hhProver.prover_config) =
      case hhProver.find_exec config of
          SOME _ => true
        | NONE =>
            (print_endline ("no binary for " ^ #name config); false)
    val available = filter available configs
  in
    if null available then no_prover caller else available
  end

(* Deliberately a function: state_dir needs HOME and creates directories,
   so binding it at structure-initialisation time would make merely loading
   holyHammer fail wherever HOME is unset or the home is read-only. *)
fun workdir () = hhConfig.state_dir ()

val attrib =
  [Thread.InterruptState Thread.InterruptAsynch,
   Thread.EnableBroadcastInterrupt true]

fun interactive_options provers (options : hhConfig.hh_options) :
    hhConfig.hh_options =
  {timeout = #timeout options, max_proofs = 1, provers = provers,
   slices = #slices options, cores = #cores options,
   filter = #filter options, max_facts = #max_facts options,
   format = #format options, type_enc = #type_enc options,
   lam_trans = #lam_trans options, mono_iters = #mono_iters options,
   mono_instances = #mono_instances options, minimize = #minimize options,
   preplay_timeout = #preplay_timeout options,
   minimize_timeout = #minimize_timeout options,
   cache = #cache options, cache_dir = #cache_dir options,
   cache_max_entries = #cache_max_entries options,
   debug_dir = #debug_dir options}

type unverified = hhProver.slice * string list

(* The schedule's own reporting, plus a record of the proofs it announced. *)
fun progress found event =
  (case event of
       hhSchedule.ProofFound pair => found := pair :: !found
     | _ => ();
   hhSchedule.default_progress event)

val problem_path = hhSchedule.problem_path

fun output_paths directory prover =
  let
    val prefix = prover ^ "-"
    fun is_output name =
      String.isPrefix prefix name andalso String.isSuffix ".out" name
  in
    map (fn name => OS.Path.concat (directory, name))
      (List.filter is_output (hhConfig.directory_names directory))
  end

fun unverified_line debug_dir (slice, lemmas) =
  let
    val heading =
      "  " ^ #prover slice ^ ": [" ^ String.concatWith ", " lemmas ^ "]"
  in
    case debug_dir of
        NONE => heading
      | SOME directory =>
          let
            val outputs = output_paths directory (#prover slice)
            val output_text =
              if null outputs then OS.Path.concat (directory, #prover slice ^
                "-*.out")
              else String.concatWith ", " outputs
          in
            heading ^ "\n    problem: " ^ problem_path slice ^
            "\n    output: " ^ output_text
          end
  end

fun failed caller options found =
  if null found then
    (print_endline "  ATPs could not find a proof";
     raise ERR caller "ATPs could not find a proof")
  else
    let
      val message =
        "ATPs found proofs, but reconstruction failed for:\n" ^
        String.concatWith "\n"
          (map (unverified_line (#debug_dir options)) (List.rev found))
    in
      print_endline ("  " ^ message);
      raise ERR caller message
    end

fun run_schedule caller options premises goal =
  let
    val found = ref ([] : unverified list)
    val result = hhSchedule.run
      {options = options, goal = goal, premises = premises,
       progress = SOME (progress found)}
  in
    case #suggestions result of
        suggestion :: _ => suggestion
      | [] => failed caller options (!found)
  end

fun max_schedule_facts schedule =
  foldl Int.max 0 (map (#nfacts o #2) schedule)

fun premise_order (options : hhConfig.hh_options) thmdata n goal =
  if #filter options = "none" then map #1 (#2 thmdata)
  else thmknn_wdep thmdata n (fea_of_goal true goal)

fun options_for caller wanted_atps =
  let
    val configs = available_configs caller (configs_of caller wanted_atps)
  in
    interactive_options (map #name configs) (hhConfig.snapshot ())
  end

fun hh_pb _ wanted_atps premises goal =
  #tac (run_schedule "hh_pb" (options_for "hh_pb" wanted_atps)
    premises goal)

fun main_hh_result caller thmdata goal =
  let
    val snapshot = hhConfig.snapshot ()
    val configs = available_configs caller
      (configs_of caller (#provers snapshot))
    val options = interactive_options (map #name configs) snapshot
    val schedule = hhSlice.mk_schedule options
    val premises = premise_order options thmdata
      (max_schedule_facts schedule) goal
  in
    run_schedule caller options premises goal
  end

fun main_hh _ thmdata goal = #tac (main_hh_result "main_hh" thmdata goal)

fun main_hh_lemmas _ thmdata goal =
  SOME (#lemmas (main_hh_result "main_hh_lemmas" thmdata goal))
  handle HOL_ERR _ => NONE

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)

fun hh_goal goal =
  if not (has_boolty_goal goal) then
    raise ERR "hh_goal" "a term is not of type bool"
  else
    let val thmdata = hidef create_thmdata () in
      main_hh (workdir ()) thmdata goal
    end

fun hh_fork goal = Thread.fork (fn () => ignore (hh_goal goal), attrib)
fun hh goal = let val tac = hh_goal goal in hidef tac goal end
fun holyhammer tm = hidef TAC_PROOF (([], tm), hh_goal ([], tm))

end
