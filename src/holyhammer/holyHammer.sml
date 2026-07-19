(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Premise selection and external provers                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib Thread aiLib
  smlExecute smlRedirect smlParallel smlTimeout
  mlFeature mlThmData mlTacticData mlNearestNeighbor
  hhExportFof hhReconstruct hhTranslate hhTptp

val ERR = mk_HOL_ERR "holyHammer"

(* -------------------------------------------------------------------------
   Settings
   ------------------------------------------------------------------------- *)

val timeout_glob = ref 10
fun set_timeout n = timeout_glob := n
val premise_selection_flag = ref true

(* -------------------------------------------------------------------------
   ATPs
   ------------------------------------------------------------------------- *)

(* Registry names called by holyhammer when their binaries exist. *)
val all_atps = ref ["e", "vampire", "zipperposition"]

fun known_atps () = map #name (hhProver.all ())

fun config_of caller name =
  case hhProver.lookup name of
      SOME config => config
    | NONE =>
        raise ERR caller
          ("unknown HolyHammer prover '" ^ name ^ "'; known provers: " ^
           String.concatWith ", " (known_atps ()))

fun configs_of caller names = map (config_of caller) names

fun nfacts_of (config : hhProver.prover_config) =
  if !premise_selection_flag then #default_nfacts config else 100000

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

(* -------------------------------------------------------------------------
   Directories
   ------------------------------------------------------------------------- *)

fun pathl sl = case sl of
    []  => raise ERR "pathl" "empty"
  | [a] => a
  | a :: m => OS.Path.concat (a, pathl m)

val hhdir = pathl [HOLDIR,"src","holyhammer"]
(* Deliberately a function: state_dir needs HOME and creates directories,
   so binding it at structure-initialisation time would make merely
   loading holyHammer fail wherever HOME is unset or the home is
   read-only. *)
fun workdir () = hhConfig.state_dir ()
fun fof_dir dir (config : hhProver.prover_config) =
  pathl [dir, #name config ^ "_files"]

(* ---------------------------------------------------------------------------
   Run functions in parallel and terminate as soon as one returned a
   positive result in the private race result.
   ------------------------------------------------------------------------- *)

val (race_lemmas : string list option ref) = ref NONE
val (lemmas_glob : string list option ref) = ref NONE

val attrib = [Thread.InterruptState Thread.InterruptAsynch,
  Thread.EnableBroadcastInterrupt true]

fun parallel_call t fl =
  let
    val _ = race_lemmas := NONE
    val _ = lemmas_glob := NONE
    fun rec_fork f = Thread.fork (fn () => f (), attrib)
    val threadl = map rec_fork fl
    val rt = Timer.startRealTimer ()
    fun loop () =
      (
      OS.Process.sleep (Time.fromReal 0.01);
      if isSome (!race_lemmas) orelse
         not (exists Thread.isActive threadl) orelse
         Timer.checkRealTimer rt  > Time.fromReal t
      then (app interruptkill threadl; !race_lemmas)
      else loop ()
      )
  in
    loop ()
  end

(* -------------------------------------------------------------------------
   Launch an ATP
   ------------------------------------------------------------------------- *)

fun run_atp fofdir (config : hhProver.prover_config) t =
  let
    (* Keep the prover's output next to the problem, as the deleted shell
       wrappers did, so a failed hh call can still be diagnosed. *)
    val request : hhProver.run_request =
      {timeout = t, problem = pathl [fofdir, "atp_in"], extra = [],
       debug_dir = SOME fofdir}
    val result = hhProver.run config request
    val r = #used_axioms result
  in
    if isSome r
    then
      (
      print_endline ("  proof found by " ^ #name config ^ ":");
      print_endline ("    " ^ mk_metis_call (valOf r));
      race_lemmas := r
      )
    else ();
    r
  end

(* -------------------------------------------------------------------------
   HolyHammer
   ------------------------------------------------------------------------- *)

fun export_to_atp dir premises cj
    (config : hhProver.prover_config) =
  let
    val new_premises = first_n (nfacts_of config) premises
    val namethml = hidef thml_of_namel new_premises
    val fofdir = fof_dir dir config
    val _ = mkDir_err fofdir
  in
    fof_export_pb fofdir (cj,namethml)
  end

fun hh_pb_configs dir configs premises goal =
  let
    val cj = list_mk_imp goal
    val _ = app (export_to_atp dir premises cj) configs
    val t1 = !timeout_glob
    val t2 = Real.fromInt t1 + 2.0
    fun f config = fn () =>
      ignore (run_atp (fof_dir dir config) config t1)
    val olemmas = parallel_call t2 (map f configs)
  in
    case olemmas of
      NONE =>
        (print_endline "  ATPs could not find a proof";
        raise ERR "hh_pb" "ATPs could not find a proof")
    | SOME lemmas =>
      let
        (* Publish the premises before reconstructing: a reconstruction
           failure must not discard the proof the ATP did find. *)
        val _ = lemmas_glob := SOME lemmas
        val (stac,tac) = hidef (hh_reconstruct lemmas) goal
      in
        print_endline ("  minimized proof:  \n    " ^ stac);
        tac
      end
  end

fun hh_pb dir wanted_atps premises goal =
  let
    val _ = lemmas_glob := NONE
    val configs = available_configs "hh_pb"
      (configs_of "hh_pb" wanted_atps)
  in
    hh_pb_configs dir configs premises goal
  end

fun main_hh dir thmdata goal =
  let
    val _ = lemmas_glob := NONE
    val configs = available_configs "main_hh"
      (configs_of "main_hh" (!all_atps))
    val n = list_imax (map nfacts_of configs)
    val premises = thmknn_wdep thmdata n (fea_of_goal true goal)
  in
    hh_pb_configs dir configs premises goal
  end

fun main_hh_lemmas dir thmdata goal =
  (lemmas_glob := NONE; ignore (main_hh dir thmdata goal); !lemmas_glob)
  handle HOL_ERR _ => NONE

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)

fun hh_goal goal =
  if not (has_boolty_goal goal)
  then raise ERR "hh_goal" "a term is not of type bool"
  else
    let val thmdata = hidef create_thmdata () in
      main_hh (workdir ()) thmdata goal
    end

fun hh_fork goal = Thread.fork (fn () => ignore (hh_goal goal), attrib)
fun hh goal = let val tac = hh_goal goal in hidef tac goal end
fun holyhammer tm = hidef TAC_PROOF (([],tm), hh_goal ([],tm));

end (* struct *)
