structure tableauLib :> tableauLib =
struct

open Abbrev HolKernel

type proof = blastSearch.proof
type branch = blastSearch.branch
type try_result =
  {fullTrace : branch list list,
   result : proof option}

val depth_limit = blastSearch.depth_limit

fun blast_claset () =
  clasetLib.add_selims
    [("blast_not_imp", clasetSeedTheory.NOT_IMP_CELIM_THM),
     ("blast_not_forall", clasetSeedTheory.NOT_FORALL_CELIM_THM)]
    (clasetLib.the_claset ())

fun invocation_claset theorems =
  clasetLib.invocation_claset {prefix = "__blast_extra_"}
    (blast_claset ()) theorems

fun add_time elapsed accumulated =
  accumulated := Time.+ (!accumulated, elapsed)

type totals =
  {branches_created : int ref,
   branches_closed : int ref,
   choices_pruned : int ref}

fun new_totals () : totals =
  {branches_created = ref 0,
   branches_closed = ref 0,
   choices_pruned = ref 0}

fun add_statistics (totals : totals)
      (statistics : blastSearch.statistics) =
  (#branches_created totals :=
     !(#branches_created totals) + #branches_created statistics;
   #branches_closed totals :=
     !(#branches_closed totals) + #branches_closed statistics;
   #choices_pruned totals :=
     !(#choices_pruned totals) + #choices_pruned statistics)

fun statistics_text (totals : totals) =
  "branches created " ^
  Int.toString (!(#branches_created totals)) ^
  "; branches closed " ^
  Int.toString (!(#branches_closed totals)) ^
  "; choices pruned " ^
  Int.toString (!(#choices_pruned totals))

fun stats proof totals search_time reconstruction_time =
  if Feedback.current_trace "blast" >= 2 then
    Feedback.HOL_MESG
      ("Blast stats: depth " ^ Int.toString (#depth proof) ^
       "; " ^ statistics_text totals ^
       "; search " ^ Time.toString search_time ^ "s" ^
       "; reconstruction " ^
       Time.toString reconstruction_time ^ "s")
  else ()

fun failed_stats totals search_time reconstruction_time =
  if Feedback.current_trace "blast" >= 2 then
    Feedback.HOL_MESG
      ("Blast stats: no proof; " ^ statistics_text totals ^
       "; search " ^ Time.toString search_time ^ "s" ^
       "; reconstruction " ^
       Time.toString reconstruction_time ^ "s")
  else ()

fun run_depths cs initial_depth next_depth goal =
  let
    val started = Time.now ()
    val reconstruction_time = ref Time.zeroTime
    val totals = new_totals ()

    fun accept proof =
      let
        val reconstruction_started = Time.now ()
        val result = blastReconstruct.reconstructWith cs goal proof
        val elapsed = Time.- (Time.now (), reconstruction_started)
        val _ = add_time elapsed reconstruction_time
      in
        case result of
            SOME tactic_result => (proof, tactic_result)
          | NONE => raise blastSearch.PROOF_FAILED
      end

    fun search NONE = NONE
      | search (SOME depth) =
          let
            val report =
              blastSearch.searchGoalWithStats cs depth goal accept
            val _ = add_statistics totals (#statistics report)
          in
            case #result report of
                NONE => search (next_depth depth)
              | result => result
          end

    val result = search initial_depth
    val total_time = Time.- (Time.now (), started)
    val search_time = Time.- (total_time, !reconstruction_time)
    val _ =
      case result of
          SOME (proof, _) =>
            stats proof totals search_time (!reconstruction_time)
        | NONE =>
            failed_stats totals search_time (!reconstruction_time)
  in
    case result of
        SOME (_, tactic_result) => tactic_result
      | NONE =>
          raise mk_HOL_ERR "tableauLib" "run_depths"
            "blast search found no reconstructible proof"
  end

fun next_through limit depth =
  if depth >= limit then NONE else SOME (depth + 1)

(* Read global configuration when the tactic runs, like classicalLib's
   public tactics, rather than when its tactic value is constructed. *)
fun BLAST_DEPTH_TAC depth theorems goal =
  run_depths (invocation_claset theorems) (SOME depth)
    (fn _ => NONE) goal

fun BLAST_TAC theorems goal =
  let
    val limit = !depth_limit
    val initial = if limit < 0 then NONE else SOME 0
  in
    run_depths (invocation_claset theorems) initial
      (next_through limit) goal
  end

fun tryIt depth theorems goal =
  blastSearch.debugGoal (invocation_claset theorems) depth goal

end
