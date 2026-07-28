structure tableauLib :> tableauLib =
struct

open Abbrev HolKernel

type proof = blastSearch.proof
type branch = blastSearch.branch
type try_result =
  {fullTrace : branch list list,
   result : proof option}

val depth_limit = blastSearch.depth_limit

(* The safe elimination rules the tableau engine needs to decompose a
   negated implication or a negated universal.  Every search goes through
   run_depths, which is where they are added, so no caller can hand the
   engine a claset that lacks them. *)
val add_blast_selims =
  clasetLib.add_selims
    [("blast_not_imp", clasetSeedTheory.NOT_IMP_CELIM_THM),
     ("blast_not_forall", clasetSeedTheory.NOT_FORALL_CELIM_THM)]

fun invocation_claset theorems =
  clasetLib.invocation_claset (clasetLib.the_claset ()) theorems

fun invoke tactic theorems goal =
  let
    val (cs, facts) = invocation_claset theorems
  in
    Tactical.THEN (clasetLib.INSERT_FACTS_TAC facts, tactic cs) goal
  end

fun add_time elapsed accumulated =
  accumulated := Time.+ (!accumulated, elapsed)

(* Iterative deepening performs independent fixed-depth searches.  Preserve
   the last run for honest per-run reporting and name sums explicitly as
   cumulative.  In particular, cumulative branch and inference counts are
   not comparable with Isabelle's Table-1 ntried column. *)
type run_statistics =
  {fixed_depth_runs : int ref,
   final_fixed_depth : blastSearch.statistics option ref,
   cumulative_inferences_performed : int ref,
   cumulative_branches_created : int ref,
   cumulative_branches_closed : int ref,
   cumulative_choices_pruned : int ref}

fun new_run_statistics () : run_statistics =
  {fixed_depth_runs = ref 0,
   final_fixed_depth = ref NONE,
   cumulative_inferences_performed = ref 0,
   cumulative_branches_created = ref 0,
   cumulative_branches_closed = ref 0,
   cumulative_choices_pruned = ref 0}

fun add_statistics (summary : run_statistics)
      (statistics : blastSearch.statistics) =
  (#fixed_depth_runs summary := !(#fixed_depth_runs summary) + 1;
   #final_fixed_depth summary := SOME statistics;
   #cumulative_inferences_performed summary :=
     !(#cumulative_inferences_performed summary) +
     #inferences_performed statistics;
   #cumulative_branches_created summary :=
     !(#cumulative_branches_created summary) +
     #branches_created statistics;
   #cumulative_branches_closed summary :=
     !(#cumulative_branches_closed summary) +
     #branches_closed statistics;
   #cumulative_choices_pruned summary :=
     !(#cumulative_choices_pruned summary) +
     #choices_pruned statistics)

fun statistics_text (summary : run_statistics) =
  let
    val final_text =
      case !(#final_fixed_depth summary) of
          NONE => "final fixed-depth run none"
        | SOME statistics =>
            "final fixed-depth configured depth " ^
            Int.toString (#configured_depth statistics) ^
            "; final fixed-depth maximum resource cost " ^
            Int.toString (#maximum_resource_cost statistics) ^
            "; final fixed-depth inferences performed " ^
            Int.toString (#inferences_performed statistics) ^
            "; final fixed-depth branches created " ^
            Int.toString (#branches_created statistics) ^
            "; final fixed-depth branches closed " ^
            Int.toString (#branches_closed statistics) ^
            "; final fixed-depth choices pruned " ^
            Int.toString (#choices_pruned statistics)
  in
    "fixed-depth runs " ^
    Int.toString (!(#fixed_depth_runs summary)) ^ "; " ^ final_text ^
    "; cumulative inferences performed " ^
    Int.toString (!(#cumulative_inferences_performed summary)) ^
    "; cumulative branches created " ^
    Int.toString (!(#cumulative_branches_created summary)) ^
    "; cumulative branches closed " ^
    Int.toString (!(#cumulative_branches_closed summary)) ^
    "; cumulative choices pruned " ^
    Int.toString (!(#cumulative_choices_pruned summary))
  end

fun stats proof summary search_time reconstruction_time =
  Feedback.HOL_MESG
    ("Blast stats: depth " ^ Int.toString (#depth proof) ^
     "; " ^ statistics_text summary ^
     "; search " ^ Time.toString search_time ^ "s" ^
     "; reconstruction " ^
     Time.toString reconstruction_time ^ "s")

fun failed_stats summary search_time reconstruction_time =
  Feedback.HOL_MESG
    ("Blast stats: no proof; " ^ statistics_text summary ^
     "; search " ^ Time.toString search_time ^ "s" ^
     "; reconstruction " ^
     Time.toString reconstruction_time ^ "s")

fun run_depths base_cs initial_depth next_depth goal =
  let
    val cs = add_blast_selims base_cs
    val started = Time.now ()
    val reconstruction_time = ref Time.zeroTime
    (* Ordinary public tactics retain the uninstrumented search path.  The
       documented level-2 statistics trace explicitly opts into counters.
       Keep the summary absent in the quiet path so it allocates and updates
       none of the expanded per-run/cumulative statistic refs. *)
    val summary =
      if Feedback.current_trace "blast" >= 2 then
        SOME (new_run_statistics ())
      else NONE

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
            val result =
              case summary of
                  NONE => blastSearch.searchGoal cs depth goal accept
                | SOME statistics =>
                    let
                      val report =
                        blastSearch.searchGoalWithStats
                          cs depth goal accept
                      val _ =
                        add_statistics statistics (#statistics report)
                    in
                      #result report
                    end
          in
            case result of
                NONE => search (next_depth depth)
              | SOME _ => result
          end

    val result = search initial_depth
    val total_time = Time.- (Time.now (), started)
    val search_time = Time.- (total_time, !reconstruction_time)
    val _ =
      case summary of
          NONE => ()
        | SOME statistics =>
            (case result of
                 SOME (proof, _) =>
                   stats proof statistics search_time
                     (!reconstruction_time)
               | NONE =>
                   failed_stats statistics search_time
                     (!reconstruction_time))
  in
    case result of
        SOME (_, tactic_result) => tactic_result
      | NONE =>
          raise mk_HOL_ERR "tableauLib" "run_depths"
            "blast search found no reconstructible proof"
  end

fun CS_BLAST_DEPTH_TAC cs depth =
  run_depths cs (SOME depth) (fn _ => NONE)

fun next_through limit depth =
  if depth >= limit then NONE else SOME (depth + 1)

(* Read global configuration when the tactic runs, like classicalLib's
   public tactics, rather than when its tactic value is constructed. *)
fun blast_depth_tac depth theorems goal =
  invoke (fn cs => CS_BLAST_DEPTH_TAC cs depth) theorems goal

fun BLAST_DEPTH_TAC depth =
  markerLib.ABBRS_THEN (blast_depth_tac depth)

fun blast_tac theorems goal =
  let
    val limit = !depth_limit
    val initial = if limit < 0 then NONE else SOME 0
  in
    invoke
      (fn cs => run_depths cs initial (next_through limit))
      theorems goal
  end

val BLAST_TAC = markerLib.ABBRS_THEN blast_tac

fun tryIt depth theorems goal =
  let
    val (cs, facts) = invocation_claset theorems
    val (goals, _) = clasetLib.INSERT_FACTS_TAC facts goal
  in
    blastSearch.debugGoal (add_blast_selims cs) depth
      (Lib.singleton_of_list goals)
  end

end
