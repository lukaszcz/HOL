structure tableauLib :> tableauLib =
struct

open Abbrev HolKernel

type proof = blastSearch.proof
type branch = blastSearch.branch
type try_result =
  {fullTrace : branch list list,
   result : proof option}

val depth_limit = blastSearch.depth_limit

fun has_marker_head marker theorem =
  let val (head, _) = strip_comb (concl theorem)
  in same_const marker head end
  handle HOL_ERR _ => false

fun is_bounded theorem =
  Option.isSome (total BoundedRewrites.DEST_BOUNDED theorem)

(* Generic simplifier markers are not classical-rule declarations. *)
fun is_passthrough_marker theorem =
  has_marker_head markerSyntax.AC_tm theorem orelse
  has_marker_head markerSyntax.Cong_tm theorem orelse
  has_marker_head markerSyntax.Split_tm theorem orelse
  Option.isSome (markerLib.destExcl theorem) orelse
  Option.isSome (markerLib.destExclSF theorem) orelse
  Option.isSome (markerLib.destFRAG theorem) orelse
  is_bounded theorem

fun rule_name_exists name cs =
  List.exists (fn (_, (old_name, _)) => name = old_name)
    (clasetLib.rules_of cs)

fun next_extra_name cs index =
  let val name = "__blast_extra_" ^ Int.toString index
  in
    if rule_name_exists name cs then next_extra_name cs (index + 1)
    else (name, index + 1)
  end

(* process_claset_tags consumes the classical marker vocabulary.  Plain
   leftovers become unsafe intros; Cong, Excl, SF, and related generic
   markers deliberately pass through without becoming tableau rules. *)
fun add_plain_theorems theorems cs =
  let
    fun add (theorem, (current, index)) =
      if is_passthrough_marker theorem then (current, index)
      else
        let val (name, next) = next_extra_name current index
        in
          (clasetLib.add_intros [(name, theorem)] current, next)
        end
  in
    #1 (List.foldl add (cs, 0) theorems)
  end

fun invocation_claset theorems =
  let
    val (tagged, leftovers) =
      clasetLib.process_claset_tags theorems (clasetLib.the_claset ())
  in
    add_plain_theorems leftovers tagged
  end

fun add_time elapsed accumulated =
  accumulated := Time.+ (!accumulated, elapsed)

fun stats proof search_time reconstruction_time =
  if Feedback.current_trace "blast" >= 2 then
    Feedback.HOL_MESG
      ("Blast stats: depth " ^ Int.toString (#depth proof) ^
       "; branches created " ^
       Int.toString (#branches_created proof) ^
       "; branches closed " ^
       Int.toString (#branches_closed proof) ^
       "; choices pruned " ^
       Int.toString (#choices_pruned proof) ^
       "; search " ^ Time.toString search_time ^ "s" ^
       "; reconstruction " ^
       Time.toString reconstruction_time ^ "s")
  else ()

fun failed_stats search_time reconstruction_time =
  if Feedback.current_trace "blast" >= 2 then
    Feedback.HOL_MESG
      ("Blast stats: no proof; search " ^
       Time.toString search_time ^ "s" ^
       "; reconstruction " ^
       Time.toString reconstruction_time ^ "s")
  else ()

fun run_depths cs depths goal =
  let
    val started = Time.now ()
    val reconstruction_time = ref Time.zeroTime

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

    fun search [] = NONE
      | search (depth :: rest) =
          (case blastSearch.searchGoal cs depth goal accept of
               NONE => search rest
             | result => result)

    val result = search depths
    val total_time = Time.- (Time.now (), started)
    val search_time = Time.- (total_time, !reconstruction_time)
    val _ =
      case result of
          SOME (proof, _) =>
            stats proof search_time (!reconstruction_time)
        | NONE => failed_stats search_time (!reconstruction_time)
  in
    case result of
        SOME (_, tactic_result) => tactic_result
      | NONE =>
          raise mk_HOL_ERR "tableauLib" "run_depths"
            "blast search found no reconstructible proof"
  end

fun through limit =
  let
    fun count depth =
      if depth > limit then [] else depth :: count (depth + 1)
  in
    count 0
  end

(* Read global configuration when the tactic runs, like classicalLib's
   public tactics, rather than when its tactic value is constructed. *)
fun BLAST_DEPTH_TAC depth theorems goal =
  run_depths (invocation_claset theorems) [depth] goal

fun BLAST_TAC theorems goal =
  run_depths (invocation_claset theorems) (through (!depth_limit)) goal

fun tryIt depth theorems goal =
  blastSearch.debugGoal (invocation_claset theorems) depth goal

end
