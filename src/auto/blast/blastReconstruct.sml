structure blastReconstruct :> blastReconstruct =
struct

open Abbrev HolKernel

type claset = clasetLib.claset
type proof = blastSearch.proof

fun first_result sequence =
  case seq.cases sequence of
      SOME (result, _) => result
    | NONE =>
        raise mk_HOL_ERR "blastReconstruct" "first_result"
          "the recorded step does not apply"

fun apply step node = seq.map #2 (step (node, 1))

fun move_children count node =
  let
    fun move position current =
      if position > count then current
      else
        move (position + 1)
          (#2
            (first_result
              (clasetStep.blast_move_back_step 1
                (current, position))))
  in
    move 1 node
  end

(* Static stored-rule prefixes may already account for an explicit tableau
   introduction.  Keep the zero-cost fallback for genuine tableau-only
   pseudo-steps, without adding another stored-rule replay action. *)
fun apply_pseudo step node =
  seq.append (apply step node) (seq.result node)

fun apply_rule cs duplicate major rule node =
  case #origin rule of
      blastRule.ImpIntro =>
        apply_pseudo clasetStep.blast_disch_step node
    | blastRule.AllIntro => apply_pseudo clasetStep.blast_gen_step node
    | blastRule.Stored {is_elim, theorem} =>
        let
          val replay_theorem =
            if duplicate andalso is_elim then
              clasetRules.REV_DUP_ELIM_RULE theorem
            else theorem
          val old_count = length (clasetGoal.goals node)
          val transitions =
            apply
              (clasetStep.blast_rule_step_at cs
                {theorem = replay_theorem, elim = is_elim,
                 major = major}) node

          fun finish next =
            let
              val child_count =
                length (clasetGoal.goals next) - old_count + 1
            in
              if duplicate andalso is_elim then
                move_children child_count next
              else next
            end
        in
          seq.mapPartial (total finish) transitions
        end

fun execute cs step node =
  case step of
      blastSearch.HypSubst {equality} =>
        apply (clasetStep.blast_hyp_subst_step_at equality) node
    | blastSearch.CloseAssume {assumption} =>
        apply (clasetStep.blast_assumption_step_at assumption) node
    | blastSearch.CloseContradiction positions =>
        apply (clasetStep.blast_contradiction_step_at positions) node
    | blastSearch.SafeRule {rule, major, ...} =>
        apply_rule cs false major rule node
    | blastSearch.DeferGoal =>
        apply clasetStep.blast_ccontr_step node
    | blastSearch.UnsafeRule {rule, duplicate, major, ...} =>
        apply_rule cs duplicate major rule node

(* Every ambiguous script step selects its exact typed assumption occurrence.
   Pull the resulting typed engine sequence lazily, but never fall back to a
   different assumption or rule position.  Only a completely grounded,
   kernel-valid replay is accepted; failure rejects this tableau through the
   search continuation's PROOF_FAILED hook. *)
fun perform_with cs goal ({script, ...} : proof) =
  let
    fun finish final =
      let
        val _ =
          if null (clasetGoal.goals final) then ()
          else
            raise mk_HOL_ERR "blastReconstruct" "finish"
              "the recorded script leaves open engine goals"
        val grounded =
          clasetReplay.ground (clasetGoal.store final)
            (clasetGoal.replay final)
        val result as (residuals, _) =
          Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
        val _ =
          if null residuals then ()
          else
            raise mk_HOL_ERR "blastReconstruct" "finish"
              "kernel replay leaves open goals"
      in
        result
      end

    fun replay [] node = total finish node
      | replay (step :: rest) node =
          let
            fun alternatives sequence =
              case seq.cases sequence of
                  NONE => NONE
                | SOME (next, nodes) =>
                    (case replay rest next of
                         NONE => alternatives nodes
                       | result => result)
          in
            alternatives (execute cs step node)
          end
          handle HOL_ERR _ => NONE
  in
    case replay script (clasetGoal.from_goal goal) of
        SOME result => result
      | NONE =>
          raise mk_HOL_ERR "blastReconstruct" "perform_with"
            "the recorded tableau has no kernel-valid replay"
  end

fun reconstructWith cs goal proof =
  total (perform_with cs goal) proof

fun reconstruct goal proof =
  reconstructWith clasetLib.empty_cs goal proof

fun accept cs goal proof =
  case reconstructWith cs goal proof of
      SOME result => (proof, result)
    | NONE => raise blastSearch.PROOF_FAILED

fun searchGoal cs depth goal =
  blastSearch.searchGoal cs depth goal (accept cs goal)

fun deepenGoal cs goal =
  blastSearch.deepenGoal cs goal (accept cs goal)

fun tactic_result function_name result =
  case result of
      SOME (_, tactic_result) => tactic_result
    | NONE =>
        raise mk_HOL_ERR "blastReconstruct" function_name
          "blast search found no reconstructible proof"

fun DEPTH_TAC cs depth goal =
  tactic_result "DEPTH_TAC" (searchGoal cs depth goal)

fun DEEPEN_TAC cs goal =
  tactic_result "DEEPEN_TAC" (deepenGoal cs goal)

end
