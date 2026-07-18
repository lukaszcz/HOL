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

fun apply step node = #2 (first_result (step (node, 1)))

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

fun apply_rule cs duplicate rule node =
  case #origin rule of
      blastRule.ImpIntro => apply clasetStep.blast_disch_step node
    | blastRule.AllIntro => apply clasetStep.blast_gen_step node
    | blastRule.Stored {is_elim, theorem} =>
        let
          val replay_theorem =
            if duplicate andalso is_elim then
              clasetRules.REV_DUP_ELIM_RULE theorem
            else theorem
          val old_count = length (clasetGoal.goals node)
          val next =
            apply
              (clasetStep.blast_rule_step cs
                {theorem = replay_theorem, elim = is_elim}) node
          val child_count =
            length (clasetGoal.goals next) - old_count + 1
        in
          if duplicate andalso is_elim then
            move_children child_count next
          else next
        end

fun execute cs step node =
  case step of
      blastSearch.HypSubst =>
        apply clasetStep.blast_hyp_subst_step node
    | blastSearch.CloseAssume =>
        apply clasetStep.blast_assumption_step node
    | blastSearch.CloseContradiction =>
        apply clasetStep.blast_contradiction_step node
    | blastSearch.SafeRule {rule, ...} =>
        apply_rule cs false rule node
    | blastSearch.DeferGoal =>
        apply clasetStep.blast_ccontr_step node
    | blastSearch.UnsafeRule {rule, duplicate, ...} =>
        apply_rule cs duplicate rule node

(* The exact claset is used only to retain rule provenance in replay
   diagnostics.  Rule application itself always uses the recorded theorem. *)
fun perform_with cs goal ({script, ...} : proof) =
  let
    val final = List.foldl (fn (step, node) => execute cs step node)
      (clasetGoal.from_goal goal) script
    val _ =
      if null (clasetGoal.goals final) then ()
      else
        raise mk_HOL_ERR "blastReconstruct" "reconstruct"
          "the recorded script leaves open engine goals"
    val grounded =
      clasetReplay.ground (clasetGoal.store final)
        (clasetGoal.replay final)
    val result as (residuals, _) =
      Tactical.VALID (clasetReplay.REPLAY_TAC grounded) goal
    val _ =
      if null residuals then ()
      else
        raise mk_HOL_ERR "blastReconstruct" "reconstruct"
          "kernel replay leaves open goals"
  in
    result
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
