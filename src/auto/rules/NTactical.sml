structure NTactical :> NTactical =
struct

open Abbrev


type nresult = goal list * validation
type ntactic = goal -> nresult seq.seq
type wrapper = ntactic -> ntactic

fun LIFT tac g =
  seq.delay
    (fn () =>
       seq.result (tac g) handle Feedback.HOL_ERR _ => seq.empty)

fun DETERM ntac g =
  case seq.cases (ntac g) of
      NONE => Tactical.NO_TAC g
    | SOME (result, _) => result

val NNO_TAC : ntactic = fn _ => seq.empty
val NALL_TAC : ntactic = LIFT Tactical.ALL_TAC

fun NTHEN (tac1, tac2) g =
  let
    fun all_goals ([] : goal list) :
          (goal list * int list * validation list) seq.seq =
          seq.result ([], [], [])
      | all_goals (g0 :: gs0) =
          seq.delay
            (fn () =>
               seq.bind (tac2 g0)
                 (fn (gs1, v1) =>
                    seq.map
                      (fn (gs2, lengths, vs) =>
                         (gs1 @ gs2, length gs1 :: lengths, v1 :: vs))
                      (all_goals gs0)))
  in
    seq.delay
      (fn () =>
         seq.bind (tac1 g)
           (fn (gs, v) =>
              seq.map
                (fn (gs', lengths, vs) =>
                   (gs', v o Lib.mapshape lengths vs))
                (all_goals gs)))
  end

fun NORELSE (tac1, tac2) g =
  seq.delay
    (fn () =>
       case seq.cases (tac1 g) of
           NONE => tac2 g
         | SOME (result, rest) => seq.cons result rest)

fun NAPPEND (tac1, tac2) g =
  seq.append (seq.delay (fn () => tac1 g)) (seq.delay (fn () => tac2 g))

fun NTRY tac = NORELSE (tac, NALL_TAC)

fun NREPEAT tac = LIFT (Tactical.REPEAT (DETERM tac))

fun same_goal ((asms1, tm1), (asms2, tm2)) =
  ListPair.allEq (fn (a1, a2) => Term.aconv a1 a2) (asms1, asms2)
  andalso Term.aconv tm1 tm2

fun NCHANGED tac g =
  seq.delay
    (fn () =>
       seq.filter
         (fn (gs, _) =>
            case gs of
                [g'] => not (same_goal (g, g'))
              | _ => true)
         (tac g))

fun NFIRST [] = NNO_TAC
  | NFIRST (tac :: tacs) = NORELSE (tac, NFIRST tacs)

fun nEVERY [] = NALL_TAC
  | nEVERY (tac :: tacs) = NTHEN (tac, nEVERY tacs)

end
