structure clasetNorm :> clasetNorm =
struct

open Abbrev HolKernel boolSyntax

type origin = string * string

fun error (origin_structure, origin_function) message =
  raise mk_HOL_ERR origin_structure origin_function message

val normalize_conv =
  Conv.QCONV
    (Conv.REDEPTH_CONV
      (Conv.ORELSEC (BETA_CONV, Drule.ETA_CONV)))

fun normalize_thm theorem =
  Conv.CONV_RULE normalize_conv theorem

fun normalize_rule_thm theorem =
  let
    fun normalize_hypothesis (hypothesis, current) =
      let
        val equality = normalize_conv hypothesis
        val normalized = rhs (concl equality)
        val original = EQ_MP (SYM equality) (ASSUME normalized)
      in
        Drule.PROVE_HYP original current
      end
  in
    normalize_thm
      (List.foldl normalize_hypothesis theorem (hyp theorem))
  end

fun normalize_assumption_thm theorem =
  let
    val equality = normalize_conv (concl theorem)
  in
    (rhs (concl equality), EQ_MP equality theorem)
  end

fun normalize_assumption assumption =
  normalize_assumption_thm (ASSUME assumption)

fun split_imp_prefix origin arity tm =
  let
    fun split 0 premises conclusion =
          (List.rev premises, conclusion)
      | split remaining premises current =
          (case total dest_imp_only current of
               SOME (premise, rest) =>
                 split (remaining - 1) (premise :: premises) rest
             | NONE =>
                 error origin
                   "the instantiated rule has fewer premises than recorded")
  in
    if arity < 0 then
      error origin "negative implication-prefix arity"
    else
      split arity [] tm
  end

fun nth1 origin values pos =
  if pos < 1 then error origin "positions are one-based"
  else
    List.nth (values, pos - 1)
    handle Subscript => error origin "position out of range"

fun delete_nth origin values pos =
  let
    val _ = nth1 origin values pos
  in
    List.take (values, pos - 1) @ List.drop (values, pos)
  end

fun term_size tm =
  case dest_term tm of
      COMB (rator, rand) => term_size rator + term_size rand
    | LAMB (_, body) => 1 + term_size body
    | _ => 1

end
