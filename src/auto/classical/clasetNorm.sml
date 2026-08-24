structure clasetNorm :> clasetNorm =
struct

open Abbrev HolKernel boolSyntax

type origin = string * string

fun error (origin_structure, origin_function) message =
  raise mk_HOL_ERR origin_structure origin_function message

(* [IN] is a boolTheory constant, [IN = \x f. f x], so [x IN P] and [P x]
   are one proposition written two ways, and a search that reads them as
   two atoms cannot get from one to the other.  Membership is the normal
   form because it is the one a search can hold on to: a set inside
   [x IN A] stays inside it however [A] is instantiated, whereas [A x]
   with [A] instantiated to a set former is an atom no rule about that
   former can match.

   The crossing is made at formula positions only.  Term positions keep
   beta-eta, so [\x. f x] still contracts to [f]; and a body wrapped as
   [x IN P] is no longer an eta redex, which is what stops [!x. P x] from
   collapsing to [$! P] and coming back applied when a search instantiates
   it.  A formula position is one the engines themselves decompose; an
   atom is compared whole, so a formula buried in a term position needs no
   crossing. *)

(* |- !item set. item IN set = set item *)
val membership_thm =
  let
    val item = mk_var ("item", Type.alpha)
    val set = mk_var ("set", Type.alpha --> Type.bool)
    val definition =
      Thm.AP_THM (Thm.AP_THM boolTheory.IN_DEF item) set
  in
    GENL [item, set]
      (Conv.CONV_RULE
        (Conv.RAND_CONV (Conv.REDEPTH_CONV BETA_CONV))
        definition)
  end

(* |- !item set. set item = item IN set *)
val applied_thm = Conv.GSYM membership_thm

fun head_beta_conv tm =
  if is_abs (rator tm) then BETA_CONV tm
  else Conv.RATOR_CONV head_beta_conv tm

fun expand_conv tm =
  let
    val (domain, _) = Type.dom_rng (type_of tm)
    val variable = variant (free_vars tm) (mk_var ("x", domain))
  in
    Thm.SYM (Drule.ETA_CONV (mk_abs (variable, mk_comb (tm, variable))))
  end

fun connective tm =
  let
    val (head, arguments) = strip_comb tm
  in
    case total dest_thy_const head of
        NONE => NONE
      | SOME {Thy, Name, ...} => SOME (Thy, Name, arguments)
  end

(* [is_hole] tells the crossing which variables stand for an unknown rather
   than for a set.  [?P x] is how a search asks pattern unification to build
   a predicate, and writing it as a membership would leave a first-order
   problem that only another membership can solve.  Each engine names its own
   holes: the classical engine's metavariables, blast's rule variables. *)
fun formula is_hole tm =
  Conv.ORELSEC
    (Conv.THENC (head_beta_conv, formula is_hole), shape is_hole) tm

and shape is_hole tm =
    let
      val descend = formula is_hole
    in
      case connective tm of
          SOME ("bool", "!", [_]) => binder is_hole tm
        | SOME ("bool", "?", [_]) => binder is_hole tm
        | SOME ("bool", "?!", [_]) => binder is_hole tm
        | SOME ("bool", "~", [_]) => Conv.RAND_CONV descend tm
        | SOME ("bool", "/\\", [_, _]) => Conv.BINOP_CONV descend tm
        | SOME ("bool", "\\/", [_, _]) => Conv.BINOP_CONV descend tm
        | SOME ("min", "==>", [_, _]) => Conv.BINOP_CONV descend tm
        | SOME ("min", "=", [left, _]) =>
            if type_of left = Type.bool then Conv.BINOP_CONV descend tm
            else atom is_hole tm
        | SOME ("bool", "IN", [_, set]) =>
            if is_abs set then
              Conv.THENC
                (Conv.REWR_CONV membership_thm,
                 Conv.THENC (BETA_CONV, descend)) tm
            else Conv.ALL_CONV tm
        | _ => atom is_hole tm
    end

and binder is_hole tm =
    let
      val predicate = rand tm
    in
      if is_abs predicate then
        Conv.RAND_CONV (Conv.ABS_CONV (formula is_hole)) tm
      else if is_var predicate andalso not (is_hole predicate) then
        (* [!x. P x] contracted to [$! P] would come back applied when a
           search instantiates it, so it is expanded and its body crossed. *)
        Conv.THENC (Conv.RAND_CONV expand_conv, formula is_hole) tm
      else Conv.ALL_CONV tm
    end

and atom is_hole tm =
    (* The type test keeps the conversion total: a caller may hand it a term
       position, where an application over a variable is not an atom at all. *)
    if is_comb tm andalso is_var (rator tm) andalso
       not (is_hole (rator tm)) andalso type_of tm = Type.bool
    then Conv.REWR_CONV applied_thm tm
    else Conv.ALL_CONV tm

fun membership_conv_with is_hole = Conv.QCONV (formula is_hole)

val membership_conv = membership_conv_with clasetMeta.is_meta

(* The other direction: [IN] unfolded, which is its definition.  Unfolding is
   sound at every position, so this needs no notion of a formula position.
   It exists for looking a goal up in an index keyed on the rules as stated;
   nothing normalises to it. *)
val applied_conv =
  Conv.QCONV
    (Conv.REDEPTH_CONV
      (Conv.ORELSEC (Conv.REWR_CONV membership_thm, BETA_CONV)))

(* [x IN (\y. b)] is a beta redex written through the definition of [IN],
   so reducing it is reduction and not the crossing: it makes a strictly
   simpler term, and a membership in anything else is left alone.  Leaving
   it unreduced would keep the engine's state opaque -- every step would
   have to re-cross an atom whose body the rules are stated about. *)
val member_beta_conv =
  Conv.THENC (Conv.REWR_CONV membership_thm, BETA_CONV)

(* [reduce_conv] is what shapes the engine's terms: an instantiated rule is
   reduced, and its premises become goals the caller reads.  The crossing
   deliberately stays out of it, so a residual goal comes back written the
   way it was posed.  [normalize_conv] adds the crossing and is for
   comparing: the matcher and [align_conclusion] use it, and nothing that
   builds a goal does. *)
val reduction =
  Conv.REDEPTH_CONV
    (Conv.ORELSEC (BETA_CONV, Conv.ORELSEC (Drule.ETA_CONV,
     member_beta_conv)))

val reduce_conv = Conv.QCONV reduction

val normalize_conv =
  Conv.QCONV (Conv.THENC (formula clasetMeta.is_meta, reduction))

(* A rule application proves a goal in the normal form; the goal is the
   user's, as written.  This carries the proof back to the statement the
   caller has to produce. *)
fun align_conclusion target theorem =
  let
    val conclusion = concl theorem
  in
    if aconv conclusion target then
      EQ_MP (ALPHA conclusion target) theorem
    else
      let
        val target_equality = normalize_conv target
        val target' = rhs (concl target_equality)
        val conclusion_equality = normalize_conv conclusion
        val conclusion' = rhs (concl conclusion_equality)
      in
        if aconv conclusion' target' then
          EQ_MP (Thm.SYM target_equality)
            (EQ_MP (ALPHA conclusion' target')
              (EQ_MP conclusion_equality theorem))
        else
          error ("clasetNorm", "align_conclusion")
            "the theorem does not prove the target in normal form"
      end
  end

fun normalize_thm theorem =
  Conv.CONV_RULE reduce_conv theorem

fun normalize_rule_thm theorem =
  let
    fun normalize_hypothesis (hypothesis, current) =
      let
        val equality = reduce_conv hypothesis
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
    val equality = reduce_conv (concl theorem)
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
