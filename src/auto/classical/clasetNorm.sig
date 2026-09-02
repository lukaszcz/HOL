signature clasetNorm =
sig
  include Abbrev

  type origin = string * string

  (* Beta, eta, and the membership crossing at formula positions.  See
     the note in the implementation for why membership is the normal
     form. *)
  val reduce_conv : conv
  (* [reduce_conv] without eta, for a goal the caller posed: eta changes
     a binder's shape and a goal is handed to tactics that take it
     apart. *)
  val goal_reduce_conv : conv
  val normalize_conv : conv
  (* The crossing alone, for a caller that keeps its own beta-eta, and its
     inverse, for a caller that has to try both spellings.  The [_with]
     form takes the caller's test for the variables that are holes rather
     than sets; [membership_conv] uses the classical engine's own. *)
  val membership_conv_with : (term -> bool) -> conv
  val membership_conv : conv
  val applied_conv : conv

  (* Membership at every position: the mirror of [applied_conv], for a
     lookup that must ask for both spellings of an application whose head
     is compound, where neither is a normal form. *)
  val crossed_conv : conv

  (* Carry a proof of a target's normal form back to the target. *)
  val align_conclusion : term -> thm -> thm
  val normalize_thm : thm -> thm
  val normalize_rule_thm : thm -> thm
  val normalize_assumption_thm : thm -> term * thm
  val normalize_assumption : term -> term * thm
  val split_imp_prefix :
    origin -> int -> term -> term list * term
  val nth1 : origin -> 'a list -> int -> 'a
  val delete_nth : origin -> 'a list -> int -> 'a list
  val term_size : term -> int
end
