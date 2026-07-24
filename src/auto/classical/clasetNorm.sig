signature clasetNorm =
sig
  include Abbrev

  type origin = string * string

  val normalize_conv : conv
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
