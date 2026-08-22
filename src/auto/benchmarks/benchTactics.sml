structure benchTactics :> benchTactics =
struct

open HolKernel

(* The carriers the numeric methods have instances for.  Integer wins
   over real when a goal mentions both, because an integer subterm
   cannot be discharged by a field procedure.  [Abstract] is a goal
   over an explicit ring record, whose operations are projections
   rather than numeric constants, so no numeric instance applies. *)
datatype carrier = Num | Int | Real | Abstract

fun mentions ty term =
  can (find_term (fn sub => Type.compare (type_of sub, ty) = EQUAL)) term

fun ring_typed term =
  case Lib.total Type.dest_thy_type (type_of term) of
      SOME {Thy = "ring", Tyop = "ring", ...} => true
    | _ => false

fun carrier_of goal =
  if can (find_term ring_typed) goal then Abstract
  else if mentions intSyntax.int_ty goal then Int
  else if mentions realSyntax.real_ty goal then Real
  else Num

fun fixed tactic (_ : term) = [tactic]

(* Isabelle's presburger decides linear arithmetic over int and nat
   alike; intLib.COOPER_TAC is the HOL4 procedure for both. *)
fun presburger (_ : term) = [benchLib.Cooper]

(* Isabelle's [algebra] does two things behind one name: it normalises
   a ring or field identity, and it decides ideal membership.  Its
   [algebra_tac] is [ring_tac ORELSE ideal_tac], so both are offered
   here in that order and the goal is read for its carrier only.  An
   earlier version chose between them by asking whether the conclusion
   was existential; that guess agreed with the disjunction on every
   goal in the corpus, but it could only ever have turned a mapping
   failure into a reported HOL4 limitation.

   Where the list is a singleton, HOL4 has no second procedure for that
   carrier: the ideal decision procedure is the integer one, and
   [RealField.REAL_FIELD_TAC] already subsumes the real normaliser. *)
fun algebra goal =
  case carrier_of goal of
      Num => [benchLib.NumRing]
    | Int => [benchLib.IntRing, benchLib.IntIdeal]
    | Real => [benchLib.RealField]
    | Abstract => [benchLib.ExplicitRing]

val table : (string * (term -> benchLib.tactic_id list)) list =
  [("simp", fixed benchLib.Simp),
   ("simp_all", fixed benchLib.Simp),
   ("auto", fixed benchLib.Auto),
   ("blast", fixed benchLib.Blast),
   ("force", fixed benchLib.Force),
   ("fastforce", fixed benchLib.Fastforce),
   ("safe", fixed benchLib.Safe),
   ("clarify", fixed benchLib.Clarify),
   ("clarsimp", fixed benchLib.Clarsimp),
   ("metis", fixed benchLib.Metis),
   ("meson", fixed benchLib.Metis),
   ("arith", fixed benchLib.Linarith),
   ("linarith", fixed benchLib.Linarith),
   ("presburger", presburger),
   ("algebra", algebra)]

fun tactics name goal =
  case List.find (fn (covered, _) => covered = name) table of
      SOME (_, choose) => choose goal
    | NONE =>
        raise mk_HOL_ERR "benchTactics" "tactics"
          ("no HOL4 tactic for the Isabelle method " ^ name)

val methods = map #1 table

end
