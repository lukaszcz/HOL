structure orderData :> orderData =
struct

open HolKernel boolLib relationTheory orderRulesTheory

type axioms =
  {reflexive : thm option,
   transitive : thm option,
   antisymmetric : thm option,
   total : thm option}

type context =
  {relation : term,
   axioms : axioms,
   reduction : conv}

datatype literal =
    Weak of term * term
  | Strict of term * term
  | Equal of term * term
  | Distinct of term * term

type fact = {literal : literal, theorem : thm}

(* ------------------------------------------------------------------ *)
(* Reading an atom                                                     *)
(* ------------------------------------------------------------------ *)

val strord_tm = prim_mk_const {Thy = "relation", Name = "STRORD"}

(* Exactly two arguments come off, and what is left is compared with the
   relation.  Peeling by [strip_comb] instead would break a relation
   that is itself an application -- [RC R] is one, and that is the shape
   a strict primitive is read in. *)
fun dest_pair tm =
  case Lib.total dest_comb tm of
      NONE => NONE
    | SOME (left, right) =>
        (case Lib.total dest_comb left of
             NONE => NONE
           | SOME (head, argument) => SOME (head, argument, right))

fun dest_weak relation tm =
  case dest_pair tm of
      SOME (head, x, y) => if aconv head relation then SOME (x, y) else NONE
    | NONE => NONE

fun dest_strict relation tm =
  case dest_pair tm of
      SOME (head, x, y) =>
        (case Lib.total dest_comb head of
             SOME (strord, argument) =>
               if same_const strord strord_tm andalso aconv argument relation
               then SOME (x, y) else NONE
           | NONE => NONE)
    | NONE => NONE

(* ------------------------------------------------------------------ *)
(* Discovering the contexts a goal supplies                            *)
(* ------------------------------------------------------------------ *)

val order_definitions =
  [PreOrder, Order, WeakOrder, StrongOrder,
   LinearOrder, StrongLinearOrder, WeakLinearOrder]

val axiom_names =
  ["reflexive", "irreflexive", "transitive", "antisymmetric",
   "total", "trichotomous"]

fun conjuncts theorem =
  case Lib.total dest_conj (concl theorem) of
      SOME _ => conjuncts (CONJUNCT1 theorem) @ conjuncts (CONJUNCT2 theorem)
    | NONE => [theorem]

(* One atomic axiom: the predicate's name and the relation it is about. *)
fun dest_axiom theorem =
  case Lib.total dest_comb (concl theorem) of
      NONE => NONE
    | SOME (predicate, relation) =>
        (case Lib.total dest_thy_const predicate of
             SOME {Thy = "relation", Name, ...} =>
               if Lib.mem Name axiom_names then SOME (Name, relation, theorem)
               else NONE
           | _ => NONE)

fun axioms_of theorems =
  let
    val expand = PURE_REWRITE_RULE order_definitions
    fun atoms theorem = List.mapPartial dest_axiom (conjuncts (expand theorem))
  in
    List.concat (List.map atoms theorems)
  end

(* Group by relation, keeping the order the goal presents them in so a
   run is reproducible. *)
fun group atoms =
  let
    fun add ((name, relation, theorem), groups) =
      let
        fun place [] = [(relation, [(name, theorem)])]
          | place ((r, entries) :: rest) =
              if aconv r relation then (r, entries @ [(name, theorem)]) :: rest
              else (r, entries) :: place rest
      in
        place groups
      end
  in
    List.foldl add [] atoms
  end

fun lookup entries name =
  Option.map snd (List.find (fn (n, _) => n = name) entries)

(* The two derived axioms.  Totality is not usually stated: HOL4's linear
   orders carry [trichotomous], which with reflexivity is the same thing. *)
fun derive_total entries =
  case lookup entries "total" of
      SOME theorem => SOME theorem
    | NONE =>
        (case (lookup entries "reflexive", lookup entries "trichotomous") of
             (SOME r, SOME t) =>
               SOME (MATCH_MP (MATCH_MP order_total_of_trichotomous r) t)
           | _ => NONE)

fun weak_context relation entries reduction =
  {relation = relation,
   axioms =
     {reflexive = lookup entries "reflexive",
      transitive = lookup entries "transitive",
      antisymmetric = lookup entries "antisymmetric",
      total = derive_total entries},
   reduction = reduction}

(* A strict primitive is turned into its reflexive closure on the way in.
   [order_strict_of_strong] states [R = STRORD (RC R)], whose right side
   contains its own left, so it is applied at the outermost position it
   matches and not underneath -- rewriting to a fixpoint would not
   terminate. *)
fun strict_reduction equation =
  Conv.QCONV (ONCE_DEPTH_CONV (REWR_CONV equation))

fun strict_context relation entries irreflexive transitive =
  let
    val strong =
      MATCH_MP (MATCH_MP order_strong_of_parts irreflexive) transitive
    val weak = MATCH_MP order_weak_of_strong strong
    val closure = rand (concl weak)
    val equation = MATCH_MP order_strict_of_strong strong
    val closure_atoms =
      List.mapPartial dest_axiom
        (conjuncts (PURE_REWRITE_RULE [WeakOrder] weak))
    val closure_entries = List.map (fn (n, _, th) => (n, th)) closure_atoms
    val trichotomous_entries =
      case lookup entries "trichotomous" of
          NONE => []
        | SOME theorem =>
            [("trichotomous", MATCH_MP order_trichotomous_of_RC theorem)]
  in
    weak_context closure (closure_entries @ trichotomous_entries)
      (strict_reduction equation)
  end

fun context_of (relation, entries) =
  case lookup entries "transitive" of
      NONE => NONE
    | SOME transitive =>
        (case (lookup entries "irreflexive", lookup entries "reflexive") of
             (SOME irreflexive, NONE) =>
               SOME (strict_context relation entries irreflexive transitive)
           | _ => SOME (weak_context relation entries Conv.ALL_CONV))

fun contexts theorems =
  List.mapPartial context_of (group (axioms_of theorems))

val order_names =
  axiom_names @
  ["PreOrder", "Order", "WeakOrder", "StrongOrder",
   "LinearOrder", "StrongLinearOrder", "WeakLinearOrder"]

fun names_order tm =
  case dest_term tm of
      COMB (rator, rand) => names_order rator orelse names_order rand
    | LAMB (_, body) => names_order body
    | CONST _ =>
        (case Lib.total dest_thy_const tm of
             SOME {Thy = "relation", Name, ...} => Lib.mem Name order_names
           | _ => false)
    | VAR _ => false

fun has_order_axiom theorems =
  List.exists (fn theorem => names_order (concl theorem)) theorems

(* ------------------------------------------------------------------ *)
(* Reading a fact                                                      *)
(* ------------------------------------------------------------------ *)

fun negated_rule rule {reflexive, total, ...} =
  case (reflexive, total) of
      (SOME r, SOME t) => SOME (MATCH_MP (MATCH_MP rule r) t)
    | _ => NONE

fun classify (context : context) theorem =
  let
    val relation = #relation context
    val (domain, _) = Type.dom_rng (type_of relation)
    val statement = concl theorem
    fun at_domain tm = Type.compare (type_of tm, domain) = EQUAL
    fun equation tm =
      case Lib.total dest_eq tm of
          SOME (left, right) =>
            if at_domain left then SOME (left, right) else NONE
        | NONE => NONE
  in
    case dest_weak relation statement of
        SOME (x, y) => SOME {literal = Weak (x, y), theorem = theorem}
      | NONE =>
    case dest_strict relation statement of
        SOME (x, y) => SOME {literal = Strict (x, y), theorem = theorem}
      | NONE =>
    case equation statement of
        SOME (x, y) => SOME {literal = Equal (x, y), theorem = theorem}
      | NONE =>
    case Lib.total dest_neg statement of
        NONE => NONE
      | SOME body =>
    case dest_weak relation body of
        SOME (x, y) =>
          (case negated_rule order_not_weak (#axioms context) of
               SOME rule =>
                 SOME {literal = Strict (y, x),
                       theorem = MATCH_MP rule theorem}
             | NONE => NONE)
      | NONE =>
    case dest_strict relation body of
        SOME (x, y) =>
          (case negated_rule order_not_strict (#axioms context) of
               SOME rule =>
                 SOME {literal = Weak (y, x), theorem = MATCH_MP rule theorem}
             | NONE => NONE)
      | NONE =>
    case equation body of
        SOME (x, y) => SOME {literal = Distinct (x, y), theorem = theorem}
      | NONE => NONE
  end

fun literal_of_term (context : context) tm =
  let
    val relation = #relation context
    val (domain, _) = Type.dom_rng (type_of relation)
    fun equation t =
      case Lib.total dest_eq t of
          SOME (left, right) =>
            if Type.compare (type_of left, domain) = EQUAL
            then SOME (left, right) else NONE
        | NONE => NONE
  in
    case dest_weak relation tm of
        SOME (x, y) => SOME (Weak (x, y))
      | NONE =>
    case dest_strict relation tm of
        SOME (x, y) => SOME (Strict (x, y))
      | NONE =>
    case equation tm of
        SOME (x, y) => SOME (Equal (x, y))
      | NONE =>
    case Lib.total dest_neg tm of
        NONE => NONE
      | SOME body =>
          (case equation body of
               SOME (x, y) => SOME (Distinct (x, y))
             | NONE => NONE)
  end

fun is_literal context tm =
  let
    val tm = rhs (concl (Conv.QCONV (#reduction (context : context)) tm))
    fun positive t = Option.isSome (literal_of_term context t)
  in
    positive tm orelse
    (case Lib.total dest_neg tm of
         SOME body => positive body
       | NONE => false)
  end

fun reduce (context : context) tm = Conv.QCONV (#reduction context) tm

fun normalise context theorem = CONV_RULE (reduce context) theorem

fun facts_of context theorem =
  List.mapPartial (classify context) (conjuncts (normalise context theorem))

fun facts_of_all context theorems =
  List.concat (List.map (facts_of context) theorems)

end
