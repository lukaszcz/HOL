structure hhMePo :> hhMePo =
struct

open HolKernel boolSyntax aiLib

type ptype = int * hol_type list
type pconst = string * ptype
type pconst_table = (string, ptype list) Redblackmap.dict
type ptype_counts = (ptype, int) Redblackmap.dict
type frequency_table = (string, ptype_counts) Redblackmap.dict

type fudge =
  {local_const_multiplier : real,
   worse_irrel_freq : real,
   higher_order_irrel_weight : real,
   abs_rel_weight : real,
   abs_irrel_weight : real,
   theory_const_rel_weight : real,
   theory_const_irrel_weight : real,
   chained_const_irrel_weight : real,
   intro_bonus : real,
   elim_bonus : real,
   simp_bonus : real,
   local_bonus : real,
   assum_bonus : real,
   chained_bonus : real,
   max_imperfect : real,
   max_imperfect_exp : real,
   threshold_divisor : real,
   ridiculous_threshold : real,
   fact_threshold0 : real,
   fact_threshold1 : real,
   perfect_threshold : real,
   hopeless_threshold : real,
   special_fact_index : int,
   hopeless_iter : int}

(* Isabelle's MePo defaults are kept together so that later tuning cannot
   accidentally produce a mixture of parameter sets. *)
val default_fudge : fudge =
  {local_const_multiplier = 1.5,
   worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   chained_const_irrel_weight = 0.25,
   intro_bonus = 0.15,
   elim_bonus = 0.15,
   simp_bonus = 0.15,
   local_bonus = 0.55,
   assum_bonus = 1.05,
   chained_bonus = 1.5,
   max_imperfect = 11.5,
   max_imperfect_exp = 1.0,
   threshold_divisor = 2.0,
   ridiculous_threshold = 0.1,
   fact_threshold0 = 0.45,
   fact_threshold1 = 0.85,
   perfect_threshold = 0.99999,
   hopeless_threshold = 0.001,
   special_fact_index = 45,
   hopeless_iter = 5}

val default_relevance_fudge = default_fudge

val pseudo_abs_name = "%abs"
fun pseudo_theory_name thy = "%thy%" ^ thy

fun order_of_type ty =
  case total Type.dom_rng ty of
      SOME (domain, range) =>
        Int.max (order_of_type domain + 1, order_of_type range)
    | NONE =>
        if Type.is_type ty then
          foldl Int.max 0 (map order_of_type (#Args (Type.dest_thy_type ty)))
        else 0

fun type_name ty =
  let val {Thy, Tyop, Args} = Type.dest_thy_type ty in
    (Thy ^ "$" ^ Tyop, Args)
  end

fun patternT_eq (pattern, instance) =
  if Type.is_vartype pattern then Type.is_vartype instance
  else if Type.is_type pattern andalso Type.is_type instance then
    let
      val (name, patterns) = type_name pattern
      val (name', instances) = type_name instance
    in
      name = name' andalso patternsT_eq (patterns, instances)
    end
  else false
and patternsT_eq ([], []) = true
  | patternsT_eq (pattern :: patterns, instance :: instances) =
      patternT_eq (pattern, instance) andalso
      patternsT_eq (patterns, instances)
  | patternsT_eq _ = false

fun ptype_eq ((order, patterns), (order', instances)) =
  order = order' andalso patternsT_eq (patterns, instances)

fun match_patternT (pattern, instance) =
  if Type.is_vartype pattern then true
  else if Type.is_type pattern andalso Type.is_type instance then
    let
      val (name, patterns) = type_name pattern
      val (name', instances) = type_name instance
    in
      name = name' andalso match_patternsT (patterns, instances)
    end
  else false
and match_patternsT (_, []) = true
  | match_patternsT ([], _ :: _) = false
  | match_patternsT (pattern :: patterns, instance :: instances) =
      match_patternT (pattern, instance) andalso
      match_patternsT (patterns, instances)

fun match_ptype ((_, patterns), (_, instances)) =
  match_patternsT (patterns, instances)

fun list_compare compare ([], []) = EQUAL
  | list_compare compare ([], _ :: _) = LESS
  | list_compare compare (_ :: _, []) = GREATER
  | list_compare compare (x :: xs, y :: ys) =
      (case compare (x, y) of
           EQUAL => list_compare compare (xs, ys)
         | order => order)

fun patternT_compare (left, right) =
  if Type.is_vartype left then
    if Type.is_vartype right then EQUAL else LESS
  else if Type.is_vartype right then GREATER
  else
    let
      val (name, arguments) = type_name left
      val (name', arguments') = type_name right
    in
      case String.compare (name, name') of
          EQUAL => list_compare patternT_compare (arguments, arguments')
        | order => order
    end

fun ptype_compare ((order, patterns), (order', patterns')) =
  case list_compare patternT_compare (patterns, patterns') of
      EQUAL => Int.compare (order, order')
    | result => result

fun empty_pconst_table () = dempty String.compare

fun add_pconst_to_table (name, ptype) table =
  let
    val old =
      case Redblackmap.peek (table, name) of
          SOME ptypes => ptypes
        | NONE => []
    val ptypes =
      if List.exists (fn old_ptype => ptype_eq (ptype, old_ptype)) old
      then old
      else ptype :: old
  in
    dadd name ptypes table
  end

fun const_ptype tm =
  let
    val {Thy, Name, Ty} = dest_thy_const tm
    val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
    val arguments =
      case total (Type.match_type generic) Ty of
          NONE => []
        | SOME substitution =>
            map (Type.type_subst substitution) (Type.type_vars generic)
  in
    (Thy ^ "$" ^ Name, (order_of_type Ty, arguments))
  end

fun free_ptype tm =
  let val (name, ty) = dest_var tm in
    (name, (order_of_type ty, []))
  end

fun irrelevant_const name =
  List.exists (fn irrelevant => irrelevant = name)
    ["min$=", "min$==>", "bool$T", "bool$F", "bool$~",
     "bool$/\\", "bool$\\/", "bool$COND", "bool$LET"]

fun set_const name = name = "bool$IN" orelse name = "pred_set$GSPEC"

fun add_pconsts_in_term thy tm initial =
  let
    fun add pconst table = add_pconst_to_table pconst table

    fun do_const bound head arguments table =
      let val pconst as (name, _) = const_ptype head in
        if set_const name then foldl (do_term bound) table arguments
        else
          foldl (do_term bound)
            (if irrelevant_const name then table else add pconst table)
            arguments
      end

    and do_term bound (term, table) =
      do_term_ext bound false term table

    and do_term_ext bound ext_arg term table =
      let val (head, arguments) = strip_comb term in
        if is_const head then do_const bound head arguments table
        else if is_var head then
          foldl (do_term bound)
            (if List.exists (fn variable => aconv variable head) bound then
               table
             else add (free_ptype head) table)
            arguments
        else if is_abs head then
          let
            (* HOL's destructor opens the binder as a free variable.  Keep
               an explicit scope so it retains Isabelle Bound semantics. *)
            val (variable, body) = dest_abs head
            val table' =
              if null arguments andalso not ext_arg then
                add (pseudo_abs_name,
                     (order_of_type (type_of variable) + 1, [])) table
              else table
            val table'' = do_term (variable :: bound) (body, table')
          in
            foldl (do_term bound) table'' arguments
          end
        else foldl (do_term bound) table arguments
      end

    and do_term_or_formula bound ext_arg term table =
      if type_of term = Type.bool then do_formula bound term table
      else do_term_ext bound ext_arg term table

    and do_formula bound term table =
      if is_forall term then do_quantifier dest_forall bound term table
      else if is_exists term then do_quantifier dest_exists bound term table
      else if is_exists1 term then
        do_quantifier dest_exists1 bound term table
      else if is_imp_only term then
        let val (left, right) = dest_imp_only term in
          do_formula bound right (do_formula bound left table)
        end
      else if is_conj term then
        let val (left, right) = dest_conj term in
          do_formula bound right (do_formula bound left table)
        end
      else if is_disj term then
        let val (left, right) = dest_disj term in
          do_formula bound right (do_formula bound left table)
        end
      else if is_neg term then do_formula bound (dest_neg term) table
      else if is_eq term then
        let val (left, right) = dest_eq term in
          do_term_or_formula bound true right
            (do_term_or_formula bound false left table)
        end
      else if is_cond term then
        let
          val (condition, then_branch, else_branch) = dest_cond term
          val table' = do_formula bound condition table
          val table'' =
            do_term_or_formula bound false then_branch table'
        in
          do_term_or_formula bound false else_branch table''
        end
      else if is_res_forall term then
        do_restricted dest_res_forall bound term table
      else if is_res_exists term then
        do_restricted dest_res_exists bound term table
      else do_term_ext bound false term table

    and do_quantifier dest bound term table =
      let val (variable, body) = dest term in
        do_formula (variable :: bound) body table
      end

    and do_restricted dest bound term table =
      let
        val (variable, restriction, body) = dest term
        val restricted = mk_comb (restriction, variable)
        val body_bound = variable :: bound
      in
        do_formula body_bound body
          (do_formula body_bound restricted table)
      end

    val with_theory =
      add (pseudo_theory_name thy, (0, [])) initial
  in
    do_formula [] tm with_theory
  end

fun pconsts_of_table table =
  dfoldl
    (fn (name, ptypes, result) =>
      foldl (fn (ptype, entries) => (name, ptype) :: entries)
        result ptypes)
    [] table

fun pconsts_in_term thy tm =
  pconsts_of_table (add_pconsts_in_term thy tm (empty_pconst_table ()))

fun pconst_hyper_mem match table (name, ptype) =
  case Redblackmap.peek (table, name) of
      NONE => false
    | SOME ptypes => List.exists (fn other => match (ptype, other)) ptypes

fun empty_frequency_table () = dempty String.compare

fun increment_frequency (name, ptype) table =
  let
    val counts =
      case Redblackmap.peek (table, name) of
          SOME old => old
        | NONE => dempty ptype_compare
    val count =
      case Redblackmap.peek (counts, ptype) of
          SOME old => old
        | NONE => 0
  in
    dadd name (dadd ptype (count + 1) counts) table
  end

fun count_term_consts bound (tm, table) =
  let val (head, arguments) = strip_comb tm in
    if is_const head then
      foldl (count_term_consts bound)
        (increment_frequency (const_ptype head) table) arguments
    else if is_var head then
      foldl (count_term_consts bound)
        (if List.exists (fn variable => aconv variable head) bound then table
         else increment_frequency (free_ptype head) table)
        arguments
    else if is_abs head then
      let
        val (variable, body) = dest_abs head
        val table' = count_term_consts (variable :: bound) (body, table)
      in
        foldl (count_term_consts bound) table' arguments
      end
    else foldl (count_term_consts bound) table arguments
  end

fun count_fact ((thy, term), table) =
  count_term_consts []
    (term, increment_frequency (pseudo_theory_name thy, (0, [])) table)

fun count_fact_consts facts =
  foldl count_fact (empty_frequency_table ()) facts

fun pconst_freq match table (name, ptype) =
  case Redblackmap.peek (table, name) of
      NONE => 0
    | SOME counts =>
        dfoldl
          (fn (other, count, total) =>
            if match (ptype, other) then total + count else total)
          0 counts

fun frequency_entries table =
  dfoldl
    (fn (name, counts, result) =>
      dfoldl (fn (ptype, count, entries) =>
        ((name, ptype), count) :: entries) result counts)
    [] table

end
