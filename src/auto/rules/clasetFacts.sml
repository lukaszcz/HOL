structure clasetFacts :> clasetFacts =
struct

open Abbrev HolKernel

type fact =
  {id : int,
   original : thm,
   hypotheses : term list,
   fixed_terms : term list,
   fixed_types : hol_type list,
   loose_terms : term list,
   loose_types : hol_type list,
   schematic : thm option ref}

type environment = fact list

type view =
  {source_id : int, source : thm, theorem : thm,
   support : term list}

fun create (assumptions, target) theorems =
  let
    val goal_variables = Term.free_varsl (target :: assumptions)

    fun prepare (id, original) =
      let
        val hypotheses = Thm.hyp original
        val supported = Term.free_varsl hypotheses
        val genuine = Term.free_vars (Thm.concl original)
        val shared =
          List.filter
            (fn variable =>
              Lib.op_mem Term.aconv variable goal_variables)
            genuine
        val fixed_terms = Lib.op_union Term.aconv supported shared
        val support_types =
          List.foldl
            (fn (term, types) =>
              Lib.union (type_vars_in_term term) types)
            [] hypotheses
        val fixed_types =
          List.foldl
            (fn (variable, types) =>
              Lib.union (Type.type_vars (Term.type_of variable)) types)
            support_types shared
        val loose_terms =
          List.filter
            (fn variable =>
              not (Lib.op_mem Term.aconv variable fixed_terms))
            genuine
        val loose_types =
          Lib.set_diff
            (type_vars_in_term (Thm.concl original)) fixed_types
      in
        {id = id, original = original, hypotheses = hypotheses,
         fixed_terms = fixed_terms, fixed_types = fixed_types,
         loose_terms = loose_terms, loose_types = loose_types,
         schematic = ref NONE}
      end
  in
    map prepare (Lib.enumerate 0 theorems)
  end

fun facts environment = environment
fun source_id ({id, ...} : fact) = id
fun source ({original, ...} : fact) = original
fun support ({hypotheses, ...} : fact) = hypotheses
fun fixed_terms ({fixed_terms, ...} : fact) = fixed_terms
fun fixed_types ({fixed_types, ...} : fact) = fixed_types
fun has_schematic_types ({loose_types, ...} : fact) =
  not (null loose_types)

fun literal_view ({id, original, hypotheses, ...} : fact) =
  {source_id = id, source = original, theorem = original,
   support = hypotheses} : view

fun literal_views environment = map literal_view environment

fun schematic_view
      ({id, original, hypotheses, loose_terms, loose_types,
        schematic, ...} : fact) =
  let
    val theorem =
      case !schematic of
          SOME theorem => theorem
        | NONE =>
            let
              val term_fresh =
                map
                  (fn variable =>
                    {redex = variable,
                     residue = Term.genvar (Term.type_of variable)})
                  loose_terms
              val type_fresh =
                map
                  (fn ty =>
                    {redex = ty, residue = Type.gen_tyvar ()})
                  loose_types
              val theorem =
                Thm.INST_TYPE type_fresh
                  (Thm.INST term_fresh original)
            in
              schematic := SOME theorem; theorem
            end
  in
    {source_id = id, source = original, theorem = theorem,
     support = hypotheses}
  end

fun schematic_views environment =
  map schematic_view environment

fun match_view (entry : fact) pattern site =
  let
    val {source_id, source, theorem, support} = schematic_view entry
    val substitution =
      Term.match_terml
        (#fixed_types entry)
        (HOLset.fromList Term.compare (#fixed_terms entry))
        pattern site
    val instance = Drule.INST_TY_TERM substitution theorem
  in
    SOME
      {source_id = source_id, source = source,
       theorem = instance, support = support}
  end
  handle HOL_ERR _ => NONE
       | Match => NONE

fun implication_rule_view entry =
  if boolSyntax.is_imp_only
       (Thm.concl (Drule.SPEC_ALL (source entry))) then
    SOME (schematic_view entry)
  else NONE

fun equational theorem =
  let
    val (_, conclusion) =
      boolSyntax.strip_imp_only
        (Thm.concl (Drule.SPEC_ALL theorem))
  in
    boolSyntax.is_eq conclusion
  end

fun conjuncts theorem =
  Drule.CONJUNCTS theorem handle HOL_ERR _ => [theorem]

fun equational_views environment =
  List.concat
    (map
      (fn entry =>
        if not (List.exists equational
                  (conjuncts (source entry))) then []
        else
          let
            val {source_id, source, support, theorem} =
              schematic_view entry
          in
            map
              (fn piece =>
                {source_id = source_id, source = source,
                 theorem = piece, support = support} : view)
              (List.filter equational (conjuncts theorem))
          end)
      environment)

end
