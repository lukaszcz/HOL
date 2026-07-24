structure clasimpLib :> clasimpLib =
struct

open Abbrev HolKernel

val safe_solver =
  simpLib.mk_tactic_solver
    ("clasimp safe",
     Tactical.FIRST
       [Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
        Tactic.REFL_TAC,
        Tactic.ACCEPT_TAC boolTheory.TRUTH,
        Tactical.FIRST_ASSUM Tactic.CONTR_TAC])

fun derive_clasimp_ss ss _ =
  ss
  |> simpLib.set_cond_depth 40
  |> (fn ss' => simpLib.++ (ss', simpLib.split_ss))
  |> simpLib.set_safe_solvers [safe_solver]

(* This accessor is the only visible part of the private derived-value
   record.  BasicProvers marks the cache stale whenever srw_ss changes. *)
val {get = clasimp_ss, set = _} =
  BasicProvers.make_simpset_derived_value
    derive_clasimp_ss simpLib.empty_ss

(* Isabelle's asm_full_simp_tac simplifies premises mutually and turns the
   mksimps_pairs decomposition of premises into usable rewrites.

   strip=true       decomposes simplified conjunction, existential and
                    implication assumptions, covering that premise view;
   elimvars=false   avoids HOL4's stronger, Isabelle-incompatible
                    substitution and deletion of variable equations;
   droptrues=true   removes premises simplified to T, as implication
                    simplification does;
   oldestfirst=true visits assumptions in their original implication order.

   The two extended flags supply mut_impc parity: the conclusion participates
   in the fixpoint and implication-shaped rewrites can rebuild the goal. *)
val asm_full_simp_base : simpLib.simptac_config =
  {strip = true, elimvars = false, droptrues = true, oldestfirst = true}

val asm_full_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = true}

fun asm_full_simp ss =
  simpLib.GEN_GLOBAL_SIMP_TAC {safe = false} asm_full_simp_config ss

fun safe_asm_full_simp ss =
  simpLib.GEN_GLOBAL_SIMP_TAC {safe = true} asm_full_simp_config ss

fun add_simp_wrapper_with ss simp_args =
  let
    fun wrapper step =
      NTactical.NAPPEND
        (NTactical.NCHANGED
           (NTactical.LIFT (asm_full_simp ss simp_args)),
         step)
  in
    clasetLib.add_unsafe_wrapper ("asm_full_simp_tac", wrapper)
  end

fun add_safe_simp_wrapper_with ss simp_args =
  let
    fun wrapper step =
      NTactical.NORELSE
        (step,
         NTactical.NCHANGED
           (NTactical.LIFT (safe_asm_full_simp ss simp_args)))
  in
    clasetLib.add_safe_wrapper
      ("safe_asm_full_simp_tac", wrapper)
  end

fun add_simp_wrapper ss = add_simp_wrapper_with ss []

fun add_safe_simp_wrapper ss = add_safe_simp_wrapper_with ss []

fun process_clasimp_args body base_cs base_ss =
  markerLib.ABBRS_THEN
    (fn theorems =>
      let
        fun partition (simp_rules, rest) [] =
              (List.rev simp_rules, List.rev rest)
          | partition (simp_rules, rest) (theorem :: tail) =
              (case clasetLib.destSimp theorem of
                   SOME rule =>
                     partition (rule :: simp_rules, rest) tail
                 | NONE =>
                     (case clasetLib.destIff theorem of
                          SOME _ =>
                            raise mk_HOL_ERR
                              "clasimpLib" "process_clasimp_args"
                              "Iff marker is not yet implemented"
                        | NONE =>
                            partition
                              (simp_rules, theorem :: rest) tail))

        val (simp_rules, classical_args) =
          partition ([], []) theorems
        val invocation_ss =
          List.foldl
            (fn (rule, ss) => simpLib.++ (ss, simpLib.rewrites [rule]))
            base_ss simp_rules
        val (invocation_cs, leftovers) =
          clasetLib.process_claset_tags classical_args base_cs
        val (simp_args, facts) =
          List.partition markerLib.is_generic_simp_marker leftovers
        val insert = Tactical.MAP_EVERY Tactic.ASSUME_TAC facts
      in
        Tactical.THEN
          (insert, body invocation_cs invocation_ss simp_args)
      end)

fun must_close name tactic goal =
  let
    val result as (goals, _) = tactic goal
  in
    if null goals then result
    else
      raise mk_HOL_ERR "clasimpLib" name
        "tactic did not close the goal"
  end

(* The classical search drivers already succeed only with a closed engine
   state.  must_close is the public contract guard in case that invariant
   changes; it does not add another search step. *)
fun search_with_simp name engine cs ss simp_args =
  must_close name
    (NTactical.DETERM
       (engine (add_simp_wrapper_with ss simp_args cs)))

fun CS_FASTFORCE_TAC cs ss =
  search_with_simp "CS_FASTFORCE_TAC"
    classicalLib.CS_FAST_TAC cs ss []

fun CS_SLOWSIMP_TAC cs ss =
  search_with_simp "CS_SLOWSIMP_TAC"
    classicalLib.CS_SLOW_TAC cs ss []

fun CS_BESTSIMP_TAC cs ss =
  search_with_simp "CS_BESTSIMP_TAC"
    classicalLib.CS_BEST_TAC cs ss []

fun clarsimp_with cs ss simp_args =
  let
    val clarify =
      NTactical.DETERM
        (classicalLib.CS_CLARIFY_TAC
           (add_safe_simp_wrapper_with ss simp_args cs))
    val script =
      Tactical.THEN
        (safe_asm_full_simp ss simp_args,
         (* Isabelle's clarify tactic succeeds unchanged.  The HOL4
            CS_CLARIFY_TAC deliberately fails on a no-op, so TRY restores
            the sequencing behavior; CHANGED_TAC below guards the complete
            script. *)
         Tactical.TRY clarify)
  in
    Tactical.CHANGED_TAC script
  end

fun CS_CLARSIMP_TAC cs ss = clarsimp_with cs ss []

fun public body theorems goal =
  process_clasimp_args body
    (clasetLib.the_claset ()) (clasimp_ss ()) theorems goal

fun FASTFORCE_TAC theorems =
  public
    (search_with_simp "FASTFORCE_TAC"
       classicalLib.CS_FAST_TAC) theorems

fun SLOWSIMP_TAC theorems =
  public
    (search_with_simp "SLOWSIMP_TAC"
       classicalLib.CS_SLOW_TAC) theorems

fun BESTSIMP_TAC theorems =
  public
    (search_with_simp "BESTSIMP_TAC"
       classicalLib.CS_BEST_TAC) theorems

fun CLARSIMP_TAC theorems =
  public clarsimp_with theorems

end
