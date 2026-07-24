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

fun add_simp_wrapper ss =
  let
    fun wrapper step =
      NTactical.NAPPEND
        (NTactical.NCHANGED
           (NTactical.LIFT (asm_full_simp ss [])),
         step)
  in
    clasetLib.add_unsafe_wrapper ("asm_full_simp_tac", wrapper)
  end

fun add_safe_simp_wrapper ss =
  let
    fun wrapper step =
      NTactical.NORELSE
        (step,
         NTactical.NCHANGED
           (NTactical.LIFT (safe_asm_full_simp ss [])))
  in
    clasetLib.add_safe_wrapper
      ("safe_asm_full_simp_tac", wrapper)
  end

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

end
