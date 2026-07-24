structure clasimpLib :> clasimpLib =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "clasimpLib"

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

fun iff_declaration name theorem =
  let
    val th = Drule.SPEC_ALL theorem
    val (prems, final) = boolSyntax.strip_imp_only (concl th)
    val safe = null prems
    fun spec kind =
      {kind = kind, safe = safe, prio = NONE}

    fun undisch [] result = result
      | undisch (prem :: rest) result =
          undisch rest (MP result (ASSUME prem))

    (* The derived iff/not rule initially has the source antecedents as
       hypotheses and its new major premise last.  Discharge the source
       antecedents first, then the major, to put the major premise at the
       front as Isabelle's rotate_prems n does. *)
    fun rotate_major major result =
      Drule.GEN_ALL
        (DISCH major
          (List.foldr
            (fn (prem, current) => DISCH prem current)
            result prems))

    fun iff_rules () =
      let
        val core = undisch prems th
        val (left, right) = boolSyntax.dest_eq final
        val (forward, backward) = EQ_IMP_RULE core
        val intro =
          rotate_major right (MP backward (ASSUME right))
        val dest =
          rotate_major left (MP forward (ASSUME left))
      in
        [(spec clasetRules.Intro, (name ^ "_intro", intro)),
         (spec clasetRules.Dest, (name ^ "_dest", dest))]
      end

    fun not_rule () =
      let
        val core = undisch prems th
        val major = boolSyntax.dest_neg final
        val false_th = MP (NOT_ELIM core) (ASSUME major)
        val result_var =
          variant (free_varsl (concl core :: hyp core))
            (mk_var ("iff_result", Type.bool))
        val result =
          MP (SPEC result_var boolTheory.FALSITY) false_th
        val elim = rotate_major major result
      in
        [(spec clasetRules.Elim, (name ^ "_elim", elim))]
      end

    val rules =
      if boolSyntax.is_eq final andalso
         type_of (fst (boolSyntax.dest_eq final)) = Type.bool
      then iff_rules ()
      else if boolSyntax.is_neg final then not_rule ()
      else
        [(spec clasetRules.Intro,
          (name ^ "_intro", Drule.GEN_ALL th))]
  in
    {rules = rules, rewrite = th}
  end

fun add_iff_declaration name theorem (cs, ss) =
  let
    val {rules, rewrite} = iff_declaration name theorem
    val cs' =
      List.foldl
        (fn ((rule_spec, named_rule), current) =>
          clasetLib.add_rule rule_spec named_rule current)
        cs rules
    val ss' =
      simpLib.++ (ss, simpLib.rewrites [rewrite])
  in
    (cs', ss')
  end

fun persistent_iff_name name = KernelSig.name_toString name

fun normalise_iff_name name =
  if String.isSubstring "$" name then name
  else
    (persistent_iff_name (ThmSetData.toKName name)
     handle HOL_ERR _ => name)

fun iff_fragment_name name = "__clasimp_iff_" ^ name

fun remove_iff_rules name =
  clasetLib.remove_rule (name ^ "_intro") o
  clasetLib.remove_rule (name ^ "_dest") o
  clasetLib.remove_rule (name ^ "_elim")

fun retract_iff_declaration name =
  let
    val _ = clasetLib.augment_claset (remove_iff_rules name)
    val _ =
      (BasicProvers.diminish_srw_ss [iff_fragment_name name]
       handle Conv.UNCHANGED => ())
  in
    ()
  end

fun install_persistent_iff name theorem =
  let
    val {rules, rewrite} = iff_declaration name theorem
    fun add_rules cs =
      List.foldl
        (fn ((spec, named_rule), current) =>
          clasetLib.add_rule spec named_rule current)
        cs rules
    val fragment =
      simpLib.named_rewrites (iff_fragment_name name) [rewrite]
    val _ = retract_iff_declaration name
    val _ = clasetLib.augment_claset add_rules
  in
    BasicProvers.augment_srw_ss [fragment]
  end

fun apply_iff_delta delta db =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        Symtab.update (persistent_iff_name name, theorem) db
    | ThmSetData.REMOVE name =>
        Symtab.delete_safe (normalise_iff_name name) db

fun apply_iff_to_global delta db =
  let
    val _ =
      case delta of
          ThmSetData.ADD (name, theorem) =>
            install_persistent_iff
              (persistent_iff_name name) theorem
        | ThmSetData.REMOVE name =>
            retract_iff_declaration (normalise_iff_name name)
  in
    apply_iff_delta delta db
  end

val _ =
  if List.exists (equal "iff") (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute "iff"
  then raise ERR "registration" "settype or attribute iff already exists"
  else ()

(* The source theorem is the only persistent declaration.  Its claset and
   simpset views are recomputed by this hook whenever the iff stream is
   replayed.  The views deliberately use the public augmentation APIs, so
   neither the claset cdelta schema nor the simp declaration stream changes.

   Claset candidate order uses declaration recency as a tie-break.  Since
   [intro] and [iff] inhabit different delta streams, their relative recency
   in one theory may be permuted on reload.  This affects ties only; a shared
   declaration counter can be introduced if later benchmarks need one. *)
val iff_data =
  ThmSetData.export_with_ancestry
    {settype = "iff",
     delta_ops =
       {apply_to_global = apply_iff_to_global,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_iff_delta}}

fun remove_iff name =
  let
    val delta = ThmSetData.REMOVE (normalise_iff_name name)
  in
    #record_delta iff_data delta;
    #update_global_value iff_data (apply_iff_to_global delta)
  end

fun process_clasimp_args body base_cs base_ss =
  markerLib.ABBRS_THEN
    (fn theorems =>
      let
        fun partition (simp_rules, iff_rules, rest) [] =
              (List.rev simp_rules, List.rev iff_rules, List.rev rest)
          | partition (simp_rules, iff_rules, rest)
              (theorem :: tail) =
              (case clasetLib.destSimp theorem of
                   SOME rule =>
                     partition
                       (rule :: simp_rules, iff_rules, rest) tail
                 | NONE =>
                     (case clasetLib.destIff theorem of
                          SOME rule =>
                            partition
                              (simp_rules, rule :: iff_rules, rest)
                              tail
                        | NONE =>
                            partition
                              (simp_rules, iff_rules,
                               theorem :: rest) tail))

        val (simp_rules, iff_rules, classical_args) =
          partition ([], [], []) theorems
        val simp_ss =
          List.foldl
            (fn (rule, ss) => simpLib.++ (ss, simpLib.rewrites [rule]))
            base_ss simp_rules
        val (iff_cs, invocation_ss) =
          List.foldl
            (fn ((index, rule), pair) =>
              add_iff_declaration
                ("__clasimp_iff_arg_" ^ Int.toString index)
                rule pair)
            (base_cs, simp_ss) (Lib.enumerate 0 iff_rules)
        val (invocation_cs, leftovers) =
          clasetLib.process_claset_tags classical_args iff_cs
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

fun auto_with {blast, depth} cs ss simp_args =
  let
    val search_cs = add_simp_wrapper_with ss simp_args cs
    val final_cs = add_safe_simp_wrapper_with ss simp_args cs
    val initial_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)
    val search =
      Tactical.ORELSE
        (tableauLib.CS_BLAST_DEPTH_TAC cs blast,
         NTactical.DETERM
           (classicalLib.CS_DEPTH_SOLVE_TAC
              {dup = false} depth search_cs))
    val final_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC final_cs)

    (* Isabelle repeatedly selects the first goal on which search succeeds.
       Both search legs solve their selected goal, and the repetition only
       revisits a residue when solving another goal instantiates shared
       schematic variables.  HOL4 kernel subgoals cannot share
       metavariables, so one TRY per subgoal (from THEN) is equivalent. *)
    val script =
      Tactical.EVERY
        [asm_full_simp ss simp_args,
         Tactical.TRY initial_safe,
         Tactical.TRY search,
         Tactical.TRY final_safe]
  in
    Tactical.CHANGED_TAC script
  end

fun CS_AUTO_TAC bounds cs ss = auto_with bounds cs ss []

fun force_with name cs ss simp_args =
  let
    val search_cs = add_simp_wrapper_with ss simp_args cs

    (* add_simp_wrapper installs an unsafe wrapper.  It is deliberately
       inert under CS_CLARIFY_TAC, which consults only safe wrappers; this
       follows Isabelle's force_tac literally.  Isabelle's clarify succeeds
       unchanged, whereas CS_CLARIFY_TAC reports a no-op as failure, so TRY
       restores the upstream sequencing behavior. *)
    val clarify =
      NTactical.DETERM
        (classicalLib.CS_CLARIFY_TAC search_cs)
    val search =
      NTactical.DETERM
        (classicalLib.CS_FIRST_BEST_TAC search_cs)
    val script =
      Tactical.EVERY
        [Tactical.TRY clarify,
         asm_full_simp ss simp_args,
         search]
  in
    must_close name script
  end

fun CS_FORCE_TAC cs ss = force_with "CS_FORCE_TAC" cs ss []

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

fun AUTO_DEPTH_TAC bounds theorems =
  public (auto_with bounds) theorems

fun AUTO_TAC theorems =
  AUTO_DEPTH_TAC {blast = 4, depth = 2} theorems

fun FORCE_TAC theorems =
  public (force_with "FORCE_TAC") theorems

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
