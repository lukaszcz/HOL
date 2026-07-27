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

fun add_simp_wrapper ss simp_args =
  let
    fun wrapper step =
      NTactical.NAPPEND
        (NTactical.NCHANGED
           (NTactical.LIFT (asm_full_simp ss simp_args)),
         step)
  in
    clasetLib.add_unsafe_wrapper ("asm_full_simp_tac", wrapper)
  end

fun add_safe_simp_wrapper ss simp_args =
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

fun iff_declaration name theorem =
  let
    val th = Drule.SPEC_ALL theorem
  in
    {rules = clasetLib.iff_rules name theorem, rewrite = th}
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

val normalise_iff_name = clasetLib.normalise_rule_name

(* Simp deletion keys use the public "Thy.Name" spelling.  Claset and iff-db
   keys deliberately retain the kernel's "Thy$Name" spelling. *)
fun simp_delete_key ({Thy, Name} : KernelSig.kernelname) =
  Thy ^ "." ^ Name

(* Scratch theories are not members of [ancestry "-"], whose name parser
   validates qualified deletion keys.  An unqualified key has the same
   current-theory meaning and keeps the interactive path usable. *)
fun active_simp_delete_key (kname as {Thy, Name}) =
  if List.exists (equal Thy) (ancestry "-")
  then simp_delete_key kname
  else Name

fun persistent_iff_kname name =
  case String.fields (equal #"$") name of
      [thy, theorem] => {Thy = thy, Name = theorem}
    | _ => ThmSetData.toKName name

fun remove_iff_rules name =
  clasetLib.remove_rule (name ^ "_intro") o
  clasetLib.remove_rule (name ^ "_dest") o
  clasetLib.remove_rule (name ^ "_elim")

fun retract_iff_declaration kname =
  let
    val name = persistent_iff_name kname
    val _ = clasetLib.augment_claset (remove_iff_rules name)
  in
    BasicProvers.temp_delsimps [active_simp_delete_key kname]
  end

fun install_persistent_iff kname theorem =
  let
    val name = persistent_iff_name kname
    val {rules, rewrite} = iff_declaration name theorem
    fun add_rules cs =
      List.foldl
        (fn ((spec, named_rule), current) =>
          clasetLib.add_rule spec named_rule current)
        cs rules
    val fragment =
      simpLib.named_rewrites_with_names (#Thy kname)
        [(kname, rewrite)]
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

(* Retraction only ever applies to a name the db records as installed.
   Skipping it otherwise avoids a whole-history rebuild of the global
   simpset for every declaration replayed at theory load. *)
fun apply_iff_to_global delta db =
  let
    fun retract_if_present kname =
      if Symtab.defined db (persistent_iff_name kname)
      then retract_iff_declaration kname
      else ()
    val _ =
      case delta of
          ThmSetData.ADD (name, theorem) =>
            (retract_if_present name;
             install_persistent_iff name theorem)
        | ThmSetData.REMOVE name =>
            retract_if_present
              (persistent_iff_kname (normalise_iff_name name))
  in
    apply_iff_delta delta db
  end

(* Loading a theory resolves repeated declarations by their final event.
   Final-touch order preserves the recency tie-break of sequential replay. *)
fun iff_finaliser {thyname} deltas db =
  let
    fun remove_kname name =
      case String.fields (equal #"$") name of
          [thy, theorem] => {Thy = thy, Name = theorem}
        | _ =>
            (case String.fields (equal #".") name of
                 [thy, theorem] => {Thy = thy, Name = theorem}
               | [theorem] => {Thy = thyname, Name = theorem}
               | _ =>
                   raise ERR "iff_finaliser"
                     ("malformed iff name: " ^ name))

    fun delta_info delta =
      case delta of
          ThmSetData.ADD (kname, theorem) =>
            (kname, SOME (kname, theorem))
        | ThmSetData.REMOVE name =>
            (remove_kname name, NONE)

    fun remember (delta, (recent, states)) =
      let
        val (kname, state) = delta_info delta
        val key = persistent_iff_name kname
      in
        (key :: List.filter (fn key' => key <> key') recent,
         Symtab.update (key, state) states)
      end

    val (recent, states) =
      List.foldl remember ([], Symtab.empty) deltas
    val touched =
      map
        (fn key =>
          case Symtab.lookup states key of
              SOME (SOME (kname, _)) => kname
            | SOME NONE => remove_kname key
            | NONE => raise Fail "iff_finaliser: missing final state")
        (List.rev recent)
    val stale =
      List.filter
        (fn kname => Symtab.defined db (persistent_iff_name kname))
        touched
    val live =
      List.mapPartial
        (fn kname =>
          case Symtab.lookup states (persistent_iff_name kname) of
              SOME (SOME declaration) => SOME declaration
            | _ => NONE)
        touched
    val simp_deltas =
      ThmSetData.theory_data {settype = "simp", thy = thyname}

    (* The simp stream is loaded before this later-registered iff stream.
       Respect an explicit delsimps declaration instead of resurrecting the
       named rewrite when the iff view is replayed afterwards. *)
    fun explicitly_delsimped (kname : KernelSig.kernelname) =
      List.exists
        (fn ThmSetData.REMOVE name =>
              name = #Name kname orelse name = simp_delete_key kname
          | _ => false)
        simp_deltas
    val live_rewrites =
      List.filter (not o explicitly_delsimped o #1) live

    fun remove_rules cs =
      List.foldl
        (fn (kname, current) =>
          remove_iff_rules (persistent_iff_name kname) current)
        cs stale

    fun add_rules ((kname, theorem), cs) =
      let
        val {rules, ...} =
          iff_declaration (persistent_iff_name kname) theorem
      in
        List.foldl
          (fn ((spec, named_rule), current) =>
            clasetLib.add_rule spec named_rule current)
          cs rules
      end

    val _ =
      if null stale then ()
      else
        (BasicProvers.temp_delsimps (map active_simp_delete_key stale);
         clasetLib.augment_claset remove_rules)
    val _ =
      if null live_rewrites then ()
      else
        BasicProvers.augment_srw_ss
          [simpLib.named_rewrites_with_names thyname
             (map
                (fn (kname, theorem) =>
                  (kname, Drule.SPEC_ALL theorem))
                (List.rev live_rewrites))]
    val _ =
      if null live then ()
      else
        clasetLib.augment_claset
          (fn cs => List.foldl add_rules cs live)
  in
    List.foldl
      (fn (delta, current) => apply_iff_delta delta current)
      db deltas
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
        thy_finaliser = SOME iff_finaliser,
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
        val {simp_rules, iff_rules, simp_controls, rest = classical_args} =
          clasetLib.classify_simp_args theorems
        val simp_ss = simpLib.++ (base_ss, simpLib.rewrites simp_rules)
        val (iff_cs, invocation_ss) =
          List.foldl
            (fn ((index, rule), pair) =>
              add_iff_declaration
                ("__clasimp_iff_arg_" ^ Int.toString index)
                rule pair)
            (base_cs, simp_ss) (Lib.enumerate 0 iff_rules)
        val (invocation_cs, leftovers) =
          clasetLib.process_claset_tags classical_args iff_cs
      in
        Tactical.THEN
          (clasetLib.INSERT_FACTS_TAC leftovers,
           body invocation_cs invocation_ss simp_controls)
      end)

fun must_close name =
  Tactical.check_delta
    (ERR name "tactic did not close the goal")
    (fn (_, goals) => null goals)

fun auto_with {blast, depth} cs ss simp_args =
  let
    val search_cs = add_simp_wrapper ss simp_args cs
    val final_cs = add_safe_simp_wrapper ss simp_args cs
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
    val search_cs = add_simp_wrapper ss simp_args cs

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
       (engine (add_simp_wrapper ss simp_args cs)))

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
           (add_safe_simp_wrapper ss simp_args cs))
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
