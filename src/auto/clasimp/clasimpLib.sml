structure clasimpLib :> clasimpLib =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "clasimpLib"

val clasimp_trace = ref 0
val _ = Feedback.register_trace ("clasimp", clasimp_trace, 3)

fun trace level message =
  if level <= Feedback.current_trace "clasimp" then
    Feedback.HOL_MESG ("Clasimp: " ^ message ())
  else ()

val safe_solver =
  simpLib.mk_tactic_solver
    ("clasimp safe",
     Tactical.FIRST
       [Tactical.FIRST_ASSUM Tactic.ACCEPT_TAC,
        Tactic.REFL_TAC,
        Tactic.ACCEPT_TAC boolTheory.TRUTH,
        Tactical.FIRST_ASSUM Tactic.CONTR_TAC])

(* HOL4's COND_CONG simplifies both branches of a conditional as well as
   its condition.  A recursive equation whose right-hand side is a
   conditional -- how an interval or an iteration is ordinarily stated --
   then rewrites its own unfolding without end: the branch holds an
   instance of the rule's own left-hand side, and rewriting it produces
   another.  Isabelle states such equations and rewrites with them, which
   its weak conditional congruence -- the condition simplified, the
   branches left alone -- is what allows.  Nothing short of that helps:
   the unfolding is licensed by the rule alone, so a congruence that
   descends into the branches at all diverges, whether or not it carries
   the condition down with it.  This layer follows Isabelle; the branch
   reasoning comes back from the case split, split_ss below.

   A congruence belongs to a fragment and a fragment is replaced whole,
   so the three other congruences of CONG_ss are restated here. *)
local
  infix THEN
  val op THEN = Tactical.THEN
in
val cond_weak_cong =
  Tactical.prove
    (``!condition simplified left right.
         (condition = simplified) ==>
         ((if condition then left else right) =
          (if simplified then left else right))``,
     Tactical.REPEAT Tactic.GEN_TAC THEN
     Tactic.DISCH_TAC THEN
     Rewrite.ASM_REWRITE_TAC [])
end

val weak_cong_ss =
  simpLib.SSFRAG
    {name = SOME "CONGWEAK",
     congs =
       [Rewrite.REWRITE_RULE [Conv.GSYM boolTheory.AND_IMP_INTRO]
          boolTheory.IMP_CONG,
        cond_weak_cong,
        boolTheory.RES_FORALL_CONG,
        boolTheory.RES_EXISTS_CONG],
     convs = [], rewrs = [], filter = NONE, ac = [], dprocs = []}

(* [remove_ssfrags] signals an absent fragment by raising UNCHANGED.
   Reporting that is what keeps the replacement honest: a caught
   exception here would leave the strong congruence in place under a
   name that says otherwise. *)
fun weaken_cond_congruence ss =
  simpLib.++
    (simpLib.remove_ssfrags ["CONG"] ss
       handle Conv.UNCHANGED =>
         raise ERR "weaken_cond_congruence"
           "the simpset carries no CONG fragment to replace",
     weak_cong_ss)

(* The unsafe side-condition solver added here reaches this simpset only:
   the simplifier offers unsafe solvers to every traversal regardless of
   the safe solvers, so a simpset with a normalisation phase to protect
   (aesop) names the decision procedures it wants rather than inheriting
   from here. *)
fun derive_clasimp_ss ss _ =
  ss
  |> weaken_cond_congruence
  |> simpLib.set_cond_depth 40
  |> (fn ss' => simpLib.++ (ss', simpLib.split_ss))
  (* ETA_ss is where Isabelle's matcher is and HOL4's is not.  Isabelle
     rewrites under higher-order patterns, which are matched modulo eta,
     so a rule about [$+ start] fires on a goal spelled
     [\offset. start + offset] as well.  HOL4's rewriter matches up to
     alpha and beta only, so without this the two silently fail to meet;
     a translated term arrives in both spellings, since the translation
     writes the abstraction and the simplifier contracts it only
     sometimes.  The classical search does close some such goals on its
     own -- it is the rewriting that stops at the mismatch. *)
  |> (fn ss' => simpLib.++ (ss', boolSimps.ETA_ss))
  (* The same mismatch one spelling further on.  Isabelle normalises the
     natural number 1 to [Suc 0] -- One_nat_def is a simp rule there --
     so a fact stated on SUC fires against a goal that bounds by a
     numeral.  HOL4 normalises the other way, numerals being the normal
     form, and a cited SUC rule then never meets the goal.  SUC_FILTER
     closes the gap from HOL4's side, deriving the numeral-matching
     variant of each SUC rule as it enters, which leaves HOL4's normal
     form alone. *)
  |> (fn ss' => simpLib.++ (ss', numSimps.SUC_FILTER_ss))
  (* HOL4 carries no order reasoning ambiently: a goal that supplies its
     own order -- as a [WeakLinearOrder] premise, say -- has the axioms
     and the steps in the assumptions and nothing chains them.  Isabelle
     reads such a chain off the linorder class without naming it
     (Provers/order_tac.ML, installed by Orderings.thy).  The decision
     procedure covers both places a chain is wanted, since it is asked
     about an atom wherever the traversal meets one: the atom the
     rewriting has left standing, and the side condition of a conditional
     rewrite, which is simplified with this same simpset. *)
  |> (fn ss' => simpLib.++ (ss', orderLib.ORDER_ss))
  |> simpLib.set_safe_solvers [safe_solver]
  |> simpLib.add_unsafe_solver linarithLib.linarith_solver

(* This accessor is the only visible part of the private derived-value
   record.  BasicProvers marks the cache stale whenever srw_ss changes. *)
val {get = clasimp_ss, set = _} =
  BasicProvers.make_simpset_derived_value
    "clasimpLib.clasimp_ss" derive_clasimp_ss simpLib.empty_ss

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

(* Inside the classical cascade the split between assumptions and
   conclusion is the cascade's own: its negation introduction strips a
   goal [~p] to [p |- F], and an implication rebuild re-forms [p ==> F]
   as [~p].  Safe saturation repeats while any step applies, so a
   wrapper that inverts one of its steps gives the two a cycle it never
   leaves; simplification participating in the cascade therefore
   normalises in place. *)
val cascade_simp_config : simpLib.xsimptac_config =
  {base = asm_full_simp_base,
   concl_in_fixpoint = true,
   imp_rebuild = false}

fun cascade_safe_simp ss =
  simpLib.GEN_GLOBAL_SIMP_TAC {safe = true} cascade_simp_config ss

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
           (NTactical.LIFT (cascade_safe_simp ss simp_args)))
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

(* The derived rules are internal to the [iff] declaration, so a clash among
   them is not a declaration the user can correct.  add_derived_rule keeps
   the diagnostics quiet, and gives each declaration its own copy of a rule
   two declarations happen to derive alike, so retracting one declaration
   cannot silently disarm another. *)
fun add_iff_rules rules cs =
  List.foldl
    (fn ((rule_spec, named_rule), current) =>
      clasetLib.add_derived_rule rule_spec named_rule current)
    cs rules

fun persistent_iff_name name = KernelSig.name_toString name

val normalise_iff_name = clasetLib.normalise_rule_name

(* Persistent iff views live below the source theorem's public name.  Simp's
   prefix deletion means that Excl/delsimps on [Thy.Name] still affect the iff
   rewrite, while the dotted private key lets remove_iff retract only its own
   contribution.  The private claset stem likewise cannot collide with the
   ordinary rule generated by a theorem called [Name_intro]. *)
fun iff_view_name name = name ^ ".__clasimp_iff"

fun iff_rule_name kname =
  iff_view_name (persistent_iff_name kname)

fun iff_simp_kname ({Thy, Name} : KernelSig.kernelname) =
  {Thy = Thy, Name = iff_view_name Name}

(* Simp deletion keys use the public "Thy.Name" spelling.  Claset and iff-db
   keys deliberately retain the kernel's "Thy$Name" spelling. *)
fun simp_delete_key ({Thy, Name} : KernelSig.kernelname) =
  Thy ^ "." ^ Name

(* The private name contains a dot, so this is a three-field simp key.  Such
   keys retain their explicit theory qualifier even for the current scratch
   theory, which is intentionally absent from [ancestry "-"]. *)
fun iff_simp_delete_key kname =
  simp_delete_key (iff_simp_kname kname)

(* The one spelling of an iff rule name, shared by the declaration path and
   by the theory finaliser: the kernel "Thy$Name" form, the public "Thy.Name"
   form, or a bare name resolved against [default_thy].  remove_iff records
   only the kernel form, so the [default_thy] fallback serves the finaliser's
   reading of a name it did not itself record. *)
fun iff_kname {default_thy} name =
  case String.fields (equal #"$") name of
      [thy, theorem] => {Thy = thy, Name = theorem}
    | _ =>
        (case String.fields (equal #".") name of
             [thy, theorem] => {Thy = thy, Name = theorem}
           | [theorem] => {Thy = default_thy, Name = theorem}
           | _ =>
               raise ERR "iff_kname" ("malformed iff name: " ^ name))

fun persistent_iff_kname name =
  iff_kname {default_thy = current_theory ()} name

fun remove_iff_rules name =
  clasetLib.remove_rule (name ^ "_intro") o
  clasetLib.remove_rule (name ^ "_dest") o
  clasetLib.remove_rule (name ^ "_elim")

(* The simp stream is loaded before this later-registered iff stream, so a
   delsimps in the declaring theory would otherwise find the iff view
   resurrecting the named rewrite behind it.  The predicate makes such a
   removal persist, and both the declaration path and the finaliser apply
   it, so what a session ends with is what a descendant theory reloads.

   Only a theory-qualified removal counts.  A bare name is theory-agnostic
   in simp and matches by prefix, so honouring one here would let a
   delsimps aimed at an ancestor's rewrite silently suppress an unrelated
   local [iff] declaration that happens to share the theorem's name -- and
   the two delta streams carry no common ordering with which to tell the
   two apart.  remove_iff is the supported way to drop one's own
   declaration; a bare delsimps of it reaches the current session only. *)
fun theory_delsimped thyname =
  let
    val names =
      List.foldl
        (fn (ThmSetData.REMOVE name, names) => Symtab.update (name, ()) names
          | (_, names) => names)
        Symtab.empty
        (ThmSetData.theory_data {settype = "simp", thy = thyname})
  in
    fn (kname : KernelSig.kernelname) =>
      Symtab.defined names (simp_delete_key kname) orelse
      Symtab.defined names (iff_simp_delete_key kname)
  end

(* Installing and retracting a single declaration and installing a theory's
   whole batch are the same operation; the batched form is the only
   implementation.  [declarations] is in claset declaration order. *)
fun retract_persistent_iffs [] = ()
  | retract_persistent_iffs knames =
      let
        fun remove_rules cs =
          List.foldl
            (fn (kname, current) =>
              remove_iff_rules (iff_rule_name kname) current)
            cs knames
      in
        BasicProvers.temp_delsimps (map iff_simp_delete_key knames);
        clasetLib.augment_claset remove_rules
      end

(* The iff batch is a fragment of its own rather than one more contribution
   to the fragment BasicProvers names after the theory.  Sharing that name
   would leave Excl/ExclSF, diminish_srw_ss and exclude_ssfrags unable to
   address the [simp] and [iff] streams separately, and would let an
   exclusion already in force drop the whole batch unannounced. *)
fun iff_fragment_name thyname = thyname ^ "-iff"

fun install_persistent_iffs thyname declarations =
  let
    val delsimped = theory_delsimped thyname
    (* Reversed so that the most recent declaration takes precedence in the
       fragment, as successive single-declaration fragments do. *)
    val rewrites =
      List.rev
        (List.filter (fn (kname, _) => not (delsimped kname)) declarations)
    fun add_rules ((kname, theorem), cs) =
      add_iff_rules
        (#rules (iff_declaration (iff_rule_name kname) theorem)) cs
    val _ =
      if null rewrites then ()
      else
        BasicProvers.augment_srw_ss
          [simpLib.named_rewrites_with_names (iff_fragment_name thyname)
             (map
                (fn (kname, theorem) =>
                  (iff_simp_kname kname, Drule.SPEC_ALL theorem))
                rewrites)]
  in
    if null declarations then ()
    else
      clasetLib.augment_claset
        (fn cs => List.foldl add_rules cs declarations)
  end

fun retract_iff_declaration kname = retract_persistent_iffs [kname]

fun install_persistent_iff kname theorem =
  install_persistent_iffs (#Thy kname) [(kname, theorem)]

(* Only the source theorem is persistent; the db is the set of names whose
   claset and simpset views are currently installed. *)
fun apply_iff_delta delta db =
  case delta of
      ThmSetData.ADD (name, _) =>
        Symtab.update (persistent_iff_name name, ()) db
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
    fun delta_info (ThmSetData.ADD (kname, theorem)) =
          (kname, SOME (kname, theorem))
      | delta_info (ThmSetData.REMOVE name) =
          (iff_kname {default_thy = thyname} name, NONE)

    (* Scanning from the right keeps each name's final event, in the order
       those final events occur.  That is the recency order sequential
       replay would leave behind, at one pass over the deltas. *)
    fun remember (delta, (seen, touched)) =
      let
        val (kname, state) = delta_info delta
        val key = persistent_iff_name kname
      in
        if Symtab.defined seen key then (seen, touched)
        else (Symtab.update (key, ()) seen, (kname, state) :: touched)
      end

    val (_, touched) = List.foldr remember (Symtab.empty, []) deltas
    val stale =
      List.mapPartial
        (fn (kname, _) =>
          if Symtab.defined db (persistent_iff_name kname) then SOME kname
          else NONE)
        touched
    val live = List.mapPartial #2 touched
  in
    retract_persistent_iffs stale;
    install_persistent_iffs thyname live;
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

(* Resolve against the declarations currently installed rather than against
   the current theory.  Removing an ancestor's declaration by its plain name
   is the ordinary case, and defaulting the theory part to the current
   theory would name nothing and retract nothing, silently.  Resolving here
   also settles the name before it reaches the delta stream: a descendant
   theory replays the recorded name, so an unknown or ambiguous one would
   otherwise be replayed as a no-op by every descendant in turn. *)
fun resolve_iff_name name =
  let
    val installed = Symtab.keys (#get_global_value iff_data ())
    fun denotes candidate =
      candidate = name orelse
      (case String.fields (equal #"$") candidate of
           [thy, theorem] => theorem = name orelse thy ^ "." ^ theorem = name
         | _ => false)
  in
    case List.filter denotes installed of
        [resolved] => resolved
      | [] =>
          raise ERR "remove_iff"
            ("no [iff] declaration named " ^ name ^ " is installed")
      | candidates =>
          raise ERR "remove_iff"
            ("ambiguous [iff] name " ^ name ^ ": " ^
             String.concatWith ", " candidates)
  end

fun remove_iff name =
  let
    val delta = ThmSetData.REMOVE (resolve_iff_name name)
  in
    #record_delta iff_data delta;
    #update_global_value iff_data (apply_iff_to_global delta)
  end

fun extend_invocation
      {iff_prefix,simp_rules,iff_rules,claset,simpset} =
  let
    val simp_ss = simpLib.++ (simpset, simpLib.rewrites simp_rules)
    val declarations =
      map
        (fn (index, rule) =>
          iff_declaration (iff_prefix ^ Int.toString index) rule)
        (Lib.enumerate 0 iff_rules)
    val invocation_cs =
      List.foldl
        (fn ({rules,...}, cs) => add_iff_rules rules cs)
        claset declarations
    (* A single fragment rebuilds the rewrite net once.  Its head has the
       highest precedence, so reverse the declarations to match successive
       fragment insertion. *)
    val invocation_ss =
      if null declarations then simp_ss
      else
        simpLib.++
          (simp_ss,
           simpLib.rewrites (List.rev (map #rewrite declarations)))
  in
    (invocation_cs, invocation_ss)
  end

fun no_extra_markers theorems cs = (cs, theorems)

fun process_clasimp_args body base_cs base_ss =
  clasetLib.with_invocation_args
    {iff_prefix="__clasimp_iff_arg_", extra_markers=no_extra_markers}
    (fn cs => fn SOME ss => body cs ss
      | _ => raise ERR "process_clasimp_args" "simpset was not installed")
    base_cs (SOME {base=base_ss, extend=extend_invocation})

fun must_close name =
  Tactical.check_delta
    (ERR name "tactic did not close the goal")
    (fn (_, goals) => null goals)

(* Search tactics benefit from putting extensional equalities into their
   pointwise form before simplification and rule search.  FUN_EQ_CONV is
   proof-producing and applies equally to ordinary functions and sets.
   The conversion is deliberately root-only: expanding a nested test such
   as [f = EMPTY] would lose a useful case split, and a pointwise goal must
   not be extensionalized again. *)
val extensional_normalize =
  Tactical.CONV_TAC
    (Conv.CHANGED_CONV boolLib.FUN_EQ_CONV)

fun search_stages limit =
  let
    fun loop bound stages =
      if bound >= limit then List.rev (limit :: stages)
      else loop (bound * 2) (bound :: stages)
  in
    if limit <= 0 then [] else loop 1 []
  end

(* Try the witness-producing tableau at its invocation bound, then deepen
   the classical engine geometrically.  Re-running tableau from depth one
   repeats its whole frontier and caused previously cheap depth-four goals
   to spend their budget before reaching that bound.  Both legs remain
   bounded, and tableau witnesses are not hidden behind a complete
   classical traversal. *)
fun staged_auto_search {blast, depth} tableau_cs classical_cs =
  let
    fun report engine bound tactic goal =
      let
        val result = tactic goal
        val suffix =
          if engine = "classical" then
            ", expansions=" ^ Int.toString (clasetSearch.node_count ())
          else
            ", enable 'blast' trace level 2 for expansion statistics"
        val _ =
          trace 1
            (fn () =>
              engine ^ " search solved at stage " ^ Int.toString bound ^
              suffix)
      in
        result
      end
    val tableau =
      if blast <= 0 then []
      else
        [report "tableau" blast
           (tableauLib.CS_BLAST_DEPTH_TAC tableau_cs blast)]
    val classical =
      map
        (fn bound =>
          report "classical" bound
            (NTactical.DETERM
               (classicalLib.CS_DEPTH_SOLVE_TAC
                  {dup = false} bound classical_cs)))
        (search_stages depth)
  in
    Tactical.FIRST (tableau @ classical)
  end

fun auto_with {blast, depth} cs ss simp_args =
  let
    val search_cs = add_simp_wrapper ss simp_args cs
    val final_cs = add_safe_simp_wrapper ss simp_args cs
    val initial_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC cs)
    val search =
      staged_auto_search {blast = blast, depth = depth} cs search_cs
    val final_safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC final_cs)

    (* Isabelle repeatedly selects the first goal on which search succeeds.
       Both search legs solve their selected goal, and the repetition only
       revisits a residue when solving another goal instantiates shared
       schematic variables.  HOL4 kernel subgoals cannot share
       metavariables, so one TRY per subgoal (from THEN) is equivalent. *)
    val script =
      Tactical.EVERY
        [Tactical.TRY extensional_normalize,
         asm_full_simp ss simp_args,
         Tactical.TRY initial_safe,
         Tactical.TRY search,
         Tactical.TRY final_safe]
  in
    Tactical.CHANGED_TAC script
  end

fun CS_of body cs ss = body cs ss []

fun CS_AUTO_TAC bounds = CS_of (auto_with bounds)

fun force_with name cs ss simp_args =
  let
    val search_cs = add_simp_wrapper ss simp_args cs
    val clarify =
      NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)

    (* Simplify before safe saturation.  In particular, this preserves an
       extensional IMAGE obligation until membership rewrites expose the
       constructor constraints from which tableau search builds a witness. *)
    val safe =
      NTactical.DETERM (classicalLib.CS_SAFE_TAC search_cs)
    val search =
      Tactical.ORELSE
        (staged_auto_search {blast = 8, depth = 4} cs search_cs,
         NTactical.DETERM
           (classicalLib.CS_FIRST_BEST_TAC search_cs))
    val script =
      Tactical.EVERY
        [Tactical.TRY clarify,
         Tactical.TRY extensional_normalize,
         simpLib.FULL_SIMP_TAC ss simp_args,
         asm_full_simp ss simp_args,
         Tactical.TRY safe,
         search]
  in
    must_close name script
  end

val CS_FORCE_TAC = CS_of (force_with "CS_FORCE_TAC")

(* The classical search drivers already succeed only with a closed engine
   state.  must_close is the public contract guard in case that invariant
   changes; it does not add another search step. *)
fun search_with_simp name engine cs ss simp_args =
  let
    val clarify =
      NTactical.DETERM (classicalLib.CS_CLARIFY_TAC cs)
  in
    must_close name
      (Tactical.EVERY
         [Tactical.TRY clarify,
          Tactical.TRY extensional_normalize,
          NTactical.DETERM
            (engine (add_simp_wrapper ss simp_args cs))])
  end

val simp_search =
  (classicalLib.CS_FAST_TAC, classicalLib.CS_SLOW_TAC,
   classicalLib.CS_BEST_TAC)
val (fast_search, slow_search, best_search) = simp_search

val CS_FASTFORCE_TAC =
  CS_of (search_with_simp "CS_FASTFORCE_TAC" fast_search)
val CS_SLOWSIMP_TAC =
  CS_of (search_with_simp "CS_SLOWSIMP_TAC" slow_search)
val CS_BESTSIMP_TAC =
  CS_of (search_with_simp "CS_BESTSIMP_TAC" best_search)

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

val CS_CLARSIMP_TAC = CS_of clarsimp_with

fun restore_normalized_target target validation theorems =
  let
    val theorem = validation theorems
    val normalization =
      Conv.QCONV
        (Conv.REDEPTH_CONV
           (Conv.ORELSEC (Thm.BETA_CONV, Drule.ETA_CONV))) target
    val normalized = boolSyntax.rhs (concl normalization)
  in
    if aconv (concl theorem) target then theorem
    else if aconv (concl theorem) normalized then
      EQ_MP (SYM normalization) theorem
    else theorem
  end

fun public body theorems (goal as (_, target)) =
  let
    val (goals, validation) =
      process_clasimp_args body
        (clasetLib.the_claset ()) (clasimp_ss ()) theorems goal
  in
    (goals, restore_normalized_target target validation)
  end

fun AUTO_DEPTH_TAC bounds theorems =
  public (auto_with bounds) theorems

fun AUTO_TAC theorems =
  AUTO_DEPTH_TAC {blast = 4, depth = 2} theorems

fun FORCE_TAC theorems =
  public (force_with "FORCE_TAC") theorems

fun FASTFORCE_TAC theorems =
  public (search_with_simp "FASTFORCE_TAC" fast_search) theorems

fun SLOWSIMP_TAC theorems =
  public (search_with_simp "SLOWSIMP_TAC" slow_search) theorems

fun BESTSIMP_TAC theorems =
  public (search_with_simp "BESTSIMP_TAC" best_search) theorems

fun CLARSIMP_TAC theorems =
  public clarsimp_with theorems

(* A first-order step meets a goal the simplification before it left in
   the ambient normal form, and HOL4's normal forms are not the ones its
   library states lemmas in: a list equation normalises [x::l] to
   [[x] ++ l], and the ambient EVERY_MEM iff reads EVERY as membership.
   A fact stated the library's way then never meets such a goal, where
   Isabelle's metis reads its facts in the one normal form its simp
   leaves goals in.  Each fact enters in both spellings -- the same
   closing of a normal-form gap from HOL4's side that SUC_FILTER
   performs for the simpset -- so nothing METIS_TAC would have found is
   lost. *)
fun ambient_forms theorem =
  let
    val normalized = simpLib.SIMP_RULE (clasimp_ss ()) [] theorem
  in
    if aconv (concl normalized) (concl theorem) then [theorem]
    else [theorem, normalized]
  end
  handle Portable.Interrupt => raise Portable.Interrupt
       | HOL_ERR _ => [theorem]

fun AMBIENT_METIS_TAC theorems =
  metisLib.METIS_TAC (List.concat (map ambient_forms theorems))

end
