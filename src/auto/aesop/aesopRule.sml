structure aesopRule :> aesopRule =
struct

open Abbrev HolKernel

datatype rphase =
    RNorm of int
  | RSafe
  | RUnsafe of int

datatype rapply =
    EngineStep of clasetStep.step
  | RenderedTactic of NTactical.ntactic
  | MultiStep of clasetStep.step list

type rule =
  {name : string, phase : rphase, apply : rapply, once : bool}

type safe_scaffold =
  {closers : rule list,
   safe0_claset : rule list,
   safe_forward : rule list,
   safep_claset : rule list,
   conclusion_splits : rule list,
   assumption_splits : rule list}

type ruleset =
  {norm : rule list, safe : safe_scaffold, unsafe : rule list}

val ERR = mk_HOL_ERR "aesopRule"
val default_percent = 50

fun checked_percent function_name percent =
  if 1 <= percent andalso percent <= 100 then percent
  else
    raise ERR function_name
      "an unsafe rule percentage must be in the range 1--100"

fun phase_of_spec ({kind, safe, prio} : clasetRules.rulespec) =
  if kind = clasetRules.Norm then
    RNorm (Option.getOpt (prio, 0))
  else if safe then
    RSafe
  else
    RUnsafe
      (checked_percent "phase_of_spec"
        (Option.getOpt (prio, default_percent)))

fun apply_rule {name, phase, theorem, mode} : rule =
  {name = name, phase = phase,
   apply =
     EngineStep
       (clasetStep.rule_step
         {theorem = theorem, elim = false, mode = mode}),
   once = false}

fun constructors_rule_with phase function_name
      {name, theorems, mode} : rule =
  if null theorems then
    raise ERR function_name "a constructors rule needs at least one theorem"
  else
    {name = name, phase = phase,
     apply =
       MultiStep
         (map
           (fn theorem =>
             clasetStep.rule_step
               {theorem = theorem, elim = false, mode = mode})
           theorems),
     once = false}

(* Lean's datatype constructors builder has no direct HOL analogue because
   HOL goals are propositions.  Here constructors means the introduction
   rules of an inductive relation. *)
fun constructors_rule {name, theorems, percent, mode} =
  constructors_rule_with
    (RUnsafe
      (checked_percent "constructors_rule"
        (Option.getOpt (percent, default_percent))))
    "constructors_rule"
    {name = name, theorems = theorems, mode = mode}

fun safe_constructors_rule {name, theorems, mode} =
  constructors_rule_with RSafe "safe_constructors_rule"
    {name = name, theorems = theorems, mode = mode}

fun simp_rule_with {name, simpset, controls} : rule =
  {name = name, phase = RNorm 0,
   apply =
     RenderedTactic
       (NTactical.LIFT
         (clasimpLib.safe_asm_full_simp simpset controls)),
   once = false}

fun simp_rule arguments =
  let
    val {simp_rules, simp_controls, ...} =
      clasetLib.classify_simp_args arguments
    val invocation_ss =
      simpLib.++
        (aesopData.aesop_ss (), simpLib.rewrites simp_rules)
  in
    simp_rule_with
      {name = "simp", simpset = invocation_ss,
       controls = simp_controls}
  end

fun closers () : rule list =
  [{name = "assumption", phase = RSafe,
    apply = EngineStep clasetStep.blast_assumption_step,
    once = false},
   {name = "contradiction", phase = RSafe,
    apply = EngineStep clasetStep.blast_contradiction_step,
    once = false}]

fun safe_rules
      ({closers, safe0_claset, safe_forward, safep_claset,
        conclusion_splits, assumption_splits} : safe_scaffold) =
  closers @ safe0_claset @ safe_forward @ safep_claset @
  conclusion_splits @ assumption_splits

fun same_name
      ((_, (left, _)) :
        clasetRules.rulespec * (string * thm))
      ((_, (right, _)) :
        clasetRules.rulespec * (string * thm)) =
  left = right

fun unique_declarations declarations =
  let
    fun add (declaration, kept) =
      if List.exists (same_name declaration) kept then kept
      else kept @ [declaration]
  in
    List.foldl add [] declarations
  end

fun candidate_declarations claset conclusion assumptions qvars =
  let
    val target =
      clasetLib.aesop_target_candidates claset
        {q = conclusion, qvars = qvars}
    fun hypothesis assumption =
      clasetLib.aesop_hyp_candidates claset
        {q = assumption, qvars = qvars}
  in
    unique_declarations
      (target @ List.concat (map hypothesis assumptions))
  end

fun ordinary_kind clasetRules.Intro = true
  | ordinary_kind clasetRules.Elim = true
  | ordinary_kind clasetRules.Dest = true
  | ordinary_kind _ = false

fun canonical_source spec theorem =
  #1 (#rl (clasetRules.ext_info spec theorem))

fun declaration_rule mode
      (spec, (name, theorem)) : rule =
  let
    val kind = #kind spec
    val source = canonical_source spec theorem
  in
    {name = name, phase = phase_of_spec spec,
     apply =
       EngineStep
         (clasetStep.rule_step
           {theorem = source, elim = kind <> clasetRules.Intro,
            mode = mode}),
     once = false}
  end

fun safe_class wanted (spec, (_, theorem)) =
  #safe spec andalso
  ordinary_kind (#kind spec) andalso
  clasetRules.safe_class_of spec (clasetRules.ext_info spec theorem) =
    SOME wanted

fun unsafe_declaration (spec, _) =
  ordinary_kind (#kind spec) andalso not (#safe spec)

fun unsafe_percent (spec, _) =
  case phase_of_spec spec of
      RUnsafe percent => percent
    | _ => raise ERR "unsafe_percent" "a safe rule reached unsafe ordering"

fun order_unsafe declarations =
  let
    val positioned = Lib.enumerate 0 declarations
    fun compare ((left_index, left), (right_index, right)) =
      case Int.compare
             (unsafe_percent right, unsafe_percent left) of
          EQUAL => Int.compare (left_index, right_index)
        | order => order
  in
    map #2 (Listsort.sort compare positioned)
  end

fun claset_rules
      {claset, mode, conclusion, assumptions, qvars, simp_args} =
  let
    val candidates =
      candidate_declarations claset conclusion assumptions qvars
    val safe0 =
      map (declaration_rule mode)
        (List.filter (safe_class clasetRules.Safe0) candidates)
    val safep =
      map (declaration_rule mode)
        (List.filter (safe_class clasetRules.SafeP) candidates)
    val unsafe =
      map (declaration_rule mode)
        (order_unsafe (List.filter unsafe_declaration candidates))
    val safe =
      {closers = closers (),
       safe0_claset = safe0,
       safe_forward = [],
       safep_claset = safep,
       conclusion_splits = [],
       assumption_splits = []}
  in
    {norm = [simp_rule simp_args], safe = safe, unsafe = unsafe}
  end

end
