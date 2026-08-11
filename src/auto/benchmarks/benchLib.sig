signature benchLib =
sig
  include Abbrev

  type provenance = {file : string, line : int, commit : string}

  datatype tactic_id =
      Simp
    | Auto
    | Blast
    | Force
    | Fastforce
    | Safe
    | Clarify
    | Clarsimp
    | Aesop
    | Linarith
    | IntArith
    | Cooper
    | NumRing
    | IntRing
    | RealRing
    | RealField

  type exclusion = {name : string, theorem : thm}

  type corpus_goal = {
    id : string,
    goal : term,
    source_method : string,
    mapped : tactic_id,
    excl : exclusion list,
    provenance : provenance,
    representative : bool
  }

  datatype outcome = SOLVED of Time.time | TIMEOUT | FAILED of string

  datatype cause =
      AcceptedGap
    | EngineLimitation
    | TranslationGap
    | UnderIteration

  type shortfall = {
    id : string,
    cause : cause,
    date : string,
    note : string
  }

  type family_result = {
    gated : (string * outcome) list,
    battery : (string * tactic_id * outcome) list
  }

  val default_budget : Time.time
  val selftest_level : unit -> int
  val tactic_name : tactic_id -> string
  val cause_name : cause -> string
  val outcome_solved : outcome -> bool

  val theorem_is_goal : term -> thm -> bool

  val exclusions_effective :
    clasetLib.claset -> corpus_goal -> bool

  val run_goal : Time.time -> tactic_id -> corpus_goal -> outcome

  val assert_accounting : {
    family : string,
    goals : corpus_goal list,
    shortfalls : shortfall list,
    gated : (string * outcome) list
  } -> unit

  val run_family : {
    family : string,
    goals : corpus_goal list,
    shortfalls : shortfall list,
    budget : Time.time,
    battery : tactic_id list,
    level : int
  } -> family_result
end
