(* Ordinary-only staged costs. Each operation escapes through a typed ref.
   Saved application includes reconstruction; checks run outside timers. *)
structure TacticInputs =
struct
open HolKernel Abbrev boolLib simpLib testutils Paired
val _ = new_theory "tactic_performance"
fun required true = () | required false = raise Fail "tactic benchmark"
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
val sizes = [0,8]
val operations = ["simp","asm","full","rev","no_strip_full",
  "no_strip_rev","global","global_req","conv","rule","asm_rule"]
val stages = ["construct","reuse","complete"]
val labels = List.concat (map (fn oper =>
  map (fn stage => oper ^ "_" ^ stage) stages) operations)
val constructs = ref 0
val applications = ref 0
val validations = ref 0
val p = mk_var ("perf_p",bool)
val target = mk_conj (p,T)
val rule = REWRITE_CONV [boolTheory.AND_CLAUSES] target
val cfg = {strip=false,elimvars=false,droptrues=false,oldestfirst=true}
datatype operation = Tac of tactic | Conversion of conv |
                     Rule of (thm -> thm)
type workload = {label:string, run:unit -> unit, verify:unit -> unit}
fun prove (asl,w) = let
  fun go t = case List.find (aconv t) asl of
      SOME a => ASSUME a
    | NONE => if aconv t T then TRUTH
              else if is_conj t then
                let val (a,b) = dest_conj t in CONJ (go a) (go b) end
              else if is_eq t andalso aconv (lhs t) (rhs t)
                   then REFL (lhs t)
              else raise Fail "unprovable residual"
in go w end
fun workloads n = let
  val extras = List.tabulate (n,fn i =>
    mk_var ("perf_extra" ^ Int.toString i,bool))
  val asl = p :: extras
  val goal : goal = (asl,target)
  val input = List.foldl (fn (t,th) => ADD_ASSUM t th)
                         (ASSUME target) extras
  (* 0: supplied rewrite; 8: same rewrite installed before construction.
     These are distinct scenarios, not an assumption-count scaling slope. *)
  val ss = if n = 0 then pureSimps.pure_ss
           else pureSimps.pure_ss ++ rewrites [rule]
  val args = if n = 0 then [rule] else []
  fun make oper = (constructs := !constructs + 1;
    case oper of
      "simp" => Tac (SIMP_TAC ss args)
    | "asm" => Tac (ASM_SIMP_TAC ss args)
    | "full" => Tac (FULL_SIMP_TAC ss args)
    | "rev" => Tac (REV_FULL_SIMP_TAC ss args)
    | "no_strip_full" => Tac (NO_STRIP_FULL_SIMP_TAC ss args)
    | "no_strip_rev" => Tac (NO_STRIP_REV_FULL_SIMP_TAC ss args)
    | "global" => Tac (global_simp_tac cfg ss args)
    | "global_req" => Tac (global_simp_tac cfg ss [ReqD rule])
    | "conv" => Conversion (SIMP_CONV ss args)
    | "rule" => Rule (SIMP_RULE ss args)
    | "asm_rule" => Rule (ASM_SIMP_RULE ss args)
    | _ => raise Fail "unknown operation")
  val saved = ref (NONE : thm option)
  val residual = ref ([] : goal list)
  fun apply oper = let
    val _ = applications := !applications + 1
    val th = case oper of
        Tac tac => let
          val (gs,vf) = runtac tac goal
          val proofs = map prove gs
          val _ = residual := gs
          val _ = validations := !validations + 1
        in vf proofs end
      | Conversion cv => let val th = cv target
          val _ = validations := !validations + 1 in th end
      | Rule f => let val th = f input
          val _ = validations := !validations + 1 in th end
  in saved := SOME th end
  fun verify oper = let
    val th = valOf (!saved)
    val expected = case oper of
        "conv" => rule
      | "rule" => EQ_MP rule input
      | "asm_rule" => ADD_ASSUM target
          (List.foldl (fn (t,th) => ADD_ASSUM t th) TRUTH extras)
      | "simp" => CONJ (ASSUME p) TRUTH
      | "asm" => CONJ (ASSUME p) TRUTH
      | "global" => CONJ (ASSUME p) TRUTH
      | "global_req" => CONJ (ASSUME p) TRUTH
      | _ => List.foldl (fn (t,th) => ADD_ASSUM t th)
                        (CONJ (ASSUME p) TRUTH) extras
    val _ = if same (th,expected) then () else
      raise Fail (oper ^ "." ^ Int.toString n ^ " actual: " ^
        thm_to_string th ^ " expected: " ^ thm_to_string expected)
    val _ = required (List.all (fn s => s = "DISK_THM")
                                  (#1 (Tag.dest_tag (tag th))))
    (* Ordered residual goals and complete hypotheses are checked, not just
       pretty endpoints. Non-SIMP tactics discharge using the assumption p. *)
    val _ = if oper = "simp" then
      required (case !residual of [(a,w)] =>
        ListPair.allEq (fn (x,y) => aconv x y) (a,asl) andalso
        aconv w p | _ => false)
      else if List.exists (fn x => x = oper) ["conv","rule","asm_rule"]
           then () else required (null (!residual))
  in () end
  fun workload oper stage = let
    val slot = ref (make oper)
    fun run () = case stage of
        "construct" => slot := make oper
      | "reuse" => apply (!slot)
      | "complete" => (slot := make oper; apply (!slot))
      | _ => raise Fail "unknown stage"
    fun check () =
      (if stage = "construct" then apply (!slot) else (); verify oper)
  in {label=oper ^ "_" ^ stage,run=run,verify=check}:workload end
in List.concat (map (fn oper => map (workload oper) stages) operations) end
end
