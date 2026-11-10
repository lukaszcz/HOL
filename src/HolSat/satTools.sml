structure satTools = struct

local

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback
open SatSolvers satCommonTools satTheory

in

infix |->;

(*
** Use Binaryset to encode mapping between HOL variable names
** and DIMACS  variable numbers as a set of string*int pairs.
*)

(* Functions for parsing the output of SAT solvers *)

(*
** substringContains s ss
** tests whether substring ss contains string s
*)

fun substringContains s ss =
    not(Substring.isEmpty(snd(Substring.position s ss)));

(*
** parseSat (s1,s2) ss
** returns a list of numbers corresponding to the tokenised
** substring of ss (tokenised wrt Char.isSpace) that starts immediately
** after the first occurrence of s1 and ends just before the first
** occurrence of s2 that is after the first occurrence of s1
*)

fun parseSat (s1,s2) ss =
 let val (ss1,ss2) = Substring.position s1 ss
     val ss3       = Substring.triml (String.size s1) ss2
     val (ss4,ss5) = Substring.position s2 ss3
     val ssl       = Substring.tokens Char.isSpace ss4
 in
  List.map (valOf o Int.fromString o Substring.string) ssl
 end
 handle e => if dimacsTools.is_terminal e then raise e
             else failwith("parseSat");

fun isSuccess s = Process.isSuccess s

(*
** invokeSat solver t
** invokes solver on t and returns SOME s (where s is the satisfying instance
** as a string of integers) or NONE, if unsatisfiable
*)

(* Optional coarse benchmark observations of the actual secondary solver.
   Default NONE creates no timers and leaves the old command path literal. *)
type solver_statistics =
  {external_calls : int,internal_calls : int,
   external_wall : Time.time,external_child_user : Time.time,
   external_child_system : Time.time,internal_wall : Time.time,
   internal_user : Time.time,internal_system : Time.time}
local
type solver_meter =
  {external_calls : int ref,internal_calls : int ref,
   external_wall : Time.time ref,external_child_user : Time.time ref,
   external_child_system : Time.time ref,internal_wall : Time.time ref,
   internal_user : Time.time ref,internal_system : Time.time ref}
val solver_meter : solver_meter option ref = ref NONE
fun add_solver_time cell elapsed = cell := Time.+ (!cell,elapsed)
in
fun with_solver_statistics action =
  let
    val _ = case !solver_meter of NONE => () | SOME _ =>
      raise Feedback.mk_HOL_ERR "satTools" "with_solver_statistics"
        "observation reentry"
    val fields : solver_meter =
      {external_calls = ref 0,internal_calls = ref 0,
       external_wall = ref Time.zeroTime,
       external_child_user = ref Time.zeroTime,
       external_child_system = ref Time.zeroTime,
       internal_wall = ref Time.zeroTime,internal_user = ref Time.zeroTime,
       internal_system = ref Time.zeroTime}
    val _ = solver_meter := SOME fields
    val result = Exn.capture action ()
    val _ = solver_meter := NONE
    val observed : solver_statistics =
      {external_calls = !(#external_calls fields),
       internal_calls = !(#internal_calls fields),
       external_wall = !(#external_wall fields),
       external_child_user = !(#external_child_user fields),
       external_child_system = !(#external_child_system fields),
       internal_wall = !(#internal_wall fields),
       internal_user = !(#internal_user fields),
       internal_system = !(#internal_system fields)}
  in (Exn.release result,observed) end
fun sat_sysl command = case !solver_meter of
    NONE => SatProcess.system command
  | SOME fields =>
      let
        val _ = #external_calls fields := !(#external_calls fields) + 1
        val wall = Timer.startRealTimer ()
        val child_times_before = Posix.ProcEnv.times ()
        val result = Exn.capture SatProcess.system command
        val measured = Exn.capture (fn () =>
          let val after = Posix.ProcEnv.times ()
          in add_solver_time (#external_wall fields)
                (Timer.checkRealTimer wall);
             add_solver_time (#external_child_user fields)
                (Time.- (#cutime after,#cutime child_times_before));
             add_solver_time (#external_child_system fields)
                (Time.- (#cstime after,#cstime child_times_before)) end) ()
      in case result of Exn.Exn _ => Exn.release result
         | Exn.Res value => (Exn.release measured;value) end
fun observed_internal_solver action = case !solver_meter of
    NONE => action ()
  | SOME fields =>
      let
        val _ = #internal_calls fields := !(#internal_calls fields) + 1
        val wall = Timer.startRealTimer ()
        val cpu = Timer.startCPUTimer ()
        val result = Exn.capture action ()
        val measured = Exn.capture (fn () =>
          let val {nongc,gc} = Timer.checkCPUTimes cpu
          in add_solver_time (#internal_wall fields)
                (Timer.checkRealTimer wall);
             add_solver_time (#internal_user fields)
                (Time.+ (#usr nongc,#usr gc));
             add_solver_time (#internal_system fields)
                (Time.+ (#sys nongc,#sys gc)) end) ()
      in case result of Exn.Exn _ => Exn.release result
         | Exn.Res value => (Exn.release measured;value) end

end

fun invokeSat sat_solver tm vc nr svm sva infile =
 let
   val (name,executable,notime_run,only_true,failure_string,start_string,
        end_string) =
       (getSolverName sat_solver,getSolverExe sat_solver,
        getSolverRun sat_solver, getSolverTrue sat_solver,
        getSolverFail sat_solver, getSolverStart sat_solver,
        getSolverEnd sat_solver)
   val outfile    = infile ^ "." ^ name
   val run_cmd    = notime_run executable (infile,outfile)
   val code       = sat_sysl run_cmd
   val _          = if isSuccess code orelse
                       (name="minisat" orelse name="minisatp")
                    then () (* minisat returns non-std exit code on success *)
                    else print("Warning:\n Process.system reports failure \
                               \signal returned by\n " ^ run_cmd ^ "\n")
   val ins        = TextIO.openIn outfile
   val sat_res_ss = Substring.full
     (dimacsTools.with_cleanup (fn () => TextIO.closeIn ins)
        TextIO.inputAll ins)
   val result     = substringContains failure_string sat_res_ss
 in
  if result
   then NONE
   else
    let val model1 = parseSat (start_string,end_string) sat_res_ss
        val model2 = if only_true then
                       model1 @
                       (map (fn n => 0-n)
                            (subtract
                               (map snd (snd(dimacsTools.showSatVarMap svm)))
                               model1))
                     else model1
    in let val model3 = SOME(map (dimacsTools.intToLiteral sva) model2)
        in model3 end
    end
 end
handle e as Io _ => if dimacsTools.is_terminal e then raise e else NONE

(*
** satCheck [l1,...,ln] t
** attempts to prove (l1 /\ ... /\ ln) ==> t
** if it succeeds then the theorem is returned, else
** exception satCheckError is raised
*)

exception satCheckError;
fun satCheck model t =
   let
      val mtm  = list_mk_conj model (*  (l1 /\ ... /\ ln) *)
      val th1  = ASSUME mtm (* l1 /\ ... /\ ln |- l1 /\ ... /\ ln *)
      val thl  = map
                  (fn th => if is_neg(concl th)
                             then MP (SPEC (dest_neg(concl th))EQF_Imp1) th
                             else MP (SPEC(concl th)EQT_Imp1) th)
                  (CONJUNCTS th1) (* [ l1 /\ ... /\ ln |- l1 = T, ... ] *)
      val subl = map (fn th => lhs(concl th) |-> th) thl
                 (*[l1 |-> l1 /\ ... /\ ln |- l1 = T,...]*)
      val th2 = SUBST_CONV subl t t (* l1 /\ ... /\ ln |- t = t[l1/T,...] *)
      val th3 = CONV_RULE (RHS_CONV computeLib.EVAL_CONV) th2
                (* l1 /\ ... /\ ln |- t = T *)
      val th4 = EQT_ELIM th3 (* l1 /\ ... /\ ln |- t *)
   in
      DISCH mtm th4 (* |- l1 /\ ... /\ ln ==> t *)
   end
   handle Interrupt => raise Interrupt
        | HOL_ERR herr =>
            if top_function_of herr = "EQT_ELIM" andalso is_neg t then
                 (UNDISCH (EQF_ELIM (REWRITE_CONV [] t))
                  handle HOL_ERR _ => raise satCheckError)
            else raise satCheckError
        | otherwise => if dimacsTools.is_terminal otherwise
                       then raise otherwise else raise satCheckError;

end
end
