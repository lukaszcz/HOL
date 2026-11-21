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
 let val (_,start) = Substring.position s1 ss
     val rest = Substring.triml (String.size s1) start
     val (numbers,_) = Substring.position s2 rest
     val (source,offset,length) = Substring.base numbers
     val limit = offset + length
     fun getc i =
         if i < limit then SOME (String.sub (source,i),i+1) else NONE
     val scan = Int.scan StringCvt.DEC getc
     fun skip_space i =
         if i < limit andalso Char.isSpace (String.sub (source,i)) then
           skip_space (i+1)
         else i
     (* Int.fromString accepts an integer prefix. Skip any remainder of
        that token before scanning the next integer. *)
     fun skip_suffix i =
         if i < limit andalso not (Char.isSpace (String.sub (source,i))) then
           skip_suffix (i+1)
         else i
     fun loop i acc =
         let val start = skip_space i in
           if start = limit then List.rev acc
           else
             let val (number,next) = valOf (scan start)
             in loop (skip_suffix next) (number :: acc) end
         end
 in loop offset [] end
 handle e => if dimacsTools.is_terminal e then raise e
             else failwith("parseSat");

fun isSuccess s = Process.isSuccess s

(*
** invokeSat solver t
** invokes solver on t and returns SOME s (where s is the satisfying instance
** as a string of integers) or NONE, if unsatisfiable
*)

(* Optional coarse benchmark observations of the actual secondary solver.
   Default NONE leaves the old command path literal. *)
type solver_statistics = {external_calls : int,internal_calls : int}
local
type solver_meter = {external_calls : int ref,internal_calls : int ref}
val solver_meter : solver_meter option ref = ref NONE
in
fun with_solver_statistics action =
  let
    val _ = case !solver_meter of NONE => () | SOME _ =>
      raise Feedback.mk_HOL_ERR "satTools" "with_solver_statistics"
        "observation reentry"
    val fields : solver_meter =
      {external_calls = ref 0,internal_calls = ref 0}
    val _ = solver_meter := SOME fields
    val result = Exn.capture action ()
    val _ = solver_meter := NONE
    val observed : solver_statistics =
      {external_calls = !(#external_calls fields),
       internal_calls = !(#internal_calls fields)}
  in (Exn.release result,observed) end
fun count_call field =
    case !solver_meter of NONE => ()
       | SOME fields => let val r = field fields in r := !r + 1 end
fun sat_sysl command =
    (count_call #external_calls; SatProcess.system command)
fun observed_internal_solver action =
    (count_call #internal_calls; action ())
end

fun invokeSat_result model sat_solver infile =
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
    SOME (model only_true (parseSat (start_string,end_string) sat_res_ss))
 end
handle e as Io _ => if dimacsTools.is_terminal e then raise e else NONE

fun invokeSat sat_solver tm vc nr svm sva infile =
  let
    fun model only_true numbers =
      let
        val all = if only_true then
                    numbers @ map (fn n => 0-n)
                      (subtract
                         (map snd (snd (dimacsTools.showSatVarMap svm)))
                         numbers)
                  else numbers
      in map (dimacsTools.intToLiteral sva) all end
  in invokeSat_result model sat_solver infile end

(* Keep parsing and variable-number validation for proof-only SAT answers.
   Missing variables for only_true solvers come from the valid DIMACS map;
   completing that assignment is only needed when returning a model. *)
fun invokeSat_status sat_solver sva infile =
  invokeSat_result
    (fn _ => List.app (fn n => ignore (dimacsTools.lookup_sat_num sva (abs n))))
    sat_solver infile

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
