open HolKernel testutils
(* Explicit module prerequisites: these signatures and functor bodies must
   elaborate when the launcher runs, not merely produce .uo files. *)
val _ = Meta.load "Task08Clients"
val _ = Meta.load "Task08Cutovers"
val _ = Task08Reducers.lift
val _ = Task08Controls.prepare
fun check label ok = (tprint label; if ok then OK () else die label)
val checks = ref 0
fun pin label ok = (check label ok; checks := !checks + 1)
val _ = Theory.new_theory "task08_interfaces"
val _ = pin "prototype signatures and consumer functor elaborated" true

val collects = ref 0
val applies = ref 0
val payload = ref 17
exception Ctx of int ref
exception Foreign of int ref
val plain = Traverse.REDUCER
  {name=SOME "opaque", initial=Ctx payload,
   addcontext=fn (c,_) => (collects := !collects + 1; c),
   apply=fn {context,...} => fn tm =>
     (applies := !applies + 1;
      case context of Ctx p =>
        if p = payload then REFL tm else raise Foreign p
      | _ => raise Fail "recoded context")}
val lifted = Task08Reducers.lift plain
val data = Task08Reducers.reducer_config_data lifted
val _ = pin "lifting and projection invoke no callbacks"
  (!collects = 0 andalso !applies = 0)
val _ = pin "original exception-valued context retained"
  (case #initial data of Ctx p => p = payload | _ => false)
val relation = (boolSyntax.equality,REFL)
fun args context depth =
  {solver=fn _ => ASSUME,conv=fn _ => REFL,context=context,stack=[],
   cond_depth=depth,term_ord=Cond_rewr.ac_term_ord,relation=relation}
val _ = #apply data (args (#initial data) NONE) boolSyntax.T
val _ = Task08Reducers.addctxt [boolTheory.TRUTH] lifted
val _ = pin "lift preserves exact apply and collector counts"
  (!collects = 1 andalso !applies = 1)
val raised = Task08Reducers.lift (Traverse.REDUCER
  {name=NONE,initial=Ctx payload,addcontext=fn (c,_) => c,
   apply=fn _ => fn _ => raise Foreign payload})
val _ = pin "foreign callback exception identity and payload"
  ((#apply (Task08Reducers.reducer_config_data raised)
      (args (Ctx payload) NONE) boolSyntax.T; false)
   handle Foreign p => p = payload)
val seen = ref ([] : int option list)
val configured = Task08Reducers.CONFIG_REDUCER
  {name=NONE,initial=Ctx payload,addcontext=fn (c,_) => c,
   apply=fn {cond_depth,...} => fn tm =>
     (seen := cond_depth :: !seen; REFL tm)}
val _ = #apply (Task08Reducers.reducer_config_data configured)
  (args (Ctx payload) NONE) boolSyntax.T
val _ = #apply (Task08Reducers.reducer_config_data configured)
  (args (Ctx payload) (SOME 29)) boolSyntax.T
val _ = pin "configured depth retains NONE versus explicit value"
  (!seen = [SOME 29,NONE])
val depths = ref ([] : int list)
val contextual = Task08Reducers.CONTEXT_REDUCER
  {name=NONE,initial=Ctx payload,addcontext=fn (c,_) => c,
   apply=fn {cond_depth,...} => fn tm =>
     (depths := cond_depth :: !depths; REFL tm)}
val apply_context = #apply (Task08Reducers.reducer_config_data contextual)
val saved_depth = !Cond_rewr.stack_limit
val _ = Cond_rewr.stack_limit := 7
val _ = apply_context (args (Ctx payload) NONE) boolSyntax.T
val _ = Cond_rewr.stack_limit := 11
val _ = apply_context (args (Ctx payload) NONE) boolSyntax.T
val _ = apply_context (args (Ctx payload) (SOME 29)) boolSyntax.T
val _ = Cond_rewr.stack_limit := saved_depth
val _ = pin "integer-depth adapter samples live cell at each apply"
  (!depths = [29,11,7])

val rule = Drule.SPEC_ALL (CONJUNCT1 boolTheory.NOT_CLAUSES)
val tm = boolSyntax.lhs (concl rule)
fun solver _ _ = raise Fail "unexpected condition"
val cfg = {solver=solver,stack=[],cond_depth=NONE,
           term_ord=Cond_rewr.ac_term_ord}
fun legacy e = #legacy (Task08Controls.projections e) solver [] tm
fun extended e = #configured (Task08Controls.projections e) cfg tm
fun proves th = aconv (concl th) (concl rule) andalso null (hyp th)
fun exhausted f = (f (); false) handle Fail "exhausted" => true
val e = Task08Controls.prepare ("task08",rule) (SOME 2)
val _ = pin "real paired legacy runner validates proof" (proves (legacy e))
val late = Task08Controls.projections e
val _ = pin "late extraction does not refresh partial allowance"
  (Task08Controls.remaining e = SOME 1)
val _ = pin "late configured runner validates proof"
  (proves (#configured late cfg tm))
val _ = pin "late extraction after exhaustion stays exhausted"
  (exhausted (fn () => extended e) andalso
   exhausted (fn () => legacy e) andalso
   Task08Controls.remaining e = SOME 0)
val surviving = Task08Controls.filter_preserving (fn _ => true) [e,e]
val _ = pin "preserving filter keeps actual exhausted ref and aliases"
  (List.all (fn x => Task08Controls.same_control (e,x)) surviving andalso
   exhausted (fn () => extended (hd surviving)))
val reset = Task08Controls.reset_prepared surviving
val _ = pin "reset replay creates one fresh control per alias group"
  (Task08Controls.same_control (hd reset,List.nth (reset,1)) andalso
   not (Task08Controls.same_control (e,hd reset)) andalso
   Task08Controls.remaining (hd reset) = SOME 2 andalso
   Task08Controls.remaining e = SOME 0)
val _ = extended (hd reset)
val _ = legacy (List.nth (reset,1))
val _ = pin "both projection orders consume the same real control"
  (Task08Controls.remaining (hd reset) = SOME 0)
val _ = pin "private scope uses declared allowance without public handles"
  (Task08Controls.with_private_allowances [e,e]
     (fn () => proves (legacy e) andalso proves (extended e)) () andalso
   Task08Controls.remaining e = SOME 0)
fun restores label exn matches =
  pin label
    (((Task08Controls.with_private_allowances [e]
         (fn () => (ignore (legacy e); raise exn)) (); false)
      handle x => matches x) andalso Task08Controls.remaining e = SOME 0)
val _ = restores "private restoration on foreign exception"
  (Foreign payload) (fn Foreign p => p = payload | _ => false)
val _ = restores "private restoration on HOL_ERR"
  (mk_HOL_ERR "task08" "scope" "test")
  (fn Feedback.HOL_ERR _ => true | _ => false)
val _ = restores "private restoration on interrupt"
  Portable.Interrupt (fn Portable.Interrupt => true | _ => false)
val (_,tracked) = Cond_rewr.with_tracking
  (fn () => Task08Controls.with_private_allowances [e]
     (fn () => (ignore (legacy e); ignore (extended e))) ()) ()
val _ = pin "both real runners use one tracking extent" (length tracked = 2)
val (_,outer) = Cond_rewr.with_tracking
  (fn () => Task08Controls.with_private_allowances [e]
    (fn () =>
      let val _ = legacy e
          val (_,inner) = Cond_rewr.with_tracking extended e
          val _ = pin "nested tracking reports only inner extent"
            (length inner = 1)
      in () end) ()) ()
val _ = pin "nested tracking restores outer extent" (length outer = 1)

(* Each negative body must fail statically, not through an applied stub. *)
val negatives =
  ["reducer-to-legacy", "reducer-from-legacy", "set-to-legacy",
   "set-from-legacy", "fragment-to-legacy", "fragment-from-legacy",
   "congset-to-legacy", "provider-from-legacy"]
val negative_dir =
  case OS.Process.getEnv "TASK08_NEGATIVE_DIR" of
      NONE => "negative" | SOME path => path
fun rejected name =
  let
    val file = OS.Path.concat (negative_dir,name ^ ".ML")
    val rejected = (PolyML.use file; false)
      handle Fail msg =>
        if String.isSubstring "Static Errors" msg then true
        else raise Fail ("nonstatic failure: " ^ msg)
  in pin ("static rejection: " ^ name) rejected end
val _ = List.app rejected negatives
val _ = List.app (fn (file,dir) =>
  if String.isPrefix "Task08" file then
    print ("TASK08_LOADED " ^ OS.Path.concat (dir,file) ^ "\n")
  else ()) (Binarymap.listItems (Meta.fileDirMap ()))
val _ = print ("TASK08_COMPLETE checks=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success
