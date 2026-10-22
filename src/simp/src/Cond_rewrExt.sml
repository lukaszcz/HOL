(* Explicit paired compilation. Public mutable controls and exception
   identities belong to the existing shared modules, never copies here. *)
structure Cond_rewrExt :> Cond_rewrExt =
struct
open HolKernel boolLib liteLib Trace

(* Preserve the observable diagnostic origin of the conditional engine. *)
fun WRAP_ERR x = STRUCT_WRAP "Cond_rewr" x
fun ERR x = STRUCT_ERR "Cond_rewr" x
val is_var_perm = Cond_rewr.is_var_perm

type config =
  {solver : term list -> term -> thm, stack : term list,
   cond_depth : int option, term_ord : term * term -> order}
type runners =
  {legacy : (term list -> term -> thm) -> term list -> conv,
   configured : config -> conv}

   (* Prepare once; both runners use the same theorem and matcher.  The
      caller retains the actual bound reference and supplies its status. *)
   fun COND_REWR_CONVS (nm,th) bounded =
      let val eqn = snd (strip_imp (concl th))
          val isperm = Cond_rewr.is_var_perm (dest_eq eqn)
          val instth = HO_PART_MATCH (lhs o snd o strip_imp) th
                       handle HOL_ERR _ => ERR("COND_REWR_CONV",
                         "bad theorem argument (not a conditional equation)")
          val legacy =
      fn solver => fn stack => fn tm =>
       (let val conditional_eqn = instth tm
            val (conditions,eqn) = strip_imp (concl conditional_eqn)
            val _ = if exists (C (op_mem aconv) stack) conditions
                        then (trace(1, TEXT "looping - cut");
                              failwith "looping!") else ()
            val _ = if length stack + length conditions > (!Cond_rewr.stack_limit)
                    then (trace(1, TEXT "looping - stack limit reached");
                          failwith "stack limit") else ()
            val (l,r) = dest_eq eqn
            val _ =
              if Term.aconv l r then
                (trace(4, IGNORE ("Rewrite loops", conditional_eqn));
                 failwith "looping rewrite")
              else ()

            val _ = if isperm andalso Cond_rewr.ac_term_ord(l, r) <> GREATER andalso
                       not bounded
                    then
                      (trace(4, IGNORE("possibly looping",conditional_eqn));
                       failwith "permutative rewr: not applied")
                    else ()
            val _ = if null conditions then ()
                    else trace(if isperm then 2 else 1, REWRITING(nm,tm,th))
            val new_stack = conditions@stack
            fun solver' condition =
                 let val _   = trace(2,SIDECOND_ATTEMPT condition)
                     val res = solver new_stack condition
                      handle e as HOL_ERR _
                       =>  (trace(1,SIDECOND_NOT_SOLVED condition); raise e)
                 in trace(2,SIDECOND_SOLVED res);
                    res
                 end
            val condition_thms = map solver' conditions
            val disch_eqn = rev_itlist (C MP) condition_thms conditional_eqn
            val final_thm = if aconv l tm then disch_eqn
                            else TRANS (ALPHA tm l) disch_eqn
            val _ = if null conditions then
              trace(if isperm then 2 else 1, REWRITING(nm,tm,th))
                    else ()
            (* note_rewrite is a no-op unless someone is tracking *)
            val _ = if null stack then SimpTracking.note_rewrite th else ()
        in trace(if isperm then 3 else 2,PRODUCE(tm,nm,final_thm));
            final_thm
        end
        handle e => WRAP_ERR("COND_REWR_CONV (application)",e))
          val configured =
      fn {solver,stack,cond_depth,term_ord} => fn tm =>
       (let val conditional_eqn = instth tm
            val (conditions,eqn) = strip_imp (concl conditional_eqn)
            val _ = if exists (C (op_mem aconv) stack) conditions
                        then (trace(1, TEXT "looping - cut");
                              failwith "looping!") else ()
            val depth = case cond_depth of
                            NONE => !Cond_rewr.stack_limit
                          | SOME n => n
            val _ = if length stack + length conditions > depth
                    then (trace(1, TEXT "looping - stack limit reached");
                          failwith "stack limit") else ()
            val (l,r) = dest_eq eqn
            val _ =
              if Term.aconv l r then
                (trace(4, IGNORE ("Rewrite loops", conditional_eqn));
                 failwith "looping rewrite")
              else ()

            val _ = if isperm andalso term_ord (l, r) <> GREATER andalso
                       not bounded
                    then
                      (trace(4, IGNORE("possibly looping",conditional_eqn));
                       failwith "permutative rewr: not applied")
                    else ()
            val _ = if null conditions then ()
                    else trace(if isperm then 2 else 1, REWRITING(nm,tm,th))
            val new_stack = conditions@stack
            fun solver' condition =
                 let val _   = trace(2,SIDECOND_ATTEMPT condition)
                     val res = solver new_stack condition
                      handle e as HOL_ERR _
                       =>  (trace(1,SIDECOND_NOT_SOLVED condition); raise e)
                 in trace(2,SIDECOND_SOLVED res);
                    res
                 end
            val condition_thms = map solver' conditions
            val disch_eqn = rev_itlist (C MP) condition_thms conditional_eqn
            val final_thm = if aconv l tm then disch_eqn
                            else TRANS (ALPHA tm l) disch_eqn
            val _ = if null conditions then
              trace(if isperm then 2 else 1, REWRITING(nm,tm,th))
                    else ()
            (* note_rewrite is a no-op unless someone is tracking *)
            val _ = if null stack then SimpTracking.note_rewrite th else ()
        in trace(if isperm then 3 else 2,PRODUCE(tm,nm,final_thm));
            final_thm
        end
        handle e => WRAP_ERR("COND_REWR_CONV (application)",e))
      in
        {legacy=legacy, configured=configured}
      end
      handle e  => WRAP_ERR("COND_REWR_CONV (construction) ",e);

   fun COND_REWR_CONV_WITH_CONFIG nmth bounded =
      #configured (COND_REWR_CONVS nmth bounded);

   fun COND_REWR_CONV_WITH_CONTEXT nmth bounded =
      let val conv = COND_REWR_CONV_WITH_CONFIG nmth bounded
      in
        fn {solver,stack,cond_depth,term_ord} =>
           conv {solver=solver, stack=stack, cond_depth=SOME cond_depth,
                 term_ord=term_ord}
      end;

(* Binding happens at tracked construction, not at projection. No shadow
   allowance: aliases/conjuncts may deliberately supply the same reference.
   As in the baseline bound wrapper, failures do not spend an allowance. *)
datatype prepared = Prepared of
  {shape : runners, bounded : bool, bound : runners}
fun is_bounded BoundedRewrites.UNBOUNDED = false
  | is_bounded (BoundedRewrites.BOUNDED _) = true
fun bind (shape : runners) control =
  case control of
      BoundedRewrites.UNBOUNDED => shape
    | BoundedRewrites.BOUNDED r =>
        {legacy = fn solver => fn stack => fn tm =>
           if !r = 0 then failwith "exceeded rewrite bound"
           else #legacy shape solver stack tm before Portable.dec r,
         configured = fn ctxt => fn tm =>
           if !r = 0 then failwith "exceeded rewrite bound"
           else #configured shape ctxt tm before Portable.dec r}
fun prepare nmth control =
  let
    val bounded = is_bounded control
    val shape = COND_REWR_CONVS nmth bounded
  in Prepared {shape=shape,bounded=bounded,bound=bind shape control} end

(* Replay can bind a new actual control to an already prepared matcher.
   Bounded status affects permutation checking inside that matcher, so it
   cannot be changed by rebinding. No preparation or tracing happens here. *)
fun rebind (Prepared {shape,bounded,...}) control =
  if bounded = is_bounded control then
    Prepared {shape=shape,bounded=bounded,bound=bind shape control}
  else raise ERR ("rebind","cannot change prepared bounded status")
fun runners (Prepared {bound,...}) = bound
end
