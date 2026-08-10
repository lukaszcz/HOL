(* =====================================================================
 * FILE          : traverse.sml
 * DESCRIPTION   : A programmable term traversal engine
 *
 * AUTHOR        : Donald Syme
 *                 Based loosely on original HOL rewriting by
 *                 Larry Paulson et al.
 * ===================================================================== *)

(* =====================================================================
 * The Traversal/Reduction Engine.  Its pretty simple really
 *   - start with an intial context
 *   - collect context that arises from congruence rules
 *   - apply reducers where possible, "rewriters" at high priority and
 *     "dprocs" at low.
 * =====================================================================*)


structure Traverse :> Traverse =
struct

open HolKernel Drule Conv Psyntax Abbrev liteLib Trace Travrules Opening;

infix THENQC THENCQC ORELSEC IFCQC

val ERR   = mk_HOL_ERR "Traverse" ;

val equality = boolSyntax.equality;

(* ---------------------------------------------------------------------
 * reducers and contexts
 * ---------------------------------------------------------------------*)

type context = exn   (* well known SML hack to allow any kind of data *)

datatype reducer =
  REDUCER of {name : string option,
              initial: context,
              addcontext : context * Thm.thm list -> context,
              apply: {solver:term list -> term -> thm,
                      conv: term list -> term -> thm,
                      context: context,
                      stack: term list,
                      relation : term * (term -> thm)} -> conv}
  | CONTEXT_REDUCER of
             {name : string option,
              initial: context,
              addcontext : context * Thm.thm list -> context,
              apply: {solver:term list -> term -> thm,
                      conv: term list -> term -> thm,
                      context: context,
                      stack: term list,
                      cond_depth: int,
                      term_ord: term * term -> order,
                      relation : term * (term -> thm)} -> conv
              };
fun dest_reducer (REDUCER x) = x
  | dest_reducer
      (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation} =>
         apply {solver=solver, conv=conv, context=context, stack=stack,
                cond_depth= !Cond_rewr.stack_limit,
                term_ord=Cond_rewr.ac_term_ord, relation=relation}}

fun reducer_data (REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,cond_depth,term_ord,relation} =>
         apply {solver=solver, conv=conv, context=context, stack=stack,
                relation=relation}}
  | reducer_data (CONTEXT_REDUCER x) = x

fun addctxt ths (REDUCER {name,initial,addcontext,apply}) =
    REDUCER{name = name, initial = addcontext(initial,ths), apply = apply,
            addcontext = addcontext}
  | addctxt ths (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
    CONTEXT_REDUCER
      {name=name, initial=addcontext (initial,ths), apply=apply,
       addcontext=addcontext}

type simp_prover_ctxt =
  {stack : term list, context_thms : thm list, recurse : term -> thm}
type ssolver =
  {name : string, solve : simp_prover_ctxt -> term -> thm}
type subgoaler = simp_prover_ctxt -> term -> thm


(* ---------------------------------------------------------------------
 * Traversal states
 *    - stores the state of the reducers during the simpl. process
 * ---------------------------------------------------------------------*)

datatype trav_state =
  TSTATE of {relation_info : preorder,
             relation : term,
             contexts1 : context list,
             contexts2 : context list,
             context_thms : thm list,
             freevars : term list};

fun initial_context {rewriters:reducer list,
                     dprocs:reducer list,
                     travrules=TRAVRULES tsdata,
                     relation, limit} =
  TSTATE{contexts1=map (#initial o reducer_data) rewriters,
         contexts2=map (#initial o reducer_data) dprocs,
         context_thms=[],
         freevars=[],
         relation_info = find_relation relation (#relations tsdata),
         relation = relation};

(* ---------------------------------------------------------------------
 * add_context
 *
 * ---------------------------------------------------------------------*)

fun add_context rewriters dprocs = let
  val rewrite_collectors' = map (#addcontext o reducer_data) rewriters
  val dproc_collectors' = map (#addcontext o reducer_data) dprocs
  fun doit (context, thms) = let
    val TSTATE {contexts1,contexts2,context_thms,freevars,
                relation_info,relation} = context
  in
    if null thms then context
    else let
        val more_freevars = free_varsl (flatten (map hyp thms))
        val _ = map (fn thm => trace(2,MORE_CONTEXT thm)) thms
        fun mk_privcontext maker privcontext = maker (privcontext,thms)
        val newcontexts1 =
          if null thms then contexts1
          else map2 mk_privcontext rewrite_collectors' contexts1
        val newcontexts2 =
          if null thms then contexts2
          else map2 mk_privcontext dproc_collectors' contexts2
        val newfreevars =
          if null more_freevars then freevars
          else more_freevars@freevars
      in
        TSTATE{contexts1=newcontexts1,
               contexts2=newcontexts2,
               context_thms=thms @ context_thms,
               freevars=newfreevars,
               relation=relation, relation_info = relation_info}
      end
  end
in
  doit
end

(* Add facts to the generic prover and binder-capture contexts without also
   reinstalling them in every reducer.  Hypothesis free variables force
   capture-avoiding renaming when traversal descends under a binder. *)
fun add_solver_context (context, thms) =
  if null thms then context
  else
    let
      val TSTATE {contexts1,contexts2,context_thms,freevars,
                  relation_info,relation} = context
      val more_freevars = free_varsl (flatten (map hyp thms))
      val _ = map (fn thm => trace(2,MORE_CONTEXT thm)) thms
    in
      TSTATE
        {contexts1=contexts1, contexts2=contexts2,
         context_thms=context_thms @ thms,
         freevars=freevars @ more_freevars,
         relation=relation, relation_info=relation_info}
    end


(* ---------------------------------------------------------------------
 * get_relation
 *
 * ---------------------------------------------------------------------*)

fun get_relation (TRAVRULES{relations,...}) rel =
    let val PREORDER(_,TRANS,refl) = find_relation rel relations
    in PREORDER (rel,TRANS,refl) end

(* ---------------------------------------------------------------------
 * Quick, General conversion routines.  These work for any preorder,
 * not just equality.
 * ---------------------------------------------------------------------*)

fun GEN_THENQC (PREORDER(_,TRANS,_)) (conv1,conv2) tm =
  let val th1 = conv1 tm
  in TRANS th1 (conv2 (rand (concl th1)))
     handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 tm

fun GEN_THENCQC  (PREORDER(_,TRANS,_)) (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2(rand(concl th1))
     in TRANS th1 th2
     end
     handle HOL_ERR _ => th1
  end;;

(* perform continuation with argumnt indicating whether a change occurred *)
fun GEN_IFCQC  (PREORDER(_,TRANS,_)) (conv1,conv2) tm =
  let val th1 = conv1 tm
  in let val th2 = conv2 true (rand(concl th1))
     in TRANS th1 th2
     end
     handle HOL_ERR _ => th1
  end
  handle HOL_ERR _ => conv2 false tm;;


fun GEN_REPEATQC rel =
   let val op THENCQC = GEN_THENCQC rel
       fun REPEATQC conv tm =
           (conv THENCQC (REPEATQC conv)) tm
   in REPEATQC
   end;

(* This code is used just once, to do the right thing with the
   application of congruence rules: if a congruence succeeds by not
   changing anything, then don't go onto try other congruences.  Doing
   so will ultimately lead to the standard equality congruences being
   used, and this traversal of the term will result in basically all
   of the succeeding congruence's work being done again.  If the
   sub-terms include further matches for the first congruence (as in p
   ==> q ==> r, say), then you'll get an explosion of work being
   duplicated.

   Note that the exception being caught is exactly that generated by
   Opening.CONGPROC, so there's a tight link between there and here.
   Don't change one without changing the other! *)

fun FIRSTCQC_CONV [] t = failwith "no conversion worked"
  | FIRSTCQC_CONV (c::cs) t = let
    in
      c t
      handle UNCHANGED => failwith "unchanged" (* Need to raise a HOL_ERR *)
           | HOL_ERR _ => FIRSTCQC_CONV cs t
    end

(* And another thing.  The current simplifer doesn't allow users to
   get their hands on the possibility of flipping to relations other
   than equality.  This means that weakenprocs below are always [].
   If this was to change, then the code probably should still use
   FIRST_CONV, and not FIRSTCQC_CONV above because weakening
   congruences should probably all get a bite at the cherry. *)

fun mapfilter2 f (h1::t1) (h2::t2) =
      let val X = mapfilter2 f t1 t2
      in f h1 h2::X handle Interrupt => raise Interrupt | _ => X
      end
  | mapfilter2 f _ _ = [];

(* ---------------------------------------------------------------------
 * TRAVERSE_IN_CONTEXT
 *
 * NOTES
 *   - Rewriters/Dprocs should always fail if unchanged (but not with
 *     UNCHANGED).
 *   - Congruence rule procs should only fail if they do not match.
 *     They can fail with UNCHANGED if nothing changes.
 *   - The depther should only fail with UNCHANGED.
 * ---------------------------------------------------------------------*)


type traverse_data = {limit : int option,
                      rewriters: reducer list,
                      dprocs: reducer list,
                      travrules: Travrules.travrules,
                      relation: term};

type traverse_config = {subgoaler: subgoaler option,
                        solvers: ssolver list,
                        cond_depth: int option,
                        term_ord: (term * term -> order) option};

type xtraverse_data = traverse_data * traverse_config

val default_config : traverse_config =
  {subgoaler=NONE, solvers=[], cond_depth=NONE, term_ord=NONE};

fun TRAVERSE_IN_CONTEXT root_only
      (({limit,rewriters,dprocs,travrules,relation=rel} : traverse_data,
        {subgoaler,solvers,cond_depth,term_ord} : traverse_config))
      stack ctxt tm = let
  open Uref
  val TRAVRULES {relations,congprocs,weakenprocs,...} = travrules
  val add_context' = add_context rewriters dprocs
  val get_relation' = get_relation travrules
  val lim_r = Uref.new limit
  (* An unconfigured depth follows the user-level default, and is read
     afresh at every reducer application as it was when the depth was
     read inside Cond_rewr.COND_REWR_CONV itself. *)
  fun current_cond_depth () =
      Option.getOpt (cond_depth, !Cond_rewr.stack_limit)
  val term_ord = Option.getOpt (term_ord, Cond_rewr.ac_term_ord)
  fun check r = case !r of NONE => ()
    | SOME n => if n <= 0 then
                               (trace(2,TEXT "Limit exhausted");
                                raise ERR "TRAVERSE_IN_CONTEXT"
                                          "Limit exhausted")
                             else ()
  fun dec r = case !r of NONE => ()
    | SOME n => r := SOME (n - 1)
  (* [trav_with_rel] yields both entry conversions for a context: [root]
     reduces at the root only, [loop] traverses the whole term.  Only the
     caller below picks between them; every recursive call continues with
     [loop], so root-only-ness never propagates inwards. *)
  fun trav_with_rel rel_info stack context  = let
    val PREORDER(relname , _, _) = rel_info
    fun apply_relation f = f relname
    val congprocs' = mapfilter apply_relation congprocs
    val weakenprocs' = mapfilter apply_relation weakenprocs
    val op IFCQC = GEN_IFCQC rel_info
    val op THENCQC = GEN_THENCQC rel_info
    val op THENQC = GEN_THENQC rel_info
    val REPEATQC = GEN_REPEATQC rel_info
    fun mkrefl t = let
        val PREORDER(_, _, irefl) = rel_info
    in
        irefl {Rinst = relname, arg = t}
    end

    fun trav stack context =
        let val {loop, root = _} = trav_convs stack context in loop end
    and trav_convs stack context = let
      val TSTATE {contexts1,contexts2,context_thms,freevars,...} = context
      fun trav_with_rel' new_relation stack context =
          if samerel relname new_relation then trav stack context
          else
            let val {loop, root = _} =
                    trav_with_rel (get_relation' new_relation) stack context
            in loop end

      fun ctxt_solver stack tm = let
        val old = !lim_r
        fun raw_recurse tm = trav_with_rel' equality stack context tm
        (* The prover context and its closures are built only when a
           subgoaler or solver can actually read them; side-condition
           solving is hot enough that the unconfigured path should
           allocate nothing extra. *)
        fun pipeline tm = let
          fun recurse tm = let
            val recurse_old = !lim_r
          in
            raw_recurse tm
            handle HOL_ERR _ => (lim_r := recurse_old; REFL tm)
          end
          val prover_ctxt =
            {stack=stack, context_thms=context_thms, recurse=recurse}
          fun first_solver [] _ =
                raise ERR "ctxt_solver" "Unsolved condition"
            | first_solver ({solve,...}::rest) tm =
                solve prover_ctxt tm
                handle HOL_ERR _ => first_solver rest tm
          val eq = case subgoaler of
                       NONE => recurse tm
                     | SOME subgoal => subgoal prover_ctxt tm
          val tm' = rand (concl eq)
        in
          if aconv tm' boolSyntax.T then EQT_ELIM eq
          else EQ_MP (SYM eq) (first_solver solvers tm')
        end
      in
        (case (subgoaler,solvers) of
             (NONE,[]) => EQT_ELIM (raw_recurse tm)
           | _ => pipeline tm)
        handle e as HOL_ERR _ => (lim_r := old; raise e)
      end
      fun ctxt_conv stack tm = let
        val old = !lim_r
      in
        trav_with_rel' equality stack context tm
        handle e as HOL_ERR _ => (lim_r := old ; raise e)
      end
      fun apply_reducer reducer context tm =
        let val rdata = reducer_data reducer
        in
          (#apply rdata) {solver=ctxt_solver,
                          conv=ctxt_conv,
                          context=context,
                          stack=stack,
                          cond_depth=current_cond_depth (),
                          term_ord=term_ord,
                          relation=(relname, mkrefl)}
                         tm before
          dec lim_r
        end
      fun high_priority tm =
          (check lim_r;
           FIRST_CONV (mapfilter2 apply_reducer rewriters contexts1) tm)
      fun low_priority tm =
          (check lim_r ;
           FIRST_CONV (mapfilter2 apply_reducer dprocs contexts2) tm)
      fun depther (thms,relation) =
          trav_with_rel' relation stack (add_context' (context,thms))
      val congproc_args =
          {solver=(fn tm => ctxt_solver stack tm), (* do not eta-convert! *)
           depther=depther,
           freevars=freevars}
      fun apply_congproc congproc = congproc congproc_args
      val descend = FIRSTCQC_CONV (mapfilter apply_congproc congprocs')
      val weaken = FIRST_CONV (mapfilter apply_congproc weakenprocs')

      fun loop tm = let
        val conv =
            REPEATQC high_priority THENQC
            (descend IFCQC
                (fn change =>
                  ((if change then high_priority else NO_CONV) ORELSEC
                   low_priority ORELSEC weaken) THENCQC loop))
               (* THENCQC above causes the loop to happen only if
                  the stuff before it hasn't raised an exception *)
      in
        (trace(4,REDUCE ("Reducing",tm)); conv tm)
      end;
    in
      {root = high_priority ORELSEC low_priority, loop = loop}
    end
  in
    trav_convs stack context
  end
  val {root,loop} = trav_with_rel (get_relation' rel) stack ctxt
in
  (if root_only then root else loop) tm
end

(* ---------------------------------------------------------------------
 * TRAVERSE
 *
 * ---------------------------------------------------------------------*)
(* Reducer contexts contain mutable rewrite controls, so rebuild the context
   for every application of a reusable conversion. *)
fun GEN_TRAVERSE_WITH_CONTEXT root_only (xdata as (data,_) : xtraverse_data)
      {reducer_context,solver_context} tm =
   let
     val {dprocs,rewriters,...} = data
     val context' =
       add_solver_context
         (add_context rewriters dprocs
            (initial_context data,reducer_context),
          solver_context)
   in
     TRAVERSE_IN_CONTEXT root_only xdata [] context' tm
   end;

fun GEN_TRAVERSE root_only xdata thms =
  GEN_TRAVERSE_WITH_CONTEXT root_only xdata
    {reducer_context=thms,solver_context=[]}

val XTRAVERSE = GEN_TRAVERSE false
val ROOT_REWRITE = GEN_TRAVERSE true
val TRAVERSE_WITH_CONTEXT = GEN_TRAVERSE_WITH_CONTEXT false
val ROOT_REWRITE_WITH_CONTEXT = GEN_TRAVERSE_WITH_CONTEXT true

(* The unextended entry point runs at the unconfigured settings. *)
fun TRAVERSE (data : traverse_data) = XTRAVERSE (data, default_config)

end (* struct *)
