(* Extended traversal extracted additively from Traverse.
   The mixed legacy implementation remains until TASK_11. Shared Trace,
   Cond_rewr controls, Opening/Travrules types and exceptions are referenced,
   never copied. There is no reverse reducer/traversal adapter. *)
structure TraverseExt :> TraverseExt =
struct
open HolKernel Drule Conv Psyntax Abbrev liteLib Trace Travrules Opening;
infix THENQC THENCQC ORELSEC IFCQC
val ERR = mk_HOL_ERR "Traverse";
val equality = boolSyntax.equality;

  open Abbrev
  type context = exn
  type reducer_config_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int option,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  type reducer_context_data =
    {name : string option, initial : context,
     addcontext : context * thm list -> context,
     apply : {solver : term list -> term -> thm,
              conv : term list -> term -> thm, context : context,
              stack : term list, cond_depth : int,
              term_ord : term * term -> order,
              relation : term * (term -> thm)} -> conv}
  datatype reducer = LIFTED of Traverse.reducer
                   | CONTEXT_REDUCER of reducer_context_data
                   | CONFIG_REDUCER of reducer_config_data
  val lift = LIFTED
  fun reducer_config_data (CONFIG_REDUCER r) = r
    | reducer_config_data (LIFTED r) =
      let val {name,initial,addcontext,apply} = Traverse.dest_reducer r
      in
        {name=name, initial=initial, addcontext=addcontext,
         apply=fn {solver,conv,context,stack,relation,...} =>
           apply {solver=solver,conv=conv,context=context,stack=stack,
                  relation=relation}}
      end
    | reducer_config_data
        (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=case cond_depth of NONE => !Cond_rewr.stack_limit
                                           | SOME n => n}}
  fun reducer_data r =
    let val {name,initial,addcontext,apply} = reducer_config_data r
    in
      {name=name, initial=initial, addcontext=addcontext,
       apply=fn {solver,conv,context,stack,relation,cond_depth,term_ord} =>
         apply {solver=solver,conv=conv,context=context,stack=stack,
                relation=relation,term_ord=term_ord,
                cond_depth=SOME cond_depth}}
    end
  fun addctxt ths (LIFTED r) = LIFTED (Traverse.addctxt ths r)
    | addctxt ths (CONTEXT_REDUCER {name,initial,addcontext,apply}) =
      CONTEXT_REDUCER {name=name,initial=addcontext (initial,ths),
                       addcontext=addcontext,apply=apply}
    | addctxt ths (CONFIG_REDUCER {name,initial,addcontext,apply}) =
      CONFIG_REDUCER {name=name,initial=addcontext (initial,ths),
                      addcontext=addcontext,apply=apply}

type simp_prover_ctxt =
  {stack : term list, context_thms : thm list, recurse : term -> thm}
type ssolver =
  {name : string, solve : simp_prover_ctxt -> term -> thm}
type subgoaler = simp_prover_ctxt -> term -> thm

datatype trav_state =
  TSTATE of {relation_info : preorder,
             relation : term,
             contexts1 : context list,
             contexts2 : context list,
             context_thms : thm list,
             freevars : term list};

(* Project setup fields without constructing an unused apply adapter. *)
fun reducer_initial (LIFTED r) = #initial (Traverse.dest_reducer r)
  | reducer_initial (CONTEXT_REDUCER {initial,...}) = initial
  | reducer_initial (CONFIG_REDUCER {initial,...}) = initial

fun reducer_addcontext (LIFTED r) =
      #addcontext (Traverse.dest_reducer r)
  | reducer_addcontext (CONTEXT_REDUCER {addcontext,...}) = addcontext
  | reducer_addcontext (CONFIG_REDUCER {addcontext,...}) = addcontext

fun initial_context {rewriters:reducer list,
                     dprocs:reducer list,
                     travrules=TRAVRULES tsdata,
                     relation, limit} =
  TSTATE{contexts1=map reducer_initial rewriters,
         contexts2=map reducer_initial dprocs,
         context_thms=[],
         freevars=[],
         relation_info = find_relation relation (#relations tsdata),
         relation = relation};

(* ---------------------------------------------------------------------
 * add_context
 *
 * ---------------------------------------------------------------------*)

fun add_context collect_thms rewriters dprocs = let
  val rewrite_collectors' = map reducer_addcontext rewriters
  val dproc_collectors' = map reducer_addcontext dprocs
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
               context_thms=if collect_thms then thms @ context_thms
                            else context_thms,
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
fun add_solver_context collect_thms (context, thms) =
  if null thms then context
  else
    let
      val TSTATE {contexts1,contexts2,context_thms,freevars,
                  relation_info,relation} = context
      (* A term set: free_varsl's list union is quadratic in the context's
         free variables, and this runs on every application.  Renaming
         reads the list as a set. *)
      val more_freevars =
        HOLset.listItems (FVL (flatten (map hyp thms)) empty_tmset)
      val _ = map (fn thm => trace(2,MORE_CONTEXT thm)) thms
    in
      TSTATE
        {contexts1=contexts1, contexts2=contexts2,
         context_thms=if collect_thms then context_thms @ thms
                      else context_thms,
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

(* Only the configured prover pipeline can expose generic facts. *)
fun needs_prover_context
      ({subgoaler=NONE,solvers=[],...} : traverse_config) = false
  | needs_prover_context _ = true

type child_first_policy =
  {charge : unit -> unit, keep_abstraction : term -> bool}
datatype traversal_policy = ParentFirst | ChildFirst of child_first_policy

fun charge_only charge = {charge=charge, keep_abstraction=fn _ => false}

fun keep_abstraction (policy : child_first_policy) tm =
  #keep_abstraction policy tm

(* A function argument written as [\x. f x] names the same head as [f].
   Contracting it before visiting the body keeps that head available to a
   parent rewrite unless its application requires the abstraction. *)
fun eta_argument policy tm =
  if is_comb tm then
    if is_abs (rand tm) andalso
       not (boolSyntax.is_exists tm orelse
            boolSyntax.is_forall tm orelse boolSyntax.is_select tm)
       andalso not (keep_abstraction policy tm)
    then
      (RAND_CONV ETA_CONV ORELSEC RATOR_CONV (eta_argument policy)) tm
    else RATOR_CONV (eta_argument policy) tm
  else NO_CONV tm

fun NORMALIZE_ARGUMENTS (policy : child_first_policy) child tm =
  let
    (* TRY_CONV and eta fallback treat HOL_ERR as conversion failure, not
       as a policy abort. Keep policy failures across those combinators.
       This state belongs to one application, including reentrant calls. *)
    val aborted = ref (NONE : exn option)
    fun protected callback argument =
      case !aborted of
          SOME e => raise e
        | NONE => callback argument
            handle e => (aborted := SOME e; raise e)
    val policy = {charge=protected (#charge policy),
                  keep_abstraction=protected (#keep_abstraction policy)}
    fun check_abort () =
      case !aborted of NONE => () | SOME e => raise e
    fun guarded_child tm = (check_abort (); child tm)
    fun arguments tm =
      (check_abort ();
       if is_comb tm then
         Conv.THENC (RATOR_CONV arguments,
                     RAND_CONV (TRY_CONV guarded_child)) tm
       else if is_abs tm then ABS_CONV (TRY_CONV guarded_child) tm
       else REFL tm)
    fun normalize tm =
      let
        val _ = #charge policy ()
        val eta = QCONV (TRY_CONV (eta_argument policy)) tm
        val result = TRANS eta (QCONV arguments (rand (concl eta)))
        val next = rand (concl result)
      in
        if aconv tm next then result
        else TRANS result (normalize next)
      end
  in
    let val theorem = normalize tm
    in case !aborted of NONE => theorem | SOME e => raise e end
    handle e =>
      (case !aborted of NONE => raise e | SOME original => raise original)
  end

fun TRAVERSE_IN_CONTEXT check_external_abort
      eager_cong_schedule observer policy root_only
      (({limit,rewriters,dprocs,travrules,relation=rel} : traverse_data,
        config as {subgoaler,solvers,cond_depth,term_ord}
          : traverse_config))
      stack ctxt tm = let
  open Uref
  val TRAVRULES {relations,congprocs,weakenprocs,...} = travrules
  val add_context' =
    add_context (needs_prover_context config) rewriters dprocs
  val get_relation' = get_relation travrules
  val lim_r = Uref.new limit
  (* Conditional-rewrite wrappers can turn callback exceptions into
     HOL_ERR, and reducer dispatch can treat those as a failed attempt.
     Retain the original callback exception across the whole traversal. *)
  val aborted = ref (NONE : exn option)
  fun check_abort () =
    (check_external_abort ();
     case !aborted of NONE => () | SOME e => raise e)
  fun protected callback argument =
    case !aborted of
        SOME e => raise e
      | NONE => callback argument
          handle e => (aborted := SOME e; raise e)
  val policy =
    case policy of
        ParentFirst => ParentFirst
      | ChildFirst {charge,keep_abstraction} =>
          ChildFirst {charge=charge,
                      keep_abstraction=protected keep_abstraction}
  (* CONFIG_REDUCER transports NONE unchanged: native candidates read the
     live default themselves.  Older CONTEXT_REDUCER clients need an int. *)
  val term_ord = Option.getOpt (term_ord, Cond_rewr.ac_term_ord)
  fun check r = case !r of NONE => ()
    | SOME n => if n <= 0 then
                               (trace(2,TEXT "Limit exhausted");
                                raise ERR "TRAVERSE_IN_CONTEXT"
                                          "Limit exhausted")
                             else ()
  fun dec r = case !r of NONE => ()
    | SOME n => r := SOME (n - 1)
  fun observe tm =
    (check_abort ();
     case observer of
        NONE => ()
      | SOME visit =>
          (case !aborted of
               SOME e => raise e
             | NONE => visit tm
                 handle e => (aborted := SOME e; raise e)))
  fun charge tm =
    (check_abort ();
     case policy of
        ParentFirst => ()
      | ChildFirst {charge,...} =>
          (case !aborted of
               SOME e => raise e
             | NONE => (observe tm; charge ())
                 handle e => (aborted := SOME e; raise e)))
  (* Select a root entry only at the outside. Every recursive context
     uses the full loop, including side conditions of a root rewrite. *)
  fun trav_with_rel select_root rel_info stack context = let
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
    val reducer_relation = (relname, mkrefl)

    fun trav stack context = trav_entry false stack context
    and trav_entry select_root stack context = let
      val TSTATE {contexts1,contexts2,context_thms,freevars,...} = context
      fun trav_with_rel' new_relation stack context =
          if samerel relname new_relation then trav stack context
          else
            trav_with_rel false (get_relation' new_relation) stack context

      fun ctxt_solver stack tm = let
        val _ = observe tm
        val old = !lim_r
        fun raw_recurse tm = trav_with_rel' equality stack context tm
        (* The prover context and its closures are built only when a
           subgoaler or solver can actually read them; side-condition
           solving is hot enough that the unconfigured path should
           allocate nothing extra. *)
        fun pipeline tm = let
          fun recurse tm = let
            val _ = check_abort ()
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
                (check_abort (); solve prover_ctxt tm)
                handle HOL_ERR _ => first_solver rest tm
          val eq = case subgoaler of
                       NONE => recurse tm
                     | SOME subgoal =>
                         (check_abort (); subgoal prover_ctxt tm)
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
      (* Lifted ordinary callbacks receive exactly their original record. *)
      fun apply_reducer reducer context tm =
        (charge tm;
         (case reducer of
              LIFTED r =>
                #apply (Traverse.dest_reducer r) {solver=ctxt_solver, conv=ctxt_conv, context=context,
                       stack=stack, relation=reducer_relation} tm
            | CONTEXT_REDUCER {apply,...} =>
                apply {solver=ctxt_solver, conv=ctxt_conv, context=context,
                       stack=stack,
                       cond_depth=(case cond_depth of
                                       NONE => !Cond_rewr.stack_limit
                                     | SOME n => n),
                       term_ord=term_ord, relation=reducer_relation} tm
            | CONFIG_REDUCER {apply,...} =>
                apply {solver=ctxt_solver, conv=ctxt_conv, context=context,
                       stack=stack, cond_depth=cond_depth,
                       term_ord=term_ord, relation=reducer_relation} tm)
         before dec lim_r)
      fun high_priority tm =
          (check lim_r;
           FIRST_CONV (mapfilter2 apply_reducer rewriters contexts1) tm)
      fun low_priority tm =
          (check lim_r ;
           FIRST_CONV (mapfilter2 apply_reducer dprocs contexts2) tm)
      fun depther (thms,relation) =
          (check_abort ();
           trav_with_rel' relation stack (add_context' (context,thms)))
      val congproc_args =
          {solver=(fn tm => ctxt_solver stack tm), (* do not eta-convert! *)
           depther=depther,
           freevars=freevars}
      fun apply_congproc congproc =
        (check_abort (); congproc congproc_args)
      (* Preserve eager per-context factory construction only for the
         ordinary legacy entry point. Extended paths retain lazy attempts. *)
      val (descend,weaken) =
        if eager_cong_schedule then
          (FIRSTCQC_CONV (mapfilter apply_congproc congprocs'),
           FIRST_CONV (mapfilter apply_congproc weakenprocs'))
        else
          (fn tm =>
             (charge tm;
              FIRSTCQC_CONV (mapfilter apply_congproc congprocs') tm),
           fn tm =>
             (charge tm;
              FIRST_CONV (mapfilter apply_congproc weakenprocs') tm))

      fun loop tm = let
        val conv =
          case policy of
              ParentFirst =>
                REPEATQC high_priority THENQC
                (descend IFCQC
                  (fn change =>
                    ((if change then high_priority else NO_CONV) ORELSEC
                     low_priority ORELSEC weaken) THENCQC loop))
            | ChildFirst child_policy =>
                let
                  val after_children =
                    descend IFCQC
                      (fn _ =>
                        (high_priority ORELSEC low_priority ORELSEC weaken)
                        THENCQC loop)
                  fun preserve_head term =
                    (charge term; eta_argument child_policy term)
                in
                  if is_comb tm then
                    (preserve_head THENCQC loop) ORELSEC after_children
                  else after_children
                end
      in
        (check_abort (); trace(4,REDUCE ("Reducing",tm)); conv tm)
      end;
    in
      if select_root then high_priority ORELSEC low_priority else loop
    end
  in
    trav_entry select_root stack context
  end
  val entry = trav_with_rel root_only (get_relation' rel) stack ctxt
in
  let
    val theorem = entry tm
  in
    case !aborted of NONE => theorem | SOME e => raise e
  end
  handle e =>
    (case !aborted of NONE => raise e | SOME original => raise original)
end

(* ---------------------------------------------------------------------
 * TRAVERSE
 *
 * ---------------------------------------------------------------------*)
(* The explicit extended entry points refresh supplied reducer contexts
   for every application.  Legacy TRAVERSE retains its construction-time
   context, including mutable rewrite controls and user callback results. *)
fun GEN_TRAVERSE_WITH_CONTEXT check_abort observer policy root_only
      (xdata as (data,config) : xtraverse_data)
      {reducer_context,solver_context} tm =
   let
     val _ = check_abort ()
     val {dprocs,rewriters,...} = data
     val collect_thms = needs_prover_context config
     val context' =
       add_solver_context collect_thms
         (add_context collect_thms rewriters dprocs
            (initial_context data,reducer_context),
          solver_context)
   in
     TRAVERSE_IN_CONTEXT check_abort false observer policy root_only
       xdata [] context' tm
   end;

fun GEN_TRAVERSE policy root_only xdata thms =
  GEN_TRAVERSE_WITH_CONTEXT (fn () => ()) NONE policy root_only xdata
    {reducer_context=thms,solver_context=[]}

val XTRAVERSE = GEN_TRAVERSE ParentFirst false
val ROOT_REWRITE = GEN_TRAVERSE ParentFirst true
fun TRAVERSE_WITH_CONTEXT policy =
  GEN_TRAVERSE_WITH_CONTEXT (fn () => ()) NONE policy false
fun CHILD_FIRST_WITH_ABORT check_abort observer policy =
  GEN_TRAVERSE_WITH_CONTEXT check_abort observer (ChildFirst policy) false
fun CHILD_FIRST_WITH_OBSERVER observe policy =
  CHILD_FIRST_WITH_ABORT (fn () => ()) (SOME observe) policy
val ROOT_REWRITE_WITH_CONTEXT =
  GEN_TRAVERSE_WITH_CONTEXT (fn () => ()) NONE ParentFirst true


(* Unlike the explicit extended entries, default TRAVERSE collects once
   before returning a reusable conversion and constructs factories eagerly. *)
fun TRAVERSE (data as {rewriters,dprocs,...} : traverse_data) thms =
  let
    val context =
      add_context false rewriters dprocs (initial_context data,thms)
  in
    TRAVERSE_IN_CONTEXT (fn () => ()) true NONE ParentFirst false
      (data,default_config) [] context
  end

end
