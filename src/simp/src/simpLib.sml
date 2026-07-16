(*===========================================================================*)
(* FILE          : simpLib.sml                                               *)
(* DESCRIPTION   : A programmable, contextual, conditional simplifier        *)
(*                                                                           *)
(* AUTHOR        : Donald Syme                                               *)
(*                 Based loosely on original HOL rewriting by                *)
(*                 Larry Paulson et al,                                      *)
(*                 and not-so-loosely on the Isabelle simplifier.            *)
(*===========================================================================*)

structure simpLib :> simpLib =
struct

infix oo;

open HolKernel boolLib liteLib Trace Cond_rewr Travrules Traverse Ho_Net

structure Set = Binaryset

type thname = KernelSig.kernelname

local open markerTheory in end;

fun ERR x      = STRUCT_ERR "simpLib" x ;
fun WRAP_ERR x = STRUCT_WRAP "simpLib" x;

fun option_cases f e (SOME x) = f x
  | option_cases f e NONE = e;

fun f oo g = fn x => flatten (map f (g x));

(*---------------------------------------------------------------------------*)
(* Representation of conversions manipulated by the simplifier.              *)
(*---------------------------------------------------------------------------*)


type convdata = {name  : string,
                 key   : (term list * term) option,
                 trace : int,
                 conv  : (term list -> term -> thm) -> term list -> conv};
type tagged_convdata = {thypart : string option, cd : convdata}
fun opttheory NONE s = s | opttheory (SOME thy) s = thy ^ "." ^ s

type stdconvdata = { name: string,
                     pats: term list,
                     conv: conv}

(*---------------------------------------------------------------------------*)
(* Make a rewrite rule into a conversion.                                    *)
(*---------------------------------------------------------------------------*)

(* boolean argument to c is whether or not the rewrite is bounded *)
fun appconv (c,UNBOUNDED) = c false (* do not eta expand! *)
  | appconv (c,BOUNDED r) =
    let
      val c = c true (* do not inline! *)
    in
      (fn solver => fn stk => fn tm =>
      if !r = 0 then failwith "exceeded rewrite bound"
      else c solver stk tm before
      Portable.dec r)
    end

fun split_name {Thy,Name} = (SOME Thy, Name)
fun mk_rewr_convdata (nmopt,(thm,tag)) : tagged_convdata option = let
  val th = SPEC_ALL thm
  val (thypart,nm) =
      case Option.map split_name nmopt of
          NONE => (NONE, "rewrite:<anonymous>")
        | SOME (thypart,b) => (thypart, "rewrite:"^b)
in
  SOME {thypart = thypart,
        cd = {name  = nm,
              key   = SOME (free_varsl (hyp th),
                            lhs (#2 (strip_imp (concl th)))),
              trace = 100, (* no need to provide extra tracing here;
                              COND_REWR_CONV provides enough tracing itself *)
              conv  = appconv (COND_REWR_CONV (nm,th), tag)}
       } before
  trace(2, LZ_TEXT(fn () => "New rewrite: " ^ thm_to_string th))
  handle HOL_ERR _ =>
         (trace (2, LZ_TEXT(fn () =>
                               thm_to_string th ^
                               " dropped (conversion to rewrite failed)"));
          NONE)
end

(*---------------------------------------------------------------------------*)
(* Composable simpset fragments                                              *)
(*---------------------------------------------------------------------------*)

type relsimpdata = {refl: thm, trans:thm, weakenings:thm list,
                    subsets : thm list, rewrs : thm list}

type conv_info =
  {name : string,
   conval : (term list -> term -> thm) -> term list -> conv}
type net_conv_info = {thypart : string option, ci : conv_info}
type net = net_conv_info Ho_Net.net
type weakener_data =
  Travrules.preorder list * thm list * Traverse.reducer

datatype ssfrag = SSFRAG_CON of {
    name           : string option,
    convs          : tagged_convdata list,
    rewrs          : (thname option * thm) list,
    ac             : (thm * thm) list,
    filter         : (controlled_thm -> controlled_thm list) option,
    dprocs         : Traverse.reducer list,
    congs          : thm list,
    relsimps       : relsimpdata list,
    loopers        : (string * (simpset -> tactic)) list,
    unsafe_solvers : Traverse.ssolver list,
    safe_solvers   : Traverse.ssolver list,
    congprocs      : {name : string, relation : term,
                      proc : Opening.congproc} list
}
and history_item = ADDFRAG of ssfrag
                 | DELETE_EVENT of string list
                 | ADDWEAKENER of weakener_data
                 | STRATEGY_EVENT of strategy_event
                 | SET_MK_REWRS of
                     (controlled_thm -> controlled_thm list)
and strategy_event =
    ADD_LOOPER_EVENT of string * (simpset -> tactic)
  | DEL_LOOPER_EVENT of string
  | SET_LOOPER_EVENT of string * (simpset -> tactic)
  | ADD_UNSAFE_SOLVER_EVENT of Traverse.ssolver
  | ADD_SAFE_SOLVER_EVENT of Traverse.ssolver
  | SET_UNSAFE_SOLVERS_EVENT of Traverse.ssolver list
  | SET_SAFE_SOLVERS_EVENT of Traverse.ssolver list
  | REMOVE_SOLVER_EVENT of string
  | SET_SUBGOALER_EVENT of Traverse.subgoaler option
  | SET_COND_DEPTH_EVENT of int option
  | SET_TERM_ORD_EVENT of (term * term -> order) option
  | SET_EXCL_LOOPERS_EVENT of string Binaryset.set
and simpset = SS of {
    mk_rewrs       : controlled_thm -> controlled_thm list,
    history        : history_item list,
    initial_net    : net,
    dprocs         : reducer list,
    travrules      : travrules,
    limit          : int option,
    excluded       : string Binaryset.set,
    loopers        : (string * (simpset -> tactic)) list,
    unsafe_solvers : Traverse.ssolver list,
    safe_solvers   : Traverse.ssolver list,
    subgoaler      : Traverse.subgoaler option,
    cond_depth     : int option,
    term_ord       : (term * term -> order) option,
    excl_loopers   : string Binaryset.set
}

fun frag_name (SSFRAG_CON {name,...}) = name

fun normCong cong_th = PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] cong_th

fun SSFRAG {name,convs,rewrs,ac,filter,dprocs,congs} =
  SSFRAG_CON
    {name = name, rewrs = rewrs, ac = ac,
     convs = map (fn c => {thypart=NONE, cd = c}) convs,
     filter = filter, dprocs = dprocs, congs = map normCong congs,
     relsimps = [], loopers = [], unsafe_solvers = [], safe_solvers = [],
     congprocs = []}

val empty_ssfrag = SSFRAG{name = NONE, rewrs = [], convs = [], ac = [],
                          filter = NONE, dprocs = [], congs = []}
fun ssf_upd_rewrs f (SSFRAG_CON s) =
    let
      val {name,rewrs,convs,ac,filter,dprocs,congs,relsimps,loopers,
           unsafe_solvers,safe_solvers,congprocs} = s
    in
      SSFRAG_CON
        {name = name, rewrs = f rewrs, convs = convs, ac = ac,
         filter = filter, dprocs = dprocs, congs = congs,
         relsimps = relsimps, loopers = loopers,
         unsafe_solvers = unsafe_solvers, safe_solvers = safe_solvers,
         congprocs = congprocs}
    end

(* ----------------------------------------------------------------------
    maintain a global database of (named) ssfrags
   ---------------------------------------------------------------------- *)

val ssfragDB = Sref.new (Symtab.empty : ssfrag Symtab.table)
fun register_frag ssf =
    case frag_name ssf of
        NONE => raise ERR ("register_frag", "Can only register named ssfrags")
      | SOME n =>
        (case Symtab.lookup (Sref.value ssfragDB) n of
             NONE => (Sref.update ssfragDB (Symtab.update(n,ssf)); ssf)
           | SOME _ => (HOL_WARNING "simpLib" "register_frag"
                                    ("Discarding existing entry for "^n);
                        Sref.update ssfragDB $ Symtab.update(n,ssf);
                        ssf))
fun lookup_named_frag n = Symtab.lookup (Sref.value ssfragDB) n
fun all_named_frags() = Symtab.keys (Sref.value ssfragDB)

(*---------------------------------------------------------------------------*)
(* Operation on ssfrag values                                                *)
(*---------------------------------------------------------------------------*)

fun name_ss s (SSFRAG_CON f) =
  SSFRAG_CON
    {name=SOME s, convs= #convs f, rewrs= #rewrs f, filter= #filter f,
     ac= #ac f, dprocs= #dprocs f, congs= #congs f,
     relsimps= #relsimps f, loopers= #loopers f,
     unsafe_solvers= #unsafe_solvers f, safe_solvers= #safe_solvers f,
     congprocs= #congprocs f};

fun base_ssfrag {rewrs,convs,ac,dprocs,relsimps,loopers,unsafe_solvers,
                 safe_solvers,congprocs} =
  SSFRAG_CON
    {name=NONE, rewrs=rewrs, convs=convs, ac=ac, filter=NONE,
     dprocs=dprocs, congs=[], relsimps=relsimps, loopers=loopers,
     unsafe_solvers=unsafe_solvers, safe_solvers=safe_solvers,
     congprocs=congprocs}

fun rewrites rewrs =
  base_ssfrag
    {rewrs=map (fn th => (NONE,th)) rewrs, convs=[], ac=[], dprocs=[],
     relsimps=[], loopers=[], unsafe_solvers=[], safe_solvers=[],
     congprocs=[]}

fun rewrites_with_names rewrs =
  base_ssfrag
    {rewrs=map (apfst SOME) rewrs, convs=[], ac=[], dprocs=[],
     relsimps=[], loopers=[], unsafe_solvers=[], safe_solvers=[],
     congprocs=[]}

fun dproc_ss dproc =
  base_ssfrag
    {rewrs=[], convs=[], ac=[], dprocs=[dproc], relsimps=[], loopers=[],
     unsafe_solvers=[], safe_solvers=[], congprocs=[]}

fun ac_ss aclist =
  base_ssfrag
    {rewrs=[], convs=[], ac=aclist, dprocs=[], relsimps=[], loopers=[],
     unsafe_solvers=[], safe_solvers=[], congprocs=[]}

fun conv_ss conv =
  base_ssfrag
    {rewrs=[], convs=[{thypart=NONE,cd=conv}], ac=[], dprocs=[],
     relsimps=[], loopers=[], unsafe_solvers=[], safe_solvers=[],
     congprocs=[]}

fun relsimp_ss rsdata =
  base_ssfrag
    {rewrs=[], convs=[], ac=[], dprocs=[], relsimps=[rsdata], loopers=[],
     unsafe_solvers=[], safe_solvers=[], congprocs=[]}

fun looper_ss looper =
  base_ssfrag
    {rewrs=[], convs=[], ac=[], dprocs=[], relsimps=[], loopers=[looper],
     unsafe_solvers=[], safe_solvers=[], congprocs=[]}

fun solver_ss solver =
  base_ssfrag
    {rewrs=[], convs=[], ac=[], dprocs=[], relsimps=[], loopers=[],
     unsafe_solvers=[solver], safe_solvers=[], congprocs=[]}

fun safe_solver_ss solver =
  base_ssfrag
    {rewrs=[], convs=[], ac=[], dprocs=[], relsimps=[], loopers=[],
     unsafe_solvers=[], safe_solvers=[solver], congprocs=[]}

fun congproc_ss congproc =
  base_ssfrag
    {rewrs=[], convs=[], ac=[], dprocs=[], relsimps=[], loopers=[],
     unsafe_solvers=[], safe_solvers=[], congprocs=[congproc]}

fun D (SSFRAG_CON s) = s;
fun frag_rewrites ssf = map #2 (#rewrs (D ssf))

fun add_named_rwt nth ssfrag = ssf_upd_rewrs (cons (apfst SOME nth)) ssfrag

fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

(*---------------------------------------------------------------------------*)
(* Possibly need to suppress duplicates in the merge?                        *)
(*---------------------------------------------------------------------------*)

fun merge_ss (s:ssfrag list) =
  SSFRAG_CON
    { name     = merge_names (map (#name o D) s),
      convs    = flatten (map (#convs o D) s),
      rewrs    = flatten (map (#rewrs o D) s),
      filter   = SOME (end_foldr (op oo) (mapfilter (the o #filter o D) s))
                 handle HOL_ERR _ => NONE,
      ac       = flatten (map (#ac o D) s),
      dprocs   = flatten (map (#dprocs o D) s),
      congs    = flatten (map (#congs o D) s),
      relsimps = flatten (map (#relsimps o D) s),
      loopers  = flatten (map (#loopers o D) s),
      unsafe_solvers = flatten (map (#unsafe_solvers o D) s),
      safe_solvers = flatten (map (#safe_solvers o D) s),
      congprocs = flatten (map (#congprocs o D) s)
    }

fun named_rewrites name = (name_ss name) o rewrites;
fun named_rewrites_with_names name = (name_ss name) o rewrites_with_names;
fun named_merge_ss name = (name_ss name) o merge_ss;

fun std_conv_ss {name,conv,pats} =
  let
    fun cnv k = conv_ss {conv = K (K conv), trace = 2, name = name, key = k}
  in
    if null pats then
      cnv NONE
    else
      merge_ss (map (fn p => cnv (SOME([],p))) pats)
  end

fun ssfrag_name (SSFRAG_CON s) = #name s

fun partition_ssfrags names ssdata =
     List.partition
       (fn SSFRAG_CON s =>
          case #name s
          of SOME name => Lib.mem name names
           | NONE => false) ssdata

(*---------------------------------------------------------------------------*)
(* Simpsets and basic operations on them. Simpsets contain enough            *)
(* information to spark off term traversal quickly and efficiently. In       *)
(* theory the net need not be stored (and the code would look neater if it   *)
(* wasn't), but in practice it has to be.                                    *)
(* --------------------------------------------------------------------------*)

(* Names in [excluded] are forbidden from being added by [++].
   [exclude_ssfrags] sets them and [force_add] clears them per name. *)

val empty_excluded : string Binaryset.set = Binaryset.empty String.compare

fun ssupd_net f (SS s) =
  SS{mk_rewrs= #mk_rewrs s, history= #history s,
     initial_net=f (#initial_net s), dprocs= #dprocs s,
     travrules= #travrules s, limit= #limit s, excluded= #excluded s,
     loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
     safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
     cond_depth= #cond_depth s, term_ord= #term_ord s,
     excl_loopers= #excl_loopers s}

val empty_ss =
  SS{mk_rewrs=fn x => [x], history=[], limit=NONE, initial_net=empty,
     dprocs=[], travrules=EQ_tr, excluded=empty_excluded, loopers=[],
     unsafe_solvers=[], safe_solvers=[], subgoaler=NONE, cond_depth=NONE,
     term_ord=NONE, excl_loopers=empty_excluded}

 fun ssfrags_of (SS x) =
     List.mapPartial (fn ADDFRAG sf => SOME sf | _ => NONE) (#history x)

fun optprint NONE = "NONE"
  | optprint (SOME s) = "SOME "^s
fun name_match ({thypart,ci}:net_conv_info) (* thing in simpset's net *) pats =
    let (* true will lead to removal *)
      val ssnm = #name ci
      fun check1 (patthyopt, patbase) =
          let
            val checknamepart =
                patbase = ssnm orelse
                "rewrite:" ^ patbase = ssnm orelse
                String.isPrefix ("rewrite:" ^ patbase ^ ".") ssnm
            val checkthypart =
                case patthyopt of NONE => true | _ => patthyopt = thypart
          in
            checkthypart andalso checknamepart
          end
    in
      List.exists check1 pats
    end

fun filter_net_by_names nms net =
    let
      fun munge_pat p =
          case String.fields (equal #".") p of
              [_] => (NONE, p)
            | [s1,s2] =>
                if CharVector.all Char.isDigit s2 then (NONE, p)
                else if mem s1 (ancestry "-") then (SOME s1, s2)
                else raise ERR ("-*", "bad theory name: "^s1)
            | [s1,s2,s3] => (SOME s1, s2 ^ "." ^ s3)
            | _ => raise ERR ("-*", "User key has too many dots")
      val munged_pats = map munge_pat nms
    in
      Ho_Net.vfilter (fn nd => not (name_match nd munged_pats)) net
    end

fun dphas_name_from nms (REDUCER {name = SOME n,...}) = Lib.mem n nms
  | dphas_name_from _ _ = false
fun filter_dprocs_by_names nms = List.filter (not o dphas_name_from nms)

fun (ss as SS s) -* nms =
    if null nms then ss
    else
      SS{initial_net=filter_net_by_names nms (#initial_net s),
         history=DELETE_EVENT nms :: #history s,
         mk_rewrs= #mk_rewrs s,
         dprocs=filter_dprocs_by_names nms (#dprocs s),
         travrules= #travrules s, limit= #limit s, excluded= #excluded s,
         loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
         safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
         cond_depth= #cond_depth s, term_ord= #term_ord s,
         excl_loopers= #excl_loopers s}
fun remove_simps nms ss = ss -* nms


  (* ---------------------------------------------------------------------
   * USER_CONV wraps a bit of tracing around a user conversion.
   *
   * net_add_convs (internal function) adds conversions to the
   * initial context net.
   * ---------------------------------------------------------------------*)

 fun USER_CONV {name,key,trace=trace_level,conv} =
  let val trace_string1 = "trying "^name^" on"
      val trace_string2 = name^" ineffectual"
      val trace_string3 = name^" left term unchanged"
      val trace_string4 = name^" raised an unusual exception (ignored)"
  in fn solver => fn stack => fn tm =>
      let val _ = trace(trace_level+2,REDUCE(trace_string1,tm))
          val thm = conv solver stack tm
      in
        trace(trace_level,PRODUCE(tm,name,thm));
        thm
      end
      handle e as HOL_ERR _ =>
             (trace (trace_level+2,TEXT trace_string2); raise e)
           | e as Conv.UNCHANGED =>
             (trace (trace_level+2,TEXT trace_string3); raise e)
           | e => (trace (trace_level, TEXT trace_string4); raise e)
  end;

 val any = mk_var("x",Type.alpha);

 fun net_add_conv {thypart,cd = data as {name,key,trace,conv}:convdata} =
     enter (option_cases #1 [] key,
            option_cases #2 any key,
            {thypart = thypart, ci = {name = name, conval = USER_CONV data}})

(* itlist is like foldr, so that theorems get added to the context starting
   from the end of the list *)
 fun net_add_convs net convs = itlist net_add_conv convs net;


 fun mk_ac p A =
   let val (a,b,c) = Drule.MK_AC_LCOMM p
       val opn = a |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #1
       val nm = let val {Name,Thy,...} = dest_thy_const opn
                in
                  SOME {Thy = Thy, Name = "AC " ^ Name}
                end handle HOL_ERR _ => NONE
   in (nm, (a, UNBOUNDED))::(nm, (b, UNBOUNDED))::(nm, (c, UNBOUNDED))::A
   end handle HOL_ERR _ => A;

 fun ac_rewrites aclist = Lib.itlist mk_ac aclist [];

 fun same_frag (SSFRAG_CON{name=SOME n1, ...})
               (SSFRAG_CON{name=SOME n2, ...}) = n1=n2
   | same_frag other wise = false;

 fun ssfrag_names_of ss =
       ss |> ssfrags_of
          |> List.mapPartial ssfrag_name
          |> Lib.mk_set

 fun fupdlimit f (SS s) =
   SS{mk_rewrs= #mk_rewrs s, history= #history s,
      travrules= #travrules s, initial_net= #initial_net s,
      dprocs= #dprocs s, limit=f (#limit s), excluded= #excluded s,
      loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
      safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
      cond_depth= #cond_depth s, term_ord= #term_ord s,
      excl_loopers= #excl_loopers s}

 fun limit n = fupdlimit (fn _ => SOME n)

val unlimit = fupdlimit (fn _ => NONE)

fun getlimit (SS ss) = #limit ss

type strategy_data =
  {loopers : (string * (simpset -> tactic)) list,
   unsafe_solvers : Traverse.ssolver list,
   safe_solvers : Traverse.ssolver list,
   subgoaler : Traverse.subgoaler option,
   cond_depth : int option,
   term_ord : (term * term -> order) option,
   excl_loopers : string Binaryset.set}

fun map_strategy f (SS s) =
  let
    val strategy : strategy_data =
      f {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
         safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
         cond_depth= #cond_depth s, term_ord= #term_ord s,
         excl_loopers= #excl_loopers s}
  in
    SS{mk_rewrs= #mk_rewrs s, history= #history s,
       initial_net= #initial_net s, dprocs= #dprocs s,
       travrules= #travrules s, limit= #limit s, excluded= #excluded s,
       loopers= #loopers strategy,
       unsafe_solvers= #unsafe_solvers strategy,
       safe_solvers= #safe_solvers strategy,
       subgoaler= #subgoaler strategy, cond_depth= #cond_depth strategy,
       term_ord= #term_ord strategy, excl_loopers= #excl_loopers strategy}
  end

fun fupdhistory f (SS s) =
  SS{mk_rewrs= #mk_rewrs s, history=f (#history s),
     initial_net= #initial_net s, dprocs= #dprocs s,
     travrules= #travrules s, limit= #limit s, excluded= #excluded s,
     loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
     safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
     cond_depth= #cond_depth s, term_ord= #term_ord s,
     excl_loopers= #excl_loopers s}

fun record_strategy event =
  fupdhistory (fn history => STRATEGY_EVENT event::history)

fun update_looper ((name,tac),[]) = [(name,tac)]
  | update_looper (looper as (name,_),(entry as (name',_))::rest) =
      if name = name' then looper::rest
      else entry::update_looper(looper,rest)

fun add_looper looper ss =
  map_strategy
    (fn s =>
       {loopers=update_looper(looper,#loopers s),
        unsafe_solvers= #unsafe_solvers s, safe_solvers= #safe_solvers s,
        subgoaler= #subgoaler s, cond_depth= #cond_depth s,
        term_ord= #term_ord s, excl_loopers= #excl_loopers s}) ss
  |> record_strategy (ADD_LOOPER_EVENT looper)

fun del_looper name (ss as SS s) =
  if List.exists (fn (name',_) => name = name') (#loopers s) then
    map_strategy
      (fn strategy =>
         {loopers=List.filter (fn (name',_) => name <> name')
                              (#loopers strategy),
          unsafe_solvers= #unsafe_solvers strategy,
          safe_solvers= #safe_solvers strategy,
          subgoaler= #subgoaler strategy,
          cond_depth= #cond_depth strategy, term_ord= #term_ord strategy,
          excl_loopers= #excl_loopers strategy}) ss
    |> record_strategy (DEL_LOOPER_EVENT name)
  else
    (HOL_WARNING "simpLib" "del_looper" ("No looper called " ^ name);
     ss)

fun split_looper_name name th =
  (if splitLib.is_asm_split th then "split_asm " else "split ") ^ name

fun add_split th =
  add_looper
    (split_looper_name (splitLib.split_thm_name th) th,
     K (splitLib.SPLIT_TAC [th]))

fun del_split name ss =
  let
    val names =
      if String.isPrefix "split " name orelse
         String.isPrefix "split_asm " name
      then [name]
      else ["split " ^ name, "split_asm " ^ name]
    fun present candidate (SS s) =
      List.exists (fn (name,_) => name = candidate) (#loopers s)
    fun remove (candidate, result) =
      if present candidate result then del_looper candidate result
      else result
  in
    List.foldl remove ss names
  end

fun case_types goal_terms =
  let
    fun case_info tyinfo =
      SOME (TypeBasePure.case_const_of tyinfo,
            TypeBasePure.ty_of tyinfo)
      handle HOL_ERR _ => NONE
    val cases = List.mapPartial case_info (TypeBase.elts ())
    fun occurs head tm =
      can (find_term
        (fn subtm =>
          let val (subhead, args) = strip_comb subtm
              val arity = length (#1 (strip_fun (type_of head)))
          in
            same_const head subhead andalso length args >= arity
          end)) tm
    fun add ((head, ty), result) =
      if List.exists (occurs head) goal_terms then ty :: result else result
  in
    List.foldl add [] cases
  end

fun splitter_looper (SS s) (asms, goal) =
  let
    val excluded = #excl_loopers s
    fun enabled name = not (Binaryset.member (excluded, name))
    fun enabled_named (name, th) = enabled (split_looper_name name th)
    val persistent =
      splitLib.named_split_thms ()
      |> List.filter enabled_named
      |> map #2
    fun type_name ty =
      let val {Thy,Tyop,...} = dest_thy_type ty
      in (Thy ^ "$" ^ Tyop, Tyop)
      end
    fun type_enabled ty =
      let val (full, short) = type_name ty
      in
        enabled ("split.case " ^ full) andalso
        enabled ("split.case " ^ short)
      end
    fun type_rules ty = [splitLib.type_split_of ty]
    val datatype_rules =
      case_types (goal :: asms)
      |> List.filter type_enabled
      |> map type_rules
      |> List.concat
  in
    splitLib.SPLIT_TAC (persistent @ datatype_rules) (asms, goal)
  end

val cases_simp =
  let
    val b = mk_var ("b", bool)
    val t = mk_var ("t", bool)
    val expand = SPECL [b,t,t] boolTheory.COND_EXPAND_IMP
    val identity = ISPECL [b,t] boolTheory.COND_ID
  in
    TRANS (SYM expand) identity
  end

val split_ss =
  named_merge_ss "split"
    [looper_ss ("splitter", splitter_looper), rewrites [cases_simp]]

fun set_looper looper ss =
  map_strategy
    (fn s =>
       {loopers=[looper], unsafe_solvers= #unsafe_solvers s,
        safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
        cond_depth= #cond_depth s, term_ord= #term_ord s,
        excl_loopers= #excl_loopers s}) ss
  |> record_strategy (SET_LOOPER_EVENT looper)

fun add_solver (solver : Traverse.ssolver,
                solvers : Traverse.ssolver list) =
  if List.exists (fn {name,...} => name = #name solver) solvers then solvers
  else solvers @ [solver]

fun dedup_solvers solvers = List.foldl add_solver [] solvers

fun add_unsafe_solver solver ss =
  map_strategy
    (fn strategy =>
       {loopers= #loopers strategy,
        unsafe_solvers=add_solver(solver,#unsafe_solvers strategy),
        safe_solvers= #safe_solvers strategy,
        subgoaler= #subgoaler strategy,
        cond_depth= #cond_depth strategy, term_ord= #term_ord strategy,
        excl_loopers= #excl_loopers strategy}) ss
  |> record_strategy (ADD_UNSAFE_SOLVER_EVENT solver)

fun add_safe_solver solver ss =
  map_strategy
    (fn strategy =>
       {loopers= #loopers strategy,
        unsafe_solvers= #unsafe_solvers strategy,
        safe_solvers=add_solver(solver,#safe_solvers strategy),
        subgoaler= #subgoaler strategy,
        cond_depth= #cond_depth strategy, term_ord= #term_ord strategy,
        excl_loopers= #excl_loopers strategy}) ss
  |> record_strategy (ADD_SAFE_SOLVER_EVENT solver)

fun set_unsafe_solvers solvers ss =
  let val solvers = dedup_solvers solvers
  in
    map_strategy
      (fn s =>
         {loopers= #loopers s, unsafe_solvers=solvers,
          safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
          cond_depth= #cond_depth s, term_ord= #term_ord s,
          excl_loopers= #excl_loopers s}) ss
    |> record_strategy (SET_UNSAFE_SOLVERS_EVENT solvers)
  end

fun set_safe_solvers solvers ss =
  let val solvers = dedup_solvers solvers
  in
    map_strategy
      (fn s =>
         {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
          safe_solvers=solvers, subgoaler= #subgoaler s,
          cond_depth= #cond_depth s, term_ord= #term_ord s,
          excl_loopers= #excl_loopers s}) ss
    |> record_strategy (SET_SAFE_SOLVERS_EVENT solvers)
  end

fun remove_solver name (ss as SS s) =
  let
    fun matches {name=name',...} = name = name'
    fun keep solver = not (matches solver)
    val found = List.exists matches (#unsafe_solvers s) orelse
                List.exists matches (#safe_solvers s)
  in
    if not found then ss
    else
      map_strategy
        (fn strategy =>
           {loopers= #loopers strategy,
            unsafe_solvers=List.filter keep (#unsafe_solvers strategy),
            safe_solvers=List.filter keep (#safe_solvers strategy),
            subgoaler= #subgoaler strategy,
            cond_depth= #cond_depth strategy, term_ord= #term_ord strategy,
            excl_loopers= #excl_loopers strategy}) ss
      |> record_strategy (REMOVE_SOLVER_EVENT name)
  end

fun set_subgoaler subgoaler ss =
  map_strategy
    (fn s =>
       {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
        safe_solvers= #safe_solvers s, subgoaler=SOME subgoaler,
        cond_depth= #cond_depth s, term_ord= #term_ord s,
        excl_loopers= #excl_loopers s}) ss
  |> record_strategy (SET_SUBGOALER_EVENT (SOME subgoaler))

fun set_cond_depth cond_depth ss =
  map_strategy
    (fn s =>
       {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
        safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
        cond_depth=SOME cond_depth, term_ord= #term_ord s,
        excl_loopers= #excl_loopers s}) ss
  |> record_strategy (SET_COND_DEPTH_EVENT (SOME cond_depth))

fun set_term_ord term_ord ss =
  map_strategy
    (fn s =>
       {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
        safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
        cond_depth= #cond_depth s, term_ord=SOME term_ord,
        excl_loopers= #excl_loopers s}) ss
  |> record_strategy (SET_TERM_ORD_EVENT (SOME term_ord))

fun mk_tactic_solver (name,tac) =
  let
    fun solve {context_thms,...} c =
      TAC_PROOF ((map concl context_thms,c),tac)
      |> Lib.itlist PROVE_HYP context_thms
  in
    {name=name,solve=solve}
  end

 fun wk_mk_travrules (rels, congs) = let
   fun cong2proc th = let
     open Opening Travrules
     fun mk_refl (x as {Rinst=rel,arg= t}) = let
       val PREORDER(_,_,refl) = find_relation rel rels
     in
       refl x
     end
     val congproc = CONGPROC mk_refl th (* do not inline *)
   in
     (fn rel => QCHANGED_CONV o congproc rel) (* do not eta expand *)
   end
 in
   TRAVRULES {relations = rels,
              congprocs = [],
              weakenprocs = map cong2proc congs}
 end

 fun add_weakener (wd as (rels,congs,dp)) (SS s) =
   SS{mk_rewrs= #mk_rewrs s,
      history=ADDWEAKENER wd :: #history s,
      travrules=merge_travrules
                  [#travrules s,wk_mk_travrules(rels,congs)],
      initial_net= #initial_net s, dprocs= #dprocs s @ [dp],
      limit= #limit s, excluded= #excluded s, loopers= #loopers s,
      unsafe_solvers= #unsafe_solvers s, safe_solvers= #safe_solvers s,
      subgoaler= #subgoaler s, cond_depth= #cond_depth s,
      term_ord= #term_ord s, excl_loopers= #excl_loopers s}

(* ----------------------------------------------------------------------
    add_relsimp : {trans,refl,weakenings,subsets} -> simpset -> simpset

    trans and refl are the transitivity and reflexivity theorems for the
    relation.  weakenings are theorems for turning (at least) equality goals
    into goals over the new relation.  subsets are theorems that help the
    munger: they say that certain forms imply rules for the relation.  For
    example, if using RTC R as the relation, then RTC_R, which states
      !x y. R x y ==> RTC R x y
    is a good subset theorem
   ---------------------------------------------------------------------- *)

 fun dest_binop t = let
   val (fx,y) = dest_comb t
   val (f,x) = dest_comb fx
 in
   (f,x,y)
 end

 fun vperm(tm1,tm2) =
     case (dest_term tm1, dest_term tm2) of
       (VAR v1,VAR v2)   => (snd v1 = snd v2)
     | (LAMB t1,LAMB t2) => vperm(snd t1, snd t2)
     | (COMB t1,COMB t2) => vperm(fst t1,fst t2) andalso vperm(snd t1,snd t2)
     | (x,y) => aconv tm1 tm2

 fun is_var_perm(tm1,tm2) =
     vperm(tm1,tm2) andalso
     HOLset.equal(FVL [tm1] empty_tmset, FVL [tm2] empty_tmset)

 datatype munge_action = TH of thm | POP

 fun munge base subsets asms (thlistlist, n) = let
   val munge = munge base subsets
   val isbase = can (match_term base)
 in
   case thlistlist of
     [] => n
   | [] :: rest => munge asms (rest, n)
   | (TH th :: ths) :: rest => let
     in
       case CONJUNCTS (SPEC_ALL th) of
         [] => raise Fail "munge: Can't happen"
       | [th] => let
           open Net
         in
           if is_imp (concl th) then
             munge (#1 (dest_imp (concl th)) :: asms)
                   ((TH (UNDISCH th)::POP::ths)::rest, n)
           else
             case total dest_binop (concl th) of
               SOME (R,from,to) => let
                 fun foldthis (t,th) = DISCH t th
                 fun insert (t,th0) n = let
                   val (th,bound) = dest_tagged_rewrite th0
                   val looksloopy = aconv from to orelse
                                    (is_var_perm (from,to) andalso
                                     case bound of UNBOUNDED => true
                                                 | _ => false)
                 in
                   if looksloopy then n
                   else
                     Net.insert (t, (bound, List.foldl foldthis th asms)) n
                 end

               in
                 if isbase R then
                   munge asms (ths :: rest, insert (mk_comb(R,from),th) n)
                 else
                   case List.find (fn (t,_) => aconv R t) subsets of
                     NONE => munge asms (ths :: rest, n)
                   | SOME (_, sub_th) => let
                       val new_th = MATCH_MP sub_th th
                     in
                       munge asms ((TH new_th :: ths) :: rest, n)
                     end
               end
             | NONE => munge asms (ths :: rest, n)
         end
       | thlist => munge asms (map TH thlist :: ths :: rest, n)
     end
   | (POP :: ths) :: rest => munge (tl asms) (ths::rest, n)
 end

 fun po_rel (Travrules.PREORDER(r,_,_)) = r

 fun mk_reducer rel_t subsets initial_rewrites = let
   exception redExn of (control * thm) Net.net
   fun munge_subset_th th = let
     val (_, impn) = strip_forall (concl th)
     val (a, _) = dest_imp impn
     val (f, _, _) = dest_binop a
   in
     (f, th)
   end
   val subsets = map munge_subset_th subsets
   fun addcontext (ctxt, thms) = let
     val n = case ctxt of redExn n => n
                        | _ => raise ERR ("mk_reducer.addcontext",
                                          "Wrong sort of ctxt")
     val n' = munge rel_t subsets [] ([map TH thms], n)
   in
     redExn n'
   end
   val initial_ctxt = addcontext (redExn Net.empty, initial_rewrites)
   fun applythm solver t (bound, th) = let
     val _ =
         trace(7, LZ_TEXT (fn () => "Attempting rewrite: "^thm_to_string th))
     fun dec() = case bound of
                   BOUNDED r =>
                     let val n = !r in
                       if n > 0 then r := n - 1
                       else raise ERR ("mk_reducer.applythm",
                                       "Bound exceeded on rwt.")
                     end
                 | UNBOUNDED => ()
     val matched = PART_MATCH (rator o #2 o strip_imp) th t
     open Trace
     fun do_sideconds th =
         if is_imp (concl th) then let
           val (h,c) = dest_imp (concl th)
           val _ = trace(3,SIDECOND_ATTEMPT h)
           val scond = solver h
           val _ = trace(2,SIDECOND_SOLVED scond)
         in
           do_sideconds (MP th scond)
         end
       else (dec(); trace(2,REWRITING("?",t,th)); th)
   in
     do_sideconds matched
   end

   fun mk_icomb(f, x) = let
     val (f_domty, _) = dom_rng (type_of f)
     val xty = type_of x
     val theta = match_type f_domty xty
   in
     mk_comb(Term.inst theta f, x)
   end

   fun apply {solver,conv,context,stack,relation = (relation,_)} t = let
     val _ = can (match_term rel_t) relation orelse
             raise ERR ("mk_reducer.apply", "Wrong relation")
     val n = case context of redExn n => n
                           | _ => raise ERR ("apply", "Wrong sort of ctxt")
     val lookup_t = mk_icomb(relation,t)
     val _ = trace(7, LZ_TEXT(fn () => "Looking up "^term_to_string lookup_t))
     val matches = Net.match lookup_t n
     val _ = trace(7, LZ_TEXT(fn () => "Found "^Int.toString (length matches)^
                                       " matches"))
   in
     tryfind (applythm (solver stack) lookup_t) matches
   end
 in
   Traverse.REDUCER {name = SOME ("reducer for "^term_to_string rel_t),
                     addcontext = addcontext,
                     apply = apply,
                     initial = initial_ctxt}
 end

 val equality_po = let
   open Travrules
   val TRAVRULES {relations,...} = EQ_tr
 in
   hd relations
 end

 fun rsd_rel {refl,trans,weakenings,subsets,rewrs} =
     #1 (dest_binop (#2 (strip_forall (concl refl))))
 fun rsd_po {refl,trans,weakenings,subsets,rewrs} =
     Travrules.mk_preorder(trans,refl)

 fun rsd_travrules (rsd as {refl,trans,weakenings,subsets,rewrs}) =
     wk_mk_travrules([rsd_po rsd, equality_po], weakenings)

 fun rsd_reducer rsd =
     mk_reducer (rsd_rel rsd) (#subsets rsd) (#rewrs rsd)


 fun add_relsimp (rsd as {refl,trans,weakenings,subsets,rewrs}) ss = let
   val rel_t = rsd_rel rsd
   val rel_po = rsd_po rsd
   val reducer = mk_reducer rel_t subsets rewrs
 in
   add_weakener ([rel_po, equality_po], weakenings, reducer) ss
 end

 fun mk_named_rewrs mk_rewrs (nmopt, th) =
     let
       val ths = mk_rewrs th
       fun reduce {Thy,Name=s} th (i,A) =
           (i + 1,
            (SOME {Thy=Thy,Name=s ^ "." ^ Int.toString i},th) :: A)
     in
       case nmopt of
           NONE => map (fn th => (NONE, th)) ths
         | SOME s => (1,[]) |> Portable.foldl' (reduce s) ths |> #2 |> List.rev
     end


 fun is_excluded (SS{excluded,...}) f =
     case frag_name f of
         SOME n => Binaryset.member(excluded, n)
       | NONE => false

 fun op++(ss as SS sset, f as SSFRAG_CON ssf) =
   if is_excluded ss f then ss
   else let
   val mk_rewrs' = #mk_rewrs sset
   val history = #history sset
   val travrules = #travrules sset
   val initial_net = #initial_net sset
   val dprocs' = #dprocs sset
   val {convs,rewrs,filter,ac,dprocs,congs,relsimps,...} = ssf
   val mk_rewrs = case filter of
                    SOME f => f oo mk_rewrs'
                  | _ => mk_rewrs'
   val crewrs = map (fn (nmopt,th) => (nmopt, dest_tagged_rewrite th)) rewrs
   val rewrs' : (thname option * controlled_thm) list =
       flatten (map (mk_named_rewrs mk_rewrs') (ac_rewrites ac @ crewrs))
   val newconvdata = convs @ List.mapPartial mk_rewr_convdata rewrs'
   val net = net_add_convs initial_net newconvdata
   fun travrel (TRAVRULES{relations,...}) = relations
   val sset_rels = travrel travrules
   (* give the existing dprocs the rewrs as additional context -
      assume the provided dprocs in the frag have already been
      primed *)
   val relreducers = map rsd_reducer relsimps
   val new_dprocs = map (Traverse.addctxt (map #2 rewrs)) dprocs' @ dprocs @
                    relreducers

   val reltravs = map rsd_travrules relsimps
   val relrels = List.concat (map travrel reltravs)
   val relations = sset_rels @ relrels
   val loopers = List.foldl update_looper (#loopers sset) (#loopers ssf)
   val unsafe_solvers =
     List.foldl add_solver (#unsafe_solvers sset) (#unsafe_solvers ssf)
   val safe_solvers =
     List.foldl add_solver (#safe_solvers sset) (#safe_solvers ssf)
 in
   SS{mk_rewrs=mk_rewrs, history=ADDFRAG f :: history,
      initial_net=net, limit= #limit sset, dprocs=new_dprocs,
      excluded= #excluded sset,
      travrules=merge_travrules
                  (travrules::mk_travrules relations congs::reltravs),
      loopers=loopers, unsafe_solvers=unsafe_solvers,
      safe_solvers=safe_solvers, subgoaler= #subgoaler sset,
      cond_depth= #cond_depth sset, term_ord= #term_ord sset,
      excl_loopers= #excl_loopers sset}
 end

val mk_simpset = foldl (fn (f,ss) => ss ++ f) empty_ss

fun apply_strategy_event event =
  map_strategy
    (fn s =>
       case event of
           ADD_LOOPER_EVENT looper =>
             {loopers=update_looper(looper,#loopers s),
              unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | DEL_LOOPER_EVENT name =>
             {loopers=List.filter (fn (name',_) => name <> name')
                                  (#loopers s),
              unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | SET_LOOPER_EVENT looper =>
             {loopers=[looper], unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | ADD_UNSAFE_SOLVER_EVENT solver =>
             {loopers= #loopers s,
              unsafe_solvers=add_solver(solver,#unsafe_solvers s),
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | ADD_SAFE_SOLVER_EVENT solver =>
             {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
              safe_solvers=add_solver(solver,#safe_solvers s),
              subgoaler= #subgoaler s, cond_depth= #cond_depth s,
              term_ord= #term_ord s, excl_loopers= #excl_loopers s}
         | SET_UNSAFE_SOLVERS_EVENT solvers =>
             {loopers= #loopers s, unsafe_solvers=solvers,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | SET_SAFE_SOLVERS_EVENT solvers =>
             {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
              safe_solvers=solvers, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | REMOVE_SOLVER_EVENT name =>
             let fun keep {name=name',...} = name <> name'
             in
               {loopers= #loopers s,
                unsafe_solvers=List.filter keep (#unsafe_solvers s),
                safe_solvers=List.filter keep (#safe_solvers s),
                subgoaler= #subgoaler s, cond_depth= #cond_depth s,
                term_ord= #term_ord s, excl_loopers= #excl_loopers s}
             end
         | SET_SUBGOALER_EVENT subgoaler =>
             {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler=subgoaler,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | SET_COND_DEPTH_EVENT cond_depth =>
             {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth=cond_depth, term_ord= #term_ord s,
              excl_loopers= #excl_loopers s}
         | SET_TERM_ORD_EVENT term_ord =>
             {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord=term_ord,
              excl_loopers= #excl_loopers s}
         | SET_EXCL_LOOPERS_EVENT excl_loopers =>
             {loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
              safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
              cond_depth= #cond_depth s, term_ord= #term_ord s,
              excl_loopers=excl_loopers})

fun set_mk_rewrs mk_rewrs (SS s) =
  SS{mk_rewrs=mk_rewrs, history= #history s,
     initial_net= #initial_net s, dprocs= #dprocs s,
     travrules= #travrules s, limit= #limit s, excluded= #excluded s,
     loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
     safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
     cond_depth= #cond_depth s, term_ord= #term_ord s,
     excl_loopers= #excl_loopers s}

fun build_from_history h0 =
    let
      fun foldthis (hi, ss) =
          case hi of
              ADDFRAG sf => ss ++ sf
            | DELETE_EVENT sl => ss -* sl
            | ADDWEAKENER wd => add_weakener wd ss
            | STRATEGY_EVENT event =>
                apply_strategy_event event ss |> record_strategy event
            | SET_MK_REWRS mk_rewrs =>
                set_mk_rewrs mk_rewrs ss
                |> fupdhistory (fn h => SET_MK_REWRS mk_rewrs::h)
    in
      List.foldl foldthis empty_ss (List.rev h0)
    end

fun setexcluded e (SS s) =
  SS{mk_rewrs= #mk_rewrs s, history= #history s,
     initial_net= #initial_net s, dprocs= #dprocs s,
     travrules= #travrules s, limit= #limit s, excluded=e,
     loopers= #loopers s, unsafe_solvers= #unsafe_solvers s,
     safe_solvers= #safe_solvers s, subgoaler= #subgoaler s,
     cond_depth= #cond_depth s, term_ord= #term_ord s,
     excl_loopers= #excl_loopers s}

fun remove_ssfrags names (ss as SS{history,limit,excluded,...}) =
    let
      val s = Set.addList (Binaryset.empty String.compare, names)
      val nil_included = Set.member(s, "")
      fun member (SSFRAG_CON{name = SOME n,...}) = Binaryset.member(s,n)
        | member (SSFRAG_CON{name = NONE,...}) = nil_included
      fun filterthis (hi as ADDFRAG f) = not(member f)
        | filterthis hi = true
      val history' = List.filter filterthis history
      val _ = length history' < length history orelse
              raise Conv.UNCHANGED
    in
      build_from_history history' |> fupdlimit (fn _ => limit)
                                  |> setexcluded excluded
    end

(* Like `remove_ssfrags`, but additionally records the names so that any
   subsequent `++` of a fragment with one of those names is silently
   skipped.  `force_add` is the override that bypasses (and clears) this
   prohibition for a given fragment.  Never raises Conv.UNCHANGED.

   Desired invariant on every simpset:
       no ADDFRAG in `history` has a name in `excluded`.
   The other simpset operations (`++`, `-*`, `add_weakener`, `force_add`,
   `remove_ssfrags`) all preserve this invariant, so in principle we
   could filter `history` against `names` alone here.  We defensively
   filter against `excluded ∪ names` instead so that this function stays
   correct in isolation even if some future operation accidentally
   introduces an ADDFRAG of an already-excluded name. *)
fun exclude_ssfrags names (ss as SS{history,limit,excluded,...}) =
    let
      val excluded' = Binaryset.addList (excluded, names)
      val nil_included = Binaryset.member(excluded', "")
      fun isexcl (SSFRAG_CON{name = SOME n,...}) =
            Binaryset.member(excluded',n)
        | isexcl (SSFRAG_CON{name = NONE,...}) = nil_included
      fun filterthis (hi as ADDFRAG f) = not(isexcl f)
        | filterthis hi = true
      val history' = List.filter filterthis history
    in
      build_from_history history' |> fupdlimit (fn _ => limit)
                                  |> setexcluded excluded'
    end

(* Force-include a fragment, even if its name is in the simpset's
   excluded set — and remove that name from the excluded set so that
   subsequent `++` of the same fragment also succeeds. *)
fun force_add (ss as SS sset) f =
    let val excluded' =
            case frag_name f of
                SOME n => (Binaryset.delete(#excluded sset, n)
                           handle NotFound => #excluded sset)
              | NONE => #excluded sset
    in
      setexcluded excluded' ss ++ f
    end

fun clear_rules (SS s) =
  let
    val history =
      [STRATEGY_EVENT (SET_EXCL_LOOPERS_EVENT (#excl_loopers s)),
       STRATEGY_EVENT (SET_TERM_ORD_EVENT (#term_ord s)),
       STRATEGY_EVENT (SET_COND_DEPTH_EVENT (#cond_depth s)),
       STRATEGY_EVENT (SET_SUBGOALER_EVENT (#subgoaler s)),
       STRATEGY_EVENT (SET_SAFE_SOLVERS_EVENT (#safe_solvers s)),
       STRATEGY_EVENT (SET_UNSAFE_SOLVERS_EVENT (#unsafe_solvers s)),
       SET_MK_REWRS (#mk_rewrs s)]
  in
  SS{mk_rewrs= #mk_rewrs s, history=history, initial_net=empty, dprocs=[],
     travrules=EQ_tr, limit= #limit s, excluded= #excluded s, loopers=[],
     unsafe_solvers= #unsafe_solvers s, safe_solvers= #safe_solvers s,
     subgoaler= #subgoaler s, cond_depth= #cond_depth s,
     term_ord= #term_ord s, excl_loopers= #excl_loopers s}
  end

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

 exception CONVNET of net;

 fun rewriter_for_ss (SS{mk_rewrs,travrules,initial_net,...}) = let
   fun addcontext (context,thms) = let
     val net = (raise context) handle CONVNET net => net
     val cthms = map dest_tagged_rewrite thms
     val new_rwts0 = flatten (map mk_rewrs cthms)
     val new_rwts =
         map (fn th => (SOME {Thy = "", Name = "rewrite: from context"}, th))
             new_rwts0
   in
     CONVNET
       (net_add_convs net (List.mapPartial mk_rewr_convdata new_rwts))
   end
   fun apply {solver,conv,context,stack,relation} tm = let
     val net = (raise context) handle CONVNET net => net
   in
     tryfind (fn {ci = {conval,...},...} => conval solver stack tm)
             (lookup tm net)
   end
   in REDUCER {name=SOME"rewriter_for_ss",
               addcontext=addcontext, apply=apply,
               initial=CONVNET initial_net}
   end;

 fun traversedata_for_ss (ss as (SS ssdata)) =
      {rewriters=[rewriter_for_ss ss],
       dprocs= #dprocs ssdata,
       relation= boolSyntax.equality,
       travrules= #travrules ssdata,
       limit = #limit ssdata,
       subgoaler= #subgoaler ssdata,
       solvers= #unsafe_solvers ssdata,
       cond_depth= #cond_depth ssdata,
       term_ord= #term_ord ssdata};

 fun SIMP_QCONV ss = TRAVERSE (traversedata_for_ss ss);

val Cong   = markerLib.Cong
val AC     = markerLib.AC;
val Excl   = markerLib.Excl
val ExclSF = markerLib.ExclSF
val Req0   = markerLib.mk_Req0
val ReqD   = markerLib.mk_ReqD

local open markerSyntax markerLib
in
fun is_AC thm = same_const(fst(strip_comb(concl thm))) AC_tm
fun is_Cong thm = same_const(fst(strip_comb(concl thm))) Cong_tm

fun extract_excls (excls, exfrags, rest) l =
    case l of
        [] => (List.rev excls, List.rev exfrags, List.rev rest)
      | th::ths =>
        case markerLib.destExcl th of
            SOME nm => extract_excls (nm::excls, exfrags, rest) ths
          | NONE => case markerLib.destExclSF th of
                        NONE => extract_excls (excls, exfrags, th::rest) ths
                      | SOME nm => extract_excls (excls, nm::exfrags, rest) ths

fun extract_frags (frags, rest) l =
    case l of
        [] => (List.rev frags, List.rev rest)
      | th :: ths => case markerLib.destFRAG th of
                         NONE => extract_frags (frags, th :: rest) ths
                       | SOME fragnm => (
                         case lookup_named_frag fragnm of
                             NONE => raise ERR ("extract_frags",
                                                "No frag called " ^ fragnm)
                           | SOME sf => extract_frags (sf::frags, rest) ths
                       )

fun SF ssfrag =
    case frag_name ssfrag of
        NONE => raise ERR ("SF",
                           "Can't use anonymous ssfrags in thm list arguments")
      | SOME nm => ((case lookup_named_frag nm of
                         NONE => (ignore (register_frag ssfrag);
                                  HOL_WARNING "simpLib" "SF"
                                              ("Registering ssfrag " ^ nm ^
                                               "; this doesn't persist after "^
                                               "theory export!"))
                       | _ => ());
                    markerLib.FRAG nm)

fun process_tags ss thl =
    let val (Congs,rst) = Lib.partition is_Cong thl
        val (ACs,rst) = Lib.partition is_AC rst
        val (excludes, exclfrags, rst) = extract_excls ([],[],[]) rst
        val (frags, rst) = extract_frags ([],[]) rst
    in
      if null Congs andalso null ACs andalso null excludes andalso
         null frags andalso null exclfrags
      then (ss,thl)
      else
        let val base = remove_ssfrags exclfrags ss handle Conv.UNCHANGED => ss
            val cong_ac =
                SSFRAG_CON
                  {name=SOME "Cong and/or AC", relsimps=[],
                   ac=map unAC ACs,
                   congs=map (normCong o unCong) Congs,
                   convs=[], rewrs=[], filter=NONE, dprocs=[], loopers=[],
                   unsafe_solvers=[], safe_solvers=[], congprocs=[]}
            (* Cong/AC is named but never user-excludable; SF-derived frags
               go through force_add so they override any active exclusion. *)
            val withCongAc = base ++ cong_ac
            val withFrags = List.foldl (fn (f,ss) => force_add ss f)
                                       withCongAc frags
        in
          (withFrags -* excludes, rst)
        end
    end

fun SIMP_CONV ss l tm =
  let val (ss', l') = process_tags ss l
  in TRY_CONV (SIMP_QCONV ss' l') tm
  end;

fun SIMP_PROVE ss l t =
  let val (ss', l') = process_tags ss l
  in EQT_ELIM (SIMP_QCONV ss' l' t)
  end;

infix &&;

fun (ss && thl) =
  let val (ss',thl') = process_tags ss thl
  in ss' ++ rewrites thl'
  end;

end;

(*---------------------------------------------------------------------------*)
(*   SIMP_TAC      : simpset -> thm list -> tactic                           *)
(*   ASM_SIMP_TAC  : simpset -> thm list -> tactic                           *)
(*   FULL_SIMP_TAC : simpset -> thm list -> tactic                           *)
(*                                                                           *)
(* FAILURE CONDITIONS                                                        *)
(*                                                                           *)
(* These tactics never fail, though they may diverge.                        *)
(* --------------------------------------------------------------------------*)


fun SIMP_RULE ss l = CONV_RULE (SIMP_CONV ss l)

fun ASM_SIMP_RULE ss l th = SIMP_RULE ss (l@map ASSUME (hyp th)) th;

type simp_mode = {safe : bool}

fun reconcile_hyps asl th =
  let
    fun asm_for h =
      case List.find (aconv h) asl of
          SOME a => a
        | NONE => raise ERR ("GEN_SIMP_TAC", "Solver introduced a hypothesis")
    fun replace_hyp h result = PROVE_HYP (ASSUME (asm_for h)) result
  in
    Lib.itlist ADD_ASSUM asl (Lib.itlist replace_hyp (hyp th) th)
  end

fun final_solver_tac mode ss context_thms =
  let
    val SS s = ss
    val solvers =
      if #safe mode then #safe_solvers s else #unsafe_solvers s
    val prover_ctxt =
      {stack=[], context_thms=context_thms,
       recurse=QCONV (SIMP_CONV ss context_thms)}
    fun solve_with ({solve,...} : Traverse.ssolver) (asl,w) =
      let
        val th = solve prover_ctxt w
        val _ = aconv (concl th) w orelse
                raise ERR ("GEN_SIMP_TAC", "Solver proved the wrong term")
      in
        ACCEPT_TAC (reconcile_hyps asl th) (asl,w)
      end
  in
    FIRST (map solve_with solvers)
  end

fun looper_tac (ss as SS s) =
  let
    fun enabled (name,_) =
      not (Binaryset.member (#excl_loopers s,name))
    fun apply (_,looper) g =
      looper ss g
      handle Conv.UNCHANGED => NO_TAC g
  in
    FIRST (map apply (List.filter enabled (#loopers s)))
  end

fun bounded_looper rounds tac g =
  case !rounds of
      SOME n =>
        if n <= 0 then NO_TAC g
        else
          let val result = tac g
          in
            rounds := SOME (n - 1);
            result
          end
    | NONE => tac g

fun gen_simp_tac extra_context (mode : simp_mode) ss ths =
  fn g =>
    let
      val rounds = ref (getlimit ss)
      fun start recur tagged_thms =
        let
          fun main tagged_thms =
            let
              val (invocation_ss,context_thms) =
                process_tags ss tagged_thms
              val rewr_tac =
                CONV_TAC (SIMP_CONV invocation_ss context_thms)
              val solve_tac =
                final_solver_tac mode invocation_ss
                                 (context_thms @ extra_context)
              val loop_tac =
                bounded_looper rounds (looper_tac invocation_ss)
            in
              rewr_tac THEN
              (solve_tac ORELSE
               TRY (loop_tac THEN_LT ALLGOALS (recur main)))
            end
        in
          main tagged_thms
        end
    in
      markerLib.process_taclist_then_recur {arg=ths} start g
    end

fun GEN_SIMP_TAC mode = gen_simp_tac [] mode

fun ASM_SIMP_TAC ss = GEN_SIMP_TAC {safe=false} ss
val asm_simp_tac = ASM_SIMP_TAC
fun SIMP_TAC ss ths = ASM_SIMP_TAC ss (markerLib.NoAsms::ths)
val simp_tac = SIMP_TAC

(* differs from default strip_assume_tac base in that it doesn't call
   OPPOSITE_TAC or DISCARD_TAC.

   Both are reasonable omissions: OPPOSITE_TAC detects mutually
   contradictory assumptions; we'd hope that simplification will turn
   one or the other into F, which is then caught by CONTR_TAC.
   DISCARD_TAC drops duplicates. This should turn into T, which we can
   discard if droptrues is true.
*)

type simptac_config =
     {strip : bool, elimvars : bool, droptrues : bool, oldestfirst : bool}

(* back/front assume_tac; backp is true if the new assumption should go at the
   back of the list *)
fun BF_ASSUME_TAC backp th (g as (asl,w)) =
    if backp then ([(asl @ [concl th], w)],
                   fn resths => PROVE_HYP th (hd resths))
    else ASSUME_TAC th g

(* contr/accept/assume *)
fun caa_tac0 backp (c : simptac_config) th =
    let
      val base = FIRST [CONTR_TAC th, ACCEPT_TAC th,
                        BF_ASSUME_TAC backp th]
    in
      if #droptrues c andalso concl th ~~ boolSyntax.T then ALL_TAC
      else base
    end

local
   val caa_tac =
       caa_tac0 false {elimvars = false, droptrues = false, strip = false,
                       oldestfirst = true}
   val STRIP_ASSUME_TAC' = STRIP_ALL_THEN caa_tac
   fun drop r =
      fn n =>
         POP_ASSUM_LIST
           (fn l =>
              MAP_EVERY ASSUME_TAC
                 (Lib.with_exn (r o List.take) (l, List.length l - n)
                   (Feedback.mk_HOL_ERR "simpLib" "drop"
                                        "Bad cut off number")))
   fun GEN_FULL_SIMP_TAC (drop, r) tac =
      fn ss => fn thms =>
         let
            fun simp_asm (t, l') = SIMP_RULE ss (l' @ thms) t :: l'
            fun f asms = MAP_EVERY tac (List.foldl simp_asm [] (r asms))
                         THEN drop (List.length asms)
         in
            markerLib.ABBRS_THEN
               (fn l => ASSUM_LIST f THEN ASM_SIMP_TAC ss l) thms
         end
   val full_tac = GEN_FULL_SIMP_TAC (drop List.rev, Lib.I)
   val rev_full_tac = GEN_FULL_SIMP_TAC (drop Lib.I, List.rev)
in
   val FULL_SIMP_TAC = markerLib.mk_require_tac o full_tac STRIP_ASSUME_TAC'
   val full_simp_tac = FULL_SIMP_TAC
   val REV_FULL_SIMP_TAC =
       markerLib.mk_require_tac o rev_full_tac STRIP_ASSUME_TAC'
   val rev_full_simp_tac = REV_FULL_SIMP_TAC
   val NO_STRIP_FULL_SIMP_TAC = markerLib.mk_require_tac o full_tac caa_tac
   val NO_STRIP_REV_FULL_SIMP_TAC =
       markerLib.mk_require_tac o rev_full_tac caa_tac
end

fun stdcon (c : simptac_config) th =
    if #elimvars c andalso eliminable (concl th) then VSUBST_TAC th
    else
      (if #strip c then STRIP_ALL_THEN else I)
        (caa_tac0 (not (#oldestfirst c)) c)
        th

fun psr (cfg : simptac_config) ss =
    let val popper = if #oldestfirst cfg then pop_last_assum else pop_assum
    in
      popper (fn th =>
                 ASSUM_LIST (fn asms => stdcon cfg (SIMP_RULE ss asms th)))
    end

fun allasms cfg ss (g as (asl,_)) = ntac (length asl) (psr cfg ss) g

fun global_simp_tac cfg ss0 =
    markerLib.mk_require_tac (
      markerLib.ABBRS_THEN (
        markerLib.LLABEL_RES_THEN (
          fn thl =>
             let
               val (ss1,thl') = process_tags ss0 thl
               val ss = ss1 ++ rewrites thl'
             in
               rpt (CHANGED_TAC (allasms cfg ss)) THEN
               gen_simp_tac thl' {safe=false} ss []
             end
        )
      )
    )





fun track f x =
 let val _ = (used_rewrites := [])
     val res = Lib.with_flag(track_rewrites,true) f x
 in used_rewrites := rev (!used_rewrites)
  ; res
 end;

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun tyi_to_ssdata tyinfo =
    let
      val (thy,tyop) = TypeBasePure.ty_name_of tyinfo
      val tyname = thy ^ "$" ^ tyop
      val {rewrs = rws0, convs} = TypeBasePure.simpls_of tyinfo;
      fun reduce (th, (i,A)) =
          (i + 1,
           (SOME {Thy="",Name=tyname ^ " simpl. " ^ Int.toString i},th) ::
           A)
      val (_, rewrs) = foldl reduce (1,[]) rws0
    in
      SSFRAG_CON
        {name=SOME ("Datatype " ^ tyname),
         convs=map (fn c => {thypart=SOME thy,cd=c}) convs,
         rewrs=rewrs, filter=NONE, dprocs=[], ac=[], congs=[], relsimps=[],
         loopers=[], unsafe_solvers=[], safe_solvers=[], congprocs=[]}
    end

fun type_ssfrag ty =
    case TypeBase.fetch ty of
        NONE => raise ERR ("type_ssfrag", "No TypeBase info for type")
      | SOME tyi => tyi_to_ssdata tyi


(*---------------------------------------------------------------------------*)
(* Pretty printers for ssfrags and simpsets                                  *)
(*---------------------------------------------------------------------------*)

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun dest_reducer (Traverse.REDUCER x) = x;

fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

fun dest_convdata tcd  =
    let
      val {thypart,cd={name,key,...} : convdata} = tcd
    in
      (thypart,name,Option.map #2 key)
    end

fun pp_ssfrag (SSFRAG_CON {name,convs,rewrs,ac,dprocs,congs,...}) =
 let open Portable smpp
     val name = (case name of SOME s => s | NONE => "<anonymous>")
     val convs = map dest_convdata convs
     val dps = case merge_names (map (#name o dest_reducer) dprocs)
                of NONE => []
                 | SOME n => [n]
     val pp_term = lift (Parse.term_pp_with_delimiters Hol_pp.pp_term)
     val pp_thm = lift pp_thm
     fun pp_named_thm (nmopt, th) =
         let
           val nmstr = case nmopt of
                           NONE => "<anon>"
                         | SOME {Thy,Name} => if Thy = "" then Name
                                              else Thy ^ "$" ^ Name
         in
           block CONSISTENT 0 (
             add_string ("[" ^ nmstr ^ "]") >> add_break(2,2) >> pp_thm th
           )
         end
     fun pp_thm_pair (th1,th2) =
        block CONSISTENT 0 (pp_thm th1 >> add_break(2,0) >> pp_thm th2)
     fun pp_conv_info (thypart,n,SOME tm) =
          block CONSISTENT 0 (
            add_string (opttheory thypart n ^ ", keyed on pattern") >>
            add_break(2,0) >> pp_term tm
          )
       | pp_conv_info (thypart,n,NONE) = add_string (opttheory thypart n)
     val nl2 = add_newline >> add_newline
     fun vspace l = if null l then nothing else nl2
     fun vblock(header, ob_pr, obs) =
       if null obs then nothing
       else
         block CONSISTENT 3 (
          add_string (header^":") >>
          add_newline >>
          pr_list ob_pr add_newline obs
         ) >> add_break(1,0)
 in
   block CONSISTENT 0 (
     add_string ("Simplification set fragment: "^name) >> add_newline >>
     vblock("Conversions",pp_conv_info,convs) >>
     vblock("Decision procedures",add_string,dps) >>
     vblock("Congruence rules",pp_thm,congs) >>
     vblock("AC rewrites",pp_thm_pair,ac) >>
     vblock("Rewrite rules",pp_named_thm,rewrs)
   )
 end

fun pp_simpset
      (ss as SS {initial_net,loopers,unsafe_solvers,safe_solvers,...}) =
  let
    open Portable smpp
    val empty_strset = Set.empty String.compare
    fun foldthis {thypart, ci = {name,...}} nms = opttheory thypart name::nms
    val keysl = Ho_Net.fold' foldthis initial_net []
    val keys = Listsort.sort String.compare keysl
    val (rewrites0,others0) = Lib.partition (String.isPrefix "rewrite:") keys
    val rewrites = map (fn s => String.extract(s, 8, NONE)) rewrites0
    val (anons, real_rewrites) = Lib.partition (equal "<anonymous>") rewrites
    val anon_string = case length anons of
                          0 => ""
                        | 1 => " (with 1 anonymous rewrite)"
                        | n => " (with " ^ Int.toString n ^
                               " anonymous rewrites)"
    val (fragname_set,anonfrag_count) =
        List.foldl (fn (ssf,(s,c)) =>
                       case ssfrag_name ssf of
                           NONE => (s,c+1)
                         | SOME n => (Set.add(s,n), c))
                   (empty_strset, 0)
                   (ssfrags_of ss)
    val rmstring = ""
    fun count n s = case n of 1 => "1" ^ s | n => Int.toString n ^ s ^ "s"
    val anon_fragstring = case anonfrag_count of
                              0 => ":"
                            | c => " (with " ^ count c " anonymous fragment" ^
                                   " [remove using name \"\"]):"
    fun titled_strlist (title, l) =
      block CONSISTENT 0 (
        add_string title >> add_break(1,3) >>
        block INCONSISTENT 0 (
          pr_list add_string (add_string "," >> add_break(1,0)) l
        )
      )
    val others = Set.listItems (Set.addList (empty_strset, others0))
    val looper_names = map #1 loopers
    val unsafe_names = map #name unsafe_solvers
    val safe_names = map #name safe_solvers
    val base_sections =
      [("Included fragments"^anon_fragstring, Set.listItems fragname_set),
       ("Rewrites"^anon_string, real_rewrites),
       ("Other net names/keys:", others)]
    fun add_section section sections =
      if null (#2 section) then sections else sections @ [section]
    val sections =
      base_sections
      |> add_section ("Loopers:",looper_names)
      |> add_section ("Unsafe solvers:",unsafe_names)
      |> add_section ("Safe solvers:",safe_names)
  in
    block CONSISTENT 0 (
      pr_list titled_strlist (add_break(1,0)) sections
    )
  end;

val pp_ssfrag = Parse.mlower o pp_ssfrag
val pp_simpset = Parse.mlower o pp_simpset

end (* struct *)
