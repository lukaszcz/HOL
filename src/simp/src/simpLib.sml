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
type reducer_ctxt =
  {solver : term list -> term -> thm,
   stack : term list,
   cond_depth : int,
   term_ord : term * term -> order}
type contextual_convdata =
  {name : string,
   key : (term list * term) option,
   trace : int,
   conv : reducer_ctxt -> conv}
type tagged_convdata = {thypart : string option, cd : contextual_convdata}

fun lift_convdata {name,key,trace,conv} : contextual_convdata =
  {name=name, key=key, trace=trace,
   conv=fn {solver,stack,...} => conv solver stack}
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
      (fn ctxt => fn tm =>
      if !r = 0 then failwith "exceeded rewrite bound"
      else c ctxt tm before
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
              conv  = appconv (COND_REWR_CONV_WITH_CONTEXT (nm,th), tag)}
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
   conval : reducer_ctxt -> conv}
type net_conv_info = {thypart : string option, ci : conv_info}
type net = net_conv_info Ho_Net.net
type weakener_data =
  Travrules.preorder list * thm list * Traverse.reducer

(* One resolved rule exclusion.  [pattern] is what [name_match] tests the
   net's entries against; [original] is the spelling a decision procedure
   is registered under, and the two are not interchangeable.  A rule
   exclusion is recorded in the simpset's history and replayed from there,
   so it carries the pattern it was resolved with rather than being parsed
   a second time: replay must not get to re-decide what a name meant. *)
type rule_exclusion = {original : string, pattern : string option * string}

datatype looper_kind = OrdinaryLooper | SplitLooper of bool
and looper_entry = LooperEntry of
  {kind : looper_kind, name : string, apply : simpset -> tactic}
and ssfrag = SSFRAG_CON of {
    name           : string option,
    convs          : tagged_convdata list,
    rewrs          : (thname option * thm) list,
    ac             : (thm * thm) list,
    filter         : (controlled_thm -> controlled_thm list) option,
    dprocs         : Traverse.reducer list,
    congs          : thm list,
    relsimps       : relsimpdata list,
    loopers        : looper_entry list,
    unsafe_solvers : Traverse.ssolver list,
    safe_solvers   : Traverse.ssolver list
}
and history_item = ADDFRAG of ssfrag
                 | DELETE_EVENT of rule_exclusion list
                 | ADDWEAKENER of weakener_data
                 | STRATEGY_EVENT of strategy_event
                 | SET_MK_REWRS of
                     (controlled_thm -> controlled_thm list)
and strategy_event =
    ADD_LOOPER_EVENT of looper_entry
  | DEL_LOOPER_EVENT of looper_kind * string
  | SET_LOOPER_EVENT of looper_entry
  | ADD_UNSAFE_SOLVER_EVENT of Traverse.ssolver
  | ADD_SAFE_SOLVER_EVENT of Traverse.ssolver
  | SET_UNSAFE_SOLVERS_EVENT of Traverse.ssolver list
  | SET_SAFE_SOLVERS_EVENT of Traverse.ssolver list
  | REMOVE_SOLVER_EVENT of string
  | SET_SUBGOALER_EVENT of Traverse.subgoaler option
  | SET_COND_DEPTH_EVENT of int option
  | SET_TERM_ORD_EVENT of (term * term -> order) option
  | SET_EXCL_LOOPERS_EVENT of string Binaryset.set
  | SET_STRATEGY_EVENT of strategy_data
and simpset = SS of {
    mk_rewrs       : controlled_thm -> controlled_thm list,
    history        : history_item list,
    initial_net    : net,
    dprocs         : reducer list,
    travrules      : travrules,
    limit          : int option,
    excluded       : string Binaryset.set,
    strategy       : strategy_data
}
(* The traversal-strategy knobs are grouped so that the simpset updaters
   that leave them alone do not have to mention them one by one. *)
withtype strategy_data =
  {loopers        : looper_entry list,
   unsafe_solvers : Traverse.ssolver list,
   safe_solvers   : Traverse.ssolver list,
   subgoaler      : Traverse.subgoaler option,
   cond_depth     : int option,
   term_ord       : (term * term -> order) option,
   excl_loopers   : string Binaryset.set}

fun frag_name (SSFRAG_CON {name,...}) = name

fun normCong cong_th = PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] cong_th

fun ordinary_looper (name,apply) =
  LooperEntry {kind=OrdinaryLooper,name=name,apply=apply}

fun updfrag z =
  let
    fun from name convs rewrs ac filter dprocs congs relsimps loopers
             unsafe_solvers safe_solvers =
      {name=name, convs=convs, rewrs=rewrs, ac=ac, filter=filter,
       dprocs=dprocs, congs=congs, relsimps=relsimps, loopers=loopers,
       unsafe_solvers=unsafe_solvers, safe_solvers=safe_solvers}
    fun from' safe_solvers unsafe_solvers loopers relsimps congs
              dprocs filter ac rewrs convs name =
      from name convs rewrs ac filter dprocs congs relsimps loopers
        unsafe_solvers safe_solvers
    fun to f {name,convs,rewrs,ac,filter,dprocs,congs,relsimps,loopers,
              unsafe_solvers,safe_solvers} =
      f name convs rewrs ac filter dprocs congs relsimps loopers
        unsafe_solvers safe_solvers
  in
    FunctionalRecordUpdate.makeUpdate11 (from,from',to)
  end z

val empty_frag_data =
  {name=NONE, convs=[], rewrs=[], ac=[], filter=NONE, dprocs=[], congs=[],
   relsimps=[], loopers=[], unsafe_solvers=[], safe_solvers=[]}
val empty_ssfrag = SSFRAG_CON empty_frag_data

fun SSFRAG {name,convs,rewrs,ac,filter,dprocs,congs} =
  SSFRAG_CON
    (updfrag empty_frag_data
       (Fld #name name)
       (Fld #convs
          (map (fn c => {thypart=NONE,cd=lift_convdata c}) convs))
       (Fld #rewrs rewrs) (Fld #ac ac) (Fld #filter filter)
       (Fld #dprocs dprocs) (Fld #congs (map normCong congs)) $$)

fun ssf_upd_rewrs f (SSFRAG_CON s) =
  SSFRAG_CON (updfrag s (Fld #rewrs (f (#rewrs s))) $$)

(* ----------------------------------------------------------------------
    maintain a global database of (named) ssfrags
   ---------------------------------------------------------------------- *)

local
  val ssfragDB_slot : ssfrag Symtab.table Context.Data.slot =
      Context.Data.new
        {name = "simpLib.ssfragDB",
         empty = Symtab.empty,
         pp = fn _ => "<simpLib.ssfragDB>"}
in
  fun ssfragDB () = Context.Data.get ssfragDB_slot (Context.snapshot())
  val upd_ssfragDB = Context.Data.modify ssfragDB_slot
end
fun register_frag ssf =
    case frag_name ssf of
        NONE => raise ERR ("register_frag", "Can only register named ssfrags")
      | SOME n =>
        (case Symtab.lookup (ssfragDB ()) n of
             NONE => (upd_ssfragDB (Symtab.update(n,ssf)); ssf)
           | SOME _ => (HOL_WARNING "simpLib" "register_frag"
                                    ("Discarding existing entry for "^n);
                        upd_ssfragDB (Symtab.update(n,ssf));
                        ssf))
fun lookup_named_frag n = Symtab.lookup (ssfragDB ()) n
fun all_named_frags() = Symtab.keys (ssfragDB ())

(*---------------------------------------------------------------------------*)
(* Operation on ssfrag values                                                *)
(*---------------------------------------------------------------------------*)

fun name_ss s (SSFRAG_CON f) =
  SSFRAG_CON (updfrag f (Fld #name (SOME s)) $$)

fun rewrites rewrs =
  SSFRAG_CON
    (updfrag empty_frag_data
       (Fld #rewrs (map (fn th => (NONE,th)) rewrs)) $$)

fun rewrites_with_names rewrs =
  SSFRAG_CON
    (updfrag empty_frag_data (Fld #rewrs (map (apfst SOME) rewrs)) $$)

fun dproc_ss dproc =
  SSFRAG_CON (updfrag empty_frag_data (Fld #dprocs [dproc]) $$)

fun ac_ss aclist =
  SSFRAG_CON (updfrag empty_frag_data (Fld #ac aclist) $$)

fun conv_ss conv =
  SSFRAG_CON
    (updfrag empty_frag_data
       (Fld #convs [{thypart=NONE,cd=lift_convdata conv}]) $$)

fun relsimp_ss rsdata =
  SSFRAG_CON (updfrag empty_frag_data (Fld #relsimps [rsdata]) $$)

fun looper_ss looper =
  SSFRAG_CON
    (updfrag empty_frag_data (Fld #loopers [ordinary_looper looper]) $$)

fun solver_ss solver =
  SSFRAG_CON (updfrag empty_frag_data (Fld #unsafe_solvers [solver]) $$)

fun safe_solver_ss solver =
  SSFRAG_CON (updfrag empty_frag_data (Fld #safe_solvers [solver]) $$)

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
      safe_solvers = flatten (map (#safe_solvers o D) s)
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

(* The functional-record-update combinator (boolLib's [Fld] and [$$]) for
   the record inside [SS]: every operation below rebuilds a simpset
   through it, naming only the fields it changes, so that a new field is
   declared here and defaulted in [empty_ss] instead of being re-listed
   at each of them. *)
fun updSS z =
  let
    fun from mk_rewrs history initial_net dprocs travrules limit excluded
             strategy =
      {mk_rewrs=mk_rewrs, history=history, initial_net=initial_net,
       dprocs=dprocs, travrules=travrules, limit=limit, excluded=excluded,
       strategy=strategy}
    (* fields in reverse order to the above *)
    fun from' strategy excluded limit travrules dprocs initial_net history
              mk_rewrs =
      {mk_rewrs=mk_rewrs, history=history, initial_net=initial_net,
       dprocs=dprocs, travrules=travrules, limit=limit, excluded=excluded,
       strategy=strategy}
    fun to f {mk_rewrs,history,initial_net,dprocs,travrules,limit,excluded,
              strategy} =
      f mk_rewrs history initial_net dprocs travrules limit excluded strategy
  in
    FunctionalRecordUpdate.makeUpdate8 (from, from', to)
  end z

fun ssupd_net f (SS s) =
  SS (updSS s (Fld #initial_net (f (#initial_net s))) $$)

val empty_strategy : strategy_data =
  {loopers=[], unsafe_solvers=[], safe_solvers=[], subgoaler=NONE,
   cond_depth=NONE, term_ord=NONE, excl_loopers=empty_excluded}

val empty_ss =
  SS{mk_rewrs=fn x => [x], history=[], limit=NONE, initial_net=empty,
     dprocs=[], travrules=EQ_tr, excluded=empty_excluded,
     strategy=empty_strategy}

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

(* A user key names a theorem in the kernel [Thy$Name] spelling, in the
   [Thy.Name] spelling, or with no theory part at all.  A dot is not
   decisive on its own: a theorem name can carry a numeric suffix, and can
   itself contain a dot.  [unknown_thy] decides what a theory part that is
   not an ancestor of the current theory means; that single question is
   the only one the two readings below differ on. *)
fun parse_simpset_name {unknown_thy} p =
  let
    fun known_thy (thy,name) =
      if mem thy (ancestry "-") then (SOME thy,name)
      else unknown_thy (thy,name)
    fun dotted () =
      case String.fields (equal #".") p of
          [_] => (NONE,p)
        | [s1,s2] =>
            if CharVector.all Char.isDigit s2 then (NONE,p)
            else known_thy (s1,s2)
        | [s1,s2,s3] => (SOME s1,s2 ^ "." ^ s3)
        | _ => raise ERR ("-*", "User key has too many dots")
  in
    case String.fields (equal #"$") p of
        [thy,name] =>
          if thy = "" orelse name = "" then dotted ()
          else known_thy (thy,name)
      | _ => dotted ()
  end

(* [-*] is published with the strict reading and keeps it: a theory part
   that is not an ancestor is a mistake it refuses to guess at. *)
fun munge_simpset_name p =
  parse_simpset_name
    {unknown_thy = fn (thy,_) => raise ERR ("-*", "bad theory name: " ^ thy)}
    p

(* [Excl] has to be able to name what is installed.  A net entry records
   whatever theory its rewrite was named with, and nothing requires that
   theory to be an ancestor of the theory being built: a fragment carrying
   names from an unloaded theory sits in the net all the same, and its
   qualified spelling is what a user writes to exclude it.  So for
   exclusion a theory part whose only fault is not being an ancestor is
   read positionally and matched against the entries.  Nothing else is
   relaxed: a key too many dots deep is still rejected, and a key that no
   entry and no theorem answers to is still the diagnosed typo it was. *)
fun excl_simpset_name p =
  parse_simpset_name {unknown_thy = fn (thy,name) => (SOME thy,name)} p

fun filter_net_by_exclusions (excls : rule_exclusion list) net =
    let
      val pats = map #pattern excls
    in
      Ho_Net.vfilter (fn nd => not (name_match nd pats)) net
    end

(* [Ho_Net.fold'] visits every entry; an exclusion only needs to know
   whether one of them matches, so a local exception stops the traversal at
   the first hit. *)
local exception FoundEntry
in
fun net_exists P net =
  (Ho_Net.fold' (fn entry => fn () => if P entry then raise FoundEntry
                                      else ())
                net ();
   false)
  handle FoundEntry => true
end

(* Only exclusion resolution asks these questions, so they use the reading
   [Excl] answers to rather than the stricter one [-*] parses with. *)
fun net_has_name name net =
  case Lib.total excl_simpset_name name of
      NONE => false
    | SOME pattern => net_exists (fn nd => name_match nd [pattern]) net

fun simpset_has_rule name (SS s) = net_has_name name (#initial_net s)

fun simpset_has_dproc name (SS s) =
  List.exists
    (fn reducer => #name (Traverse.reducer_data reducer) = SOME name)
    (#dprocs s)

(* The historical rewrite exclusion operation also removes decision
   procedures by name.  Treat the two stores as one target here so a rewrite
   and a dproc sharing a name are excluded together, as [ss -* names] has
   always specified.  [pending] holds the rule exclusions that
   [apply_exclusions] has resolved but not yet applied to the net; masking
   them here is what makes deferring the filter invisible. *)
fun simpset_has_rule_target {pending : rule_exclusion list} name
                            (ss as SS s) =
  case pending of
      [] => simpset_has_rule name ss orelse simpset_has_dproc name ss
    | _ =>
      let
        val gone = map #pattern pending
        fun still_there nd = not (name_match nd gone)
      in
        (case Lib.total excl_simpset_name name of
             NONE => false
           | SOME pattern =>
               net_exists (fn nd => name_match nd [pattern] andalso
                                    still_there nd)
                          (#initial_net s))
        orelse
        (not (List.exists (fn e : rule_exclusion => #original e = name)
                          pending) andalso
         simpset_has_dproc name ss)
      end

(* A valid theorem name need not currently be installed in the simpset:
   theory scripts use Excl defensively around a theorem they have just put
   on the goal.  Accept an exact database binding as a rule target, while a
   spelling that denotes neither a binding nor installed strategy remains a
   diagnosed typo.  A name that carries its theory -- in either spelling --
   is one exact lookup; a bare name is sought database-wide, but by the
   exact-name entry point, which is a lookup per theory rather than a
   regexp run over every binding in the database. *)
fun theorem_name_exists original =
  let
    fun bound thy name =
      thy <> "-" andalso isSome (DB.lookup {Thy=thy,Name=name})
    fun anywhere name = not (null (DB.lookup_name name))
  in
    case String.fields (equal #"$") original of
        [thy,name] => bound thy name
      | _ =>
        case String.fields (equal #".") original of
            [name] => anywhere name
          | [thy,name] => bound thy name
          | _ => false
  end
  handle HOL_ERR _ => false

fun dphas_name_from nms reducer =
  case #name (Traverse.reducer_data reducer) of
      SOME name => Lib.mem name nms
    | NONE => false
fun filter_dprocs_by_names nms = List.filter (not o dphas_name_from nms)

(* The one place a rule exclusion is applied.  Its callers -- [-*], which
   parses its own names, the [Excl] resolution, which has already parsed
   them, and history replay, which must not parse them at all -- all
   arrive with the pattern settled, and the recorded [DELETE_EVENT] keeps
   it.  Rebuilding a simpset therefore reruns the very same exclusions,
   rather than re-asking what their names mean in whatever theory context
   the rebuild happens in. *)
fun delete_exclusions (excls : rule_exclusion list) (ss as SS s) =
    if null excls then ss
    else
      SS (updSS s
            (Fld #initial_net
               (filter_net_by_exclusions excls (#initial_net s)))
            (Fld #history (DELETE_EVENT excls :: #history s))
            (Fld #dprocs
               (filter_dprocs_by_names (map #original excls) (#dprocs s)))
            $$)

fun exclusion_of_name p : rule_exclusion =
  {original = p, pattern = munge_simpset_name p}

fun ss -* nms = delete_exclusions (map exclusion_of_name nms) ss
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
  in fn ctxt => fn tm =>
      let val _ = trace(trace_level+2,REDUCE(trace_string1,tm))
          val thm = conv ctxt tm
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

 fun net_add_conv
       {thypart,cd = data as {name,key,trace,conv}:contextual_convdata} =
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
   SS (updSS s (Fld #limit (f (#limit s))) $$)

 fun limit n = fupdlimit (fn _ => SOME n)

val unlimit = fupdlimit (fn _ => NONE)

fun getlimit (SS ss) = #limit ss

fun map_strategy f (SS s) =
  SS (updSS s (Fld #strategy (f (#strategy s))) $$)

(* As [updSS], but for [strategy_data]. *)
fun updstrategy z =
  let
    fun from loopers unsafe_solvers safe_solvers subgoaler cond_depth
             term_ord excl_loopers =
      {loopers=loopers, unsafe_solvers=unsafe_solvers,
       safe_solvers=safe_solvers, subgoaler=subgoaler,
       cond_depth=cond_depth, term_ord=term_ord, excl_loopers=excl_loopers}
    (* fields in reverse order to the above *)
    fun from' excl_loopers term_ord cond_depth subgoaler safe_solvers
              unsafe_solvers loopers =
      {loopers=loopers, unsafe_solvers=unsafe_solvers,
       safe_solvers=safe_solvers, subgoaler=subgoaler,
       cond_depth=cond_depth, term_ord=term_ord, excl_loopers=excl_loopers}
    fun to f {loopers,unsafe_solvers,safe_solvers,subgoaler,cond_depth,
              term_ord,excl_loopers} =
      f loopers unsafe_solvers safe_solvers subgoaler cond_depth term_ord
        excl_loopers
  in
    FunctionalRecordUpdate.makeUpdate7 (from, from', to)
  end z

(* Field updaters for [strategy_data]; every strategy change is expressed
   as a composition of these. *)
fun upd_loopers f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #loopers (f (#loopers s))) $$
fun upd_unsafe_solvers f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #unsafe_solvers (f (#unsafe_solvers s))) $$
fun upd_safe_solvers f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #safe_solvers (f (#safe_solvers s))) $$
fun upd_subgoaler f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #subgoaler (f (#subgoaler s))) $$
fun upd_cond_depth f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #cond_depth (f (#cond_depth s))) $$
fun upd_term_ord f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #term_ord (f (#term_ord s))) $$
fun upd_excl_loopers f (s:strategy_data) : strategy_data =
  updstrategy s (Fld #excl_loopers (f (#excl_loopers s))) $$

fun fupdhistory f (SS s) =
  SS (updSS s (Fld #history (f (#history s))) $$)

fun record_strategy event =
  fupdhistory (fn history => STRATEGY_EVENT event::history)

fun same_looper_id
      (LooperEntry {kind=OrdinaryLooper,name,...})
      (OrdinaryLooper,name') = name = name'
  | same_looper_id (LooperEntry {kind=SplitLooper asm,name,...})
      (SplitLooper asm',name') = asm = asm' andalso name = name'
  | same_looper_id _ _ = false

fun looper_data (LooperEntry data) = data

fun looper_display (LooperEntry {kind=OrdinaryLooper,name,...}) = name
  | looper_display (LooperEntry {kind=SplitLooper asm,name,...}) =
      (if asm then "split_asm " else "split ") ^ name

fun update_looper (looper,[]) = [looper]
  | update_looper (looper,entry::rest) =
      if same_looper_id entry
           (#kind (looper_data looper),#name (looper_data looper))
      then looper::rest
      else entry::update_looper(looper,rest)

fun add_solver (solver : Traverse.ssolver,
                solvers : Traverse.ssolver list) =
  if List.exists (fn {name,...} => name = #name solver) solvers then solvers
  else solvers @ [solver]

fun dedup_solvers solvers = List.foldl add_solver [] solvers

fun strategy_of (SS s) = #strategy s
fun has_looper name ss =
  List.exists
    (fn entry => same_looper_id entry (OrdinaryLooper,name))
    (#loopers (strategy_of ss))
fun has_solver name ss =
  let fun named {name=name',...} = name = name'
  in
    List.exists named (#unsafe_solvers (strategy_of ss)) orelse
    List.exists named (#safe_solvers (strategy_of ss))
  end

(* The single implementation of every strategy change.  The exported
   setters and the [build_from_history] replay both go through it, so the
   simpset a user builds and the one rebuilt from its history cannot
   drift apart. *)
fun apply_strategy_event event =
  map_strategy
    (case event of
         ADD_LOOPER_EVENT looper =>
           upd_loopers (fn ls => update_looper(looper,ls))
       | DEL_LOOPER_EVENT id =>
           upd_loopers (List.filter (fn entry => not (same_looper_id entry id)))
       | SET_LOOPER_EVENT looper => upd_loopers (K [looper])
       | ADD_UNSAFE_SOLVER_EVENT solver =>
           upd_unsafe_solvers (fn ss => add_solver(solver,ss))
       | ADD_SAFE_SOLVER_EVENT solver =>
           upd_safe_solvers (fn ss => add_solver(solver,ss))
       | SET_UNSAFE_SOLVERS_EVENT solvers => upd_unsafe_solvers (K solvers)
       | SET_SAFE_SOLVERS_EVENT solvers => upd_safe_solvers (K solvers)
       | REMOVE_SOLVER_EVENT name =>
           let fun keep {name=name',...} = name <> name'
           in upd_unsafe_solvers (List.filter keep) o
              upd_safe_solvers (List.filter keep)
           end
       | SET_SUBGOALER_EVENT subgoaler => upd_subgoaler (K subgoaler)
       | SET_COND_DEPTH_EVENT cond_depth => upd_cond_depth (K cond_depth)
       | SET_TERM_ORD_EVENT term_ord => upd_term_ord (K term_ord)
       | SET_EXCL_LOOPERS_EVENT excl => upd_excl_loopers (K excl)
       | SET_STRATEGY_EVENT strategy => K strategy)

fun strategy_op event ss =
  apply_strategy_event event ss |> record_strategy event

fun add_looper looper =
  strategy_op (ADD_LOOPER_EVENT (ordinary_looper looper))
fun set_looper looper =
  strategy_op (SET_LOOPER_EVENT (ordinary_looper looper))
fun add_unsafe_solver solver = strategy_op (ADD_UNSAFE_SOLVER_EVENT solver)
fun add_safe_solver solver = strategy_op (ADD_SAFE_SOLVER_EVENT solver)
fun set_unsafe_solvers solvers =
  strategy_op (SET_UNSAFE_SOLVERS_EVENT (dedup_solvers solvers))
fun set_safe_solvers solvers =
  strategy_op (SET_SAFE_SOLVERS_EVENT (dedup_solvers solvers))
fun set_subgoaler subgoaler =
  strategy_op (SET_SUBGOALER_EVENT (SOME subgoaler))
fun set_cond_depth depth = strategy_op (SET_COND_DEPTH_EVENT (SOME depth))
fun set_term_ord term_ord = strategy_op (SET_TERM_ORD_EVENT (SOME term_ord))

(* Deleting an absent looper is a no-op; only the exported [del_looper]
   warns about it. *)
fun has_looper_id id ss =
  List.exists (fn entry => same_looper_id entry id)
    (#loopers (strategy_of ss))

fun del_looper_id_quiet id ss =
  if has_looper_id id ss then strategy_op (DEL_LOOPER_EVENT id) ss else ss

fun del_looper_quiet name = del_looper_id_quiet (OrdinaryLooper,name)

fun del_looper name ss =
  if has_looper name ss then del_looper_quiet name ss
  else (HOL_WARNING "simpLib" "del_looper" ("No looper called " ^ name); ss)

fun remove_solver name ss =
  if has_solver name ss then strategy_op (REMOVE_SOLVER_EVENT name) ss else ss

fun split_looper_id name th =
  (SplitLooper (splitLib.is_asm_split th),name)

fun split_looper_display name th =
  (if splitLib.is_asm_split th then "split_asm " else "split ") ^ name

fun add_split th =
  let val name = splitLib.split_thm_name th
      val (kind,_) = split_looper_id name th
  in
    strategy_op
      (ADD_LOOPER_EVENT
        (LooperEntry
          {kind=kind, name=name,
           apply=K (splitLib.SPLIT_TAC [th])}))
  end

fun del_split name ss =
  let
    val ids =
      if String.isPrefix "split " name then
        [(SplitLooper false,String.extract (name,6,NONE))]
      else if String.isPrefix "split_asm " name then
        [(SplitLooper true,String.extract (name,10,NONE))]
      else [(SplitLooper false,name),(SplitLooper true,name)]
  in
    List.foldl (fn (id,result) => del_looper_id_quiet id result) ss ids
  end

fun splitter_looper ss (asms, goal) =
  let
    val excluded = #excl_loopers (strategy_of ss)
    fun enabled name = not (Binaryset.member (excluded, name))
    fun enabled_named (name, th) = enabled (split_looper_display name th)
    val persistent =
      splitLib.named_split_thms ()
      |> List.filter enabled_named
      |> map #2
    fun type_enabled ty =
      let
        val {Thy,Tyop,...} = dest_thy_type ty
        val full = KernelSig.name_toString {Thy=Thy, Name=Tyop}
      in
        enabled ("split.case " ^ full) andalso
        enabled ("split.case " ^ Tyop)
      end
    val datatype_rules =
      splitLib.goal_split_rule_groups (goal :: asms)
      |> List.filter (type_enabled o #1)
      |> map #2
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

datatype exclusion_target =
    ExcludeRule of rule_exclusion
  | ExcludeLooper of looper_kind * string
  | ExcludeSolver of string
  | ExcludeSplits of string list
  | ExcludeCase of string

fun strip_namespace prefix name =
  if String.isPrefix prefix name
  then SOME (String.extract (name,size prefix,NONE))
  else NONE

fun ordinary_looper_exists name ss =
  has_looper_id (OrdinaryLooper,name) ss

(* Membership in the split and case display spaces, rather than the lists
   themselves: every Excl asks these questions, and enumerating the case
   displays means walking all of [TypeBase.elts()].  The display prefix
   settles almost every name before either store is touched. *)
fun split_display_exists ss display =
  (String.isPrefix "split " display orelse
   String.isPrefix "split_asm " display) andalso
  let
    fun is_local (entry as LooperEntry {kind=SplitLooper _,...}) =
          looper_display entry = display
      | is_local _ = false
    fun is_persistent (name,th) = split_looper_display name th = display
  in
    List.exists is_local (#loopers (strategy_of ss)) orelse
    List.exists is_persistent (splitLib.named_split_thms ())
  end

val case_prefix = "split.case "

fun case_display_exists display =
  String.isPrefix case_prefix display andalso
  let
    val wanted = String.extract (display,size case_prefix,NONE)
    fun names tyinfo =
      let val (thy,tyop) = TypeBasePure.ty_name_of tyinfo
      in
        wanted = tyop orelse
        wanted = KernelSig.name_toString {Thy=thy,Name=tyop}
      end
  in
    List.exists names (TypeBase.elts ())
  end

(* A namespaced Excl says which kind of target is meant, so matching
   nothing there is a diagnosed typo -- [no_target].  An unqualified one is
   written defensively often enough -- around a theorem that may not be
   installed, or naming a conversion or decision procedure that was never a
   simpset entry at all -- that matching nothing is reported and ignored
   instead of aborting the tactic.  A name that matches several kinds stays
   an error either way: there is no way to guess which was meant. *)
fun no_target original =
  raise ERR ("process_tags", "Excl did not match " ^ original)

fun ambiguous_target original =
  raise ERR
    ("process_tags",
     "Excl name " ^ original ^
     " is ambiguous; qualify it with rule:, looper:, solver:, " ^
     "split:, or case:")

fun optional_target {report} original [] =
      (if report then
         HOL_WARNING "simpLib" "process_tags"
                     ("Ignoring Excl that matched nothing: " ^ original)
       else ();
       NONE)
  | optional_target _ _ [target] = SOME target
  | optional_target _ original _ = ambiguous_target original

(* A rule name is parsed once, here, and the pattern travels with the
   target: neither [apply_exclusion] nor the history replay that follows
   it gets to parse the name a second time. *)
fun resolve_exclusion {report,pending} ss original =
  let
    fun rule_target name =
      case Lib.total excl_simpset_name name of
          NONE => NONE
        | SOME pattern =>
            if simpset_has_rule_target {pending=pending} name ss orelse
               theorem_name_exists name
            then SOME {original = name, pattern = pattern}
            else NONE
  in
  case strip_namespace "rule:" original of
      SOME name =>
        (case rule_target name of
             SOME excl => SOME (ExcludeRule excl)
           | NONE => no_target original)
    | NONE =>
      case strip_namespace "looper:" original of
          SOME name =>
            if ordinary_looper_exists name ss
            then SOME (ExcludeLooper (OrdinaryLooper,name))
            else no_target original
        | NONE =>
          case strip_namespace "solver:" original of
              SOME name =>
                if has_solver name ss then SOME (ExcludeSolver name)
                else no_target original
            | NONE =>
              case strip_namespace "split:" original of
                  SOME name =>
                    let
                      val candidates = ["split " ^ name,"split_asm " ^ name]
                      val matches =
                        List.filter (split_display_exists ss) candidates
                    in
                      if null matches then no_target original
                      else SOME (ExcludeSplits matches)
                    end
                | NONE =>
                  case strip_namespace "case:" original of
                      SOME name =>
                        let val display = case_prefix ^ name
                        in
                          if case_display_exists display
                          then SOME (ExcludeCase display)
                          else no_target original
                        end
                    | NONE =>
                      let
                        val targets =
                          (case rule_target original of
                               SOME excl => [ExcludeRule excl]
                             | NONE => []) @
                          (if ordinary_looper_exists original ss
                           then [ExcludeLooper (OrdinaryLooper,original)]
                           else []) @
                          (if has_solver original ss
                           then [ExcludeSolver original] else []) @
                          (if split_display_exists ss original
                           then [ExcludeSplits [original]] else []) @
                          (if case_display_exists original
                           then [ExcludeCase original] else [])
                      in
                        optional_target {report=report} original targets
                      end
  end

fun exclude_split_display (display,ss) =
  let
    val ids =
      List.mapPartial
        (fn entry as LooperEntry {kind=SplitLooper _,name,...} =>
              if looper_display entry = display
              then SOME (#kind (looper_data entry),name) else NONE
          | _ => NONE)
        (#loopers (strategy_of ss))
    val without_local =
      List.foldl (fn (id,result) => del_looper_id_quiet id result) ss ids
  in
    map_strategy
      (upd_excl_loopers (fn excluded => Binaryset.add (excluded,display)))
      without_local
  end

fun apply_exclusion (target,ss) =
  case target of
      ExcludeRule excl => delete_exclusions [excl] ss
    | ExcludeLooper id => del_looper_id_quiet id ss
    | ExcludeSolver solver => remove_solver solver ss
    | ExcludeSplits displays => List.foldl exclude_split_display ss displays
    | ExcludeCase display =>
        map_strategy
          (upd_excl_loopers
             (fn excluded => Binaryset.add (excluded,display))) ss

(* Each rule exclusion filters the whole rewrite net, so the resolved
   exclusions are collected and handed to [delete_exclusions] once.  They
   carry their patterns, so the batch is applied without any name being
   parsed twice.  The exclusions collected so far go back into
   [resolve_exclusion], which is what makes the deferral invisible: a later
   name still resolves against the simpset it would have seen had each
   exclusion been applied where it was written.  The other kinds touch
   disjoint parts of the simpset, so their order relative to the deferred
   filter -- in the simpset and in its history -- does not matter. *)
fun apply_exclusions {report} ss names =
  let
    fun step (name,(ss,pending)) =
      case resolve_exclusion {report=report,pending=pending} ss name of
          NONE => (ss,pending)
        | SOME (ExcludeRule excl) => (ss,excl::pending)
        | SOME target => (apply_exclusion (target,ss),pending)
    val (excluded,pending) = List.foldl step (ss,[]) names
  in
    delete_exclusions (List.rev pending) excluded
  end

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
   SS (updSS s
         (Fld #history (ADDWEAKENER wd :: #history s))
         (Fld #travrules
            (merge_travrules [#travrules s,wk_mk_travrules(rels,congs)]))
         (Fld #dprocs (#dprocs s @ [dp]))
         $$)

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

   fun apply {solver,conv,context,stack,
              relation = (relation,_),...} t = let
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
   val strategy =
     #strategy sset
       |> upd_loopers (fn ls => List.foldl update_looper ls (#loopers ssf))
       |> upd_unsafe_solvers
            (fn ss => List.foldl add_solver ss (#unsafe_solvers ssf))
       |> upd_safe_solvers
            (fn ss => List.foldl add_solver ss (#safe_solvers ssf))
 in
   SS (updSS sset
         (Fld #mk_rewrs mk_rewrs)
         (Fld #history (ADDFRAG f :: history))
         (Fld #initial_net net)
         (Fld #dprocs new_dprocs)
         (Fld #travrules
            (merge_travrules
               (travrules::mk_travrules relations congs::reltravs)))
         (Fld #strategy strategy)
         $$)
 end

val mk_simpset = foldl (fn (f,ss) => ss ++ f) empty_ss

fun set_mk_rewrs mk_rewrs (SS s) =
  SS (updSS s (Fld #mk_rewrs mk_rewrs) $$)

fun build_from_history h0 =
    let
      fun foldthis (hi, ss) =
          case hi of
              ADDFRAG sf => ss ++ sf
            | DELETE_EVENT excls => delete_exclusions excls ss
            | ADDWEAKENER wd => add_weakener wd ss
            | STRATEGY_EVENT event => strategy_op event ss
            | SET_MK_REWRS mk_rewrs =>
                set_mk_rewrs mk_rewrs ss
                |> fupdhistory (fn h => SET_MK_REWRS mk_rewrs::h)
    in
      List.foldl foldthis empty_ss (List.rev h0)
    end

fun setexcluded e (SS s) =
  SS (updSS s (Fld #excluded e) $$)

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
    val strategy = upd_loopers (K []) (#strategy s)
    (* Rules and fragment loopers are dropped; every other strategy field is
       retained as one value, so adding a field cannot make replay lose it. *)
    val history =
      [STRATEGY_EVENT (SET_STRATEGY_EVENT strategy),
       SET_MK_REWRS (#mk_rewrs s)]
  in
    SS (updSS s
          (Fld #history history)
          (Fld #initial_net empty)
          (Fld #dprocs [])
          (Fld #travrules EQ_tr)
          (Fld #strategy strategy)
          $$)
  end

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

 exception CONVNET of net;

 (* Invocation-supplied bounded rewrites are decoded once, then compiled
    against each marker-adjusted simpset without allocating fresh controls. *)
 type prepared_rewrites = controlled_thm list

 fun prepare_rewrites thms : prepared_rewrites =
   map dest_tagged_rewrite thms

 fun source_thms (prepared : prepared_rewrites) = map #1 prepared

 fun prepared_convdata mk_rewrs (prepared : prepared_rewrites) =
   let
     val rwts0 = flatten (map mk_rewrs prepared)
     val rwts =
       map (fn th =>
               (SOME {Thy = "", Name = "rewrite: prepared context"}, th))
           rwts0
   in
     List.mapPartial mk_rewr_convdata rwts
   end

 fun rewriter_for_ss_prepared
       (SS{mk_rewrs,travrules,initial_net,...}) prepared = let
   val prepared_net =
     net_add_convs initial_net (prepared_convdata mk_rewrs prepared)
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
   fun apply {solver,conv,context,stack,cond_depth,term_ord,relation} tm = let
     val net = (raise context) handle CONVNET net => net
   in
     tryfind
       (fn {ci = {conval,...},...} =>
           conval {solver=solver, stack=stack, cond_depth=cond_depth,
                   term_ord=term_ord} tm)
             (lookup tm net)
   end
   in CONTEXT_REDUCER
        {name=SOME"rewriter_for_ss", addcontext=addcontext, apply=apply,
         initial=CONVNET prepared_net}
   end;

 fun traversedata_for_ss_prepared
       (ss as (SS ssdata)) (prepared : prepared_rewrites)
       : Traverse.traverse_data =
   let
     val dprocs =
       if null prepared then #dprocs ssdata
       else
         map (Traverse.addctxt (source_thms prepared)) (#dprocs ssdata)
   in
      {rewriters=[rewriter_for_ss_prepared ss prepared],
       dprocs=dprocs,
       relation= boolSyntax.equality,
       travrules= #travrules ssdata,
       limit = #limit ssdata}
   end;

 (* The traversal-strategy settings that traverse_data does not carry.
    They are kept apart so that traversedata_for_ss can stay the record
    the published signature promises. *)
 fun traverseconfig_for_ss (SS ssdata) : Traverse.traverse_config =
   let
     val strategy = #strategy ssdata
   in
      {subgoaler= #subgoaler strategy,
       solvers= #unsafe_solvers strategy,
       cond_depth= #cond_depth strategy,
       term_ord= #term_ord strategy}
   end;

 fun xtraversedata_for_ss_prepared ss prepared : Traverse.xtraverse_data =
   (traversedata_for_ss_prepared ss prepared, traverseconfig_for_ss ss);

 fun traversedata_for_ss ss = traversedata_for_ss_prepared ss [];
 fun xtraversedata_for_ss ss = xtraversedata_for_ss_prepared ss [];

 fun SIMP_QCONV_WITH_PREPARED_CONTEXT
       ss prepared reducer_context solver_context =
   Traverse.TRAVERSE_WITH_CONTEXT
     (xtraversedata_for_ss_prepared ss prepared)
     {reducer_context=reducer_context,solver_context=solver_context};

 fun SIMP_QCONV ss thms =
   SIMP_QCONV_WITH_PREPARED_CONTEXT ss [] thms [];

val Cong   = markerLib.Cong
val Split  = markerLib.Split
val AC     = markerLib.AC;
val Excl   = markerLib.Excl
val ExclSF = markerLib.ExclSF
val Req0   = markerLib.mk_Req0
val ReqD   = markerLib.mk_ReqD

val is_AC = markerLib.is_AC
val is_Cong = markerLib.is_Cong
val is_Split = markerLib.is_Split

local open markerLib
in
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

(* A [Split] marker whose theorem cannot be turned into a split rule --
   one with no database name to build a looper name from, or one that is
   not shaped like a split rule at all -- drops the marker instead of
   aborting.  [process_tags] is applied to the goal's own assumptions as
   well as to a rule list (see [counted_psr] and the implication rebuild
   in [GEN_GLOBAL_SIMP_TAC]), and there a marker-headed assumption is a
   term the user is reasoning about rather than an instruction to the
   simplifier; the tactics that scan assumptions are documented never to
   fail.  Where the marker was written explicitly the drop is reported,
   because silently ignoring a rule that was asked for is worse than a
   warning. *)
fun add_split_marker report th ss =
    add_split (destSplit th) ss
    handle HOL_ERR e =>
      (if report then
         HOL_WARNING "simpLib" "process_tags"
                     ("Ignoring unusable Split rule: " ^ message_of e)
       else ();
       ss)

fun process_tags0 {report} ss thl =
    let
      val (Congs,rst) = Lib.partition is_Cong thl
      val (Splits,rst) = Lib.partition is_Split rst
      val (ACs,rst) = Lib.partition is_AC rst
      val (excludes, exclfrags, rst) = extract_excls ([],[],[]) rst
      val (frags, rst) = extract_frags ([],[]) rst
    in
      (* When no marker matched, the argument simpset is returned as it
         stands rather than rebuilt.  [GEN_GLOBAL_SIMP_TAC]'s traversal
         cache tests its key with [Portable.pointer_eq], so physical
         identity here -- not merely an equal simpset -- is what keeps
         that tactic's assumption scan linear. *)
      if null Congs andalso null Splits andalso null ACs andalso
         null excludes andalso null frags andalso null exclfrags
      then (ss,thl)
      else
        let
          val base =
            remove_ssfrags exclfrags ss handle Conv.UNCHANGED => ss
          val cong_ac =
            SSFRAG_CON
              (updfrag empty_frag_data
                 (Fld #name (SOME "Cong and/or AC"))
                 (Fld #ac (map unAC ACs))
                 (Fld #congs (map (normCong o unCong) Congs)) $$)
          (* Cong/AC is named but never user-excludable; SF-derived frags
             go through force_add so they override any active exclusion. *)
          val withCongAc = base ++ cong_ac
          val withFrags =
            List.foldl (fn (f,ss) => force_add ss f) withCongAc frags
          val withSplits =
            List.foldl (fn (th,ss) => add_split_marker report th ss)
                       withFrags Splits
          val invocation =
            apply_exclusions {report=report} withSplits excludes
        in
          (invocation, rst)
        end
    end

(* [process_tags] handles a rule list the user wrote; [process_asm_tags]
   handles theorems taken from the goal's assumptions, where a marker is
   an accident of the terms being reasoned about. *)
fun process_tags ss thl = process_tags0 {report=true} ss thl
fun process_asm_tags ss thl = process_tags0 {report=false} ss thl

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

fun simp_conv_with_prepared_context
      ss prepared reducer_context solver_context =
  TRY_CONV
    (SIMP_QCONV_WITH_PREPARED_CONTEXT
       ss prepared reducer_context solver_context)

fun simp_rule_with_prepared_context
      ss prepared reducer_context solver_context =
  CONV_RULE
    (simp_conv_with_prepared_context
       ss prepared reducer_context solver_context)

fun final_solver_tac prepared mode ss reducer_context solver_context =
  let
    val s = strategy_of ss
    val solvers =
      if #safe mode then #safe_solvers s else #unsafe_solvers s
    val prover_ctxt =
      {stack=[], context_thms=reducer_context @ solver_context,
       recurse=QCONV
         (simp_conv_with_prepared_context
            ss prepared reducer_context solver_context)}
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

fun looper_tac ss =
  let
    val s = strategy_of ss
    fun enabled entry =
      not
        (Binaryset.member (#excl_loopers s,looper_display entry))
    fun apply (LooperEntry {apply,...}) g =
      apply ss g
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

fun gen_simp_tac_with_prepared
      prepared solver_context (mode : simp_mode) ss ths =
  fn g =>
    let
      val rounds = ref (getlimit ss)
      fun start recur =
        let
          fun main tagged_thms =
            let
              val (invocation_ss,context_thms) =
                process_tags ss tagged_thms
              val rewr_tac =
                CONV_TAC
                  (simp_conv_with_prepared_context
                     invocation_ss prepared context_thms solver_context)
              val solve_tac =
                final_solver_tac prepared mode invocation_ss
                                 context_thms solver_context
              val loop_tac =
                bounded_looper rounds (looper_tac invocation_ss)
            in
              rewr_tac THEN
              (solve_tac ORELSE
               TRY (loop_tac THEN_LT ALLGOALS (recur main)))
            end
        in
          main
        end
    in
      markerLib.process_taclist_then_recur {arg=ths} start g
    end

fun gen_simp_tac solver_context =
  gen_simp_tac_with_prepared [] solver_context

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

fun popper_of (cfg : simptac_config) =
    if #oldestfirst cfg then pop_last_assum else pop_assum

fun psr (cfg : simptac_config) ss =
    popper_of cfg
      (fn th => ASSUM_LIST (fn asms => stdcon cfg (SIMP_RULE ss asms th)))

fun allasms cfg ss (g as (asl,_)) = ntac (length asl) (psr cfg ss) g

type xsimptac_config =
     {base : simptac_config, concl_in_fixpoint : bool, imp_rebuild : bool}

fun same_goals (goals1,goals2) = boolSyntax.goals_eq goals1 goals2

(* Apply a continuation independently to annotated goals, retaining all
   validation functions. *)
fun map_annotated next annotated =
    let
      val results = map (fn (g,state) => next state g) annotated
      val output = List.concat (map #1 results)
      val validations = map #2 results
      val lengths = map (length o #1) results
      val validate = mapshape lengths validations
    in
      (output,validate)
    end

fun bind_annotated (annotated,validation) next =
    let val (output,validate) = map_annotated next annotated
    in (output,validation o validate)
    end

fun continue_annotated (annotated,validation) next =
    let
      fun tag_result state g =
        let val (goals,validate) = next state g
        in (map (fn goal => (goal,())) goals,validate)
        end
      val (tagged,validate) = map_annotated tag_result annotated
    in
      (map #1 tagged,validation o validate)
    end

(* Continue from an unannotated tactic result. *)
fun then_annotated (goals,validation) next =
    continue_annotated (map (fn g => (g,())) goals,validation) (fn () => next)

fun rotate_assumption cfg =
    popper_of cfg (BF_ASSUME_TAC (not (#oldestfirst cfg)))

fun counted_psr cfg ss prepared solver_context g =
    let
      (* [simplify] runs inside a callback, so what it learns about the
         assumption is smuggled out through this cell. *)
      val outcome = ref (NONE : {changed:bool, expected:goal list} option)
      fun simplify th =
        ASSUM_LIST
          (fn asms => fn popped_goal =>
             let
               val (invocation_ss,reducer_context) =
                 process_asm_tags ss asms
               val simplified =
                 simp_rule_with_prepared_context
                   invocation_ss prepared reducer_context solver_context th
               val ordinary =
                 BF_ASSUME_TAC (not (#oldestfirst cfg)) simplified popped_goal
               val _ =
                 outcome :=
                   SOME {changed=not (aconv (concl th) (concl simplified)),
                         expected= #1 ordinary}
             in
               stdcon cfg simplified popped_goal
             end)
      val (goals,validation) = popper_of cfg simplify g
      val {changed,expected} =
        case !outcome of
            SOME outcome => outcome
          | NONE => raise ERR ("counted_psr", "missing assumption")
      val structural = not (same_goals (goals,expected))
      val info = {changed=changed orelse structural,
                  structural=structural}
    in
      (map (fn goal => (goal,info)) goals,validation)
    end

fun counted_pass cfg ss prepared solver_context initial_k (g as (asl,_)) =
    let
      val n = length asl
      val initial =
        {last= ~1, structural=false, k=initial_k, index=0}
      fun loop state goal =
        if #index state = n then ([(goal,state)],hd)
        else
          let
            val step =
              if #k state = 0 then
                let val (goals,validation) = rotate_assumption cfg goal
                    val info = {changed=false,structural=false}
                in (map (fn g => (g,info)) goals,validation)
                end
              else counted_psr cfg ss prepared solver_context goal
            fun next {changed,structural} =
              let
                val k =
                  if changed then ~1
                  else if #k state < 0 then ~1
                  else Int.max (0,#k state - 1)
                val state' =
                  {last=if changed then #index state else #last state,
                   structural= #structural state orelse structural,
                   k=k, index= #index state + 1}
              in
                loop state'
              end
          in
            bind_annotated step next
          end
    in
      loop initial g
    end

fun GEN_GLOBAL_SIMP_TAC mode
      ({base,concl_in_fixpoint,imp_rebuild} : xsimptac_config) ss0 =
    markerLib.mk_require_tac (
      markerLib.ABBRS_THEN (
        markerLib.LLABEL_RES_THEN (
          fn thl =>
             let
               val (ss1,thl') = process_tags ss0 thl
               val prepared = prepare_rewrites thl'
               val solver_context = source_thms prepared
               (* Each local marker-adjusted simpset compiles these prepared
                  rules while retaining their invocation-wide controls. *)
               val ss = ss1
               val conclusion_tac =
                 gen_simp_tac_with_prepared
                   prepared solver_context mode ss []

               fun strip_implications (g as (_,w)) =
                 if can boolSyntax.dest_imp_only w then
                   (DISCH_TAC THEN strip_implications) g
                 else ALL_TAC g

               val pop_head_mp = POP_ASSUM MP_TAC

               (* The scan below asks its question of every suffix of the
                  assumption list, and compiling the traversal state costs
                  a pass over the invocation's rules.  Markers among the
                  assumptions are the exception, so the suffixes almost
                  always present the same simpset and get the same state
                  back; the state is a function of that simpset and of the
                  prepared rules alone, so one built for an earlier suffix
                  serves a later one and the scan stays linear.

                  The key test is [Portable.pointer_eq], so the hits
                  depend on [process_tags0] handing back its argument
                  simpset itself on the marker-free path.  A version that
                  rebuilt the simpset unconditionally would turn every hit
                  into a miss and make this scan quadratic, with no test
                  failing. *)
               val traversal_cache = ref NONE
               fun traversal_state invocation_ss =
                 let
                   fun build () =
                     let
                       val data =
                         xtraversedata_for_ss_prepared invocation_ss prepared
                     in
                       traversal_cache := SOME (invocation_ss,data);
                       data
                     end
                 in
                   case !traversal_cache of
                       SOME (cached_ss,data) =>
                         if Portable.pointer_eq (cached_ss,invocation_ss)
                         then data else build ()
                     | NONE => build ()
                 end

               (* [outer] is a suffix of the assumption list and [assumed]
                  the matching suffix of its theorems, so that the scan
                  does not re-[ASSUME] the tail it is about to walk. *)
               fun find_rebuild nested (outer,assumed) count =
                 case (outer,assumed) of
                     (a::rest, _::assumed_rest) =>
                       let
                         val target = mk_imp (a,nested)
                         val (invocation_ss,reducer_context) =
                           process_asm_tags ss assumed_rest
                         val root_rewrite =
                           Traverse.ROOT_REWRITE_WITH_CONTEXT
                             (traversal_state invocation_ss)
                       in
                         case SOME
                                (root_rewrite
                                   {reducer_context=reducer_context,
                                    solver_context=solver_context} target)
                              handle HOL_ERR _ => NONE
                                   | Conv.UNCHANGED => NONE of
                             SOME eq => SOME (count,target,eq)
                           | NONE =>
                               find_rebuild target (rest,assumed_rest)
                                            (count + 1)
                       end
                   | _ => NONE

               fun fixpoint k goal =
                 let
                   val pass as (annotated,validation) =
                     counted_pass base ss prepared solver_context k goal
                   val unchanged =
                     same_goals (map #1 annotated,[goal])
                   fun clear_change state =
                     if unchanged then
                       {last= ~1,structural=false,k= #k state,
                        index= #index state}
                     else state
                   val pass' =
                     (map (fn (g,state) => (g,clear_change state)) annotated,
                      validation)
                 in
                   continue_annotated pass' after_pass
                 end

               and after_pass state goal =
                 if concl_in_fixpoint then
                   let
                     val result as (goals,_) = conclusion_tac goal
                     fun continue next = then_annotated result next
                   in
                     if not (same_goals (goals,[goal])) then
                       continue (fixpoint ~1)
                     else if #structural state then
                       continue (fixpoint ~1)
                     else if #last state > 0 then
                       continue (fixpoint (#last state))
                     else if imp_rebuild then continue rebuild
                     else result
                   end
                 else if #structural state then fixpoint ~1 goal
                 else if #last state > 0 then fixpoint (#last state) goal
                 else final_conclusion goal

               and final_conclusion goal =
                 let
                   val result = conclusion_tac goal
                 in
                   if imp_rebuild then then_annotated result rebuild
                   else result
                 end

               and rebuild (goal as (asl,w)) =
                 case find_rebuild w (asl,map ASSUME asl) 1 of
                     NONE => ALL_TAC goal
                   | SOME (count,target,eq) =>
                       let
                         val _ = aconv (lhs (concl eq)) target orelse
                           raise ERR ("GEN_GLOBAL_SIMP_TAC",
                                      "bad root rewrite")
                       in
                         (ntac count pop_head_mp THEN
                          CONV_TAC (K eq) THEN strip_implications THEN
                          fixpoint ~1) goal
                       end
             in
               fixpoint ~1
             end
        )
      )
    )

fun global_simp_tac cfg =
    GEN_GLOBAL_SIMP_TAC {safe=false}
      {base=cfg,concl_in_fixpoint=false,imp_rebuild=false}





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
        (updfrag empty_frag_data
           (Fld #name (SOME ("Datatype " ^ tyname)))
           (Fld #convs
              (map
                (fn c => {thypart=SOME thy,cd=lift_convdata c}) convs))
           (Fld #rewrs rewrs) $$)
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

val reducer_data = Traverse.reducer_data

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
      val {thypart,cd={name,key,...} : contextual_convdata} = tcd
    in
      (thypart,name,Option.map #2 key)
    end

fun pp_ssfrag (SSFRAG_CON {name,convs,rewrs,ac,dprocs,congs,...}) =
 let open Portable smpp
     val name = (case name of SOME s => s | NONE => "<anonymous>")
     val convs = map dest_convdata convs
     val dps = case merge_names (map (#name o reducer_data) dprocs)
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

fun pp_simpset (ss as SS {initial_net,strategy,...}) =
  let
    val {loopers,unsafe_solvers,safe_solvers,...} = strategy
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
    val looper_names = map looper_display loopers
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
