structure clasetLib :> clasetLib =
struct

open Abbrev HolKernel boolLib

type rulekind = clasetRules.rulekind
type rulespec = clasetRules.rulespec
type tag = clasetRules.tag
type brl = clasetRules.brl
type info = clasetRules.info

local
  open clasetRules
in

type net_entry = tag * brl
type netpair = net_entry clasetNet.net * net_entry clasetNet.net

(* [info] is the declaration's canonical rule forms, which [make_rule_decl]
   already derived -- with real kernel inferences -- when the rule was
   declared.  Carrying it through retrieval is what keeps an engine from
   deriving it again for every rule that matches a goal. *)
type aesop_rule =
  {name : string, spec : rulespec, thm : thm, info : info}
type aentry = {tag : tag, rule : aesop_rule}
type aesop_index =
  {target : aentry clasetNet.net, hyp : aentry clasetNet.net}

datatype claset =
  CS of {decls : decls,
         safe_wrappers : (string * NTactical.wrapper) list,
         unsafe_wrappers : (string * NTactical.wrapper) list,
         safe0_netpair : netpair,
         safep_netpair : netpair,
         unsafe_netpair : netpair,
         dup_netpair : netpair,
         aesop_index : aesop_index,
         norm_decls : decl list}

type claset_part = netpair

datatype part = Safe0Part | SafePPart | UnsafePart | DupPart

(* Everything a claset derives from its declarations -- the four classical
   netpairs, the aesop index and the Norm list -- travels as one record,
   which is also what [add_decl] and [delete_decl] thread.  Clasets are
   built through [mk_cs] alone, so a further derived component is added
   here and in those two functions rather than at every rebuild site. *)
type cs_index =
  {safe0 : netpair, safep : netpair, unsafe : netpair, dup : netpair,
   aesop_index : aesop_index, norm_decls : decl list}

type cs_wrappers =
  (string * NTactical.wrapper) list * (string * NTactical.wrapper) list

val empty_netpair = (clasetNet.empty, clasetNet.empty)
val empty_aesop_index =
  {target = clasetNet.empty, hyp = clasetNet.empty}

val empty_index : cs_index =
  {safe0 = empty_netpair, safep = empty_netpair, unsafe = empty_netpair,
   dup = empty_netpair, aesop_index = empty_aesop_index, norm_decls = []}

fun mk_cs decls ((safe_wrappers, unsafe_wrappers) : cs_wrappers)
  ({safe0, safep, unsafe, dup, aesop_index, norm_decls} : cs_index) =
  CS {decls = decls,
      safe_wrappers = safe_wrappers,
      unsafe_wrappers = unsafe_wrappers,
      safe0_netpair = safe0,
      safep_netpair = safep,
      unsafe_netpair = unsafe,
      dup_netpair = dup,
      aesop_index = aesop_index,
      norm_decls = norm_decls}

fun decls_of (CS {decls, ...}) = decls

fun wrappers_of (CS {safe_wrappers, unsafe_wrappers, ...}) =
  (safe_wrappers, unsafe_wrappers)

fun index_of (CS {safe0_netpair, safep_netpair, unsafe_netpair,
                  dup_netpair, aesop_index, norm_decls, ...}) =
  {safe0 = safe0_netpair, safep = safep_netpair, unsafe = unsafe_netpair,
   dup = dup_netpair, aesop_index = aesop_index, norm_decls = norm_decls}

val empty_cs = mk_cs empty_decls ([], []) empty_index

fun rule_brl kind th = (is_elim kind, th)

fun indexed_brl is_elim tag th =
  let
    val kind = if is_elim then Elim else Intro
    val form = canonical_form_of kind th
    val pat = rule_index_of kind form
  in
    ({pat = pat, patvars = #patvars form}, (tag, (is_elim, th)))
  end

fun insert_brl is_elim tag th (inet, enet) =
  let
    val entry = indexed_brl is_elim tag th
  in
    if is_elim then (inet, clasetNet.insert entry enet)
    else (clasetNet.insert entry inet, enet)
  end

fun insert_rl kind index (rl : rl) netpair =
  let
    val (th, swapped) = rl
    val is_elim' = is_elim kind
    val tag = {weight = subgoals_of (is_elim', th),
               index = 2 * index + 1}
    val netpair' = insert_brl is_elim' tag th netpair
  in
    case swapped of
        NONE => netpair'
      | SOME th' =>
          let
            val tag' = {weight = subgoals_of (true, th'),
                        index = 2 * index}
          in
            insert_brl true tag' th' netpair'
          end
  end

fun delete_tagged_rule index netpair =
  let
    fun keep ({index = index', ...}, _) = index <> index'
  in
    (clasetNet.vfilter keep (#1 netpair),
     clasetNet.vfilter keep (#2 netpair))
  end

fun delete_rl index netpair =
  delete_tagged_rule (2 * index + 1)
    (delete_tagged_rule (2 * index) netpair)

(* Norm rules are not indexed: the normalisation phase takes the whole list
   (see [norm_rules]), so an entry here would be retrieved, ordered and
   deduplicated on every goal expansion only to be filtered out again. *)
fun insert_aesop_decl (decl : decl)
  ({target, hyp} : aesop_index) =
  let
    val {name, spec, tag, orig, info} = decl
    val kind = #kind spec
    val form = canonical_form_of kind orig
    val indexed =
      ({pat = rule_index_of kind form, patvars = #patvars form},
       {tag = tag,
        rule = {name = name, spec = spec, thm = orig, info = info}})
  in
    if kind = Intro then
      {target = clasetNet.insert indexed target, hyp = hyp}
    else
      {target = target, hyp = clasetNet.insert indexed hyp}
  end

fun delete_aesop_decl (decl : decl)
  ({target, hyp} : aesop_index) =
  let
    val {index, ...} = #tag decl
    fun keep ({tag = {index = index', ...}, ...} : aentry) =
      index <> index'
  in
    {target = clasetNet.vfilter keep target,
     hyp = clasetNet.vfilter keep hyp}
  end

(* Norm rules never enter the four classical netpairs, so the claset keeps
   them as an ordered list instead -- the aesop normalisation phase wants
   all of them, not the ones matching one goal.  Held in [dest_decls] order
   so that [norm_rules] agrees with filtering [rules_of], which is the
   tiebreak the penalty sort relies on. *)
fun insert_norm_decl (decl : decl) decls =
  let
    fun insert [] = [decl]
      | insert (current :: rest) =
          case decl_order (decl, current) of
              GREATER => current :: insert rest
            | _ => decl :: current :: rest
  in
    insert decls
  end

fun add_decl (decl : decl)
  {safe0, safep, unsafe, dup, aesop_index, norm_decls} =
  let
    val {spec, tag = {index, ...}, info, ...} = decl
    val kind = #kind spec
  in
    if kind = Norm then
      {safe0 = safe0, safep = safep, unsafe = unsafe, dup = dup,
       aesop_index = aesop_index,
       norm_decls = insert_norm_decl decl norm_decls}
    else
      let
        val aesop_index = insert_aesop_decl decl aesop_index
      in
        if kind = Forward then
          {safe0 = safe0, safep = safep, unsafe = unsafe, dup = dup,
           aesop_index = aesop_index, norm_decls = norm_decls}
        else if #safe spec then
          (case safe_class_of spec info of
              SOME Safe0 =>
                {safe0 = insert_rl kind index (#rl info) safe0,
                 safep = safep, unsafe = unsafe, dup = dup,
                 aesop_index = aesop_index, norm_decls = norm_decls}
            | SOME SafeP =>
                {safe0 = safe0,
                 safep = insert_rl kind index (#rl info) safep,
                 unsafe = unsafe, dup = dup,
                 aesop_index = aesop_index, norm_decls = norm_decls}
            | NONE => raise Fail "safe rule has no safe classification")
        else
          {safe0 = safe0, safep = safep,
           unsafe = insert_rl kind index (#rl info) unsafe,
           dup = insert_rl kind index (#dup_rl info) dup,
           aesop_index = aesop_index, norm_decls = norm_decls}
      end
  end

(* A declaration is retracted by its tag index, which is unique across the
   claset, so every component is filtered without consulting the kind. *)
fun delete_decl (decl : decl)
  ({safe0, safep, unsafe, dup, aesop_index, norm_decls} : cs_index) =
  let
    val {index, ...} = #tag decl
    fun keep ({tag = {index = index', ...}, ...} : decl) = index <> index'
  in
    {safe0 = delete_rl index safe0,
     safep = delete_rl index safep,
     unsafe = delete_rl index unsafe,
     dup = delete_rl index dup,
     aesop_index = delete_aesop_decl decl aesop_index,
     norm_decls = List.filter keep norm_decls}
  end

fun make_rule_decl spec (name, th) =
  let
    val info = ext_info spec th
    val weight = subgoals_of (rule_brl (#kind spec) (#1 (#rl info)))
  in
    make_decl {name = name, spec = spec, weight = weight,
               info = info, orig = th}
  end

fun add_rule_by extend spec named_th cs =
  let
    val decl = make_rule_decl spec named_th
  in
    case extend decl (decls_of cs) of
        (NONE, _) => cs
      | (SOME new_decl, decls') =>
          mk_cs decls' (wrappers_of cs)
            (add_decl new_decl (index_of cs))
  end

val add_rule = add_rule_by extend_decl

(* Rules a library derives from a user declaration rather than rules the
   user named.  Such a rule belongs to the declaration that produced it, so
   it is installed even when its conclusion duplicates an installed rule,
   and it carries none of the diagnostics add_rule prints. *)
val add_derived_rule = add_rule_by extend_derived_decl

val sintro_spec = {kind = Intro, safe = true, prio = NONE}
val intro_spec = {kind = Intro, safe = false, prio = NONE}
val selim_spec = {kind = Elim, safe = true, prio = NONE}
val elim_spec = {kind = Elim, safe = false, prio = NONE}
val sdest_spec = {kind = Dest, safe = true, prio = NONE}
val dest_spec = {kind = Dest, safe = false, prio = NONE}
val forward_spec = {kind = Forward, safe = false, prio = NONE}
val sforward_spec = {kind = Forward, safe = true, prio = NONE}
val norm_spec = {kind = Norm, safe = false, prio = NONE}

fun add_rules spec rules cs =
  List.foldl (fn (rule, acc) => add_rule spec rule acc) cs rules

val add_sintros = add_rules sintro_spec
val add_intros = add_rules intro_spec
val add_selims = add_rules selim_spec
val add_elims = add_rules elim_spec
val add_sdests = add_rules sdest_spec

fun remove_rule name cs =
  let
    val (old_decls, decls') = remove_decl name (decls_of cs)
    val index =
      List.foldl (fn (decl, index) => delete_decl decl index)
        (index_of cs) old_decls
  in
    mk_cs decls' (wrappers_of cs) index
  end

fun merge_alists left right =
  left @ List.filter
    (fn (name, _) => not (List.exists (fn (name', _) => name = name') left))
    right

(* The left claset's derived components are the accumulator: only the
   declarations the merge newly admits are indexed again. *)
fun merge_cs
  (cs, CS {decls = decls2, safe_wrappers = safe_wrappers2,
           unsafe_wrappers = unsafe_wrappers2, ...}) =
  let
    val (safe_wrappers, unsafe_wrappers) = wrappers_of cs
    val (new_decls, decls') = merge_decls (decls_of cs, decls2)
    val index =
      List.foldl (fn (decl, index) => add_decl decl index)
        (index_of cs) new_decls
  in
    mk_cs decls'
      (merge_alists safe_wrappers safe_wrappers2,
       merge_alists unsafe_wrappers unsafe_wrappers2)
      index
  end

(* Replace an existing entry in place; put a new entry at the front. *)
fun update_alist (entry as (key, _)) entries =
  let
    fun replace [] = NONE
      | replace ((old as (old_key, _)) :: rest) =
          if key = old_key then SOME (entry :: rest)
          else Option.map (fn rest' => old :: rest') (replace rest)
  in
    case replace entries of
        SOME entries' => entries'
      | NONE => entry :: entries
  end

fun delete_wrapper name wrappers =
  List.filter (fn (name', _) => name <> name') wrappers

fun map_safe_wrappers f cs =
  let val (safe_wrappers, unsafe_wrappers) = wrappers_of cs
  in
    mk_cs (decls_of cs) (f safe_wrappers, unsafe_wrappers) (index_of cs)
  end

fun map_unsafe_wrappers f cs =
  let val (safe_wrappers, unsafe_wrappers) = wrappers_of cs
  in
    mk_cs (decls_of cs) (safe_wrappers, f unsafe_wrappers) (index_of cs)
  end

fun add_safe_wrapper wrapper = map_safe_wrappers (update_alist wrapper)
fun add_unsafe_wrapper wrapper = map_unsafe_wrappers (update_alist wrapper)
fun del_safe_wrapper name = map_safe_wrappers (delete_wrapper name)
fun del_unsafe_wrapper name = map_unsafe_wrappers (delete_wrapper name)

fun apply_wrappers wrappers tac =
  List.foldl (fn ((_, wrapper), acc) => wrapper acc) tac wrappers

fun app_safe_wrappers (CS {safe_wrappers, ...}) =
  apply_wrappers safe_wrappers

fun app_unsafe_wrappers (CS {unsafe_wrappers, ...}) =
  apply_wrappers unsafe_wrappers

fun rule_of_decl ({spec, name, orig, info, ...} : decl) : aesop_rule =
  {spec = spec, name = name, thm = orig, info = info}

fun all_rules (CS {decls, ...}) = map rule_of_decl (dest_decls decls)

(* The name/theorem view of a retrieved declaration: what a caller that has
   no use for the canonicalisation sees, in the [rules_of] shape. *)
fun forget_info ({spec, name, thm, ...} : aesop_rule) = (spec, (name, thm))

fun rules_of cs = map forget_info (all_rules cs)

fun norm_rules (CS {norm_decls, ...}) = map rule_of_decl norm_decls

fun pp_claset0 (CS {decls, safe_wrappers, unsafe_wrappers, ...}) =
  let
    open Portable smpp

    fun has_spec safe kind (decl : decl) =
      #safe (#spec decl) = safe andalso #kind (#spec decl) = kind

    fun decls_of safe kind =
      List.filter (has_spec safe kind) (dest_decls decls)

    fun pp_decl ({name, orig, ...} : decl) =
      block CONSISTENT 0
        (add_string ("[" ^ name ^ "]") >> add_break (1, 2) >>
         lift Parse.pp_thm orig)

    fun pp_section (title, entries) =
      block CONSISTENT 0
        (add_string (title ^ ":") >> add_newline >>
         block CONSISTENT 2 (pr_list pp_decl add_newline entries))

    fun pp_wrappers (title, wrappers) =
      add_string (title ^ ":") >>
      add_break (1, 2) >>
      pr_list (fn (name, _) => add_string name) (add_break (1, 0)) wrappers

    val rule_sections =
      List.filter (fn (_, entries) => not (List.null entries))
        [("Safe introduction rules", decls_of true Intro),
         ("Safe elimination rules", decls_of true Elim),
         ("Safe destruction rules", decls_of true Dest),
         ("Unsafe introduction rules", decls_of false Intro),
         ("Unsafe elimination rules", decls_of false Elim),
         ("Unsafe destruction rules", decls_of false Dest)]
    val wrapper_sections =
      [("Safe wrappers", safe_wrappers),
       ("Unsafe wrappers", unsafe_wrappers)]
  in
    pr_list pp_section (add_newline >> add_newline) rule_sections >>
    (if List.null rule_sections then smpp.nothing else add_newline) >>
    pr_list pp_wrappers add_newline wrapper_sections
  end

val pp_claset = Parse.mlower o pp_claset0

fun claset_part Safe0Part (CS {safe0_netpair, ...}) = safe0_netpair
  | claset_part SafePPart (CS {safep_netpair, ...}) = safep_netpair
  | claset_part UnsafePart (CS {unsafe_netpair, ...}) = unsafe_netpair
  | claset_part DupPart (CS {dup_netpair, ...}) = dup_netpair

val safe0_part = claset_part Safe0Part
val safep_part = claset_part SafePPart
val unsafe_part = claset_part UnsafePart
val dup_part = claset_part DupPart

fun match_intro_candidates (inet, _) tm =
  candidate_order (clasetNet.match tm inet)
fun match_elim_candidates (_, enet) tm =
  candidate_order (clasetNet.match tm enet)

fun unify_intro_candidates_with checkpoint (inet, _) tm =
  let val qvars = Term.FVL [tm] Term.empty_tmset
  in
    candidate_order_measured checkpoint
      (clasetNet.unifyMeasured checkpoint {q = tm, qvars = qvars} inet)
  end

fun unify_elim_candidates_with checkpoint (_, enet) tm =
  let val qvars = Term.FVL [tm] Term.empty_tmset
  in
    candidate_order_measured checkpoint
      (clasetNet.unifyMeasured checkpoint {q = tm, qvars = qvars} enet)
  end

fun unify_intro_candidates netpair tm =
  unify_intro_candidates_with (fn () => ()) netpair tm

fun unify_elim_candidates netpair tm =
  unify_elim_candidates_with (fn () => ()) netpair tm

fun unify_intro_candidates_measured checkpoint netpair tm =
  unify_intro_candidates_with checkpoint netpair tm

fun unify_elim_candidates_measured checkpoint netpair tm =
  unify_elim_candidates_with checkpoint netpair tm

fun compare_aesop_tag
  ({weight = weight1, index = index1} : tag,
   {weight = weight2, index = index2} : tag) =
  case Int.compare (weight1, weight2) of
      EQUAL => Int.compare (index1, index2)
    | order => order

fun unsafe_percent ({prio, ...} : rulespec) =
  Option.getOpt (prio, 50)

(* The engine consumes phases in this order.  Within a phase, safe rules
   retain claset tag order, and unsafe rules use decreasing success
   percentage before the same tag order. *)
fun aesop_class ({safe = true, ...} : rulespec) = 0
  | aesop_class _ = 1

fun compare_aentry
  ({tag = tag1, rule = {spec = spec1, ...}} : aentry,
   {tag = tag2, rule = {spec = spec2, ...}} : aentry) =
  case Int.compare (aesop_class spec1, aesop_class spec2) of
      EQUAL =>
        if #safe spec1 andalso #safe spec2 then
          compare_aesop_tag (tag1, tag2)
        else
          (case Int.compare
                  (unsafe_percent spec2, unsafe_percent spec1) of
               EQUAL => compare_aesop_tag (tag1, tag2)
             | order => order)
    | order => order

fun aesop_rules select (CS {aesop_index, ...}) query =
  map #rule
    (Listsort.sort compare_aentry
      (clasetNet.unify query (select aesop_index)))

val aesop_target_rules = aesop_rules #target
val aesop_hyp_rules = aesop_rules #hyp

type tyinfo_contribution =
  string * (TypeBasePure.tyinfo -> (rulespec * (string * thm)) list)

type tyinfo_rule =
  {provider : string, tyname : string * string,
   spec : rulespec, named_th : string * thm}

type owned_tyinfo_rule =
  {provider : string, tyname : string * string, decl : decl}

(* An unforced state defers updates until the first demand. *)
datatype pending =
    Modify of (claset -> claset)
  | CatchUpTypeBase of tyinfo_contribution list
  | UpdateTypeInfo of
      {contributions : tyinfo_contribution list,
       tyi : TypeBasePure.tyinfo}
datatype readiness = Ready | Pending of pending list
type cstate = claset * owned_tyinfo_rule list * readiness

val state0 : cstate = (empty_cs, [], Pending [])

fun decl_is_live cs (wanted : decl) =
  List.exists
    (fn (current : decl) =>
      #name current = #name wanted andalso
      #index (#tag current) = #index (#tag wanted))
    (dest_decls (decls_of cs))

fun live_owned cs owned =
  List.filter (fn {decl, ...} => decl_is_live cs decl) owned

fun persistent_name name = KernelSig.name_toString name

(* Every theorem-set table spells its keys the same way, so normalise a
   user-written name to that spelling: a bare or "Thy.Name" source name
   becomes the "Thy$Name" key.  A name containing "$" is already a key,
   because theory names cannot contain "$", and a name ThmSetData.toKName
   rejects can spell no key at all; both come back unchanged, leaving
   each table to decide whether a name denoting nothing is a silent
   no-op (our retraction, which tries the source spelling too) or an
   error worth telling the user about (linarithData's, which shares
   this normalisation). *)
fun normalise_rule_name s =
    if String.isSubstring "$" s then s
    else (persistent_name (ThmSetData.toKName s) handle HOL_ERR _ => s)

(* Reconstruction replays deltas recorded by ancestor theories.  A rule that
   is ill-formed for its declared kind makes add_rule/make_rule_decl raise, so
   guard it: warn and drop, exactly as load_delta does for a stale theorem,
   rather than letting one bad delta abort every descendant theory's load. *)
fun drop_illformed fname name cs =
  (HOL_WARNING "clasetLib" fname
     ("Dropping ill-formed persistent rule " ^ name); cs)

fun apply_add_delta fname {name, spec} cs =
  case load_delta (ADD {name = name, spec = spec}) of
      NONE => cs
    | SOME (name', spec', th) =>
        let val pname = persistent_name name' in
          add_rule spec' (pname, th) cs
          handle HOL_ERR _ => drop_illformed fname pname cs
        end

fun apply_cdelta (ADD args) cs = apply_add_delta "apply_cdelta" args cs
  | apply_cdelta (RM name) cs = remove_rule name cs

(* Values reconstructed for an ancestry always contain their complete set of
   persistent declarations, so they need no delayed replay. *)
fun apply_delta delta (cs, owned, _) =
  let val cs' = apply_cdelta delta cs
  in (cs', live_owned cs' owned, Ready) end

(* Add all declarations before rebuilding the nets.  Theory loading uses this
   once for a delta batch, rather than extending a net for each declaration. *)
fun update_decls (ADD {name, spec}) decls =
      (case load_delta (ADD {name = name, spec = spec}) of
           NONE => decls
         | SOME (name', spec', th) =>
             let val pname = persistent_name name' in
               #2 (extend_decl (make_rule_decl spec' (pname, th)) decls)
               handle HOL_ERR _ => drop_illformed "update_decls" pname decls
             end)
  | update_decls (RM name) decls = #2 (remove_decl name decls)

fun rebuild_claset decls cs =
  let
    val index =
      List.foldl (fn (decl, index) => add_decl decl index)
        empty_index (dest_decls decls)
  in
    mk_cs decls (wrappers_of cs) index
  end

fun is_removal (RM _) = true
  | is_removal (ADD _) = false

fun apply_add_batch (ADD args, cs) =
      apply_add_delta "update_decls" args cs
  | apply_add_batch (RM _, _) =
      raise Fail "batch_apply: unexpected removal in ADD-only batch"

fun batch_apply deltas (cs as CS {decls, ...}) =
  if List.exists is_removal deltas then
    rebuild_claset
      (List.foldl (fn (delta, acc) => update_decls delta acc) decls deltas) cs
  else
    List.foldl apply_add_batch cs deltas

(* TypeBase facts are derived data: they are never ancestry deltas.  A
   contribution may decline a tyinfo by raising (as TypeBasePure's datatype
   accessors do for non-datatypes), so make the listener total.  Contributions
   are value providers and must be pure and deterministic: their invocation
   count and timing are deliberately not part of the public API. *)
val tyinfo_contributions = ref ([] : tyinfo_contribution list)

fun same_spec
  ({kind = kind1, safe = safe1, prio = prio1} : rulespec,
   {kind = kind2, safe = safe2, prio = prio2} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2 andalso prio1 = prio2

fun same_tyinfo_rule
  ({provider, tyname, decl} : owned_tyinfo_rule,
   {provider = provider', tyname = tyname', spec,
    named_th = (name, th)} : tyinfo_rule) =
  provider = provider' andalso tyname = tyname' andalso
  #name decl = name andalso same_spec (#spec decl, spec) andalso
  aconv (concl (#orig decl))
    (concl (canonical_rule_of (#kind spec) th))

fun remove_owned ({decl, ...} : owned_tyinfo_rule) cs =
  if decl_is_live cs decl then remove_rule (#name decl) cs else cs

fun extract_matching _ [] = NONE
  | extract_matching owned (candidate :: rest) =
      if same_tyinfo_rule (owned, candidate) then SOME (candidate, rest)
      else
        Option.map
          (fn (found, rest') => (found, candidate :: rest'))
          (extract_matching owned rest)

fun reconcile_owned scope desired (cs, owned) =
  let
    fun reconcile [] remaining current rev_kept =
          ((current, List.rev rev_kept), remaining)
      | reconcile (entry :: rest) remaining current rev_kept =
          if not (scope entry) then
            reconcile rest remaining current (entry :: rev_kept)
          else
            (case extract_matching entry remaining of
                 SOME (_, remaining') =>
                   reconcile rest remaining' current (entry :: rev_kept)
               | NONE =>
                   reconcile rest remaining (remove_owned entry current)
                     rev_kept)
  in
    reconcile owned desired cs []
  end

fun add_tyinfo_rule
  ({provider, tyname, spec, named_th = (name, th)} : tyinfo_rule)
  (cs as CS {decls, ...}, owned) =
  let
    fun same_class (decl : decl) =
      #kind (#spec decl) = #kind spec andalso
      #safe (#spec decl) = #safe spec
  in
    if List.exists same_class (get_decls decls th) then (cs, owned)
    else
      let val candidate = make_rule_decl spec (name, th)
      in
        case extend_decl candidate decls of
            (NONE, _) => (cs, owned)
          | (SOME installed, decls') =>
              (mk_cs decls' (wrappers_of cs)
                 (add_decl installed (index_of cs)),
               {provider = provider, tyname = tyname,
                decl = installed} :: owned)
      end
  end

fun rules_for_tyinfo contributions (tyi : TypeBasePure.tyinfo) =
  let
    val tyname = TypeBasePure.ty_name_of tyi
    fun add_contribution
      ((provider, contribution) : tyinfo_contribution, rev_rules) =
      case Lib.total contribution tyi of
          NONE => rev_rules
        | SOME rules =>
            List.revAppend
              (map
                 (fn (spec, named_th) =>
                   {provider = provider, tyname = tyname,
                    spec = spec, named_th = named_th} : tyinfo_rule)
                 rules,
               rev_rules)
  in
    List.rev (List.foldl add_contribution [] contributions)
  end

fun apply_tyinfo_rules rules cs =
  List.foldl
    (fn (rule, acc) => add_tyinfo_rule rule acc)
    cs rules

fun collect_typebase_rules contributions =
  let
    fun collect (tyi, rev_rules) =
      List.revAppend (rules_for_tyinfo contributions tyi, rev_rules)
  in
    List.rev (List.foldl collect [] (TypeBase.elts ()))
  end

fun catch_up_typebase cs =
  #1
    (apply_tyinfo_rules
      (collect_typebase_rules (!tyinfo_contributions)) (cs, []))

fun reconcile_typebase contributions state =
  let
    val (state', remaining) =
      reconcile_owned (fn _ => true)
        (collect_typebase_rules contributions) state
  in
    apply_tyinfo_rules remaining state'
  end

fun reconcile_tyinfo contributions tyi state =
  let
    val tyname = TypeBasePure.ty_name_of tyi
    val (state', remaining) =
      reconcile_owned
        (fn {tyname = owned_name, ...} => owned_name = tyname)
        (rules_for_tyinfo contributions tyi) state
  in
    apply_tyinfo_rules remaining state'
  end

fun replay_pending typebase_rules [] (cs, owned, caught_up) =
      if caught_up then (cs, owned)
      else apply_tyinfo_rules typebase_rules (cs, owned)
  | replay_pending typebase_rules (update :: updates)
      (cs, owned, caught_up) =
      (case update of
           CatchUpTypeBase catchup =>
             let
               val (cs', owned') =
                 reconcile_typebase catchup (cs, owned)
             in
               replay_pending typebase_rules updates
                 (cs', owned', true)
             end
         | Modify f =>
             let val cs' = f cs
             in
               replay_pending typebase_rules updates
                 (cs', live_owned cs' owned, false)
             end
         | UpdateTypeInfo {contributions, tyi} =>
             let
               val (cs', owned') =
                 reconcile_tyinfo contributions tyi (cs, owned)
             in
               replay_pending typebase_rules updates
                 (cs', owned', true)
             end)

fun init_state (state as (_, _, Ready)) = state
  | init_state (cs, owned, Pending pending) =
    let
      val typebase_rules =
        collect_typebase_rules (!tyinfo_contributions)
      val (cs', owned') =
        replay_pending typebase_rules (List.rev pending)
          (cs, owned, false)
    in
      (cs', owned', Ready)
    end

fun apply_to_global delta (state as (_, _, Ready)) =
      apply_delta delta state
  | apply_to_global delta (cs, owned, Pending pending) =
      (cs, owned, Pending (Modify (apply_cdelta delta) :: pending))

(* Loading invokes this once for all a theory's deltas.  In particular, an
   unforced global state retains the complete batch for one lazy replay. *)
fun batch_finaliser _ deltas (cs, owned, Ready) =
      let val cs' = batch_apply deltas cs
      in (cs', live_owned cs' owned, Ready) end
  | batch_finaliser _ deltas (cs, owned, Pending pending) =
      (cs, owned, Pending (Modify (batch_apply deltas) :: pending))

val adresult : (cdelta, cstate) AncestryData.fullresult =
  AncestryData.fullmake {
    adinfo = {tag = "claset", initial_values = [("min", state0)],
              apply_delta = apply_delta},
    uptodate_delta = uptodate_delta,
    sexps = {dec = decode_delta, enc = encode_delta},
    globinfo = {apply_to_global = apply_to_global,
                thy_finaliser = SOME batch_finaliser,
                initial_value = state0}
  }

fun update_claset f =
  #update_global_value adresult
    (fn (cs, owned, Ready) =>
          let val cs' = f cs
          in (cs', live_owned cs' owned, Ready) end
      | (cs, owned, Pending pending) =>
          (cs, owned, Pending (Modify f :: pending)))

fun the_claset () =
  (#update_global_value adresult init_state;
   #1 (#get_global_value adresult ()))

fun temp_add_rule spec named_th = update_claset (add_rule spec named_th)

fun temp_delrule name =
  update_claset (remove_rule name o remove_rule (normalise_rule_name name))

val augment_claset = update_claset

fun request_typebase_catchup contributions
      (cs, owned, Ready) =
      let val (cs', owned') = reconcile_typebase contributions (cs, owned)
      in (cs', owned', Ready) end
  | request_typebase_catchup contributions
      (cs, owned, Pending pending) =
      (cs, owned, Pending (CatchUpTypeBase contributions :: pending))

fun register_tyinfo_contribution (entry as (key, _)) =
  let
    val contributions = update_alist entry (!tyinfo_contributions)
  in
    tyinfo_contributions := contributions;
    #update_global_value adresult (request_typebase_catchup contributions)
  end

fun typebase_update tyi =
  let
    fun update (cs, owned, Ready) =
          let
            val (cs', owned') =
              reconcile_tyinfo (!tyinfo_contributions) tyi (cs, owned)
          in
            (cs', owned', Ready)
          end
      | update (cs, owned, Pending pending) =
          (cs, owned,
           Pending
             (UpdateTypeInfo
                {contributions = !tyinfo_contributions, tyi = tyi} ::
              pending))
  in
    #update_global_value adresult update;
    tyi
  end

val _ = TypeBase.register_update_fn typebase_update

fun distinct_elim_rule th =
  let
    val th' = canonical_rule th
    val (vars, _) = strip_forall (concl th')
    val vars' = fresh_forall_vars th' vars
    val core = Drule.SPECL vars' th'
    val eq = dest_neg (concl core)
    val r = variant (free_varsl (concl core :: hyp core)) (mk_var ("r", bool))
    val false_th = MP (NOT_ELIM core) (ASSUME eq)
    val result = MP (SPEC r boolTheory.FALSITY) false_th
  in
    GENL (vars' @ [r]) (DISCH eq result)
  end

fun iff_rules name theorem =
  let
    val (outer_vars, _) = strip_forall (concl theorem)
    val outer_vars' = fresh_forall_vars theorem outer_vars
    val th = Drule.SPECL outer_vars' theorem
    val (prems, final) = boolSyntax.strip_imp_only (concl th)
    val safe = null prems
    fun spec kind = {kind = kind, safe = safe, prio = NONE}

    (* GEN_ALL's set traversal may reverse source binders.  Retain their
       declaration order, then generalise any remaining conclusion-only
       variables in GEN_ALL's established order. *)
    fun gen_all_ordered result =
      let
        val eligible =
          HOLset.difference
            (FVL [concl result] empty_tmset, hyp_frees result)
        val source =
          List.filter (fn variable => HOLset.member (eligible, variable))
            outer_vars'
        val remaining =
          List.foldl
            (fn (variable, variables) =>
              HOLset.delete (variables, variable))
            eligible source
      in
        GENL (source @ HOLset.listItems remaining) result
      end

    (* The derived iff/not rule initially has the source antecedents as
       hypotheses and its new major premise last.  Discharge the source
       antecedents first, then the major, to put the major premise at the
       front as Isabelle's rotate_prems n does. *)
    fun rotate_major major result =
      gen_all_ordered
        (DISCH major (Lib.itlist DISCH prems result))

    (* Move source antecedents into hypotheses so that rotate_major can
       discharge them behind the new major premise. *)
    fun undisch_prems () = Lib.funpow (length prems) Drule.UNDISCH th

    fun equality_rules () =
      let
        val core = undisch_prems ()
        val (left, right) = boolSyntax.dest_eq final
        val (forward, backward) = EQ_IMP_RULE core
        val intro = rotate_major right (MP backward (ASSUME right))
        val dest = rotate_major left (MP forward (ASSUME left))
      in
        [(spec clasetRules.Intro, (name ^ "_intro", intro)),
         (spec clasetRules.Dest, (name ^ "_dest", dest))]
      end

    fun not_rule () =
      let
        val core = undisch_prems ()
        val major = boolSyntax.dest_neg final
        val false_th = MP (NOT_ELIM core) (ASSUME major)
        val result_var =
          variant (free_varsl (concl core :: hyp core))
            (mk_var ("iff_result", Type.bool))
        val result = MP (SPEC result_var boolTheory.FALSITY) false_th
        val elim = rotate_major major result
      in
        [(spec clasetRules.Elim, (name ^ "_elim", elim))]
      end
  in
    if boolSyntax.is_eq final andalso
       type_of (fst (boolSyntax.dest_eq final)) = Type.bool
    then equality_rules ()
    else if boolSyntax.is_neg final then not_rule ()
    else
      [(spec clasetRules.Intro,
        (name ^ "_intro", gen_all_ordered th))]
  end

fun tyinfo_stem tyi =
  case Lib.total TypeBasePure.ty_name_of tyi of
      SOME (thy, tyop) => "__claset_tyinfo_" ^ thy ^ "_" ^ tyop
    | NONE => "__claset_tyinfo_unknown"

fun number_contribution make_rule ths =
  List.concat (Lib.mapi make_rule ths)

fun distinctness_contribution tyi =
  case Lib.total TypeBasePure.distinct_of tyi of
      SOME (SOME th) =>
        let
          val stem = tyinfo_stem tyi ^ "_distinct_"
          fun make_rule index conjunct =
            [(selim_spec,
              (stem ^ Int.toString index, distinct_elim_rule conjunct)),
             (selim_spec,
              (stem ^ "sym_" ^ Int.toString index,
               distinct_elim_rule (GSYM conjunct)))]
        in
          number_contribution make_rule (CONJUNCTS th)
        end
    | _ => []

fun injectivity_contribution tyi =
  case Lib.total TypeBasePure.one_one_of tyi of
      SOME (SOME th) =>
        let
          val stem = tyinfo_stem tyi ^ "_inject_"
          fun make_rule index conjunct =
            iff_rules (stem ^ Int.toString index) conjunct
        in
          number_contribution make_rule (CONJUNCTS th)
        end
    | _ => []

val _ = register_tyinfo_contribution
  ("claset-distinctness", distinctness_contribution)

val _ = register_tyinfo_contribution
  ("claset-injectivity", injectivity_contribution)

fun export_rule spec name =
  let
    val thname = ThmSetData.toKName name
    val delta = ADD {name = thname, spec = spec}
  in
    #record_delta adresult delta;
    #update_global_value adresult (apply_to_global delta)
  end

fun delrule name =
  let val delta = RM (normalise_rule_name name)
  in
    #record_delta adresult delta;
    #update_global_value adresult (apply_to_global delta)
  end

(* The DB reconstruction is the raw ancestry-persistent view.  TypeBase facts
   are derived from the caller's ambient state and are never deltas. *)
fun persistent_claset_of_theory thy = Option.map #1 (#DB adresult thy)

(* Preserve the historical effective view by catching the persistent state up
   with the caller's current TypeBase, just as [the_claset] does. *)
fun claset_of_theory thy =
  Option.map catch_up_typebase (persistent_claset_of_theory thy)
fun merge_clasets thys =
  Option.map (catch_up_typebase o #1) (#merge adresult thys)
fun with_claset cs =
  AncestryData.with_temp_value adresult (cs, [], Ready)

fun priority_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Invalid priority for attribute " ^ attrname ^
     "; expected one integer from 1 to 100")

fun safe_priority_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Arguments not allowed for attribute " ^ attrname ^
     "; safe-rule priorities are not supported")

fun penalty_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Invalid penalty for attribute " ^ attrname ^
     "; expected one integer")

(* Int.fromString both accepts shapes an attribute argument may not take
   (leading whitespace, a "+" sign, trailing text) and raises Overflow
   rather than returning NONE for a numeral too large for a fixed-width
   Int.  The shape is therefore checked first and the conversion itself is
   guarded, so that every malformed argument yields the documented
   HOL_ERR. *)
fun decimal_int arg =
  if size arg > 0 andalso CharVector.all Char.isDigit arg then
    Option.join (Lib.total Int.fromString arg)
  else NONE

fun signed_decimal_int arg =
  if String.isPrefix "~" arg then
    Option.map Int.~ (decimal_int (String.extract (arg, 1, NONE)))
  else decimal_int arg

fun priority_spec attrname (spec : rulespec) args =
  case args of
      [] => spec
    | [arg] =>
        (case decimal_int arg of
             SOME priority =>
               if 1 <= priority andalso priority <= 100 then
                 {kind = #kind spec, safe = false, prio = SOME priority}
               else priority_error attrname
           | NONE => priority_error attrname)
    | _ => priority_error attrname

fun penalty_spec attrname (spec : rulespec) args =
  case args of
      [] => spec
    | [arg] =>
        (case signed_decimal_int arg of
             SOME penalty =>
               {kind = #kind spec, safe = #safe spec, prio = SOME penalty}
           | NONE => penalty_error attrname)
    | _ => penalty_error attrname

fun register_checked_rule_attribute (attrname, checked_spec) =
  let
    fun storedf {name, args, ...} =
      export_rule (checked_spec args) name
    fun localf {name, args, thm, ...} =
      temp_add_rule (checked_spec args) (name, thm)
  in
    ThmAttribute.register_attribute
      (attrname, {storedf = storedf, localf = localf})
  end

fun register_rule_attribute (attrname, spec) =
  register_checked_rule_attribute
    (attrname,
     fn args =>
       if #safe spec then
         if List.null args then spec else safe_priority_error attrname
       else priority_spec attrname spec args)

val _ = List.app register_rule_attribute
  [("intro", intro_spec), ("sintro", sintro_spec),
   ("elim", elim_spec), ("selim", selim_spec),
   ("dest", dest_spec), ("sdest", sdest_spec),
   ("forward", forward_spec), ("sforward", sforward_spec)]

val _ =
  register_checked_rule_attribute
    ("norm", penalty_spec "norm" norm_spec)

(* Structural node count used only to weight rules: each leaf counts 1, an
   application sums its parts, an abstraction adds 1 for the binder.  This is
   a deliberate local metric, not the kernel's Term.term_size. *)
fun default_term_size tm =
  case dest_term tm of
      COMB (rator, rand) =>
        default_term_size rator + default_term_size rand
    | LAMB (_, body) => 1 + default_term_size body
    | _ => 1

fun default_goal_size (asl, w) =
  List.foldl (fn (asm, size) => default_term_size asm + size)
    (default_term_size w) asl

val claset_config =
  {hyp_subst_tac = BasicProvers.VAR_EQ_TAC,
   size_of = default_goal_size}

end

fun mk_marker_const name =
  prim_mk_const {Thy = "clasetMarker", Name = name}

val SIntro_t = mk_marker_const "SIntro"
val Intro_t = mk_marker_const "Intro"
val SElim_t = mk_marker_const "SElim"
val Elim_t = mk_marker_const "Elim"
val SDest_t = mk_marker_const "SDest"
val Dest_t = mk_marker_const "Dest"
val Simp_t = mk_marker_const "Simp"
val Iff_t = mk_marker_const "Iff"
val Norm_t = mk_marker_const "Norm"
val Forward_t = mk_marker_const "Forward"
val SForward_t = mk_marker_const "SForward"
val Del_t = mk_marker_const "Del"

val SIntro = markerLib.genCong clasetMarkerTheory.SIntro_def
val Intro = markerLib.genCong clasetMarkerTheory.Intro_def
val SElim = markerLib.genCong clasetMarkerTheory.SElim_def
val Elim = markerLib.genCong clasetMarkerTheory.Elim_def
val SDest = markerLib.genCong clasetMarkerTheory.SDest_def
val Dest = markerLib.genCong clasetMarkerTheory.Dest_def
val Simp = markerLib.genCong clasetMarkerTheory.Simp_def
val Iff = markerLib.genCong clasetMarkerTheory.Iff_def
val Norm = markerLib.genCong clasetMarkerTheory.Norm_def
val Forward = markerLib.genCong clasetMarkerTheory.Forward_def
val SForward = markerLib.genCong clasetMarkerTheory.SForward_def

val destSIntro =
  markerLib.genUnCong SIntro_t clasetMarkerTheory.SIntro_def
val destIntro = markerLib.genUnCong Intro_t clasetMarkerTheory.Intro_def
val destSElim = markerLib.genUnCong SElim_t clasetMarkerTheory.SElim_def
val destElim = markerLib.genUnCong Elim_t clasetMarkerTheory.Elim_def
val destSDest = markerLib.genUnCong SDest_t clasetMarkerTheory.SDest_def
val destDest = markerLib.genUnCong Dest_t clasetMarkerTheory.Dest_def
val destSimp = markerLib.genUnCong Simp_t clasetMarkerTheory.Simp_def
val destIff = markerLib.genUnCong Iff_t clasetMarkerTheory.Iff_def
val destNorm = markerLib.genUnCong Norm_t clasetMarkerTheory.Norm_def
val destForward =
  markerLib.genUnCong Forward_t clasetMarkerTheory.Forward_def
val destSForward =
  markerLib.genUnCong SForward_t clasetMarkerTheory.SForward_def

val Del = markerLib.genmktagged clasetMarkerTheory.Del_def
val destDel = markerLib.gendest_tagged Del_t

datatype marker_payload = Theorem of thm | DeleteName of string
type marker_info =
  {name : string, spec : rulespec option, payload : marker_payload}

type marker_registration =
  {name : string, spec : rulespec option,
   dest : thm -> marker_payload option}

fun theorem_marker name spec dest : marker_registration =
  {name=name, spec=spec, dest=Option.map Theorem o dest}

val marker_registry =
  [theorem_marker "SIntro" (SOME sintro_spec) destSIntro,
   theorem_marker "Intro" (SOME intro_spec) destIntro,
   theorem_marker "SElim" (SOME selim_spec) destSElim,
   theorem_marker "Elim" (SOME elim_spec) destElim,
   theorem_marker "SDest" (SOME sdest_spec) destSDest,
   theorem_marker "Dest" (SOME dest_spec) destDest,
   theorem_marker "Simp" NONE destSimp,
   theorem_marker "Iff" NONE destIff,
   theorem_marker "Norm" (SOME norm_spec) destNorm,
   theorem_marker "Forward" (SOME forward_spec) destForward,
   theorem_marker "SForward" (SOME sforward_spec) destSForward,
   {name="Del", spec=NONE, dest=Option.map DeleteName o destDel}]

fun marker_of theorem =
  Lib.get_first
    (fn {name,spec,dest} =>
      Option.map
        (fn payload => {name=name, spec=spec, payload=payload})
        (dest theorem))
    marker_registry

val marker_prefix = "__claset_marker_"

(* The first "<prefix><n>" with n at least [from] that no declaration
   already uses.  Invocation-scoped rules are named this way so that a
   marker argument can never collide with a user declaration. *)
fun fresh_rule_name {prefix, from} (CS {decls, ...}) =
  let
    fun find index =
      let val name = prefix ^ Int.toString index
      in
        if clasetRules.decl_name_member decls name then find (index + 1)
        else name
      end
  in
    find from
  end

fun marker_name cs =
  fresh_rule_name {prefix = marker_prefix, from = 0} cs

fun classical_rule ({kind=clasetRules.Intro,...} : rulespec) = true
  | classical_rule {kind=clasetRules.Elim,...} = true
  | classical_rule {kind=clasetRules.Dest,...} = true
  | classical_rule _ = false

fun process_claset_tags thms cs =
  let
    fun add spec th cs = add_rule spec (marker_name cs, th) cs

    fun process (cs, rest) [] = (cs, List.rev rest)
      | process (cs, rest) (th :: ths) =
          case marker_of th of
              SOME {spec=SOME spec,payload=Theorem rule,...} =>
                if classical_rule spec then
                  process (add spec rule cs, rest) ths
                else
                  process (cs, th :: rest) ths
            | SOME {payload=DeleteName name,...} =>
                process (remove_rule name cs, rest) ths
            | _ => process (cs, th :: rest) ths
  in
    process (cs, []) thms
  end

type simp_arg_split =
  {simp_rules : thm list,
   iff_rules : thm list,
   simp_controls : thm list,
   rest : thm list}

datatype simp_arg_bucket = SimpRule | IffRule | SimpControl | Plain

fun simp_arg_bucket theorem =
  case marker_of theorem of
      SOME {name="Simp",payload=Theorem rule,...} => (SimpRule,rule)
    | SOME {name="Iff",payload=Theorem rule,...} => (IffRule,rule)
    | _ =>
        if markerLib.is_generic_simp_marker theorem
        then (SimpControl, theorem)
        else (Plain, theorem)

(* Each bucket keeps the arguments in the order they were given. *)
fun classify_simp_args theorems =
  let
    val tagged = map simp_arg_bucket theorems
    fun bucket wanted =
      List.mapPartial
        (fn (tag, theorem) => if tag = wanted then SOME theorem else NONE)
        tagged
  in
    {simp_rules = bucket SimpRule,
     iff_rules = bucket IffRule,
     simp_controls = bucket SimpControl,
     rest = bucket Plain}
  end

(* Markers naming a rule class only the aesop front end installs (see its
   own marker pass).  They survive process_claset_tags and mean nothing to
   a plain classical tactic, so they are reported rather than assumed. *)
fun aesop_marker_name theorem =
  case marker_of theorem of
      SOME {name="Norm",...} => SOME "Norm"
    | SOME {name="Forward",...} => SOME "Forward"
    | SOME {name="SForward",...} => SOME "SForward"
    | _ => NONE

(* Checked wherever arguments become assumptions, not only where the
   classical engines collect them: assuming a marker would leave a
   nonsense hypothesis on the goal with no diagnostic. *)
fun check_aesop_markers function theorems =
  case List.mapPartial aesop_marker_name theorems of
      [] => ()
    | name :: _ =>
        raise mk_HOL_ERR "clasetLib" function
          (name ^ " marker requires an Aesop-aware tactic")

(* process_claset_tags consumes the classical marker vocabulary.  Plain
   leftovers become inserted facts; generic simplifier controls are either
   unwrapped to their theorem payload or discarded as inert here. *)
fun invocation_facts theorems =
  let
    fun unwrap theorem =
      case markerLib.dest_generic_simp_wrapper theorem of
          NONE => theorem
        | SOME payload => payload
    val {simp_rules, iff_rules, rest, ...} =
      classify_simp_args (map unwrap theorems)
  in
    if not (null simp_rules) then
      raise mk_HOL_ERR "clasetLib" "invocation_facts"
        "Simp marker requires a tactic with a simpset"
    else if not (null iff_rules) then
      raise mk_HOL_ERR "clasetLib" "invocation_facts"
        "Iff marker requires a tactic with a simpset"
    else (check_aesop_markers "invocation_facts" rest; rest)
  end

(* ASSUME_TAC conses onto the assumption list, so the facts are assumed
   back-to-front to leave them in declaration order.  Order is observable:
   it is the recency tie-break the classical engines use when scanning
   assumptions, and what FIRST_ASSUM and friends see in the residue. *)
fun INSERT_FACTS_TAC facts =
  (check_aesop_markers "INSERT_FACTS_TAC" facts;
   Tactical.MAP_EVERY Tactic.ASSUME_TAC (List.rev facts))

fun invocation_claset base theorems =
  let val (tagged, leftovers) = process_claset_tags theorems base
  in
    (tagged, invocation_facts leftovers)
  end

type 'a invocation_simpset =
  {base : 'a,
   extend :
     {iff_prefix : string, simp_rules : thm list, iff_rules : thm list,
      claset : claset, simpset : 'a} -> claset * 'a}

fun with_invocation_args {iff_prefix,extra_markers} body base_cs simpset =
  markerLib.ABBRS_THEN
    (fn theorems => fn goal =>
      (let
        val (classical_cs, invocation_ss, simp_controls, leftovers) =
          case simpset of
              NONE =>
                let val (cs, facts) = invocation_claset base_cs theorems
                in (cs, NONE, [], facts)
                end
            | SOME {base,extend} =>
                let
                  val {simp_rules,iff_rules,simp_controls,rest} =
                    classify_simp_args theorems
                  val (extended_cs, extended_ss) =
                    extend
                      {iff_prefix=iff_prefix, simp_rules=simp_rules,
                       iff_rules=iff_rules, claset=base_cs, simpset=base}
                  val (cs, facts) =
                    process_claset_tags rest extended_cs
                in
                  (cs, SOME extended_ss, simp_controls, facts)
                end
        val (invocation_cs, facts) =
          extra_markers leftovers classical_cs
      in
        Tactical.THEN
          (INSERT_FACTS_TAC facts,
           body invocation_cs invocation_ss simp_controls) goal
      end))

end
