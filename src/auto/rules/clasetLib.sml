structure clasetLib :> clasetLib =
struct

open Abbrev HolKernel clasetRules

type net_entry = tag * brl
type netpair = net_entry clasetNet.net * net_entry clasetNet.net

datatype claset =
  CS of {decls : decls,
         safe_wrappers : (string * NTactical.wrapper) list,
         unsafe_wrappers : (string * NTactical.wrapper) list,
         safe0_netpair : netpair,
         safep_netpair : netpair,
         unsafe_netpair : netpair,
         dup_netpair : netpair}

type claset_part = netpair

datatype part = Safe0Part | SafePPart | UnsafePart | DupPart

val empty_netpair = (clasetNet.empty, clasetNet.empty)

val empty_cs =
  CS {decls = empty_decls,
      safe_wrappers = [],
      unsafe_wrappers = [],
      safe0_netpair = empty_netpair,
      safep_netpair = empty_netpair,
      unsafe_netpair = empty_netpair,
      dup_netpair = empty_netpair}

fun is_elim Intro = false
  | is_elim _ = true

fun rule_brl kind th = (is_elim kind, th)

fun indexed_rule kind tag ((th, _) : rl) =
  let
    val {patvars, ...} = canonical_form th
    val pat = rule_index kind th
  in
    ({pat = pat, patvars = patvars}, (tag, rule_brl kind th))
  end

fun insert_brl kind tag rl (inet, enet) =
  let
    val entry = indexed_rule kind tag rl
  in
    if is_elim kind then (inet, clasetNet.insert entry enet)
    else (clasetNet.insert entry inet, enet)
  end

fun insert_rl kind index (rl : rl) netpair =
  let
    val (th, swapped) = rl
    val tag = {weight = subgoals_of (rule_brl kind th),
               index = 2 * index + 1}
    val netpair' = insert_brl kind tag rl netpair
  in
    case swapped of
        NONE => netpair'
      | SOME th' =>
          let
            val swapped_rl = (th', NONE)
            val tag' = {weight = subgoals_of (rule_brl kind th'),
                        index = 2 * index}
          in
            insert_brl kind tag' swapped_rl netpair'
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

fun add_decl (decl : decl)
  (safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair) =
  let
    val {spec, tag = {index, ...}, info, ...} = decl
    val kind = #kind spec
  in
    if #safe spec then
      (case safe_class_of spec info of
          SOME Safe0 =>
            (insert_rl kind index (#rl info) safe0_netpair,
             safep_netpair, unsafe_netpair, dup_netpair)
        | SOME SafeP =>
            (safe0_netpair,
             insert_rl kind index (#rl info) safep_netpair,
             unsafe_netpair, dup_netpair)
        | NONE => raise Fail "safe rule has no safe classification")
    else
      (safe0_netpair, safep_netpair,
       insert_rl kind index (#rl info) unsafe_netpair,
       insert_rl kind index (#dup_rl info) dup_netpair)
  end

fun make_rule_decl spec (name, th) =
  let
    val info = ext_info spec th
    val weight = subgoals_of (rule_brl (#kind spec) (#1 (#rl info)))
  in
    make_decl {name = name, spec = spec, weight = weight,
               info = info, orig = th}
  end

fun add_rule spec named_th
  (CS {decls, safe_wrappers, unsafe_wrappers,
       safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair}) =
  let
    val decl = make_rule_decl spec named_th
  in
    case extend_decl decl decls of
        (NONE, _) =>
          CS {decls = decls,
              safe_wrappers = safe_wrappers,
              unsafe_wrappers = unsafe_wrappers,
              safe0_netpair = safe0_netpair,
              safep_netpair = safep_netpair,
              unsafe_netpair = unsafe_netpair,
              dup_netpair = dup_netpair}
      | (SOME new_decl, decls') =>
          let
            val (safe0_netpair', safep_netpair',
                 unsafe_netpair', dup_netpair') =
              add_decl new_decl
                (safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair)
          in
            CS {decls = decls',
                safe_wrappers = safe_wrappers,
                unsafe_wrappers = unsafe_wrappers,
                safe0_netpair = safe0_netpair',
                safep_netpair = safep_netpair',
                unsafe_netpair = unsafe_netpair',
                dup_netpair = dup_netpair'}
          end
  end

val sintro_spec = {kind = Intro, safe = true, prio = NONE}
val intro_spec = {kind = Intro, safe = false, prio = NONE}
val selim_spec = {kind = Elim, safe = true, prio = NONE}
val elim_spec = {kind = Elim, safe = false, prio = NONE}
val sdest_spec = {kind = Dest, safe = true, prio = NONE}
val dest_spec = {kind = Dest, safe = false, prio = NONE}

fun add_rules spec rules cs =
  List.foldl (fn (rule, acc) => add_rule spec rule acc) cs rules

val add_sintros = add_rules sintro_spec
val add_intros = add_rules intro_spec
val add_selims = add_rules selim_spec
val add_elims = add_rules elim_spec
val add_sdests = add_rules sdest_spec
val add_dests = add_rules dest_spec

fun remove_rule name
  (CS {decls, safe_wrappers, unsafe_wrappers,
       safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair}) =
  let
    val (old_decls, decls') = remove_decl name decls
    fun delete decl (safe0, safep, unsafe, dup) =
      let val {tag = {index, ...}, ...} = decl
      in (delete_rl index safe0, delete_rl index safep,
          delete_rl index unsafe, delete_rl index dup)
      end
    val (safe0_netpair', safep_netpair', unsafe_netpair', dup_netpair') =
      List.foldl (fn (decl, nets) => delete decl nets)
        (safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair) old_decls
  in
    CS {decls = decls',
        safe_wrappers = safe_wrappers,
        unsafe_wrappers = unsafe_wrappers,
        safe0_netpair = safe0_netpair',
        safep_netpair = safep_netpair',
        unsafe_netpair = unsafe_netpair',
        dup_netpair = dup_netpair'}
  end

fun merge_alists left right =
  left @ List.filter
    (fn (name, _) => not (List.exists (fn (name', _) => name = name') left))
    right

fun merge_cs
  (CS {decls, safe_wrappers, unsafe_wrappers,
       safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair},
   CS {decls = decls2, safe_wrappers = safe_wrappers2,
       unsafe_wrappers = unsafe_wrappers2, ...}) =
  let
    val (new_decls, decls') = merge_decls (decls, decls2)
    val (safe0_netpair', safep_netpair', unsafe_netpair', dup_netpair') =
      List.foldl (fn (decl, nets) => add_decl decl nets)
        (safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair) new_decls
  in
    CS {decls = decls',
        safe_wrappers = merge_alists safe_wrappers safe_wrappers2,
        unsafe_wrappers = merge_alists unsafe_wrappers unsafe_wrappers2,
        safe0_netpair = safe0_netpair',
        safep_netpair = safep_netpair',
        unsafe_netpair = unsafe_netpair',
        dup_netpair = dup_netpair'}
  end

fun update_wrapper (name, wrapper) [] = [(name, wrapper)]
  | update_wrapper (entry as (name, wrapper))
      ((old as (old_name, _)) :: rest) =
      if name = old_name then entry :: rest
      else old :: update_wrapper entry rest

fun delete_wrapper name wrappers =
  List.filter (fn (name', _) => name <> name') wrappers

fun map_safe_wrappers f
  (CS {decls, safe_wrappers, unsafe_wrappers,
       safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair}) =
  CS {decls = decls,
      safe_wrappers = f safe_wrappers,
      unsafe_wrappers = unsafe_wrappers,
      safe0_netpair = safe0_netpair,
      safep_netpair = safep_netpair,
      unsafe_netpair = unsafe_netpair,
      dup_netpair = dup_netpair}

fun map_unsafe_wrappers f
  (CS {decls, safe_wrappers, unsafe_wrappers,
       safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair}) =
  CS {decls = decls,
      safe_wrappers = safe_wrappers,
      unsafe_wrappers = f unsafe_wrappers,
      safe0_netpair = safe0_netpair,
      safep_netpair = safep_netpair,
      unsafe_netpair = unsafe_netpair,
      dup_netpair = dup_netpair}

fun add_safe_wrapper wrapper = map_safe_wrappers (update_wrapper wrapper)
fun add_unsafe_wrapper wrapper = map_unsafe_wrappers (update_wrapper wrapper)
fun del_safe_wrapper name = map_safe_wrappers (delete_wrapper name)
fun del_unsafe_wrapper name = map_unsafe_wrappers (delete_wrapper name)

fun apply_wrappers wrappers tac =
  List.foldl (fn ((_, wrapper), acc) => wrapper acc) tac wrappers

fun app_safe_wrappers (CS {safe_wrappers, ...}) =
  apply_wrappers safe_wrappers

fun app_unsafe_wrappers (CS {unsafe_wrappers, ...}) =
  apply_wrappers unsafe_wrappers

fun rules_of (CS {decls, ...}) =
  map (fn {spec, name, orig, ...} => (spec, (name, orig))) (dest_decls decls)

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
val safe0 = safe0_part
val safep = safep_part
val unsafe = unsafe_part
val dup = dup_part

fun sorted candidates = candidate_order candidates

fun match_intro_candidates (inet, _) tm = sorted (clasetNet.match tm inet)
fun match_elim_candidates (_, enet) tm = sorted (clasetNet.match tm enet)

fun free_var_set tm = HOLset.fromList Term.compare (free_vars tm)

fun unify_intro_candidates (inet, _) tm =
  sorted (clasetNet.unify {q = tm, qvars = free_var_set tm} inet)

fun unify_elim_candidates (_, enet) tm =
  sorted (clasetNet.unify {q = tm, qvars = free_var_set tm} enet)

fun default_goal_size (asl, w) =
  List.foldl (fn (asm, size) => Term.term_size asm + size)
    (Term.term_size w) asl

val claset_config =
  {hyp_subst_tac = BasicProvers.VAR_EQ_TAC,
   size_of = default_goal_size}

val Intro = clasetRules.Intro
val Elim = clasetRules.Elim
val Dest = clasetRules.Dest

end
