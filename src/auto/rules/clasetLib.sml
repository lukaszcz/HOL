structure clasetLib :> clasetLib =
struct

open Abbrev HolKernel boolLib

type rulekind = clasetRules.rulekind
type rulespec = clasetRules.rulespec
type tag = clasetRules.tag
type brl = clasetRules.brl

local
  open clasetRules
in

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
  (cs as CS {decls, safe_wrappers, unsafe_wrappers,
             safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair}) =
  let
    val decl = make_rule_decl spec named_th
  in
    case extend_decl decl decls of
        (NONE, _) => cs
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

fun match_intro_candidates (inet, _) tm =
  candidate_order (clasetNet.match tm inet)
fun match_elim_candidates (_, enet) tm =
  candidate_order (clasetNet.match tm enet)

fun free_var_set tm = boolSyntax.FVLset [tm]

fun free_var_set_measured checkpoint tm =
  let
    val empty = HOLset.empty Term.compare
    fun collect ([], variables) = variables
      | collect ((item, bound) :: rest, variables) =
          (checkpoint ();
           if is_var item then
             collect
               (rest,
                if HOLset.member (bound, item) then variables
                else HOLset.add (variables, item))
           else if is_comb item then
             let val (operator, operand) = dest_comb item
             in
               collect
                 ((operator, bound) :: (operand, bound) :: rest, variables)
             end
           else if is_abs item then
             let val (binder, body) = dest_abs item
             in
               collect
                 ((body, HOLset.add (bound, binder)) :: rest, variables)
             end
           else collect (rest, variables))
  in
    collect ([(tm, empty)], empty)
  end

fun unify_intro_candidates (inet, _) tm =
  candidate_order (clasetNet.unify {q = tm, qvars = free_var_set tm} inet)

fun unify_elim_candidates (_, enet) tm =
  candidate_order (clasetNet.unify {q = tm, qvars = free_var_set tm} enet)

fun unify_intro_candidates_measured checkpoint (inet, _) tm =
  let val qvars = free_var_set_measured checkpoint tm
  in
    candidate_order_measured checkpoint
      (clasetNet.unifyMeasured checkpoint {q = tm, qvars = qvars} inet)
  end

fun unify_elim_candidates_measured checkpoint (_, enet) tm =
  let val qvars = free_var_set_measured checkpoint tm
  in
    candidate_order_measured checkpoint
      (clasetNet.unifyMeasured checkpoint {q = tm, qvars = qvars} enet)
  end

type tyinfo_contribution =
  string * (TypeBasePure.tyinfo -> (rulespec * (string * thm)) list)

type typebase_catchup =
  {contributions : tyinfo_contribution list,
   replaced : tyinfo_contribution option}

(* The false state defers persistent updates until the first demand. *)
datatype pending =
    ApplyDelta of cdelta
  | ApplyBatch of cdelta list
  | Modify of (claset -> claset)
  | CatchUpTypeBase of typebase_catchup
type cstate = claset * bool * pending list

val state0 : cstate = (empty_cs, false, [])

fun persistent_name name = KernelSig.name_toString name

fun normalise_rule_name name =
  case String.fields (equal #"$") name of
      [_, _] => name
    | _ =>
        (persistent_name (ThmSetData.toKName name)
         handle HOL_ERR _ => name)

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
fun apply_delta delta (cs, _, _) = (apply_cdelta delta cs, true, [])

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

fun rebuild_claset decls
  (CS {safe_wrappers, unsafe_wrappers, ...}) =
  let
    val (safe0_netpair, safep_netpair, unsafe_netpair, dup_netpair) =
      List.foldl
        (fn (decl, nets) => add_decl decl nets)
        (empty_netpair, empty_netpair, empty_netpair, empty_netpair)
        (dest_decls decls)
  in
    CS {decls = decls,
        safe_wrappers = safe_wrappers,
        unsafe_wrappers = unsafe_wrappers,
        safe0_netpair = safe0_netpair,
        safep_netpair = safep_netpair,
        unsafe_netpair = unsafe_netpair,
        dup_netpair = dup_netpair}
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

fun add_tyinfo_rule spec (named_th as (_, th))
  (cs as CS {decls, ...}) =
  let
    fun same_class (decl : decl) =
      #kind (#spec decl) = #kind spec andalso
      #safe (#spec decl) = #safe spec
  in
    if List.exists same_class (get_decls decls th) then cs
    else add_rule spec named_th cs
  end

fun rules_for_tyinfo contributions (tyi : TypeBasePure.tyinfo) =
  let
    fun add_contribution
      ((_, contribution) : tyinfo_contribution, rev_rules) =
      case Lib.total contribution tyi of
          NONE => rev_rules
        | SOME rules => List.revAppend (rules, rev_rules)
  in
    List.rev (List.foldl add_contribution [] contributions)
  end

fun apply_tyinfo_rules rules cs =
  List.foldl
    (fn ((spec, named_th), acc) => add_tyinfo_rule spec named_th acc)
    cs rules

fun collect_typebase_rules contributions =
  let
    fun collect (tyi, rev_rules) =
      List.revAppend (rules_for_tyinfo contributions tyi, rev_rules)
  in
    List.rev (List.foldl collect [] (TypeBase.elts ()))
  end

fun catch_up_typebase cs =
  apply_tyinfo_rules (collect_typebase_rules (!tyinfo_contributions)) cs

fun contribution_rules (_, contribution) =
  let
    fun collect (tyi, rev_rules) =
      case Lib.total contribution tyi of
          NONE => rev_rules
        | SOME rules => List.revAppend (rules, rev_rules)
  in
    List.rev (List.foldl collect [] (TypeBase.elts ()))
  end

(* Remove only declarations that the replaced provider actually installed.
   Matching the name, canonical theorem, and rule class prevents a provider
   whose output was rejected as a duplicate from deleting the winner. *)
fun remove_contribution_rule (spec, (name, th))
  (cs as CS {decls, ...}) =
  let
    fun matches (decl : decl) =
      #name decl = name andalso
      #kind (#spec decl) = #kind spec andalso
      #safe (#spec decl) = #safe spec
  in
    if List.exists matches (get_decls decls th) then remove_rule name cs
    else cs
  end

fun reconcile_typebase
  ({contributions, replaced} : typebase_catchup) cs =
  let
    val cs' =
      case replaced of
          NONE => cs
        | SOME old =>
            List.foldl
              (fn (rule, acc) => remove_contribution_rule rule acc)
              cs (contribution_rules old)
  in
    apply_tyinfo_rules (collect_typebase_rules contributions) cs'
  end

fun replay_pending typebase_rules [] (cs, caught_up) =
      if caught_up then cs
      else apply_tyinfo_rules typebase_rules cs
  | replay_pending typebase_rules (update :: updates) (cs, caught_up) =
      (case update of
           CatchUpTypeBase catchup =>
             replay_pending typebase_rules updates
               (reconcile_typebase catchup cs, true)
         | ApplyDelta delta =>
             replay_pending typebase_rules updates
               (apply_cdelta delta cs, false)
         | ApplyBatch deltas =>
             replay_pending typebase_rules updates
               (batch_apply deltas cs, false)
         | Modify f =>
             replay_pending typebase_rules updates (f cs, false))

fun init_state (state as (cs, initialised, pending)) =
  if initialised then state
  else
    let
      val typebase_rules =
        collect_typebase_rules (!tyinfo_contributions)
    in
      (replay_pending typebase_rules (List.rev pending) (cs, false), true, [])
    end

fun apply_to_global delta (cs, initialised, pending) =
  if initialised then apply_delta delta (cs, initialised, pending)
  else (cs, false, ApplyDelta delta :: pending)

(* Loading invokes this once for all a theory's deltas.  In particular, an
   unforced global state retains the complete batch for one lazy replay. *)
fun batch_finaliser _ deltas (cs, initialised, pending) =
  if initialised then (batch_apply deltas cs, true, [])
  else (cs, false, ApplyBatch deltas :: pending)

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
    (fn (cs, initialised, pending) =>
       if initialised then (f cs, true, [])
       else (cs, false, Modify f :: pending))

fun the_claset () =
  (#update_global_value adresult init_state;
   #1 (#get_global_value adresult ()))

fun temp_add_rule spec named_th = update_claset (add_rule spec named_th)

fun temp_delrule name =
  update_claset (remove_rule name o remove_rule (normalise_rule_name name))

val augment_claset = update_claset

fun request_typebase_catchup catchup (cs, initialised, pending) =
  if initialised then (reconcile_typebase catchup cs, true, [])
  else (cs, false, CatchUpTypeBase catchup :: pending)

fun register_tyinfo_contribution (entry as (key, _)) =
  let
    val old = List.find (fn (key', _) => key = key') (!tyinfo_contributions)
    val contributions = update_alist entry (!tyinfo_contributions)
    val catchup = {contributions = contributions, replaced = old}
  in
    tyinfo_contributions := contributions;
    #update_global_value adresult (request_typebase_catchup catchup)
  end

fun typebase_update tyi =
  let val rules = rules_for_tyinfo (!tyinfo_contributions) tyi
  in update_claset (apply_tyinfo_rules rules); tyi end

val _ = TypeBase.register_update_fn typebase_update

fun fresh_outer_vars th vars =
  let
    fun freshen avoids [] = []
      | freshen avoids (v :: vs) =
          let val v' = variant avoids v
          in v' :: freshen (v' :: avoids) vs end
  in
    freshen (free_varsl (hyp th)) vars
  end

fun distinct_elim_rule th =
  let
    val th' = canonical_rule th
    val (vars, _) = strip_forall (concl th')
    val vars' = fresh_outer_vars th' vars
    val core = Drule.SPECL vars' th'
    val eq = dest_neg (concl core)
    val r = variant (free_varsl (concl core :: hyp core)) (mk_var ("r", bool))
    val false_th = MP (NOT_ELIM core) (ASSUME eq)
    val result = MP (SPEC r boolTheory.FALSITY) false_th
  in
    GENL (vars' @ [r]) (DISCH eq result)
  end

fun iff_dest_rule th =
  let
    val th' = canonical_rule th
    val (vars, _) = strip_forall (concl th')
    val vars' = fresh_outer_vars th' vars
  in
    GENL vars' (#1 (EQ_IMP_RULE (Drule.SPECL vars' th')))
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
            [(sdest_spec,
              (stem ^ Int.toString index, iff_dest_rule conjunct))]
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
fun with_claset cs = AncestryData.with_temp_value adresult (cs, true, [])

fun attribute_error attrname =
  raise mk_HOL_ERR "clasetLib" "attribute"
    ("Arguments not allowed for attribute " ^ attrname ^
     "; priorities arrive in a later phase")

fun register_rule_attribute (attrname, spec) =
  let
    fun storedf {name, args, ...} =
      if List.null args then export_rule spec name else attribute_error attrname
    fun localf {name, args, thm, ...} =
      if List.null args then temp_add_rule spec (name, thm)
      else attribute_error attrname
  in
    ThmAttribute.register_attribute
      (attrname, {storedf = storedf, localf = localf})
  end

val _ = List.app register_rule_attribute
  [("intro", intro_spec), ("sintro", sintro_spec),
   ("elim", elim_spec), ("selim", selim_spec),
   ("dest", dest_spec), ("sdest", sdest_spec)]

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
val Del_t = mk_marker_const "Del"

val SIntro = markerLib.genCong clasetMarkerTheory.SIntro_def
val Intro = markerLib.genCong clasetMarkerTheory.Intro_def
val SElim = markerLib.genCong clasetMarkerTheory.SElim_def
val Elim = markerLib.genCong clasetMarkerTheory.Elim_def
val SDest = markerLib.genCong clasetMarkerTheory.SDest_def
val Dest = markerLib.genCong clasetMarkerTheory.Dest_def

val destSIntro =
  markerLib.genUnCong SIntro_t clasetMarkerTheory.SIntro_def
val destIntro = markerLib.genUnCong Intro_t clasetMarkerTheory.Intro_def
val destSElim = markerLib.genUnCong SElim_t clasetMarkerTheory.SElim_def
val destElim = markerLib.genUnCong Elim_t clasetMarkerTheory.Elim_def
val destSDest = markerLib.genUnCong SDest_t clasetMarkerTheory.SDest_def
val destDest = markerLib.genUnCong Dest_t clasetMarkerTheory.Dest_def

val Del = markerLib.genmktagged clasetMarkerTheory.Del_def
val destDel = markerLib.gendest_tagged Del_t

val marker_prefix = "__claset_marker_"

fun marker_name (CS {decls, ...}) =
  let
    fun find index =
      let val name = marker_prefix ^ Int.toString index
      in
        if clasetRules.decl_name_member decls name then find (index + 1)
        else name
      end
  in
    find 0
  end

val theorem_markers =
  [(destSIntro, sintro_spec), (destIntro, intro_spec),
   (destSElim, selim_spec), (destElim, elim_spec),
   (destSDest, sdest_spec), (destDest, dest_spec)]

fun dest_rule_marker [] th = NONE
  | dest_rule_marker ((dest, spec) :: markers) th =
      case dest th of
          NONE => dest_rule_marker markers th
        | SOME rule => SOME (spec, rule)

fun process_claset_tags thms cs =
  let
    fun add spec th cs = add_rule spec (marker_name cs, th) cs

    fun process (cs, rest) [] = (cs, List.rev rest)
      | process (cs, rest) (th :: ths) =
          case dest_rule_marker theorem_markers th of
              SOME (spec, rule) => process (add spec rule cs, rest) ths
            | NONE =>
                (case destDel th of
                     SOME name => process (remove_rule name cs, rest) ths
                   | NONE => process (cs, th :: rest) ths)
  in
    process (cs, []) thms
  end

fun has_marker_head marker theorem =
  let val (head, _) = strip_comb (concl theorem)
  in same_const marker head end
  handle HOL_ERR _ => false

fun is_bounded theorem =
  Option.isSome (total BoundedRewrites.DEST_BOUNDED theorem)

(* Generic simplifier markers are not classical-rule declarations. *)
fun is_passthrough_marker theorem =
  has_marker_head markerSyntax.AC_tm theorem orelse
  has_marker_head markerSyntax.Cong_tm theorem orelse
  has_marker_head markerSyntax.Split_tm theorem orelse
  Option.isSome (markerLib.destExcl theorem) orelse
  Option.isSome (markerLib.destExclSF theorem) orelse
  Option.isSome (markerLib.destFRAG theorem) orelse
  Option.isSome (markerLib.dest_Req0 theorem) orelse
  Option.isSome (markerLib.dest_ReqD theorem) orelse
  is_bounded theorem

fun rule_name_exists name cs =
  List.exists (fn (_, (old_name, _)) => name = old_name) (rules_of cs)

fun next_extra_name prefix cs index =
  let val name = prefix ^ Int.toString index
  in
    if rule_name_exists name cs then next_extra_name prefix cs (index + 1)
    else (name, index + 1)
  end

(* process_claset_tags consumes the classical marker vocabulary.  Plain
   leftovers become unsafe intros; Cong, Excl, SF, requirement, and related
   generic markers deliberately pass through without becoming rules. *)
fun add_plain_theorems prefix theorems cs =
  let
    fun add (theorem, (current, index)) =
      if is_passthrough_marker theorem then (current, index)
      else
        let val (name, next) = next_extra_name prefix current index
        in
          (add_intros [(name, theorem)] current, next)
        end
  in
    #1 (List.foldl add (cs, 0) theorems)
  end

fun invocation_claset {prefix} base theorems =
  let val (tagged, leftovers) = process_claset_tags theorems base
  in
    add_plain_theorems prefix leftovers tagged
  end

end
