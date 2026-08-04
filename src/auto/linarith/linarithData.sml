structure linarithData :> linarithData =
struct

open Abbrev HolKernel

val ERR = mk_HOL_ERR "linarithData"

fun same_type left right = Type.compare (left, right) = EQUAL

(* The layer's deduplication idiom, spelled once: one item per key, in
   order of first occurrence.  Every caller here keys on something
   ordered -- a conclusion, a coefficient row, an atom -- so the set is
   the comparison's, and a scan for the key with a linear membership
   test would cost a quadratic number of those comparisons over lists
   that accumulate across the rounds of a search. *)
fun distinct_by compare key items =
  let
    fun add (item, entry as (seen, kept)) =
      let
        val item_key = key item
      in
        if HOLset.member (seen, item_key) then entry
        else (HOLset.add (seen, item_key), item :: kept)
      end
    val (_, kept) = List.foldl add (HOLset.empty compare, []) items
  in
    List.rev kept
  end

type linarith_instance = {
  ty : hol_type,
  discrete : {lessD : thm list} option,
  dest : {
    dest_plus : term -> term * term,
    dest_minus : (term -> term * term) option,
    dest_neg : (term -> term) option,
    dest_mult : term -> term * term,
    dest_div : (term -> term * term) option,
    dest_suc : (term -> term) option,
    dest_lit : term -> Arbrat.rat,
    mk_lit : Arbrat.rat -> term,
    dest_less : term -> term * term,
    dest_leq : term -> term * term
  },
  kit : {
    add_mono : thm list,
    mult_mono : thm list,
    not_less : thm,
    not_le : thm,
    neqE : thm,
    nonneg : term -> thm option
  },
  norm_conv : conv,
  nnf_rules : thm list,
  pre_split : thm list,
  atom_facts : term -> thm list
}

(* The dest record is matched whole, without a ... wildcard, so that a
   new destructor is a compile error here instead of a silently wrong
   complement at the sites that reason about it. *)
fun build_compound_ops
      ({dest = {dest_plus = _, dest_minus, dest_neg, dest_mult = _,
                dest_div, dest_suc, dest_lit = _, mk_lit = _,
                dest_less = _, dest_leq = _}, ...} : linarith_instance) =
  let
    fun recognises f tm = Option.isSome (Lib.total f tm)
  in
    List.mapPartial Lib.I
      [Option.map recognises dest_minus,
       Option.map recognises dest_neg,
       Option.map recognises dest_div,
       Option.map recognises dest_suc]
  end

type linarith_injection = {
  from_ty : hol_type,
  to_ty : hol_type,
  inj : term,
  hom : {le : thm, lt : thm, eq : thm, add : thm, mul : thm}
}

(* The registries below are the only mutable state a derivation can be
   read out of, and register_instance and register_injection are their
   only mutators, so one counter bumped there is an exact change signal
   for anything derived from them. *)
val registry_generation = Sref.new 0

fun generation () = Sref.value registry_generation

fun bump_generation () =
  Sref.update registry_generation (fn count => count + 1)

(* The equality is the caller's because not every source of a key is an
   equality type: a derivation keyed on a table of theorems compares
   them by pointer.  A false key comparison costs a recomputation and
   nothing else, so the cache cell needs no more synchronization than
   the source it is read against. *)
fun keyed_memo same compute =
  let
    val cache = ref NONE
    fun recompute key =
      let
        val value = compute key
      in
        cache := SOME (key, value); value
      end
  in
    fn key =>
      case !cache of
          SOME (recorded, value) =>
            if same recorded key then value else recompute key
        | NONE => recompute key
  end

(* A memo whose key is read from the session rather than passed in:
   compute takes no argument, and each call reads key for itself. *)
fun memo_on key compute =
  let
    val cached = keyed_memo Lib.equal (fn _ => compute ())
  in
    fn () => cached (key ())
  end

fun memo compute = memo_on generation compute

(* Both directions of an equivalence, or an implication as it stands.
   Replay MATCH_MPs against the result, so a rule that is neither is
   offered unchanged and simply fails to match. *)
fun implications theorem =
  if boolSyntax.is_imp
       (snd (boolSyntax.strip_forall (Thm.concl theorem)))
  then [theorem]
  else
    let
      val (forward, backward) =
        Thm.EQ_IMP_RULE (Drule.SPEC_ALL theorem)
    in
      [Drule.GEN_ALL forward, Drule.GEN_ALL backward]
    end
    handle HOL_ERR _ => [theorem]

type instance_implications = {
  add_mono : thm list,
  mult_mono : thm list list,
  not_less : thm list,
  not_le : thm list,
  neqE : thm list,
  lessD : thm list
}

type instance_derived = {
  implications : instance_implications,
  compound_ops : (term -> bool) list
}

(* The kit is matched whole, for the reason dest is: a rule added to it
   is then a compile error here rather than a rule replay re-derives
   per certificate node.  Only a discrete carrier can strengthen a
   strict inequality to the non-strict one about its successor, so
   lessD is empty for a dense one and the LessD and NotLeDD
   justifications never arise for it. *)
fun derive_implications (instance : linarith_instance) =
  let
    val {add_mono, mult_mono, not_less, not_le, neqE, nonneg = _} =
      #kit instance
    val lessD =
      case #discrete instance of
          SOME {lessD} => lessD
        | NONE => []
  in
    {add_mono = List.concat (map implications add_mono),
     mult_mono = map implications mult_mono,
     not_less = implications not_less,
     not_le = implications not_le,
     neqE = implications neqE,
     lessD = List.concat (map implications lessD)}
  end

fun derive_instance instance =
  {implications = derive_implications instance,
   compound_ops = build_compound_ops instance}

val instance_registry =
  Sref.new ([] : (linarith_instance * instance_derived) list)

fun instance_entries () = Sref.value instance_registry

fun register_instance instance =
  let
    val ty = #ty instance
    fun same_carrier (entry, _) = same_type ty (#ty entry)
    val entry = (instance, derive_instance instance)
    val replaced =
      Sref.gen_update instance_registry
        (fn entries =>
          (entry :: List.filter (not o same_carrier) entries,
           List.exists same_carrier entries))
    val _ = bump_generation ()
  in
    if replaced then
      HOL_WARNING "linarithData" "register_instance"
        ("replacing the linarith instance for type " ^
         Parse.type_to_string ty)
    else
      ()
  end

(* Decomposition asks for the carrier of every subterm it examines, so
   the registry is indexed rather than scanned; register_instance keeps
   one entry per carrier, so the index loses nothing. *)
val instance_table =
  memo
    (fn () =>
      List.foldl
        (fn (entry as (instance, _), table) =>
          Redblackmap.insert (table, #ty instance, entry))
        (Redblackmap.mkDict Type.compare)
        (instance_entries ()))

fun instance_entry ty = Redblackmap.peek (instance_table (), ty)

fun instance_for ty = Option.map #1 (instance_entry ty)

val all_instances = memo (fn () => map #1 (instance_entries ()))

(* The entry itself is the key, not just its carrier type: an instance
   built and handed straight to replay, or one that has since been
   replaced, must get its own derivation rather than the registered
   instance's.  Identity is what decides that -- the carrier only says
   which entry could possibly be it -- and a comparison that says "not
   this one" when it is costs a recomputation, never a wrong answer. *)
fun derived_instance instance =
  case instance_entry (#ty instance) of
      SOME (entry, derived) =>
        if Portable.pointer_eq (entry, instance) then derived
        else derive_instance instance
    | NONE => derive_instance instance

fun instance_implications instance = #implications (derived_instance instance)

fun compound_ops instance = #compound_ops (derived_instance instance)

fun same_injection left right =
  (same_type (#from_ty left) (#from_ty right) andalso
   same_type (#to_ty left) (#to_ty right)) orelse
  Term.aconv (#inj left) (#inj right)

fun injection_at_top injection tm =
  case Lib.total Term.dest_comb tm of
      SOME (operator, _) => Term.aconv operator (#inj injection)
    | NONE => false

fun orient_injection_hom injection theorem =
  let
    val opened = Drule.SPEC_ALL theorem
    val (left, right) = boolSyntax.dest_eq (Thm.concl opened)
  in
    if injection_at_top injection left then opened
    else if injection_at_top injection right then Thm.SYM opened
    else opened
  end

fun injection_rewrites injection =
  let
    val hom = #hom injection
  in
    List.mapPartial
      (Lib.total (orient_injection_hom injection))
      [#add hom, #mul hom]
  end

(* REWR_CONV precomputes a pattern per rewrite, which is the work this
   whole derivation exists to do once.  No rewrites means nothing to
   do, which is what UNCHANGED says. *)
fun rewrites_conv [] = Conv.ALL_CONV
  | rewrites_conv rewrites =
      Conv.TOP_DEPTH_CONV
        (Conv.FIRST_CONV (map Conv.REWR_CONV rewrites))

(* The order homomorphisms decide that a relation lifts along the
   injection, and replay matches against their implications once per
   injection per theorem of a conversion closure, so they are derived
   here beside the rewrites that push the injection inwards again. *)
type derived_injection = {
  injection : linarith_injection,
  relation_imps : thm list,
  rewrites : thm list,
  rewrite_conv : conv
}

fun derive_injection injection =
  let
    val hom = #hom injection
    val rewrites = injection_rewrites injection
  in
    {injection = injection,
     relation_imps =
       List.concat (map implications [#le hom, #lt hom, #eq hom]),
     rewrites = rewrites,
     rewrite_conv = rewrites_conv rewrites}
  end

(* The registry holds the derivations themselves, so walking every
   injection's derivation costs no lookup at all. *)
val injection_registry = Sref.new ([] : derived_injection list)

fun injection_entries () = Sref.value injection_registry

fun register_injection injection =
  let
    val entry = derive_injection injection
  in
    Sref.update injection_registry
      (fn entries =>
        entry ::
        List.filter
          (not o same_injection injection o #injection) entries);
    bump_generation ()
  end

val derived_injections = injection_entries

val injections = memo (fn () => map #injection (injection_entries ()))

(* Indexed like the instances, and for the same reason: decomposition
   asks about the head of every application it meets and about the type
   of every factor whose injection it has to restore.  Registration
   keeps one entry per injected constant and one per ordered pair of
   types, so neither index loses an entry. *)
val injection_tables =
  memo
    (fn () =>
      let
        val entries = injection_entries ()
        fun add_typed (entry : derived_injection, table) =
          Redblackmap.insert
            (table,
             (#from_ty (#injection entry), #to_ty (#injection entry)),
             entry)
        fun add_const (entry : derived_injection, table) =
          Redblackmap.insert (table, #inj (#injection entry), entry)
        val by_types =
          Redblackmap.mkDict (Lib.pair_compare (Type.compare, Type.compare))
        val by_const = Redblackmap.mkDict Term.compare
      in
        (List.foldl add_typed by_types entries,
         List.foldl add_const by_const entries)
      end)

fun injection_for from_ty to_ty =
  Option.map #injection
    (Redblackmap.peek (#1 (injection_tables ()), (from_ty, to_ty)))

fun injection_by_const constant =
  Option.map #injection
    (Redblackmap.peek (#2 (injection_tables ()), constant))

val all_injection_rewrite_conv =
  memo
    (fn () =>
      rewrites_conv
        (List.concat (map #rewrites (injection_entries ()))))

val persistent_name = KernelSig.name_toString

fun apply_arith_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        Symtab.update (persistent_name name, theorem) table
    | ThmSetData.REMOVE name =>
        Symtab.delete_safe (ThmSetData.toKString name) table

(* The P-form test is the whole of split validation; the two channels
   differ only in how they name what they rejected. *)
fun check_asm_split function what theorem =
  (ignore (splitLib.is_asm_split theorem)
   handle HOL_ERR _ => raise ERR function ("Malformed " ^ what))

fun apply_arith_split_delta delta table =
  case delta of
      ThmSetData.ADD (name, theorem) =>
        let
          val _ =
            check_asm_split "apply_arith_split_delta"
              ("[arith_split] theorem " ^ persistent_name name) theorem
        in
          Symtab.update (persistent_name name, theorem) table
        end
    | ThmSetData.REMOVE name =>
        Symtab.delete_safe (ThmSetData.toKString name) table

fun guard_registration settype =
  if List.exists (equal settype) (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute settype
  then
    raise ERR "registration"
      ("settype or attribute " ^ settype ^ " already exists")
  else
    ()

val _ = guard_registration "arith"
val _ = guard_registration "arith_split"

val arith_data =
  ThmSetData.export_with_ancestry
    {settype = "arith",
     delta_ops =
       {apply_to_global = apply_arith_delta,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_arith_delta}}

val arith_split_data =
  ThmSetData.export_with_ancestry
    {settype = "arith_split",
     delta_ops =
       {apply_to_global = apply_arith_split_delta,
        thy_finaliser = NONE,
        uptodate_delta = K true,
        initial_value = Symtab.empty,
        apply_delta = apply_arith_split_delta}}

fun table_thms data = map #2 (Symtab.dest (#get_global_value data ()))

fun arith_facts () = table_thms arith_data
fun arith_split_thms () = table_thms arith_split_data

fun remove data apply_delta name =
  let
    val delta = ThmSetData.REMOVE name
    val _ = #update_global_value data (apply_delta delta)
  in
    #record_delta data delta
  end

fun remove_arith name = remove arith_data apply_arith_delta name
fun remove_arith_split name =
  remove arith_split_data apply_arith_split_delta name

(* Theorem names are the table's keys, so its key set changes on every
   add, every remove, and every wholesale replacement by set_parents --
   the path a counter bumped at the delta sites would miss, because
   AncestryData's set_ancestry installs a whole table without applying
   a delta to the old one.  Extracting and comparing the keys costs a
   fraction of the split-net build it guards. *)
fun arith_split_keys () =
  map #1 (Symtab.dest (#get_global_value arith_split_data ()))

fun memo_with_splits compute =
  memo_on (fn () => (generation (), arith_split_keys ())) compute

type linarith_config = {neq_limit : int, split_limit : int}

val default_config : linarith_config = {neq_limit = 9, split_limit = 9}

val trace_level = ref 0
val _ = Feedback.register_trace ("linarith", trace_level, 3)

fun tracing level = !trace_level >= level

(* Rendering a theorem or a term list costs more than the test that
   decides whether anyone will read it, so every helper asks first.  A
   caller that has to build its message itself asks with tracing. *)
fun trace level message =
  if tracing level then print ("linarith: " ^ message ^ "\n") else ()

fun trace_thm level label theorem =
  if tracing level then
    trace level (label ^ "\n" ^ Parse.thm_to_string theorem)
  else ()

fun trace_items level label render items =
  if tracing level then
    trace level
      (label ^
       (if null items then " <none>"
        else "\n" ^ String.concatWith "\n" (map render items)))
  else ()

fun trace_terms level label terms =
  trace_items level label Parse.term_to_string terms

end
