structure clasetRules :> clasetRules =
struct

open HolKernel boolSyntax

type term = Term.term
type thm = Thm.thm
type thname = KernelSig.kernelname

datatype rulekind = Intro | Elim | Dest
type rulespec = {kind : rulekind, safe : bool, prio : int option}
type tag = {weight : int, index : int}
type brl = bool * thm
type rl = thm * thm option
type info = {rl : rl, dup_rl : rl}
type decl =
  {name : string, spec : rulespec, tag : tag, info : info, orig : thm}

type canonical =
  {thm : thm, patvars : term HOLset.set, prems : term list, concl : term}

(* Keep explicit negations opaque: dest_imp also treats ~P as P ==> F. *)
fun undisch th =
  MP th (ASSUME (fst (dest_imp_only (concl th))))

fun curry_conj_premises th =
  case total dest_imp_only (concl th) of
      NONE => th
    | SOME (prem, _) =>
        if is_conj prem then
          let
            val (left, right) = dest_conj prem
            val tail = snd (dest_imp_only (concl th))
            val curry =
              SYM (Drule.SPECL [left, right, tail] boolTheory.AND_IMP_INTRO)
          in
            curry_conj_premises (EQ_MP curry th)
          end
        else DISCH prem (curry_conj_premises (undisch th))

(* [curry_conj_premises] only rewrites a theorem whose implication spine has
   a top-level conjunction premise, so a theorem without one is already
   canonical.  ext_info re-derives from an already canonical theorem many
   times; short-circuiting keeps those calls from redoing the kernel work. *)
fun is_canonical th =
  let
    fun spine tm =
      case total dest_imp_only tm of
          NONE => true
        | SOME (prem, rest) => not (is_conj prem) andalso spine rest
  in
    spine (snd (strip_forall (concl th)))
  end

(* A quantified variable may also occur free in a theorem hypothesis (the
   quantifier then shadows that free variable in the conclusion).  Such a
   theorem is valid, but specializing and later generalizing with the
   stripped binder itself would make GEN reject the free hypothesis. *)
fun fresh_forall_vars th vars =
  let
    fun freshen avoids [] = []
      | freshen avoids (v :: vs) =
          let val v' = variant avoids v
          in v' :: freshen (v' :: avoids) vs end
  in
    freshen (free_varsl (hyp th)) vars
  end

fun canonical_rule th =
  if is_canonical th then th
  else
    let
      val (vars, _) = strip_forall (concl th)
      val vars' = fresh_forall_vars th vars
      val body = Drule.SPECL vars' th
    in
      GENL vars' (curry_conj_premises body)
    end

(* Elimination rules keep their first premise as the major premise.  The
   generic canonicalizer still curries conjunctions in introduction-rule
   premises and in the side premises below the major premise. *)
fun canonical_elim_rule th =
  let
    val (vars, _) = strip_forall (concl th)
    val vars' = fresh_forall_vars th vars
    val body = Drule.SPECL vars' th
  in
    case total dest_imp_only (concl body) of
        NONE => canonical_rule th
      | SOME (major, _) =>
          let
            val tail = MP body (ASSUME major)
            val tail' = curry_conj_premises tail
          in
            GENL vars' (DISCH major tail')
          end
  end

fun canonical_rule_of Intro = canonical_rule
  | canonical_rule_of (Elim | Dest) = canonical_elim_rule

fun form_of th' =
  let
    val (vars, body) = strip_forall (concl th')
    val (prems, cncl) = strip_imp_only body
  in
    {thm = th', patvars = HOLset.fromList Term.compare vars,
     prems = prems, concl = cncl}
  end

fun canonical_form th = form_of (canonical_rule th)
fun canonical_form_of kind th = form_of (canonical_rule_of kind th)

fun rule_premises th = #prems (canonical_form th)
fun rule_premises_of kind th = #prems (canonical_form_of kind th)
fun rule_conclusion th = #concl (canonical_form th)

fun kind_name Intro = "introduction"
  | kind_name Elim = "elimination"
  | kind_name Dest = "destruction"

fun illformed_rule fname kind =
  raise mk_HOL_ERR "clasetRules" fname
    ("Ill-formed " ^ kind_name kind ^ " rule")

fun rule_index_of Intro (form : canonical) = #concl form
  | rule_index_of (kind as (Elim | Dest)) form =
      (case #prems form of
          prem :: _ => prem
        | [] => illformed_rule "rule_index" kind)

fun rule_index kind th = rule_index_of kind (canonical_form_of kind th)

(* The derived rules below operate on this outer spine only.  In
   particular, a premise such as !x. P x ==> q is always one premise. *)
fun rule_spine_with canonicalize th =
  let
    val th' = canonicalize th
    val (vars, _) = strip_forall (concl th')
    val vars' = fresh_forall_vars th' vars
    val core = Drule.SPECL vars' th'
    val (prems, cncl) = strip_imp_only (concl core)
  in
    {thm = th', vars = vars', core = core, prems = prems, concl = cncl}
  end

val rule_spine = rule_spine_with canonical_rule
val elim_rule_spine = rule_spine_with canonical_elim_rule

fun apply_assumed th prems = Drule.LIST_MP (map ASSUME prems) th

fun apply_thms th prems = Drule.LIST_MP prems th

fun discharge_prems prems th = Lib.itlist DISCH prems th

fun finish_rule vars extras prems th =
  GENL (vars @ extras) (discharge_prems prems th)

fun fresh_bool th =
  variant (free_varsl (concl th :: hyp th)) (mk_var ("r", bool))

fun false_of not_tm tm_th = MP (NOT_ELIM not_tm) tm_th

fun MAKE_ELIM_RULE th =
  let
    val {vars, core, prems, concl, ...} = elim_rule_spine th
    val r = fresh_bool core
    val br = mk_imp (concl, r)
    val bth = apply_assumed core prems
    val rth = MP (ASSUME br) bth
  in
    finish_rule vars [r] (prems @ [br]) rth
  end

fun CLASSICAL_RULE th =
  let
    val {thm, vars, core, prems, concl, ...} = elim_rule_spine th
  in
    case prems of
        [] => illformed_rule "CLASSICAL_RULE" Elim
      | major :: rest =>
          if not (is_var concl) then thm
          else
            let
              fun needs_repair prem =
                not (Term.aconv (snd (strip_imp_only prem)) concl)
              val repairs = map needs_repair rest
              fun repair (prem, true) = mk_imp (mk_neg concl, prem)
                | repair (prem, false) = prem
              val rest' = ListPair.map repair (rest, repairs)
            in
              if not (List.exists (fn b => b) repairs) then thm
              else
                let
                  val hmajor = ASSUME major
                  val hprems = map ASSUME rest'
                  fun old_prem (h, true) = MP h (ASSUME (mk_neg concl))
                    | old_prem (h, false) = h
                  val negative' =
                    apply_thms core
                      (hmajor ::
                       ListPair.map old_prem (hprems, repairs))
                  val body =
                    DISJ_CASES (SPEC concl boolTheory.EXCLUDED_MIDDLE)
                      (ASSUME concl) negative'
                in
                  finish_rule vars [] (major :: rest') body
                end
            end
  end

fun patvars vars = HOLset.fromList Term.compare vars

fun rigid_frees pat vars =
  HOLset.fromList Term.compare
    (List.filter (fn v => not (HOLset.member (vars, v))) (free_vars pat))

fun is_instance pat vars tm =
  can (Term.raw_match [] (rigid_frees pat vars) pat tm) ([], [])

fun negation_headed tm =
  is_neg tm orelse
  (case total dest_imp tm of
       SOME (_, rhs) => Term.aconv rhs F
     | NONE => false)

fun SWAP_INTRO_RULE th =
  let
    val {vars, core, prems, concl, ...} = rule_spine th
    val not_concl = mk_neg concl
  in
    if negation_headed concl orelse
       is_instance concl (patvars vars) not_concl
    then NONE
    else
      let
        val r = fresh_bool core
        val not_r = mk_neg r
        val lifted = map (fn prem => mk_imp (not_r, prem)) prems
        val hnot_concl = ASSUME not_concl
        val hprems = map ASSUME lifted
        val args = map (fn h => MP h (ASSUME not_r)) hprems
        val cth = apply_thms core args
        val body = CCONTR r (false_of hnot_concl cth)
      in
        SOME (finish_rule vars [r] (not_concl :: lifted) body)
      end
  end

fun DUP_INTRO_RULE th =
  let
    val {vars, core, prems, concl, ...} = rule_spine th
    val not_concl = mk_neg concl
    val lifted = map (fn prem => mk_imp (not_concl, prem)) prems
    val hprems = map ASSUME lifted
    val args = map (fn h => MP h (ASSUME not_concl)) hprems
    val cth = apply_thms core args
    val body = CCONTR concl (false_of (ASSUME not_concl) cth)
  in
    finish_rule vars [] lifted body
  end

fun DUP_ELIM_RULE th =
  let
    val {thm, vars, core, prems, ...} = elim_rule_spine th
  in
    case prems of
        [] => illformed_rule "DUP_ELIM_RULE" Elim
      | major :: rest =>
          let
            val lifted = map (fn prem => mk_imp (major, prem)) rest
            val hmajor = ASSUME major
            val hprems = map ASSUME lifted
            val args = map (fn h => MP h hmajor) hprems
            val body = apply_thms core (hmajor :: args)
          in
            finish_rule vars [] (major :: lifted) body
          end
  end

(* HOL goals cons each newly discharged hypothesis.  Put the duplicate at
   the inner end of a minor premise so that it is first in the resulting
   assumption list, as required by blast's reverse duplication rule. *)
fun rev_dup_prem major prem =
  case total dest_forall prem of
      SOME (v, body) =>
        let
          val v' =
            if free_in v major then
              variant (free_vars major @ free_vars body) v
            else v
          val body' =
            if Term.aconv v v' then body else subst [v |-> v'] body
        in
          mk_forall (v', rev_dup_prem major body')
        end
    | NONE =>
        (case total dest_imp_only prem of
             SOME (ante, rest) =>
               mk_imp (ante, rev_dup_prem major rest)
           | NONE => mk_imp (major, prem))

fun restore_rev_dup_prem major prem hmajor hprem =
  case total dest_forall prem of
      SOME (v, body) =>
        let
          val avoids = free_varsl (major :: concl hprem :: hyp hprem)
          val v' = variant avoids v
          val body' =
            if Term.aconv v v' then body else subst [v |-> v'] body
        in
          GEN v'
            (restore_rev_dup_prem major body' hmajor (SPEC v' hprem))
        end
    | NONE =>
        (case total dest_imp_only prem of
             SOME (ante, rest) =>
               DISCH ante
                 (restore_rev_dup_prem major rest hmajor
                    (MP hprem (ASSUME ante)))
           | NONE => MP hprem hmajor)

fun REV_DUP_ELIM_RULE th =
  let
    val {thm, vars, core, prems, ...} = elim_rule_spine th
  in
    case prems of
        [] => illformed_rule "REV_DUP_ELIM_RULE" Elim
      | [_] => thm
      | major :: rest =>
          let
            val lifted = map (rev_dup_prem major) rest
            val hmajor = ASSUME major
            val hprems = map ASSUME lifted
            fun restore (prem, hprem) =
              restore_rev_dup_prem major prem hmajor hprem
            val args = ListPair.map restore (rest, hprems)
            val body = apply_thms core (hmajor :: args)
          in
            finish_rule vars [] (major :: lifted) body
          end
  end

fun ext_info ({kind, safe, ...} : rulespec) th =
  let
    val th' = canonical_rule_of kind th
    fun elim_rule () =
      let
        val _ = (case rule_premises_of kind th' of
                    [] => illformed_rule "ext_info" kind
                  | _ => ())
        val elim = if kind = Dest then MAKE_ELIM_RULE th' else th'
      in
        CLASSICAL_RULE elim
      end
    fun intro_info () =
      let
        val rl = (th', SWAP_INTRO_RULE th')
      in
        if safe then {rl = rl, dup_rl = rl}
        else
          let
            val dup = DUP_INTRO_RULE th'
              handle HOL_ERR _ => illformed_rule "ext_info" Intro
          in
            {rl = rl, dup_rl = (dup, SWAP_INTRO_RULE dup)}
          end
      end
    fun elim_info () =
      let
        val elim = elim_rule ()
        val rl = (elim, NONE)
      in
        if safe then {rl = rl, dup_rl = rl}
        else
          let
            val dup = DUP_ELIM_RULE elim
              handle HOL_ERR _ => illformed_rule "ext_info" kind
          in
            {rl = rl, dup_rl = (dup, NONE)}
          end
      end
  in
    case kind of
        Intro => intro_info ()
      | Elim => elim_info ()
      | Dest => elim_info ()
  end

datatype safe_class = Safe0 | SafeP

fun subgoals_of (is_elim, th) =
  let
    val kind = if is_elim then Elim else Intro
    val n = length (rule_premises_of kind th)
  in
    if is_elim then n - 1 else n
  end

fun safe_class_of ({kind, safe, ...} : rulespec) ({rl, ...} : info) =
  if not safe then NONE
  else if subgoals_of (kind <> Intro, #1 rl) = 0 then SOME Safe0
  else SOME SafeP

fun compare_tag ({weight = w1, index = i1} : tag,
                 {weight = w2, index = i2} : tag) =
  case Int.compare (w1, w2) of
      EQUAL => Int.compare (i1, i2)
    | ord => ord

fun candidate_order candidates =
  Listsort.sort (fn ((tag1, _), (tag2, _)) => compare_tag (tag1, tag2))
                candidates

fun same_kind ({kind = kind1, safe = safe1, ...} : rulespec)
              ({kind = kind2, safe = safe2, ...} : rulespec) =
  kind1 = kind2 andalso safe1 = safe2

fun is_elim Intro = false
  | is_elim _ = true

fun kind_index Intro = 0
  | kind_index Elim = 1
  | kind_index Dest = 2

(* Match Bires.decl_ord: declarations are grouped by kind-class before
   their decreasing insertion tags establish recency within that class. *)
fun decl_order (d1 : decl, d2 : decl) =
  let
    val spec1 = #spec d1
    val spec2 = #spec d2
    val safe1 = #safe spec1
    val safe2 = #safe spec2
    val safe_order =
      if safe1 andalso not safe2 then LESS
      else if safe2 andalso not safe1 then GREATER
      else EQUAL
  in
    case safe_order of
        EQUAL =>
          (case Int.compare (kind_index (#kind spec1),
                             kind_index (#kind spec2)) of
               EQUAL => compare_tag (#tag d1, #tag d2)
             | order => order)
      | order => order
  end

(* This is Bires.decl_merge_ord.  Replaying an incoming claset in this
   order gives fresh decreasing indices the same canonical relative order. *)
fun decl_merge_order (d1 : decl, d2 : decl) =
  case (is_elim (#kind (#spec d1)), is_elim (#kind (#spec d2))) of
      (false, true) => LESS
    | (true, false) => GREATER
    | _ =>
        (case compare_tag (#tag d1, #tag d2) of
            LESS => GREATER
          | EQUAL => EQUAL
          | GREATER => LESS)

fun canonical_key th = concl (canonical_rule th)

datatype decls =
  Decls of {next : int, byconcl : decl list Termtab.table,
            byname : decl Symtab.table}

val empty_decls =
  Decls {next = ~1, byconcl = Termtab.empty, byname = Symtab.empty}

fun make_decl {name, spec, weight, info, orig} =
  {name = name, spec = spec, tag = {weight = weight, index = 0},
   info = info, orig = canonical_rule_of (#kind spec) orig}

fun get_decls (Decls {byconcl, ...}) th =
  case Termtab.lookup byconcl (canonical_key th) of
      NONE => []
    | SOME ds => ds

fun has_decls decls th = not (List.null (get_decls decls th))

fun decl_name_member (Decls {byname, ...}) name =
  Option.isSome (Symtab.lookup byname name)

fun dest_decls (Decls {byconcl, ...}) =
  Listsort.sort decl_order
    (Termtab.fold (fn (_, ds) => fn acc => ds @ acc) byconcl [])

fun duplicate decl ds =
  List.exists (fn old => same_kind (#spec decl) (#spec old)) ds

fun rule_description ({kind, safe, ...} : rulespec) =
  (if safe then "safe " else "unsafe ") ^ kind_name kind ^ " rule"

fun extend_decl (decl : decl) (Decls {next, byconcl, byname}) =
  let
    val key = canonical_key (#orig decl)
    val old = Option.getOpt (Termtab.lookup byconcl key, [])
    val unchanged = Decls {next = next, byconcl = byconcl, byname = byname}
  in
    if duplicate decl old orelse
       Option.isSome (Symtab.lookup byname (#name decl))
    then
      (HOL_WARNING "clasetRules" "extend_decl"
         ("Ignoring duplicate " ^ rule_description (#spec decl));
       (NONE, unchanged))
    else
      let
        val _ =
          if List.exists (fn old => not (same_kind (#spec decl) (#spec old)))
                         old
          then HOL_WARNING "clasetRules" "extend_decl"
                 ("Rule already declared as a different " ^
                  rule_description (#spec (hd old)))
          else ()
        val {weight, ...} = #tag decl
        val decl' =
          {name = #name decl, spec = #spec decl,
           tag = {weight = weight, index = next}, info = #info decl,
           orig = #orig decl}
      in
        (SOME decl',
         Decls {next = next - 1,
                byconcl = Termtab.update (key, decl' :: old) byconcl,
                byname = Symtab.update (#name decl', decl') byname})
      end
  end

fun remove_decl name (decls as Decls {next, byconcl, byname}) =
  case Symtab.lookup byname name of
      NONE => ([], decls)
    | SOME decl =>
        let
          val key = canonical_key (#orig decl)
          val old = Option.getOpt (Termtab.lookup byconcl key, [])
          val kept = List.filter (fn d => #name d <> name) old
          val byconcl' =
            if List.null kept then Termtab.delete_safe key byconcl
            else Termtab.update (key, kept) byconcl
        in
          ([decl],
           Decls {next = next, byconcl = byconcl',
                  byname = Symtab.delete_safe name byname})
        end

fun merge_decls (left, right) =
  let
    val incoming = Listsort.sort decl_merge_order (dest_decls right)
    fun add [] decls added = (List.rev added, decls)
      | add (decl :: rest) decls added =
          (case extend_decl decl decls of
              (NONE, decls') => add rest decls' added
            | (SOME decl', decls') => add rest decls' (decl' :: added))
  in
    add incoming left []
  end

datatype cdelta = ADD of {name : thname, spec : rulespec} | RM of string

fun kind_encode Intro = ThyDataSexp.String "intro"
  | kind_encode Elim = ThyDataSexp.String "elim"
  | kind_encode Dest = ThyDataSexp.String "dest"

fun kind_decode (ThyDataSexp.String "intro") = SOME Intro
  | kind_decode (ThyDataSexp.String "elim") = SOME Elim
  | kind_decode (ThyDataSexp.String "dest") = SOME Dest
  | kind_decode _ = NONE

fun spec_encode ({kind, safe, prio} : rulespec) =
  ThyDataSexp.pair3_encode
    (kind_encode, ThyDataSexp.Bool,
     ThyDataSexp.option_encode ThyDataSexp.Int) (kind, safe, prio)

fun spec_decode sexp =
  Option.map (fn (kind, safe, prio) =>
                {kind = kind, safe = safe, prio = prio})
    (ThyDataSexp.pair3_decode
       (kind_decode, ThyDataSexp.bool_decode,
        ThyDataSexp.option_decode ThyDataSexp.int_decode) sexp)

fun encode_delta (ADD {name, spec}) =
      ThyDataSexp.tag_encode "clasetADD1"
        (ThyDataSexp.pair_encode (ThyDataSexp.KName, spec_encode))
        (name, spec)
  | encode_delta (RM name) =
      ThyDataSexp.tag_encode "clasetRM1" ThyDataSexp.String name

fun dec_add sexp =
  Option.map (fn (name, spec) => ADD {name = name, spec = spec})
    (ThyDataSexp.tag_decode "clasetADD1"
       (ThyDataSexp.pair_decode (ThyDataSexp.kname_decode, spec_decode))
       sexp)

fun dec_rm sexp =
  Option.map RM
    (ThyDataSexp.tag_decode "clasetRM1" ThyDataSexp.string_decode sexp)

fun decode_delta sexp = ThyDataSexp.first [dec_add, dec_rm] sexp

fun load_delta (ADD {name, spec}) =
      (SOME (name, spec, DB.fetch_knm name)
       handle HOL_ERR _ =>
         (HOL_WARNING "clasetRules" "load_delta"
            ("Bad claset add command, dropping theorem " ^
             KernelSig.name_toString name);
          NONE))
  | load_delta (RM _) = NONE

fun uptodate_delta (ADD {name, ...}) =
      (Theory.uptodate_thm (DB.fetch_knm name)
       handle HOL_ERR _ =>
         (HOL_WARNING "clasetRules" "uptodate_delta"
            ("Bad claset add command, dropping theorem " ^
             KernelSig.name_toString name);
          false))
  | uptodate_delta (RM _) = true

end
