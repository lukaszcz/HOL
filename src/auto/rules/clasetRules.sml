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

fun specl [] th = th
  | specl (tm :: tms) th = specl tms (SPEC tm th)

fun undisch th =
  MP th (ASSUME (fst (dest_imp (concl th))))

fun curry_conj_premises th =
  case total dest_imp (concl th) of
      NONE => th
    | SOME (prem, _) =>
        if is_conj prem then
          let
            val (left, right) = dest_conj prem
            val tail = snd (dest_imp (concl th))
            val curry =
              SYM (specl [left, right, tail] boolTheory.AND_IMP_INTRO)
          in
            curry_conj_premises (EQ_MP curry th)
          end
        else DISCH prem (curry_conj_premises (undisch th))

fun canonical_rule th =
  let
    val (vars, _) = strip_forall (concl th)
    val body = specl vars th
  in
    GENL vars (curry_conj_premises body)
  end

fun canonical_form th =
  let
    val th' = canonical_rule th
    val (vars, body) = strip_forall (concl th')
    val (prems, cncl) = strip_imp_only body
  in
    {thm = th', patvars = HOLset.fromList Term.compare vars,
     prems = prems, concl = cncl}
  end

fun rule_premises th = #prems (canonical_form th)
fun rule_conclusion th = #concl (canonical_form th)

fun rule_index Intro th = rule_conclusion th
  | rule_index (Elim | Dest) th =
      (case rule_premises th of
          prem :: _ => prem
        | [] =>
            raise mk_HOL_ERR "clasetRules" "rule_index"
              "Ill-formed elimination rule: no major premise")

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

fun decl_order (d1 : decl, d2 : decl) =
  let
    val safe1 = #safe (#spec d1)
    val safe2 = #safe (#spec d2)
  in
    if safe1 andalso not safe2 then LESS
    else if safe2 andalso not safe1 then GREATER
    else compare_tag (#tag d1, #tag d2)
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
   info = info, orig = canonical_rule orig}

fun get_decls (Decls {byconcl, ...}) th =
  case Termtab.lookup byconcl (canonical_key th) of
      NONE => []
    | SOME ds => ds

fun has_decls decls th = not (List.null (get_decls decls th))

fun dest_decls (Decls {byconcl, ...}) =
  Listsort.sort decl_order
    (Termtab.fold (fn (_, ds) => fn acc => ds @ acc) byconcl [])

fun duplicate decl ds =
  List.exists (fn old => same_kind (#spec decl) (#spec old)) ds

fun extend_decl (decl : decl) (Decls {next, byconcl, byname}) =
  let
    val key = canonical_key (#orig decl)
    val old = Option.getOpt (Termtab.lookup byconcl key, [])
  in
    if duplicate decl old orelse
       Option.isSome (Symtab.lookup byname (#name decl))
    then (NONE, Decls {next = next, byconcl = byconcl, byname = byname})
    else
      let
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
      can (fn n => Theory.uptodate_thm (DB.fetch_knm n)) name
  | uptodate_delta (RM _) = true

end
