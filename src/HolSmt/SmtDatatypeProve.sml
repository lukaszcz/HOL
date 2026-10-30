(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB datatype lemmas. *)

structure SmtDatatypeProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtDatatypeProve"

  fun profile name f x = Profile.profile_with_exn_name name f x

  val metis_limit : mlibMeter.limit = {time = SOME 1.0, infs = SOME 5000}
  fun with_metis_limit f = Lib.with_flag (metisTools.limit, metis_limit) f

  fun unsupported t =
    raise ERR "datatype_prove"
      ("unsupported th-lemma shape: theory=datatype; checked replay is only " ^
       "implemented for TypeBase datatype disjointness, injectivity, " ^
       "selector/tester, case-split reconstruction, exhaustiveness, " ^
       "and acyclicity lemmas; conclusion=" ^
       Library.term_to_string t)

  fun add_ty ty tys = if List.exists (fn ty' => ty' = ty) tys then tys
                      else ty :: tys

  fun type_closure ty tys =
    let
      val tys = add_ty ty tys
      val args = Lib.total (Lib.snd o Type.dest_type) ty
    in
      case args of
        NONE => tys
      | SOME args => List.foldl (fn (arg, acc) => type_closure arg acc)
          tys args
    end

  fun subterms t = HolKernel.find_terms (fn _ => true) t

  fun term_types t =
    List.foldl (fn (tm, acc) => type_closure (Term.type_of tm) acc)
      [] (subterms t)

  fun has_constructors ty =
    case TypeBase.fetch ty of
      NONE => false
    | SOME tyi => not (List.null (TypeBasePure.constructors_of tyi))

  fun type_has_name thy tyop ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty
    in Thy = thy andalso Tyop = tyop end
    handle Feedback.HOL_ERR _ => false

  (* These TypeBase types have an earlier semantic owner in the replay
     ladder.  In particular, [num] must not make every arithmetic or word
     term look like a datatype obligation merely because it occurs as an
     index or subterm.  Lists, products, sums, and options stay here: their
     constructor laws are genuine datatype facts even when another rung
     owns operations over a related theory such as sequences. *)
  fun earlier_rung_type ty =
    ty = Type.bool orelse ty = numSyntax.num orelse
    type_has_name "smtfloat" "smtfp" ty orelse
    type_has_name "smtfloat" "smt_rounding" ty orelse
    type_has_name "binary_ieee" "float" ty

  fun datatype_owned_type ty =
    has_constructors ty andalso not (earlier_rung_type ty)

  fun constructors_of ty =
    case TypeBase.fetch ty of
      NONE => raise ERR "constructors_of" "type is not a datatype"
    | SOME tyinfo => List.map (TypeBasePure.cinst ty)
        (TypeBasePure.constructors_of tyinfo)

  (* HOL has no primitive tester constant.  The checked SMT encoding of a
     tester is its canonical TypeBase case expression. *)
  fun datatype_tester_term ty constructor scrutinee =
    let
      val constructors = constructors_of ty
      val _ = if Term.type_of scrutinee = ty andalso
          List.exists (Term.aconv constructor) constructors then () else
        raise ERR "datatype_tester_term"
          "tester constructor/scrutinee does not belong to datatype instance"
      fun clause constructor' =
        let
          val (doms, _) = boolSyntax.strip_fun (Term.type_of constructor')
          val vars = List.map Term.genvar doms
          val pattern = Term.list_mk_comb (constructor', vars)
          val result =
            if Term.same_const constructor constructor' then boolSyntax.T
            else boolSyntax.F
        in
          (pattern, result)
        end
    in
      TypeBase.mk_case
        (scrutinee, List.map clause constructors)
    end

  (* Inferred endpoints depend on the declaration, not just the scrutinee's
     size. Admit the COMPLETE tester disjunction before any generic prover.
     The continuation belongs to the caller, not a process-wide policy. *)
  fun datatype_split_target admit scrutinee =
    let
      val _ = admit scrutinee
      val ty = Term.type_of scrutinee
      val testers = List.map (fn constructor =>
        let val tester = datatype_tester_term ty constructor scrutinee
            val _ = admit tester
        in tester end) (constructors_of ty)
      val target = boolSyntax.list_mk_disj testers
      val _ = admit target
    in target end

  fun datatype_types t =
    List.filter has_constructors (term_types t)

  (* A read-only syntactic index, NOT a simpset or a matching net. Equality
     patterns are indexed by their endpoint heads too: canonicalisation can
     add EQT wrappers or reverse a negated equality. A schematic head is a
     wildcard. Only admitted theorems become generic rewrite patterns. *)
  fun head_key tm =
    let val head = #1 (boolSyntax.strip_comb tm)
    in if Term.is_const head then
      let val {Thy,Name,...} = Term.dest_thy_const head
      in SOME (Thy ^ "." ^ Name) end
    else NONE end

  fun pattern_keys tm =
    if boolSyntax.is_eq tm then
      let
        val (l,r) = boolSyntax.dest_eq tm
        val keys = List.mapPartial Lib.I (pattern_keys l @ pattern_keys r)
      in if null keys then [head_key tm] else List.map SOME keys end
    else [head_key tm]

  fun rewrite_keys tm =
    if boolSyntax.is_forall tm then
      rewrite_keys (#2 (boolSyntax.dest_forall tm))
    else if boolSyntax.is_conj tm then
      let val (l,r) = boolSyntax.dest_conj tm
      in rewrite_keys l @ rewrite_keys r end
    else if boolSyntax.is_imp_only tm then
      let val (_,r) = boolSyntax.dest_imp_only tm
      in if Term.aconv r boolSyntax.F then [NONE] else rewrite_keys r end
    else if boolSyntax.is_eq tm then
      let val (l,r) = boolSyntax.dest_eq tm
      in pattern_keys
        (if Term.aconv l boolSyntax.T orelse Term.aconv l boolSyntax.F
         then r else l) end
    else if boolSyntax.is_neg tm then
      pattern_keys (boolSyntax.dest_neg tm)
    else if Term.aconv tm boolSyntax.F orelse
        boolSyntax.is_res_forall tm orelse
        (case Lib.total Term.dest_thy_const
            (#1 (boolSyntax.strip_comb tm)) of
           SOME {Thy="marker",Name="Abbrev",...} => true
         | _ => false) then [NONE]
    else pattern_keys tm

  (* Immutable leaf syntax only. Activity and canonical suffix predicates
     are attached from the CURRENT simpset, never frozen in this index. *)
  fun index_fragment fragment =
    let
      val sources = simpLib.frag_rewrites fragment
      val numbered = ListPair.zip
        (List.tabulate (length sources,Lib.I),sources)
      val leaves = List.concat (List.map (fn (source,th) =>
        List.map (fn leaf => (source,leaf)) (Drule.CONJUNCTS th)) numbered)
      val ranked = ListPair.zip (List.tabulate (length leaves,Lib.I),leaves)
      fun add ((rank,entry as (_,th)),index) =
        List.foldl (fn (key,index) =>
          let val saved = Option.getOpt (Redblackmap.peek (index,key),[])
          in Redblackmap.insert (index,key,(rank,entry)::saved) end)
          index (Lib.mk_set (rewrite_keys (Thm.concl th)))
    in List.foldr add (Redblackmap.mkDict (Lib.option_compare String.compare))
         ranked end

  val initial_rewrite_indices = List.map (fn fragment =>
    (fragment,index_fragment fragment))
    (simpLib.ssfrags_of (bossLib.srw_ss ()))

  (* Fixed std_ss conversion keys use bool (BETA/UNWIND) and arithmetic
     (REDUCE). Its remaining fragments contain source rewrites. A namespace
     superset is only a cheap proof of a miss, never matching authority. *)
  val standard_rewrite_theories = Lib.mk_set ("bool" :: "arithmetic" ::
    List.concat (List.map (fn fragment => List.concat
      (List.map (fn law => List.map (#Thy o Term.dest_thy_const)
        (HolKernel.find_terms Term.is_const (Thm.concl law)))
        (simpLib.frag_rewrites fragment)))
      (simpLib.ssfrags_of numLib.std_ss)))

  fun index_sources (fragment,sources) =
    let
      val index = case List.find (fn (saved,_) =>
          Portable.pointer_eq (saved,fragment)) initial_rewrite_indices of
          SOME (_,index) => index
        | NONE => index_fragment fragment
      val active = Array.array (length (simpLib.frag_rewrites fragment),NONE)
      val _ = List.app (fn entry as (rank,_,_) =>
        Array.update (active,rank,SOME entry)) sources
    in (index,active) end

  (* Each invocation supplies its own admission continuation. Declaration
     bundles are projected by kernel CONJUNCT rules before generic matching;
     an unrelated large conjunction must not hide a useful small equation. *)
  fun checked_procedures_using_preflight source_ss local_conversion
      split_conversions preflight check =
  let
  (* Admission/Work/observer failures must not become proof-search misses. *)
  exception AdmissionFailure of exn
  fun admit term = check term handle primary => raise AdmissionFailure primary
  fun protect f x = f x handle AdmissionFailure primary => raise primary
  fun admit_thm th = (admit (Thm.concl th);List.app admit (Thm.hyp th))
  (* Traverse consumes conversion sides with kernel congruence/TRANS, not
     as a combined matching operand. Seq keeps each side under its original
     cap; charging their temporary equality wrapper as an input would newly
     refuse a fitting near-cap sequence. Source rewrite patterns above and
     all assumptions/conditions still receive full native admission. *)
  fun admit_conversion th = if not split_conversions then admit_thm th else
    let val (left,right) = boolSyntax.dest_eq (Thm.concl th)
    in List.app admit (left::right::Thm.hyp th) end
  fun fitting th =
    (admit_thm th;true) handle failure as
        AdmissionFailure (Feedback.HOL_ERR detail) =>
      if Feedback.top_structure_of detail = "SmtReplayArithmetic" andalso
         Feedback.message_of detail =
           "arithmetic operator schema exceeds local admission" then false
      else raise failure

  fun add_thm th thms =
    if List.exists (fn th' => Term.aconv (Thm.concl th') (Thm.concl th))
      thms then thms
    else th :: thms

  fun add_thms thms acc = List.foldl (fn (th, acc) => add_thm th acc)
    acc thms

  fun conjuncts th = Drule.CONJUNCTS th handle Feedback.HOL_ERR _ => [th]

  (* Only admitted leaves reach this helper. *)
  fun with_gsym ths = ths @ List.mapPartial (Lib.total Conv.GSYM) ths

  fun harvest_uncached ty =
    let
      val one_one = List.mapPartial (Lib.total TypeBase.one_one_of) [ty]
      val distinct = List.mapPartial (Lib.total TypeBase.distinct_of) [ty]
      val case_defs = List.mapPartial (Lib.total TypeBase.case_def_of) [ty]
      val accessors =
        Option.getOpt (Lib.total TypeBase.accessors_of ty, [])
      val updates = Option.getOpt (Lib.total TypeBase.updates_of ty, [])
      val destructors = case TypeBase.fetch ty of NONE => []
        | SOME tyi => SmtLib.replay_datatype_destructor_theorems tyi
      fun leaves ths = List.filter fitting
        (List.concat (List.map conjuncts ths))
      val one_one_expanded = leaves one_one
      val distinct_expanded = leaves distinct
    in
      one_one_expanded @ with_gsym distinct_expanded @ leaves case_defs @
      leaves (accessors @ updates @ destructors)
    end

  (* Nested instances share the SAME generic TypeBase facts. Project and
     admit those facts once per invocation, not once per type argument.
     Physical identity is only an admission-cache key, never proof evidence.
     Failed checks are not cached; no state survives this local procedure. *)
  val harvested = ref ([] : (TypeBasePure.tyinfo * Thm.thm list) list)
  fun harvest_for_type ty =
    case TypeBase.fetch ty of NONE => []
    | SOME metadata =>
        (case List.find (fn (saved,_) =>
            Portable.pointer_eq (saved,metadata)) (!harvested) of
           SOME (_,facts) => facts
         | NONE =>
             let val facts = harvest_uncached ty
                 val _ = harvested := (metadata,facts) ::
                   List.take (!harvested,Int.min (15,length (!harvested)))
             in facts end)

  fun datatype_rewrite_thms t =
    List.foldl (fn (ty, acc) => add_thms (harvest_for_type ty) acc)
      [] (datatype_types t)

  fun size_thms_for_type ty =
    case Lib.total TypeBase.size_of ty of
      NONE => []
    | SOME (_, th) => List.filter fitting (conjuncts th)

  fun datatype_size_thms t =
    List.foldl (fn (ty, acc) => add_thms (size_thms_for_type ty) acc)
      [] (datatype_types t)

  (* Large enums omit distinct_of; TypeBase instead installs EnumType's
     representation conversion. Reconstruct that checked proof locally,
     selecting just the two representation equations by syntax. Never give
     the entire declaration bundle to a generic matcher or simplifier. *)
  val enum_facts = ref ([] : (TypeBasePure.tyinfo * Thm.thm list) list)
  fun enum_representation ty =
    case TypeBase.fetch ty of NONE => []
    | SOME metadata =>
        (case List.find (fn (saved,_) =>
            Portable.pointer_eq (saved,metadata)) (!enum_facts) of
           SOME (_,facts) => facts
         | NONE =>
             let
               (* TypeBase resolves and removes the EnumType extra sexp.
                  Its proved representation bundle remains in simpls_of. *)
               val facts = List.concat (List.map conjuncts
                 (#rewrs (TypeBasePure.simpls_of metadata)))
               val _ = enum_facts := (metadata,facts) ::
                 List.take (!enum_facts,Int.min (15,length (!enum_facts)))
             in facts end)

  fun enum_equality tm =
    let
      val (left,right) = boolSyntax.dest_eq tm
      val _ = if Term.is_const left andalso Term.is_const right andalso
          not (earlier_rung_type (Term.type_of left)) andalso
          not (Term.same_const left right) then () else raise Conv.UNCHANGED
      fun equation constructor th =
        case Lib.total (boolSyntax.dest_eq o Thm.concl) th of
          SOME (lhs,rhs) =>
            Term.is_comb lhs andalso Term.aconv (Term.rand lhs) constructor
            andalso numSyntax.is_numeral rhs
        | NONE => false
      (* A fitting distinctness law is both cheaper and more general than
         optional representation reconstruction. In particular its small
         caller cap need not admit the numerals of a high-index enum. *)
      val _ = case Lib.total TypeBase.distinct_of (Term.type_of left) of
          SOME _ => raise Conv.UNCHANGED
        | NONE => ()
      val facts = enum_representation (Term.type_of left)
      fun select constructor =
        case List.find (equation constructor) facts of
          SOME th => (admit_thm th;th)
        | NONE => raise Conv.UNCHANGED
      val lth = select left
      val rth = select right
      val rep = Term.rator (boolSyntax.lhs (Thm.concl lth))
      val _ = if Term.aconv rep (Term.rator (boolSyntax.lhs (Thm.concl rth)))
        then () else raise Conv.UNCHANGED
      val _ = admit rep
      val _ = admit (boolSyntax.mk_eq
        (Term.mk_comb (rep,left),Term.mk_comb (rep,right)))
      val numeric = boolSyntax.mk_eq
        (boolSyntax.rhs (Thm.concl lth),boolSyntax.rhs (Thm.concl rth))
      val _ = List.app admit [tm,numeric]
      val eq = Thm.AP_TERM rep (Thm.ASSUME tm)
      val numeric_eq = Thm.TRANS (Thm.SYM lth) (Thm.TRANS eq rth)
      val _ = admit_thm numeric_eq
      val falsity = Conv.CONV_RULE numLib.REDUCE_CONV numeric_eq
      val _ = admit_thm falsity
      val _ = List.app admit
        [boolSyntax.mk_imp (tm,boolSyntax.F),boolSyntax.mk_neg tm,
         boolSyntax.mk_eq (tm,boolSyntax.F)]
      val result = Drule.EQF_INTRO
        (Thm.NOT_INTRO (Thm.DISCH tm falsity))
      val _ = admit_thm result
    in result end

  (* Preserve pure srw rewrites and the bounded enum conversion above, not
     arbitrary dynamic TypeBase conversions. Ask for candidates at EACH
     redex, including new operators and side conditions. There is no
     all-exported admission/search pass. *)
  val exported_indices = ref NONE
  fun rewrite_indices () =
    let val current = source_ss ()
    in case !exported_indices of
        SOME (saved,indices) =>
          if Portable.pointer_eq (saved,current) then indices
          else fresh_indices current
      | NONE => fresh_indices current
    end
  and fresh_indices current =
    let val indices = List.map index_sources (simpLib.rewrite_sources current)
        val _ = exported_indices := SOME (current,indices)
    in indices end

  (* Count canonical names for a skipped (oversize) source leaf using
     syntax only. It must still occupy its original suffixes: deleting a
     generated name must not delete a different, fitting sibling instead.
     This mirrors Cond_rewr's cardinality, not its proof construction. *)
  fun rewrite_count (th,control) =
    let
      val bounded = case control of BoundedRewrites.UNBOUNDED => false
        | _ => true
      fun eqcount hypotheses (l,r) =
        let
          val loops = if Term.is_var l then Term.free_in l r
            else HolKernel.can (HolKernel.find_term (Term.aconv l)) r
          fun literal t = Term.aconv t boolSyntax.T orelse
            Term.aconv t boolSyntax.F
          fun member v = List.exists (Term.aconv v) hypotheses
          val safe = not (Term.is_var l) orelse Term.type_of l <> Type.bool
            orelse member l orelse bounded
          val extra = List.exists (fn v => not (member v) andalso
              not (List.exists (Term.aconv v) (Term.free_vars l)))
            (Term.free_vars r)
          val left = if safe andalso not extra then l
            else boolSyntax.mk_eq (l,r)
          val right = if safe andalso not extra then r else boolSyntax.T
          fun simple t = case Lib.total boolSyntax.dest_eq t of
              NONE => true
            | SOME (a,b) =>
                (Term.is_var a andalso Term.is_const b) orelse
                (Term.is_const a andalso Term.is_var b)
        in if loops andalso not bounded then 2
           else if literal l then 1
           else if boolSyntax.is_eq left andalso simple right then 2 else 1
        end
      fun terminal hypotheses conditions tm =
        if boolSyntax.is_eq tm then eqcount hypotheses (boolSyntax.dest_eq tm)
        else if boolSyntax.is_neg tm then
          let val body = boolSyntax.dest_neg tm
          in if boolSyntax.is_eq body then 2
             else if Term.is_var body andalso
                 not (List.exists (Term.aconv body) hypotheses) then 0 else 1
          end
        else if Term.aconv tm boolSyntax.T then 0
        else if Term.is_var tm andalso
            not (List.exists (Term.aconv tm) hypotheses) then 0
        else if head_key tm = SOME "marker.Abbrev" then
          let
            (* Abbrev recursively canonicalizes an UNDISCHed theorem;
               unlike ordinary leaves, its recursive calls see conditions
               as actual hypotheses. *)
            val hypotheses = conditions @ hypotheses
            val body = Term.rand tm
            val (l,r) = boolSyntax.dest_eq body
            fun pointwise (l,r) =
              if Term.is_abs r then
                let
                  val (v,b) = Term.dest_abs r
                  val fresh = Term.variant
                    (hypotheses @ Term.free_varsl [l,r]) v
                  val body = Term.subst [{redex=v,residue=fresh}] b
                in pointwise (Term.mk_comb (l,fresh),body) end
              else (r,l)
            val base = eqcount hypotheses (r,l)
          in if Term.is_abs r then
              base + eqcount hypotheses (pointwise (l,r)) else base end
          handle Feedback.HOL_ERR _ => 0
        else 1
      (* Pay for source-syntax inspection before unbounded metadata queries
         such as FV/occurrence tests. These are not proof operands. Work and
         observer exceptions remain terminal, including on skipped facts. *)
      fun pay [] = ()
        | pay (tm::rest) =
            (admit boolSyntax.T;
             case Term.dest_term tm of
               Term.COMB (f,x) => pay (f::x::rest)
             | Term.LAMB (_,b) => pay (b::rest)
             | _ => pay rest)
      val _ = pay (Thm.concl th :: Thm.hyp th)
      val branch_cache = ref []
      fun branches tm =
        case List.find (fn (saved,_) => Portable.pointer_eq (saved,tm))
            (!branch_cache) of
          SOME (_,n) => n
        | NONE =>
            let
              val n = if boolSyntax.is_conj tm then
                  let val (l,r) = boolSyntax.dest_conj tm
                  in branches l * branches r end
                else if boolSyntax.is_disj tm then
                  let val (l,r) = boolSyntax.dest_disj tm
                  in branches l + branches r end
                else if boolSyntax.is_exists tm then
                  branches (#2 (boolSyntax.dest_exists tm))
                else 1
              val _ = branch_cache := (tm,n) :: !branch_cache
            in n end
      fun negative tm =
        if boolSyntax.is_conj tm then
          let val (l,r) = boolSyntax.dest_conj tm
          in branches l * negative r end
        else if boolSyntax.is_disj tm then
          let val (l,r) = boolSyntax.dest_disj tm
          in negative l + negative r end
        else if boolSyntax.is_exists tm then
          let val (v,b) = boolSyntax.dest_exists tm
              val fresh = Term.variant (Term.free_vars b) v
          in negative (Term.subst [{redex=v,residue=fresh}] b) end
        else terminal [] [] (boolSyntax.mk_neg tm)
      fun has_abbrev tm =
        (admit boolSyntax.T;
         case Term.dest_term tm of
            Term.CONST {Thy,Name,...} => Thy = "marker" andalso Name = "Abbrev"
          | Term.COMB (f,x) => has_abbrev f orelse has_abbrev x
          | Term.LAMB (_,b) => has_abbrev b
          | _ => false)
      fun remove terms hyps = List.filter
        (fn h => not (List.exists (Term.aconv h) terms)) hyps
      fun insert tm hyps =
        if List.exists (Term.aconv tm) hyps then hyps else tm :: hyps
      fun finish hyps ants tm =
        let val remaining = remove ants hyps
            val _ = pay (remaining @ ants)
        in terminal (Term.free_varsl remaining) (Term.free_varsl ants) tm end
      (* Retain actual Hyp terms, not just their FV: native DISCH can remove
         an ORIGINAL hypothesis too. Only hypothesis-free, non-Abbrev paths
         may multiply branch counts without enumerating their contexts. *)
      fun count hyps ants tm =
        (admit boolSyntax.T;
         if boolSyntax.is_conj tm then
          let val (l,r) = boolSyntax.dest_conj tm
          in count hyps ants l + count hyps ants r end
        else if boolSyntax.is_forall tm then
          let val (v,b) = boolSyntax.dest_forall tm
              val _ = pay hyps
              val fresh = Term.variant (Term.free_varsl (b::hyps)) v
          in count hyps ants (Term.subst [{redex=v,residue=fresh}] b) end
        else if boolSyntax.is_res_forall tm then
          let val (v,p,b) = boolSyntax.dest_res_forall tm
          in count hyps ants (boolSyntax.mk_forall (v,
               boolSyntax.mk_imp (boolSyntax.mk_IN (v,p),b))) end
        else if boolSyntax.is_imp_only tm then
          let val (a,b) = boolSyntax.dest_imp_only tm
          in if null (remove ants hyps) andalso not (has_abbrev b) then
               if Term.aconv b boolSyntax.F then negative a
               else let val n = count [] [] b
                    in if n = 0 then 0 else branches a * n end
             else if boolSyntax.is_conj a then
               let val (l,r) = boolSyntax.dest_conj a
               in count (remove [l,r] hyps) ants
                    (boolSyntax.mk_imp (l,boolSyntax.mk_imp (r,b))) end
             else if boolSyntax.is_disj a then
               let val (l,r) = boolSyntax.dest_disj a
               in count (remove [l] hyps) ants (boolSyntax.mk_imp (l,b)) +
                  count (remove [r] hyps) ants (boolSyntax.mk_imp (r,b)) end
             else if boolSyntax.is_exists a then
               let val (v,body) = boolSyntax.dest_exists a
                   val _ = pay hyps
                   val fresh = Term.variant (Term.free_varsl (tm::hyps)) v
                   val body = Term.subst [{redex=v,residue=fresh}] body
               in count (remove [body] hyps) ants
                    (boolSyntax.mk_imp (body,b)) end
             else if Term.aconv b boolSyntax.F then
               (* Native NOT_INTRO preserves actual Hyp; only the outer
                  DISCHes in finish remove accumulated antecedents. *)
               finish hyps ants (boolSyntax.mk_neg a)
             else count (insert a hyps) (a::ants) b
          end
        else finish hyps ants tm)
    in count (Thm.hyp th) [] (Thm.concl th) end

  fun rewrite_fallback_ss () =
    let
      val indices = rewrite_indices ()
      val lists = SmtDatatypeListConv.procedures admit
      val compiled = ref []
      val selected = ref []
      val interrupted = ref NONE
      val controls = ref []
      fun same_leaf (NONE,NONE) = true
        | same_leaf (SOME l,SOME r) = Portable.pointer_eq (l,r)
        | same_leaf _ = false
      fun compile (entry as (_,source,survives),picked) =
        case List.find (fn ((saved,leaf),_) =>
            Portable.pointer_eq (saved,entry) andalso same_leaf (leaf,picked))
            (!compiled) of
          SOME (_,conversions) => (conversions,true)
        | NONE =>
              let
                val complete = ref true
                val (untagged,fresh_control) =
                  BoundedRewrites.dest_tagged_rewrite
                    (Option.getOpt (picked,source))
                (* Canonical siblings of ONE bounded source share its
                   counter; distinct additions of the same theorem do not. *)
                val control = case List.find (fn (saved,_) =>
                    Portable.pointer_eq (saved,entry)) (!controls) of
                    SOME (_,control) => control
                  | NONE => (controls := (entry,fresh_control):: !controls;
                             fresh_control)
                val suffix = ref 0
                fun canonical leaf =
                  if fitting leaf then
                    let
                      val rewrites = Cond_rewr.mk_cond_rewrs (leaf,control)
                      fun keep rewrite =
                        (suffix := !suffix+1;
                         if case survives of NONE => true
                              | SOME active => active (!suffix)
                         then SOME rewrite else NONE)
                    in List.mapPartial keep rewrites end
                  else (complete := false;
                    case survives of NONE => ()
                      | SOME _ => suffix := !suffix +
                          rewrite_count (leaf,control);[])
                fun conversion (th,control) =
                  let val th = Drule.SPEC_ALL th
                  in if not (fitting th) then (complete := false;NONE)
                  else
                    let
                      val left = boolSyntax.lhs
                        (#2 (boolSyntax.strip_imp (Thm.concl th)))
                      val rigid = Term.free_varsl (Thm.hyp th)
                      val bounded = case control of
                          BoundedRewrites.UNBOUNDED => false | _ => true
                      val conv = Cond_rewr.COND_REWR_CONV
                        ("datatype exported rewrite",th) bounded
                      fun apply solver stack tm =
                        let
                          val _ = case control of
                              BoundedRewrites.BOUNDED n =>
                                if !n = 0 then raise Conv.UNCHANGED else ()
                            | _ => ()
                          fun checked_solver assumptions condition =
                            (List.app admit assumptions;admit condition;
                             solver assumptions condition)
                            handle AdmissionFailure primary =>
                              (interrupted := SOME primary;
                               raise Portable.Interrupt)
                          (* Inspect the canonical SPEC_ALL rule before native
                             matching/INST. HOL_ERR means a normal rule miss;
                             failures from admit stay terminal via the outer
                             AdmissionFailure/Interrupt restoration path. *)
                          val _ = case preflight of NONE => ()
                            | SOME inspect => inspect admit th tm
                          val result = conv checked_solver stack tm
                          val _ = admit_conversion result
                          val _ = case control of
                              BoundedRewrites.BOUNDED n => n := !n - 1
                            | _ => ()
                        in result end
                    in SOME (rigid,left,apply) end
                  end
                val conversions = List.mapPartial conversion
                  (List.concat (List.map canonical (conjuncts untagged)))
                val _ = if !complete then
                    compiled := ((entry,picked),conversions) :: !compiled
                  else ()
              in (conversions,!complete) end
      fun candidates tm =
        let
          (* Query syntax is not a declaration: do not strip its quantifiers
             or implications, which may themselves be rewrite heads. *)
          fun keys tm =
            if boolSyntax.is_eq tm then
              let val (l,r) = boolSyntax.dest_eq tm
              in head_key tm :: keys l @ keys r end
            else if boolSyntax.is_neg tm then
              head_key tm :: keys (boolSyntax.dest_neg tm)
            else [head_key tm]
          val keys = List.map SOME
            (Lib.mk_set (List.mapPartial Lib.I (keys tm))) @ [NONE]
          fun add (entry as (rank,_),entries) =
            if List.exists (fn (saved,_) => saved = rank) entries
            then entries else entry::entries
          fun select (index,active) =
            let
              val whole = ref []
              fun resolve (_, (source,leaf)) =
                case Array.sub (active,source) of
                    NONE => NONE
                  | SOME (entry as (_,_,NONE)) => SOME (entry,SOME leaf)
                  | SOME entry =>
                      if Lib.mem source (!whole) then NONE
                      else (whole := source :: !whole;SOME (entry,NONE))
            in List.mapPartial resolve (Listsort.sort
              (fn ((l,_),(r,_)) => Int.compare (l,r))
              (List.foldr (fn (key,entries) => List.foldr add entries
                (Option.getOpt (Redblackmap.peek (index,key),[]))) [] keys))
            end
        in case List.find (fn (saved,_) => saved = keys) (!selected) of
            SOME (_,net) => Ho_Net.lookup tm net
          | NONE =>
              let
                val rules = List.map compile
                  (List.concat (List.map select indices))
                (* Use the SAME specificity and declaration ordering as the
                   native simplifier. No unchecked pattern enters this net. *)
                val net = List.foldr (fn (entry,net) =>
                    Ho_Net.enter entry net) Ho_Net.empty
                  (List.concat (List.map #1 rules))
                val _ = if List.all #2 rules then
                    selected := (keys,net) :: !selected else ()
              in Ho_Net.lookup tm net end
        end
      val standard = simpLib.traversedata_for_ss numLib.std_ss
      val ordinary = Traverse.dest_reducer (hd (#rewriters standard))
      (* Bag's preflight route has no local conversion. Its exported net
         already includes arbitrary user rewrite heads. On a net miss the
         fixed std_ss can only rewrite an abstraction-headed beta redex or
         a constant from its own rule/conversion namespaces. In particular
         it cannot rewrite an unrelated free function or user constructor.
         Keep this conservative namespace test local to that route: the
         other adapters may supply arbitrary local conversions.

         BOOL/UNWIND conversions use bool; REDUCE uses arithmetic (including
         its numeral operators). All other std_ss fragments contain only
         rewrites. Include EVERY namespace in those current source laws,
         not a finite grammar of permitted operands or successful rules. *)
      fun ordinary_head tm =
        let val head = #1 (boolSyntax.strip_comb tm)
        in Term.is_abs head orelse
          (Term.is_const head andalso Lib.mem
            (#Thy (Term.dest_thy_const head)) standard_rewrite_theories) end
      fun checked_solver solver assumptions condition =
        (List.app admit assumptions;admit condition;
         solver assumptions condition)
        handle AdmissionFailure primary =>
          (interrupted := SOME primary;raise Portable.Interrupt)
      fun ordinary_step solver stack tm =
        let
          val _ = case preflight of NONE => () | SOME _ =>
            if ordinary_head tm then admit tm else raise Conv.UNCHANGED
          val result = #apply ordinary
            {solver=checked_solver solver,conv=fn _ => Conv.NO_CONV,
             context= #initial ordinary,stack=stack,
             relation=(boolSyntax.equality,Thm.REFL)} tm
          (* The standard reducer may return primitive REFL on the entire
             current input. Discard this no-op before admitting a doubled
             equality wrapper: neither side is a new generic operand. The
             theorem, not pointer identity, remains the proof authority. *)
          val (left,right) = boolSyntax.dest_eq (Thm.concl result)
          val _ = if split_conversions andalso
              Portable.pointer_eq (left,right) then raise Conv.UNCHANGED
            else ()
          val _ = admit_conversion result
        in result end
      fun rewrite solver stack tm =
        let
          val _ = case preflight of NONE => admit tm | SOME _ => ()
          val selected = candidates tm
          val _ = case preflight of NONE => ()
            | SOME _ => admit boolSyntax.T
          fun full_equality () = Conv.CHANGED_CONV (#equality lists) tm
          fun equality () =
            #closed_equality lists tm handle Feedback.HOL_ERR _ =>
              full_equality () | Conv.UNCHANGED => full_equality ()
          fun list_step () =
            #normalise lists tm handle Feedback.HOL_ERR _ => equality ()
              | Conv.UNCHANGED => equality ()
          fun local_step () =
            let val _ = case preflight of NONE => ()
                  | SOME _ => raise Conv.UNCHANGED
                val result = local_conversion tm
                val _ = admit_conversion result
            in result end
            handle Feedback.HOL_ERR _ =>
              if split_conversions then raise Conv.UNCHANGED else list_step ()
              | Conv.UNCHANGED =>
              if split_conversions then raise Conv.UNCHANGED else list_step ()
          fun after_enum () =
            ordinary_step solver stack tm handle Feedback.HOL_ERR _ =>
              local_step () | Conv.UNCHANGED => local_step ()
          fun attempt [] =
                (enum_equality tm handle Feedback.HOL_ERR _ => after_enum ()
                 | Conv.UNCHANGED => after_enum ())
            | attempt (conv::rest) = conv solver stack tm
                handle Feedback.HOL_ERR _ => attempt rest
                     | Conv.UNCHANGED => attempt rest
        in attempt selected end
        handle AdmissionFailure primary =>
          (* Traverse.mapfilter2 discards arbitrary reducer exceptions, but
             propagates Interrupt. Abort immediately and restore the exact
             admission/Work/observer exception outside that boundary. *)
          (interrupted := SOME primary;raise Portable.Interrupt)
      (* Do not put this dispatcher behind std_ss's keyed rewrites. A
         more-specific exported rule (e.g. LENGTH xs + 0) must get its native
         chance before a general standard rule (n + 0) erases that redex.
         Pure srw facts compete in the checked net above; only then try the
         fixed standard root conversions, never a recursive inner SIMP. *)
      val base = List.foldl (fn (proc,ss) =>
          simpLib.++ (ss,simpLib.dproc_ss proc))
        (simpLib.++ (pureSimps.pure_ss,boolSimps.CONG_ss))
        (#dprocs standard)
      val ss = simpLib.++ (base,simpLib.conv_ss
        {name="admitted datatype exports",key=NONE,trace=2,conv=rewrite})
    in (ss,interrupted) end

  fun with_exported_rewrites prove =
    let
      val (ss,interrupted) = rewrite_fallback_ss ()
      fun restore () = case !interrupted of NONE => ()
        | SOME primary => raise AdmissionFailure primary
      val result = prove ss handle primary => (restore ();raise primary)
      val _ = restore ()
    in result end

  fun with_rewrite_fallback fallback prove thms =
    prove numLib.std_ss thms handle primary as Feedback.HOL_ERR _ =>
      if not fallback then raise primary
      else with_exported_rewrites (fn ss => prove ss thms)

  fun datatype_simp_with_fallback fallback t =
    let
      val _ = admit t
      (* Enum disjointness needs only two small representation equations,
         not the entire set of constructor case laws or a failed size proof.
         Discover checked local rewrites before generic simplification. The
         ordinary ladder remains available if these alone do not suffice. *)
      val enums = List.mapPartial (fn eq =>
        SOME (enum_equality eq) handle Feedback.HOL_ERR _ => NONE
          | Conv.UNCHANGED => NONE)
        (HolKernel.find_terms boolSyntax.is_eq t)
      fun ordinary () =
        let val thms = datatype_rewrite_thms t
        in if List.null thms then unsupported t
           else with_rewrite_fallback fallback
             (fn ss => fn facts => simpLib.SIMP_PROVE ss facts t) thms
        end
    in
      if null enums then ordinary ()
      else (simpLib.SIMP_PROVE numLib.std_ss enums t
        handle Feedback.HOL_ERR _ => ordinary ())
    end

  fun datatype_simp_prove t = datatype_simp_with_fallback true t

  fun datatype_nchotomy_thms t =
    List.filter fitting (List.mapPartial
      (fn ty => Lib.total TypeBase.nchotomy_of ty)
      (List.filter (fn ty => ty <> Type.bool) (datatype_types t)))

  fun constructor_headed tm =
    let
      val (head, _) = boolSyntax.strip_comb tm
      val constructors = constructors_of (Term.type_of tm)
    in
      List.exists (fn constructor => Term.same_const head constructor)
        constructors
    end
    handle Feedback.HOL_ERR _ => false

  fun compare_term_size (left, right) =
    Int.compare (Term.term_size left, Term.term_size right)

  fun datatype_split_terms t =
    let
      val goal_vars = Term.free_vars t
      fun is_goal_var variable =
        List.exists (Term.aconv variable) goal_vars
      fun datatype_term tm =
        let val ty = Term.type_of tm
        in
          ty <> Type.bool andalso has_constructors ty andalso
          not (constructor_headed tm) andalso
          List.all is_goal_var (Term.free_vars tm)
        end
      fun add_tm (tm, acc) =
        if List.exists (fn tm' => Term.aconv tm' tm) acc then acc
        else tm :: acc
    in
      Listsort.sort compare_term_size
        (List.foldl add_tm [] (List.filter datatype_term (subterms t)))
    end

  fun datatype_free_terms t =
    let
      fun datatype_term tm =
        let val ty = Term.type_of tm
        in ty <> Type.bool andalso has_constructors ty end
      fun add_tm (tm, acc) =
        if List.exists (fn tm' => Term.aconv tm' tm) acc then acc
        else tm :: acc
    in
      List.foldl add_tm [] (List.filter datatype_term (Term.free_vars t))
    end

  fun nchotomy_for_term tm =
    let
      val _ = admit tm
      val pattern = TypeBase.nchotomy_of (Term.type_of tm)
      val _ = admit_thm pattern
      (* Check the substituted conclusion before ISPEC's matching/INST.
         Term substitution here constructs syntax only, never a proof. *)
      val (variable,body) = boolSyntax.dest_forall (Thm.concl pattern)
      val types = Type.match_type (Term.type_of variable) (Term.type_of tm)
      val variable = Term.inst types variable
      val body = Term.inst types body
      val _ = admit body
      val target = Term.subst [{redex=variable,residue=tm}] body
      val _ = admit target
    in Drule.ISPEC tm pattern end

  fun split_terms_of_goal (assumptions, conclusion) =
    let
      val target = boolSyntax.list_mk_conj (conclusion :: assumptions)
      val candidates = datatype_split_terms target
      val scrutinees = List.mapPartial
        (fn term => Option.map (fn (_, scrutinee, _) => scrutinee)
          (Lib.total TypeBase.dest_case term)) (subterms target)
      fun is_scrutinee candidate =
        List.exists (Term.aconv candidate) scrutinees
      val (active, other) = List.partition is_scrutinee candidates
    in
      active @ other
    end

  (* Rediscover after every substitution: splitting an innermost application
     changes each enclosing datatype application, so a precomputed list is
     stale immediately.  The initial candidate count is a per-branch depth
     budget; recursive datatypes can introduce fresh constructor fields, but
     no branch can case-split more often than that original finite count. *)
  fun admit_goal (assumptions,conclusion) =
    (List.app admit assumptions;admit conclusion)

  fun admit_split_substitutions term (assumptions,conclusion) =
    let
      fun branch constructor =
        let
          val (domains,_) = boolSyntax.strip_fun (Term.type_of constructor)
          val pattern = Term.list_mk_comb
            (constructor,List.map Term.genvar domains)
          val _ = admit pattern
          val _ = admit (boolSyntax.mk_eq (term,pattern))
          val substitution = [{redex=term,residue=pattern}]
        in List.app (admit o Term.subst substitution)
             (conclusion :: assumptions) end
    in List.app branch (constructors_of (Term.type_of term)) end

  fun datatype_split_fixpoint_tac ss thms budget goal =
    (admit_goal goal;
     Tactical.THEN
      (bossLib.FULL_SIMP_TAC ss thms,
       fn simplified =>
         (admit_goal simplified;
          if budget = 0 then Tactical.ALL_TAC simplified
         else
           case split_terms_of_goal simplified of
             [] => Tactical.ALL_TAC simplified
           | split_term :: _ =>
               (admit_split_substitutions split_term simplified;
                Tactical.THEN
                 (profile "datatype(split)"
                    Tactic.FULL_STRUCT_CASES_TAC
                    (nchotomy_for_term split_term),
                  datatype_split_fixpoint_tac ss thms (budget - 1))
                 simplified))) goal)

  fun exhaustiveness_with_fallback fallback t =
    let
      val _ = admit t
      val thms = datatype_rewrite_thms t
      val budget = List.length (datatype_split_terms t)
    in
      if budget = 0 then unsupported t
      (* Retry simplification, never an entire split search: each branch
         must retain its original initial-subterm split budget. *)
      else if fallback then with_exported_rewrites (fn ss =>
        Tactical.prove (t,datatype_split_fixpoint_tac ss thms budget))
      else Tactical.prove (t,
        datatype_split_fixpoint_tac numLib.std_ss thms budget)
    end

  fun exhaustiveness_prove t = exhaustiveness_with_fallback true t

  fun acyclicity_prove t =
    let
      val _ = admit t
      val thms = datatype_rewrite_thms t @ datatype_size_thms t
      fun size_neq_from_eq eq =
        let
          val (l, r) = boolSyntax.dest_eq eq
          val ty = Term.type_of l
          val (size_fn, _) = TypeBase.size_of ty
          val _ = admit size_fn
          val _ = admit (boolSyntax.mk_eq
            (Term.mk_comb (size_fn,l),Term.mk_comb (size_fn,r)))
        in
          if ty = Type.bool orelse not (has_constructors ty) then
            raise ERR "acyclicity_prove" "not a datatype equality"
          else
            Tactical.prove (boolSyntax.mk_neg eq,
              Tactical.EVERY [
                Tactic.DISCH_TAC,
                Tactic.ASSUME_TAC (Thm.AP_TERM size_fn (Thm.ASSUME eq)),
                bossLib.FULL_SIMP_TAC bossLib.arith_ss thms
              ])
        end
      fun attempt eq = SOME (size_neq_from_eq eq)
        handle Feedback.HOL_ERR _ => NONE
      val acyclic_thms = List.mapPartial attempt
        (HolKernel.find_terms boolSyntax.is_eq t)
    in
      if List.null acyclic_thms then unsupported t
      else if List.exists (fn th => Term.aconv (Thm.concl th) t)
        acyclic_thms then Lib.first (fn th => Term.aconv (Thm.concl th) t)
        acyclic_thms
      else with_metis_limit (fn () =>
        metisLib.METIS_PROVE (acyclic_thms @ thms) t) ()
    end

  fun metis_datatype_prove t =
    let val _ = admit t
        val thms = datatype_rewrite_thms t
    in
      if List.null thms then unsupported t
      else with_metis_limit (fn () => metisLib.METIS_PROVE thms t) ()
    end

  fun datatype_fragment_admits t =
    List.exists (datatype_owned_type o Term.type_of) (subterms t)

  fun require_datatype_fragment t =
    if datatype_fragment_admits t then ()
    else unsupported t

  (* Syntax only: never match an unchecked exported pattern. Constructor
     cycles need size reasoning, not a second generic simp/split search.
     Defer (do not discard) exported rewrites: users may export constructor
     equations too. The direct simp/exhaustiveness APIs keep their fallback. *)
  fun constructor_only t =
    let
      fun allowed tm =
        if Term.is_comb tm then
          Term.is_const (#1 (boolSyntax.strip_comb tm))
        else if not (Term.is_const tm) then true
        else
          let
            val {Thy,Name,...} = Term.dest_thy_const tm
            val (_,range) = boolSyntax.strip_fun (Term.type_of tm)
          in
            (Thy = "min" andalso Name = "=") orelse
            (Thy = "bool" andalso List.exists (fn name => Name = name)
              ["~","/\\","\\/","==>","!","?","T","F"]) orelse
            (has_constructors range andalso
             List.exists (Term.same_const tm) (constructors_of range))
          end
    in List.all allowed (subterms t) end

  fun datatype_prove t =
    let val _ = admit t
        val _ = profile "datatype(fragment-precondition)"
          require_datatype_fragment t
        val immediate = not (constructor_only t)
        fun simplify fallback =
          profile "datatype(simp)" (datatype_simp_with_fallback fallback) t
          handle Feedback.HOL_ERR _ =>
          profile "datatype(exhaustiveness)"
            (exhaustiveness_with_fallback fallback) t
        fun finish () =
          profile "datatype(metis)" metis_datatype_prove t
    in
      (simplify immediate handle Feedback.HOL_ERR _ =>
       profile "datatype(acyclicity)" acyclicity_prove t)
      handle Feedback.HOL_ERR _ =>
        ((if immediate then finish () else
            (simplify true handle Feedback.HOL_ERR _ => finish ()))
         handle Feedback.HOL_ERR _ => unsupported t)
    end

  (* Establish a datatype consequence under its actual HOL assumptions.  The
     closed implication is proved from TypeBase facts and then instantiated
     with ASSUME, so callers never discard or manufacture hypotheses. *)
  fun datatype_consequence_prove (assumptions, conclusion) =
    let
      val _ = List.app admit (conclusion :: assumptions)
      val implication = List.foldr boolSyntax.mk_imp conclusion assumptions
      val _ = admit implication
      val theorem = datatype_prove implication
    in
      List.foldl
        (fn (assumption, thm) => Thm.MP thm (Thm.ASSUME assumption))
        theorem assumptions
    end

  in
    {prove=protect datatype_prove,simp=protect datatype_simp_prove,
     exhaustiveness=protect exhaustiveness_prove,
     acyclicity=protect acyclicity_prove,
     consequence=protect datatype_consequence_prove,
     split_terms=protect datatype_split_terms,
     fragment=protect datatype_fragment_admits,
     metis=protect metis_datatype_prove,
     with_simpset=fn prove => protect (fn () =>
       with_exported_rewrites prove) ()}
  end

  (* Existing clients do not opt into prospective rewrite admission. *)
  fun checked_procedures_using source_ss local_conversion
      split_conversions check =
    checked_procedures_using_preflight source_ss local_conversion
      split_conversions NONE check

  fun checked_procedures check =
    checked_procedures_using bossLib.srw_ss (fn _ => raise Conv.UNCHANGED)
      false check

  (* Replay-local clients can retain their own pure rewrite sources while
     sharing checked redex/condition/result admission and list conversions.
     No update is made to the ambient simpset or TypeBase. *)
  fun with_checked_rewrites_using check source_ss conversion prove =
    #with_simpset
      (checked_procedures_using source_ss conversion true check) prove
  fun with_checked_rewrites check source_ss prove =
    with_checked_rewrites_using check source_ss
      (fn _ => raise Conv.UNCHANGED) prove

  (* The callback receives the protected admission continuation, the
     canonical SPEC_ALL theorem, and the redex. Use admit for terminal
     admission failures; raise HOL_ERR directly to try the next rule. *)
  fun with_checked_rewrites_preflight check source_ss preflight prove =
    #with_simpset
      (checked_procedures_using_preflight source_ss
        (fn _ => raise Conv.UNCHANGED) true (SOME preflight) check) prove

  fun default_admission () = SmtReplayArithmetic.new_term_check
    {limit=SmtResource.max_bv_replay_term_nodes,observe=fn () => ()}
  fun datatype_prove_with_admission admit t =
    #prove (checked_procedures admit) t
  fun datatype_prove t = datatype_prove_with_admission (default_admission ()) t
  fun datatype_simp_prove t =
    #simp (checked_procedures (default_admission ())) t
  fun exhaustiveness_prove t =
    #exhaustiveness (checked_procedures (default_admission ())) t
  fun acyclicity_prove t =
    #acyclicity (checked_procedures (default_admission ())) t
  fun metis_datatype_prove t =
    #metis (checked_procedures (default_admission ())) t
  fun datatype_consequence_prove (assumptions,conclusion) =
    #consequence (checked_procedures (default_admission ()))
      (assumptions,conclusion)
  fun datatype_split_terms t =
    #split_terms (checked_procedures (default_admission ())) t
  fun datatype_fragment_admits t =
    #fragment (checked_procedures (default_admission ())) t

end
