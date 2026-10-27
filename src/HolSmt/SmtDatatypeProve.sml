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

  (* Each invocation supplies its own admission continuation. Declaration
     bundles are projected by kernel CONJUNCT rules before generic matching;
     an unrelated large conjunction must not hide a useful small equation. *)
  fun checked_procedures check =
  let
  (* Admission/Work/observer failures must not become proof-search misses. *)
  exception AdmissionFailure of exn
  fun admit term = check term handle primary => raise AdmissionFailure primary
  fun protect f x = f x handle AdmissionFailure primary => raise primary
  fun admit_thm th = (admit (Thm.concl th);List.app admit (Thm.hyp th))
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

  fun datatype_simp_prove t =
    let val _ = admit t
        val thms = datatype_rewrite_thms t
    in
      if List.null thms then unsupported t
      else simpLib.SIMP_PROVE numLib.std_ss thms t
    end

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

  fun datatype_split_fixpoint_tac thms budget goal =
    (admit_goal goal;
     Tactical.THEN
      (bossLib.FULL_SIMP_TAC numLib.std_ss thms,
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
                  datatype_split_fixpoint_tac thms (budget - 1))
                 simplified))) goal)

  fun exhaustiveness_prove t =
    let
      val _ = admit t
      val thms = datatype_rewrite_thms t
      val budget = List.length (datatype_split_terms t)
    in
      if budget = 0 then unsupported t
      else Tactical.prove (t,
        datatype_split_fixpoint_tac thms budget)
    end

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

  fun datatype_prove t =
    let val _ = admit t
        val _ = profile "datatype(fragment-precondition)"
          require_datatype_fragment t
    in
      profile "datatype(simp)" datatype_simp_prove t
      handle Feedback.HOL_ERR _ =>
      profile "datatype(exhaustiveness)" exhaustiveness_prove t
      handle Feedback.HOL_ERR _ =>
      profile "datatype(acyclicity)" acyclicity_prove t
      handle Feedback.HOL_ERR _ =>
      profile "datatype(metis)" metis_datatype_prove t
      handle Feedback.HOL_ERR _ =>
      unsupported t
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
     metis=protect metis_datatype_prove}
  end

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
