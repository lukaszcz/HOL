(* Copyright (c) 2026 The HOL4 contributors. *)

(* Solver-neutral checked replay support for SMT-LIB datatype lemmas. *)

structure SmtDatatypeProve =
struct

  val ERR = Feedback.mk_HOL_ERR "SmtDatatypeProve"

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

  fun datatype_types t =
    List.filter has_constructors (term_types t)

  fun add_thm th thms =
    if List.exists (fn th' => Term.aconv (Thm.concl th') (Thm.concl th))
      thms then thms
    else th :: thms

  fun add_thms thms acc = List.foldl (fn (th, acc) => add_thm th acc)
    acc thms

  fun conjuncts th = Drule.CONJUNCTS th handle Feedback.HOL_ERR _ => [th]

  fun with_gsym ths =
    ths @ List.mapPartial (Lib.total Conv.GSYM) ths

  fun harvest_for_type ty =
    let
      val one_one = List.mapPartial (Lib.total TypeBase.one_one_of) [ty]
      val distinct = List.mapPartial (Lib.total TypeBase.distinct_of) [ty]
      val case_defs = List.mapPartial (Lib.total TypeBase.case_def_of) [ty]
      val one_one_expanded = List.concat (List.map conjuncts one_one)
      val distinct_expanded = List.concat (List.map conjuncts distinct)
    in
      one_one_expanded @ with_gsym distinct_expanded @ case_defs
    end

  fun datatype_rewrite_thms t =
    List.foldl (fn (ty, acc) => add_thms (harvest_for_type ty) acc)
      [] (datatype_types t)

  fun size_thms_for_type ty =
    case Lib.total TypeBase.size_of ty of
      NONE => []
    | SOME (_, th) => th :: conjuncts th

  fun datatype_size_thms t =
    List.foldl (fn (ty, acc) => add_thms (size_thms_for_type ty) acc)
      [] (datatype_types t)

  fun datatype_simp_prove t =
    let val thms = datatype_rewrite_thms t
    in
      if List.null thms then unsupported t
      else simpLib.SIMP_PROVE (bossLib.srw_ss()) thms t
    end

  fun datatype_nchotomy_thms t =
    List.mapPartial
      (fn ty => Lib.total TypeBase.nchotomy_of ty)
      (List.filter (fn ty => ty <> Type.bool) (datatype_types t))

  fun datatype_split_terms t =
    let
      fun datatype_term tm =
        let val ty = Term.type_of tm
        in ty <> Type.bool andalso has_constructors ty end
      fun add_tm (tm, acc) =
        if List.exists (fn tm' => Term.aconv tm' tm) acc then acc
        else tm :: acc
    in
      List.foldl add_tm [] (List.filter datatype_term (subterms t))
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
    Drule.ISPEC tm (TypeBase.nchotomy_of (Term.type_of tm))

  fun exhaustiveness_prove t =
    let
      val thms = datatype_rewrite_thms t
      val cases = List.map nchotomy_for_term (datatype_split_terms t)
    in
      if List.null cases then unsupported t
      else Tactical.prove (t,
        Tactical.THEN
          (Tactical.EVERY (List.map Tactic.STRUCT_CASES_TAC cases),
           bossLib.RW_TAC (bossLib.srw_ss()) thms))
    end

  fun datatype_cases_prove t =
    let
      val thms = datatype_rewrite_thms t
      val cases = List.map nchotomy_for_term (datatype_free_terms t)
    in
      if List.null cases then unsupported t
      else Tactical.prove (t,
        Tactical.THEN
          (Tactical.EVERY (List.map Tactic.FULL_STRUCT_CASES_TAC cases),
           bossLib.RW_TAC (bossLib.srw_ss()) thms))
    end

  fun acyclicity_prove t =
    let
      val thms = datatype_rewrite_thms t @ datatype_size_thms t
      fun size_neq_from_eq eq =
        let
          val (l, r) = boolSyntax.dest_eq eq
          val ty = Term.type_of l
          val (size_fn, _) = TypeBase.size_of ty
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
      val acyclic_thms = List.mapPartial (Lib.total size_neq_from_eq)
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
    let val thms = datatype_rewrite_thms t
    in
      if List.null thms then unsupported t
      else with_metis_limit (fn () => metisLib.METIS_PROVE thms t) ()
    end

  fun datatype_prove t =
    Z3_ProformaThms.prove Z3_ProformaThms.datatype_thms t
    handle Feedback.HOL_ERR _ =>
    datatype_simp_prove t
    handle Feedback.HOL_ERR _ =>
    datatype_cases_prove t
    handle Feedback.HOL_ERR _ =>
    exhaustiveness_prove t
    handle Feedback.HOL_ERR _ =>
    acyclicity_prove t
    handle Feedback.HOL_ERR _ =>
    metis_datatype_prove t
    handle Feedback.HOL_ERR _ =>
    unsupported t

end
