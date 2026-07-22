structure clasetMeta :> clasetMeta =
struct

open HolKernel

type meta = term
type tymeta = hol_type

val meta_prefix = "%%claset_meta%%"
val tymeta_prefix = "'claset_tymeta_"

fun marked prefix name = String.isPrefix prefix name

fun is_meta tm =
  case dest_term tm of
    VAR (name, _) => marked meta_prefix name
  | _ => false

fun is_tymeta ty =
  is_vartype ty andalso marked tymeta_prefix (dest_vartype ty)

fun meta_name tm =
  case dest_term tm of
    VAR (name, _) => if marked meta_prefix name then SOME name else NONE
  | _ => NONE

fun tymeta_name ty =
  if is_tymeta ty then SOME (dest_vartype ty) else NONE

fun string_compare (left : string, right) = String.compare (left, right)

type store =
  {allows : (string, term list) Redblackmap.dict,
   eigens : (term, unit) Redblackmap.dict,
   metas : (string, meta) Redblackmap.dict,
   tm_bindings : (string, term) Redblackmap.dict,
   tymetas : (string, tymeta) Redblackmap.dict,
   ty_bindings :
     (string, tymeta * hol_type) Redblackmap.dict}

val empty =
  {allows = Redblackmap.mkDict string_compare,
   eigens = Redblackmap.mkDict Term.compare,
   metas = Redblackmap.mkDict string_compare,
   tm_bindings = Redblackmap.mkDict string_compare,
   tymetas = Redblackmap.mkDict string_compare,
   ty_bindings = Redblackmap.mkDict string_compare}

fun fresh_meta ty =
  let
    val generated = genvar ty
    val (name, _) = dest_var generated
  in
    mk_var (meta_prefix ^ name, ty)
  end

fun fresh_tymeta () =
  let
    val generated = dest_vartype (gen_tyvar ())
    val suffix =
      String.implode (List.filter Char.isDigit (String.explode generated))
  in
    mk_vartype (tymeta_prefix ^ suffix)
  end

fun new_meta {allow, ty} store =
  let
    fun add_eigen (eigen, eigens) =
      Redblackmap.insert (eigens, eigen, ())

    val m = fresh_meta ty
    val name = valOf (meta_name m)
    val allows = Redblackmap.insert (#allows store, name, allow)
    val eigens = List.foldl add_eigen (#eigens store) allow
    val metas = Redblackmap.insert (#metas store, name, m)
  in
    (m,
     {allows = allows,
      eigens = eigens,
      metas = metas,
      tm_bindings = #tm_bindings store,
      tymetas = #tymetas store,
      ty_bindings = #ty_bindings store})
  end

fun new_tymeta store =
  let
    val ty = fresh_tymeta ()
    val name = valOf (tymeta_name ty)
    val tymetas = Redblackmap.insert (#tymetas store, name, ty)
  in
    (ty,
     {allows = #allows store,
      eigens = #eigens store,
      metas = #metas store,
      tm_bindings = #tm_bindings store,
      tymetas = tymetas,
      ty_bindings = #ty_bindings store})
  end

fun norm_ty store ty =
  let
    fun recurse current =
      case tymeta_name current of
        SOME name =>
          (case Redblackmap.peek (#ty_bindings store, name) of
             SOME (_, residue) => recurse residue
           | NONE => current)
      | NONE =>
          if is_vartype current then current
          else
            let
              val {Thy, Tyop, Args} = dest_thy_type current
            in
              mk_thy_type
                {Thy = Thy, Tyop = Tyop, Args = map recurse Args}
            end
  in
    recurse ty
  end

val norm_type = norm_ty

fun owned_meta store tm =
  case meta_name tm of
    NONE => false
  | SOME name =>
      (case Redblackmap.peek (#metas store, name) of
         NONE => false
       | SOME registered =>
           norm_ty store (type_of tm) =
           norm_ty store (type_of registered))

fun owned_tymeta store ty =
  case tymeta_name ty of
    NONE => false
  | SOME name => Redblackmap.inDomain (#tymetas store, name)

fun type_substitution store =
  map
    (fn (_, (redex, residue)) =>
      {redex = redex, residue = norm_ty store residue})
    (Redblackmap.listItems (#ty_bindings store))

(* A replay store retains fresh variables from earlier proof steps.  Most
   terms mention only the few type variables created by their own step, so
   rebuilding a substitution for the complete historical store on every
   walk makes long proofs quadratic in dead bindings.  Instantiate exactly
   the type variables reachable from the term instead. *)
fun inst_types store tm =
  let
    fun binding ty =
      case tymeta_name ty of
          NONE => NONE
        | SOME name =>
            (case Redblackmap.peek (#ty_bindings store, name) of
                 NONE => NONE
               | SOME (redex, residue) =>
                   SOME {redex = redex, residue = norm_ty store residue})
  in
    Term.inst (List.mapPartial binding (type_vars_in_term tm)) tm
  end

fun walk_with store instantiate tm =
  let
    fun recurse current =
      let
        val current' = instantiate current
      in
        case meta_name current' of
          SOME name =>
            if owned_meta store current' then
              (case Redblackmap.peek (#tm_bindings store, name) of
                 SOME residue => recurse residue
               | NONE => current')
            else current'
        | NONE => current'
      end
  in
    recurse tm
  end

fun walk store tm = walk_with store (inst_types store) tm

fun norm store tm =
  let
    fun eta_reduce abs = Term.eta_conv abs handle HOL_ERR _ => abs
    val walk_current = walk_with store (inst_types store)

    fun recurse current =
      let
        val current' = walk_current current
      in
        if is_meta current' then current'
        else
          case dest_term current' of
            COMB (rator, rand) =>
              let
                val rator' = recurse rator
                val rand' = recurse rand
                val combination = mk_comb (rator', rand')
              in
                if is_abs rator' then recurse (beta_conv combination)
                else combination
              end
          | LAMB (bvar, body) =>
              eta_reduce (mk_abs (bvar, recurse body))
          | _ => current'
      end
  in
    recurse tm
  end

fun insert_meta store (m, metas) =
  case meta_name m of
    SOME name =>
      if owned_meta store m then Redblackmap.insert (metas, name, m)
      else metas
  | NONE => metas

fun metas_of store tm =
  Redblackmap.listItems (List.foldl (insert_meta store)
    (Redblackmap.mkDict string_compare) (free_vars (norm store tm)))
  |> map #2

fun same_var left right = aconv left right

fun listed_as_eigen store variable =
  List.exists
    (fn (eigen, ()) =>
      same_var (inst_types store variable) (inst_types store eigen))
    (Redblackmap.listItems (#eigens store))

fun is_eigen store variable =
  is_var variable andalso listed_as_eigen store variable

fun eigen_allowed store allow variable =
  not (listed_as_eigen store variable) orelse
  List.exists (same_var (inst_types store variable))
    (map (inst_types store) allow)

fun residue_owned store residue =
  List.all (fn variable =>
    not (is_meta variable) orelse owned_meta store variable)
    (free_vars residue) andalso
  List.all (fn ty => not (is_tymeta ty) orelse owned_tymeta store ty)
    (type_vars_in_term residue)

fun binding_respects_allow store (name, residue) =
  let
    val allow = valOf (Redblackmap.peek (#allows store, name))
  in
    List.all (eigen_allowed store allow)
      (free_vars (norm store residue))
  end

fun register_eigen eigen store =
  if not (is_var eigen) orelse is_meta eigen orelse
     Redblackmap.inDomain (#eigens store, eigen)
  then NONE
  else
    let
      val candidate =
        {allows = #allows store,
         eigens = Redblackmap.insert (#eigens store, eigen, ()),
         metas = #metas store,
         tm_bindings = #tm_bindings store,
         tymetas = #tymetas store,
         ty_bindings = #ty_bindings store}
      val permitted =
        List.all (binding_respects_allow candidate)
          (Redblackmap.listItems (#tm_bindings candidate))
    in
      if permitted then SOME candidate else NONE
    end

fun bind (m, tm) store =
  case meta_name m of
    NONE => NONE
  | SOME name =>
      if not (owned_meta store m) orelse
         Redblackmap.inDomain (#tm_bindings store, name)
      then NONE
      else
        let
          val residue = norm store tm
          val occurs = List.exists
            (fn other => meta_name other = SOME name)
            (metas_of store residue)
          val same_type =
            norm_ty store (type_of m) = norm_ty store (type_of residue)
        in
          if occurs orelse not same_type orelse
             not (residue_owned store residue)
          then NONE
          else
            let
              val candidate =
                {allows = #allows store,
                 eigens = #eigens store,
                 metas = #metas store,
                 tm_bindings =
                   Redblackmap.insert
                     (#tm_bindings store, name, residue),
                 tymetas = #tymetas store,
                 ty_bindings = #ty_bindings store}
              (* Adding a binding whose normalized residue contains no
                 eigenvariable cannot invalidate the eigen scopes of any
                 existing binding.  A later binding which does introduce an
                 eigenvariable still performs the complete transitive check,
                 so this fast path preserves the store invariant while
                 avoiding a quadratic rescan for rigid propositional
                 structure. *)
              val introduces_eigen =
                List.exists (listed_as_eigen candidate)
                  (free_vars (norm candidate residue))
              val permitted =
                not introduces_eigen orelse
                List.all (binding_respects_allow candidate)
                  (Redblackmap.listItems (#tm_bindings candidate))
            in
              if permitted then SOME candidate else NONE
            end
        end

fun bind_ty (tymeta, ty) store =
  case tymeta_name tymeta of
    NONE => NONE
  | SOME name =>
      if not (owned_tymeta store tymeta) orelse
         Redblackmap.inDomain (#ty_bindings store, name)
      then NONE
      else
        let
          val residue = norm_ty store ty
          val occurs = List.exists
            (fn variable => tymeta_name variable = SOME name)
            (type_vars residue)
          val owned = List.all
            (fn variable =>
              not (is_tymeta variable) orelse
              owned_tymeta store variable)
            (type_vars residue)
        in
          if occurs orelse not owned then NONE
          else
            SOME
              {allows = #allows store,
               eigens = #eigens store,
               metas = #metas store,
               tm_bindings = #tm_bindings store,
               tymetas = #tymetas store,
               ty_bindings =
                 Redblackmap.insert
                   (#ty_bindings store, name, (tymeta, residue))}
        end

(* These copies expose diagnostic phase boundaries without placing hooks in
   the ordinary persistent-store path.  Dictionary inspection and binding
   walks are StoreLookupWalk; term/type rebuilding is NormalizationSetup;
   pattern, ownership, occurs and eigen-allow predicates are Decision; only
   construction of a new persistent map/record is BindingUpdate.

   They are semantically equivalent to the ordinary path, but timed-v3
   deliberately retains its historical operation sequence.  In particular,
   it builds full-store type substitutions and scans every binding after a
   bind, whereas production filters substitutions to the current term and
   can skip the scan for an eigen-free binding.  This preserves the exact
   events, counters, checkpoints and time ownership expected by timed-v3
   tests.  Its timings and cost attribution may therefore amplify production
   reconstruction cost and must not be used as estimates of it.  Mirroring
   either optimization requires a versioned diagnostic contract and revised
   expectations. *)
datatype diagnostic_phase =
    DiagnosticNormalizationSetup
  | DiagnosticStoreLookupWalk
  | DiagnosticPatternOccursAllowDecision
  | DiagnosticPersistentBindingUpdate
  | DiagnosticTraversalOther

datatype diagnostic_boundary = DiagnosticEnter | DiagnosticExit

type diagnostic_switch = diagnostic_boundary * diagnostic_phase -> unit

fun diagnostic_scope switch phase operation =
  let
    val _ = switch (DiagnosticEnter, phase)
    val result =
      operation ()
      handle error =>
        ((switch (DiagnosticExit, phase) handle _ => ()); raise error)
    val _ = switch (DiagnosticExit, phase)
  in
    result
  end

fun norm_ty_diagnostic switch store ty =
  let
    fun recurse current =
      case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
        (fn () => tymeta_name current)
      of
            SOME name =>
              (case diagnostic_scope switch DiagnosticStoreLookupWalk
                (fn () => Redblackmap.peek (#ty_bindings store, name))
               of
                   SOME (_, residue) => recurse residue
                 | NONE => current)
          | NONE =>
              diagnostic_scope switch DiagnosticNormalizationSetup
                (fn () =>
                  if is_vartype current then current
                  else
                    let
                      val {Thy, Tyop, Args} = dest_thy_type current
                      val args = map recurse Args
                    in
                      mk_thy_type {Thy = Thy, Tyop = Tyop, Args = args}
                    end)
  in
    recurse ty
  end

val norm_type_diagnostic = norm_ty_diagnostic

fun owned_tymeta_diagnostic switch store ty =
  case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
    (fn () => tymeta_name ty)
  of
       NONE => false
     | SOME name =>
         diagnostic_scope switch DiagnosticStoreLookupWalk
           (fn () => Redblackmap.inDomain (#tymetas store, name))

fun owned_meta_diagnostic switch store tm =
  case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
    (fn () => meta_name tm)
  of
       NONE => false
     | SOME name =>
         (case diagnostic_scope switch DiagnosticStoreLookupWalk
           (fn () => Redblackmap.peek (#metas store, name))
          of
              NONE => false
            | SOME registered =>
                let
                  val left =
                    norm_ty_diagnostic switch store (type_of tm)
                  val right =
                    norm_ty_diagnostic switch store (type_of registered)
                in
                  diagnostic_scope switch
                    DiagnosticPatternOccursAllowDecision
                    (fn () => left = right)
                end)

fun type_substitution_diagnostic switch store =
  let
    val bindings =
      diagnostic_scope switch DiagnosticStoreLookupWalk
        (fn () => Redblackmap.listItems (#ty_bindings store))
  in
    map
      (fn (_, (redex, residue)) =>
        {redex = redex,
         residue = norm_ty_diagnostic switch store residue})
      bindings
  end

fun inst_types_diagnostic switch store tm =
  let
    (* Keep the full-store substitution: selecting only [tm]'s type variables
       would change timed-v3 lookup and normalization events and counters. *)
    val substitution = type_substitution_diagnostic switch store
  in
    diagnostic_scope switch DiagnosticNormalizationSetup
      (fn () => Term.inst substitution tm)
  end

fun walk_with_diagnostic switch store instantiate tm =
  let
    fun recurse current =
      let
        val current' = instantiate current
      in
        case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
          (fn () => meta_name current')
        of
            SOME name =>
              if owned_meta_diagnostic switch store current' then
                (case diagnostic_scope switch DiagnosticStoreLookupWalk
                  (fn () => Redblackmap.peek (#tm_bindings store, name))
                 of
                     SOME residue => recurse residue
                   | NONE => current')
              else current'
          | NONE => current'
      end
  in
    recurse tm
  end

fun norm_diagnostic switch store tm =
  let
    fun eta_reduce abs = Term.eta_conv abs handle HOL_ERR _ => abs
    fun instantiate current = inst_types_diagnostic switch store current
    val walk_current = walk_with_diagnostic switch store instantiate

    fun recurse current =
      let
        val current' = walk_current current
      in
        if is_meta current' then current'
        else
          case dest_term current' of
              COMB (rator, rand) =>
                let
                  val rator' = recurse rator
                  val rand' = recurse rand
                  val combination =
                    diagnostic_scope switch DiagnosticNormalizationSetup
                      (fn () => mk_comb (rator', rand'))
                in
                  if is_abs rator' then
                    recurse
                      (diagnostic_scope switch DiagnosticNormalizationSetup
                        (fn () => beta_conv combination))
                  else combination
                end
            | LAMB (bvar, body) =>
                let
                  val body' = recurse body
                in
                  diagnostic_scope switch DiagnosticNormalizationSetup
                    (fn () => eta_reduce (mk_abs (bvar, body')))
                end
            | _ => current'
      end
  in
    recurse tm
  end

fun metas_of_diagnostic switch store tm =
  let
    fun insert (m, metas) =
      case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
        (fn () => meta_name m)
      of
           SOME name =>
             if owned_meta_diagnostic switch store m then
               diagnostic_scope switch DiagnosticTraversalOther
                 (fn () => Redblackmap.insert (metas, name, m))
             else metas
         | NONE => metas
    val normalized = norm_diagnostic switch store tm
    val variables =
      diagnostic_scope switch DiagnosticTraversalOther
        (fn () => free_vars normalized)
    val initial =
      diagnostic_scope switch DiagnosticTraversalOther
        (fn () => Redblackmap.mkDict string_compare)
    val collected =
      diagnostic_scope switch DiagnosticTraversalOther
        (fn () => List.foldl insert initial variables)
  in
    diagnostic_scope switch DiagnosticTraversalOther
      (fn () => map #2 (Redblackmap.listItems collected))
  end

fun listed_as_eigen_diagnostic switch store variable =
  let
    val eigens =
      diagnostic_scope switch DiagnosticStoreLookupWalk
        (fn () => Redblackmap.listItems (#eigens store))
    fun listed (eigen, ()) =
      let
        val left = inst_types_diagnostic switch store variable
        val right = inst_types_diagnostic switch store eigen
      in
        diagnostic_scope switch DiagnosticPatternOccursAllowDecision
          (fn () => aconv left right)
      end
  in
    List.exists listed eigens
  end

fun is_eigen_diagnostic switch store variable =
  diagnostic_scope switch DiagnosticPatternOccursAllowDecision
    (fn () => is_var variable) andalso
  listed_as_eigen_diagnostic switch store variable

fun eigen_allowed_diagnostic switch store allow variable =
  not (listed_as_eigen_diagnostic switch store variable) orelse
  let
    val instantiated_variable = inst_types_diagnostic switch store variable
    fun same allowed =
      diagnostic_scope switch DiagnosticPatternOccursAllowDecision
        (fn () => aconv instantiated_variable allowed)
  in
    List.exists same (map (inst_types_diagnostic switch store) allow)
  end

fun residue_owned_diagnostic switch store residue =
  let
    fun term_owned variable =
      diagnostic_scope switch DiagnosticPatternOccursAllowDecision
        (fn () => not (is_meta variable)) orelse
      owned_meta_diagnostic switch store variable
    fun type_owned variable =
      diagnostic_scope switch DiagnosticPatternOccursAllowDecision
        (fn () => not (is_tymeta variable)) orelse
      owned_tymeta_diagnostic switch store variable
    val term_variables =
      diagnostic_scope switch DiagnosticTraversalOther
        (fn () => free_vars residue)
  in
    List.all term_owned term_variables andalso
    List.all type_owned
      (diagnostic_scope switch DiagnosticTraversalOther
        (fn () => type_vars_in_term residue))
  end

fun binding_respects_allow_diagnostic switch store (name, residue) =
  let
    val allow =
      diagnostic_scope switch DiagnosticStoreLookupWalk
        (fn () => valOf (Redblackmap.peek (#allows store, name)))
    val normalized = norm_diagnostic switch store residue
    val variables =
      diagnostic_scope switch DiagnosticTraversalOther
        (fn () => free_vars normalized)
  in
    diagnostic_scope switch DiagnosticPatternOccursAllowDecision
      (fn () =>
        List.all (eigen_allowed_diagnostic switch store allow) variables)
  end

fun register_eigen_diagnostic switch eigen store =
  if diagnostic_scope switch DiagnosticPatternOccursAllowDecision
       (fn () => not (is_var eigen) orelse is_meta eigen) orelse
     diagnostic_scope switch DiagnosticStoreLookupWalk
       (fn () => Redblackmap.inDomain (#eigens store, eigen))
  then NONE
  else
    let
      val candidate =
        diagnostic_scope switch DiagnosticPersistentBindingUpdate
          (fn () =>
            {allows = #allows store,
             eigens = Redblackmap.insert (#eigens store, eigen, ()),
             metas = #metas store,
             tm_bindings = #tm_bindings store,
             tymetas = #tymetas store,
             ty_bindings = #ty_bindings store})
      val bindings =
        diagnostic_scope switch DiagnosticStoreLookupWalk
          (fn () => Redblackmap.listItems (#tm_bindings candidate))
      val permitted =
        diagnostic_scope switch DiagnosticPatternOccursAllowDecision
          (fn () =>
            List.all
              (binding_respects_allow_diagnostic switch candidate)
              bindings)
    in
      if permitted then SOME candidate else NONE
    end

fun bind_diagnostic switch (m, tm) store =
  case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
    (fn () => meta_name m)
  of
        NONE => NONE
      | SOME name =>
          if not (owned_meta_diagnostic switch store m) orelse
             diagnostic_scope switch DiagnosticStoreLookupWalk
               (fn () => Redblackmap.inDomain (#tm_bindings store, name))
          then NONE
          else
            let
              val residue = norm_diagnostic switch store tm
              val occurs =
                diagnostic_scope switch
                  DiagnosticPatternOccursAllowDecision
                  (fn () =>
                    List.exists
                      (fn other => meta_name other = SOME name)
                      (metas_of_diagnostic switch store residue))
              val left_type =
                norm_ty_diagnostic switch store (type_of m)
              val right_type =
                norm_ty_diagnostic switch store (type_of residue)
              val same_type =
                diagnostic_scope switch
                  DiagnosticPatternOccursAllowDecision
                  (fn () => left_type = right_type)
            in
              if occurs orelse not same_type orelse
                 not (residue_owned_diagnostic switch store residue)
              then
                NONE
              else
                let
                  val candidate =
                    diagnostic_scope switch DiagnosticPersistentBindingUpdate
                      (fn () =>
                        {allows = #allows store,
                         eigens = #eigens store,
                         metas = #metas store,
                         tm_bindings =
                           Redblackmap.insert
                             (#tm_bindings store, name, residue),
                         tymetas = #tymetas store,
                         ty_bindings = #ty_bindings store})
                  (* Keep the complete scan even when [residue] is eigen-free:
                     skipping it would change timed-v3 counters and
                     checkpoints, though the acceptance result is the same. *)
                  val bindings =
                    diagnostic_scope switch DiagnosticStoreLookupWalk
                      (fn () =>
                        Redblackmap.listItems (#tm_bindings candidate))
                  val permitted =
                    diagnostic_scope switch
                      DiagnosticPatternOccursAllowDecision
                      (fn () =>
                        List.all
                          (binding_respects_allow_diagnostic switch candidate)
                          bindings)
                in
                  if permitted then SOME candidate else NONE
                end
            end

fun bind_ty_diagnostic switch (tymeta, ty) store =
  case diagnostic_scope switch DiagnosticPatternOccursAllowDecision
    (fn () => tymeta_name tymeta)
  of
        NONE => NONE
      | SOME name =>
          if not (owned_tymeta_diagnostic switch store tymeta) orelse
             diagnostic_scope switch DiagnosticStoreLookupWalk
               (fn () => Redblackmap.inDomain (#ty_bindings store, name))
          then NONE
          else
            let
              val residue = norm_ty_diagnostic switch store ty
              val occurs =
                diagnostic_scope switch
                  DiagnosticPatternOccursAllowDecision
                  (fn () =>
                    List.exists
                      (fn variable => tymeta_name variable = SOME name)
                      (diagnostic_scope switch DiagnosticTraversalOther
                        (fn () => type_vars residue)))
              val owned =
                List.all
                  (fn variable =>
                    diagnostic_scope switch
                      DiagnosticPatternOccursAllowDecision
                      (fn () => not (is_tymeta variable)) orelse
                    owned_tymeta_diagnostic switch store variable)
                  (diagnostic_scope switch DiagnosticTraversalOther
                    (fn () => type_vars residue))
            in
              if occurs orelse not owned then NONE
              else
                SOME
                  (diagnostic_scope switch
                    DiagnosticPersistentBindingUpdate
                    (fn () =>
                      {allows = #allows store,
                       eigens = #eigens store,
                       metas = #metas store,
                       tm_bindings = #tm_bindings store,
                       tymetas = #tymetas store,
                       ty_bindings =
                         Redblackmap.insert
                           (#ty_bindings store, name, (tymeta, residue))}))
            end

fun ground_types store =
  let
    fun ground_one ((name, tymeta), current) =
      if Redblackmap.inDomain (#ty_bindings current, name) then current
      else valOf (bind_ty (tymeta, Type.bool) current)
  in
    List.foldl ground_one store (Redblackmap.listItems (#tymetas store))
  end

fun ground_terms store =
  let
    fun ground_one ((name, m), current) =
      if Redblackmap.inDomain (#tm_bindings current, name) then current
      else
        let
          val ty = norm_ty current (type_of m)
        in
          valOf (bind (m, boolSyntax.mk_arb ty) current)
        end
  in
    List.foldl ground_one store (Redblackmap.listItems (#metas store))
  end

fun ground store = ground_terms (ground_types store)

fun bindings store =
  let
    fun term_binding (name, residue) =
      case Redblackmap.peek (#metas store, name) of
          SOME redex => SOME (redex, residue)
        | NONE => NONE
    fun type_binding (_, binding) = binding
  in
    {terms =
       List.mapPartial term_binding
         (Redblackmap.listItems (#tm_bindings store)),
     types =
       map type_binding
         (Redblackmap.listItems (#ty_bindings store))}
  end

fun collapse store =
  let
    val ty_subst = type_substitution store

    fun term_binding (name, residue) =
      case Redblackmap.peek (#metas store, name) of
        SOME redex =>
          SOME
            {redex = Term.inst ty_subst redex,
             residue = norm store residue}
      | NONE => NONE

    val tm_subst = List.mapPartial term_binding
      (Redblackmap.listItems (#tm_bindings store))
  in
    (ty_subst, tm_subst)
  end

end
