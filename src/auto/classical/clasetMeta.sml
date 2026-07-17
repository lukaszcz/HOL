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
   ty_bindings : (string, hol_type) Redblackmap.dict}

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
             SOME residue => recurse residue
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
  let
    fun binding (name, residue) =
      case Redblackmap.peek (#tymetas store, name) of
        SOME redex => SOME {redex = redex, residue = norm_ty store residue}
      | NONE => NONE
  in
    List.mapPartial binding
      (Redblackmap.listItems (#ty_bindings store))
  end

fun inst_types store = Term.inst (type_substitution store)

fun walk store tm =
  let
    fun recurse current =
      let
        val current' = inst_types store current
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

fun norm store tm =
  let
    fun eta_reduce abs = Term.eta_conv abs handle HOL_ERR _ => abs

    fun recurse current =
      let
        val current' = walk store current
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
  if not (is_var eigen) orelse is_meta eigen then NONE
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
              val permitted =
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
                 Redblackmap.insert (#ty_bindings store, name, residue)}
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
