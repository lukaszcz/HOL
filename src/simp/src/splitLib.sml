structure splitLib :> splitLib =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "splitLib"

fun malformed msg =
  raise ERR "analyse_rule" ("Malformed split rule: " ^ msg)

fun require true _ = ()
  | require false msg = malformed msg

type split_rule =
  {thm : thm,
   head : term,
   pattern : term,
   arity : int,
   asm : bool}

type split_key = {head : term, asm : bool}
type cmap = (split_key * split_rule list) list

fun rule_parts th =
  let
    val (qvars, body) = strip_forall (concl th)
    val _ = require (null (hyp th)) "the theorem has hypotheses"
    val (left, right) =
      dest_eq body
      handle HOL_ERR _ => malformed "the conclusion is not an equality"
    val (pred, pattern) =
      dest_comb left
      handle HOL_ERR _ =>
        malformed "the left side is not P (c a1 ... an)"
    val _ = require (is_var pred) "P is not a variable"
    val _ =
      require (List.exists (aconv pred) qvars)
        "P is not universally quantified"
    val (domain, range) =
      dom_rng (type_of pred)
      handle HOL_ERR _ => malformed "P is not a function"
    val _ = require (domain = type_of pattern) "P has the wrong domain"
    val _ = require (range = bool) "P is not bool-valued"
    val (head, args) = strip_comb pattern
    val _ = require (is_const head) "the split redex is not Const-headed"
  in
    {pred=pred, pattern=pattern, head=head, args=args,
     asm=is_neg right}
  end

fun analyse_rule th =
  let
    val {asm,...} = rule_parts th
    val sth = SPEC_ALL th
    val (left, _) = dest_eq (concl sth)
    val (_, pattern) = dest_comb left
    val (head, args) = strip_comb pattern
  in
    {thm=th, head=head, pattern=pattern, arity=length args, asm=asm}
  end

fun is_asm_split th = #asm (analyse_rule th)

fun persistent_name {Thy,Name} = Thy ^ "$" ^ Name

fun split_thm_name th =
  let
    fun stored [] = NONE
      | stored (DB.Stored name :: _) = SOME (persistent_name name)
      | stored (_ :: rest) = stored rest
    fun local_location [] = NONE
      | local_location (DB.Local name :: _) =
          SOME (Theory.current_theory () ^ "$" ^ name)
      | local_location (_ :: rest) = local_location rest
    val locations = DB.revlookup th
  in
    case local_location locations of
        SOME name => name
      | NONE =>
          (case stored locations of
               SOME name => name
             | NONE =>
                 raise ERR "split_thm_name"
                   "split theorem has no database name")
  end

fun remove_name name db =
  let
    val key =
      if String.isSubstring "$" name then name
      else persistent_name (ThmSetData.toKName name)
  in
    Symtab.delete_safe key db
  end

fun apply_split_delta delta db =
  case delta of
      ThmSetData.ADD (name, th) =>
        let val _ = is_asm_split th
        in Symtab.update (persistent_name name, th) db
        end
    | ThmSetData.REMOVE name => remove_name name db

val _ =
  if List.exists (equal "split") (ThmSetData.all_set_types ()) orelse
     ThmAttribute.is_attribute "split"
  then raise ERR "registration" "settype or attribute split already exists"
  else ()

val split_data =
  ThmSetData.export_with_ancestry
    {settype="split",
     delta_ops=
       {apply_to_global=apply_split_delta,
        thy_finaliser=NONE,
        uptodate_delta=K true,
        initial_value=Symtab.empty,
        apply_delta=apply_split_delta}}

fun named_split_thms () = Symtab.dest (#get_global_value split_data ())
fun split_thms () = map #2 (named_split_thms ())

type type_splits = {split : thm, asm_split : thm}
val type_split_cache =
  Sref.new (Symtab.empty : type_splits Symtab.table)

fun type_key tyinfo =
  let val (thy, tyop) = TypeBasePure.ty_name_of tyinfo
  in thy ^ "$" ^ tyop
  end

fun type_splits_of ty =
  let
    val tyinfo =
      case TypeBase.fetch ty of
          SOME tyinfo => tyinfo
        | NONE =>
            raise ERR "type_splits_of" "type has no TypeBase information"
    val key = type_key tyinfo
  in
    case Symtab.lookup (Sref.value type_split_cache) key of
        SOME splits => splits
      | NONE =>
          let
            val splits =
              {split=TypeBase.case_pred_imp_of ty,
               asm_split=TypeBasePure.case_elim_of tyinfo}
            val _ =
              Sref.update type_split_cache (Symtab.update (key, splits))
          in
            splits
          end
  end

fun type_split_of ty = #split (type_splits_of ty)
fun type_asm_split_of ty = #asm_split (type_splits_of ty)

fun same_type_shape (ty1, ty2) =
  let
    fun lookup_left _ [] = NONE
      | lookup_left ty ((left, right) :: rest) =
          if left = ty then SOME right else lookup_left ty rest
    fun lookup_right _ [] = NONE
      | lookup_right ty ((left, right) :: rest) =
          if right = ty then SOME left else lookup_right ty rest

    fun shapes env (left, right) =
      if Type.is_vartype left then
        if not (Type.is_vartype right) then NONE
        else
          (case (lookup_left left env, lookup_right right env) of
               (NONE, NONE) => SOME ((left, right) :: env)
             | (SOME right', SOME left') =>
                 if right = right' andalso left = left'
                 then SOME env
                 else NONE
             | _ => NONE)
      else if Type.is_vartype right then NONE
      else
        let
          val {Thy=thy1,Tyop=op1,Args=args1} =
            Type.dest_thy_type left
          val {Thy=thy2,Tyop=op2,Args=args2} =
            Type.dest_thy_type right
          fun arg_shapes ([], [], env) = SOME env
            | arg_shapes (arg1 :: rest1, arg2 :: rest2, env) =
                (case shapes env (arg1, arg2) of
                     NONE => NONE
                   | SOME env' => arg_shapes (rest1, rest2, env'))
            | arg_shapes _ = NONE
        in
          if thy1 = thy2 andalso op1 = op2
          then arg_shapes (args1, args2, env)
          else NONE
        end
  in
    Option.isSome (shapes [] (ty1, ty2))
  end

fun same_key ({head=h1,asm=a1} : split_key,
              {head=h2,asm=a2} : split_key) =
  a1 = a2 andalso same_const h1 h2 andalso
  same_type_shape (type_of h1, type_of h2)

fun insert_rule rule [] =
      [({head= #head rule, asm= #asm rule}, [rule])]
  | insert_rule rule ((key, rules) :: rest) =
      let
        val rule_key = {head= #head rule, asm= #asm rule}
      in
        if same_key (rule_key, key) then
          (key, rule :: rules) :: rest
        else
          (key, rules) :: insert_rule rule rest
      end

fun cmap_of_rules thms =
  foldl (fn (th, cmap) => insert_rule (analyse_rule th) cmap) [] thms

datatype direction = GoRator | GoRand | GoBody

type binder_info =
  {var : term,
   body_type : hol_type,
   body_path : direction list,
   depth : int}

type split_pack =
  {rule : split_rule,
   enter_path : direction list,
   redex : term,
   binders : int,
   path : int list,
   path_length : int}

fun candidates want_asm cmap head =
  let
    fun add (({head=key_head,asm,...}, rules), acc) =
      if asm = want_asm andalso same_const key_head head andalso
         can (Type.match_type (type_of key_head)) (type_of head)
      then rules @ acc
      else acc
  in
    foldr add [] cmap
  end

fun prefix_path n i =
  List.tabulate (n - i - 1, K GoRator) @ [GoRand]

fun matching rule redex =
  can (match_term (#pattern rule)) redex

fun scan want_asm cmap tm =
  let
    val root_type = type_of tm

    fun mk_pack scan_path enter_path binders node rule =
      let
        val n = #arity rule
        val (head, args) = strip_comb node
      in
        if length args < n then NONE
        else
          let
            val redex = list_mk_comb (head, List.take (args, n))
            val refs =
              List.filter (fn {var,...} => free_in var redex) binders
          in
            if not (matching rule redex) then NONE
            else
              case List.rev refs of
                  [] =>
                    if root_type = bool then
                      SOME {rule=rule, enter_path=[], redex=redex,
                            binders=0, path=scan_path,
                            path_length=length scan_path}
                    else NONE
                | ({body_type,body_path,depth,...} : binder_info) :: _ =>
                    if body_type = bool then
                      SOME {rule=rule, enter_path=body_path,
                            redex=redex, binders=depth, path=scan_path,
                            path_length=length scan_path}
                    else NONE
          end
      end

    fun walk scan_path enter_path binders node =
      if is_abs node then
        let
          val (var, body) = dest_abs node
          val body_path = enter_path @ [GoBody]
          val info = {var=var, body_type=type_of body,
                      body_path=body_path, depth=length binders + 1}
        in
          walk (scan_path @ [0]) body_path (binders @ [info]) body
        end
      else
        let
          val (head, args) = strip_comb node
          val here =
            if is_const head then
              List.mapPartial
                (mk_pack scan_path enter_path binders node)
                (candidates want_asm cmap head)
            else []
          fun descend (arg, (i, packs)) =
            let
              val arg_path =
                enter_path @ prefix_path (length args) i
            in
              (i + 1,
               packs @ walk (scan_path @ [i]) arg_path binders arg)
            end
        in
          #2 (foldl descend (0, here) args)
        end
  in
    walk [] [] [] tm
  end

fun path_le ([], _) = true
  | path_le (_ :: _, []) = false
  | path_le (x :: xs, y :: ys) =
      x < y orelse (x = y andalso path_le (xs, ys))

fun pack_le (p1 : split_pack) (p2 : split_pack) =
  #binders p1 < #binders p2 orelse
  (#binders p1 = #binders p2 andalso
   (#path_length p1 < #path_length p2 orelse
    (#path_length p1 = #path_length p2 andalso
     path_le (#path p1, #path p2))))

fun replace_all target hole tm =
  if aconv target tm then hole
  else if is_comb tm then
    let val (rator, rand) = dest_comb tm
    in
      mk_comb (replace_all target hole rator,
               replace_all target hole rand)
    end
  else if is_abs tm then
    let val (var, body) = dest_abs tm
    in mk_abs (var, replace_all target hole body)
    end
  else tm

fun fresh_parts th =
  let
    val sth = SPEC_ALL th
    val (left, _) = dest_eq (concl sth)
    val (pred, pattern) = dest_comb left
  in
    (sth, pred, pattern)
  end

fun instantiate rule target body =
  let
    val (sth, pred, pattern) = fresh_parts (#thm rule)
    val (terminst, typeinst) = match_term pattern target
    val pred' = Term.inst typeinst pred
    val hole = genvar (type_of target)
    val context = mk_abs (hole, replace_all target hole body)
    val subst = (pred' |-> context) :: terminst
    val ith = INST subst (INST_TYPE typeinst sth)
    val beta =
      LAND_CONV BETA_CONV THENC
      RAND_CONV (TOP_DEPTH_CONV BETA_CONV)
    val result = CONV_RULE beta ith
    val _ =
      if aconv (lhs (concl result)) body then ()
      else raise ERR "instantiate" "instantiated rule has the wrong left side"
  in
    result
  end

fun at_path [] conv = conv
  | at_path (GoRator :: rest) conv = RATOR_CONV (at_path rest conv)
  | at_path (GoRand :: rest) conv = RAND_CONV (at_path rest conv)
  | at_path (GoBody :: rest) conv = ABS_CONV (at_path rest conv)

fun apply_pack ({rule,enter_path,redex,...} : split_pack) =
  at_path enter_path (instantiate rule redex)

fun first_success [] _ =
      raise ERR "SPLIT_CONV" "no applicable split rule"
  | first_success (pack :: packs) tm =
      apply_pack pack tm
      handle HOL_ERR _ => first_success packs tm
           | Conv.UNCHANGED => first_success packs tm

fun SPLIT_CONV thms =
  let
    val cmap = cmap_of_rules thms
  in
    fn tm =>
      let
        val packs = sort pack_le (scan false cmap tm)
        (* Isabelle tries only the first sorted pack.  Trying later packs
           when instantiation fails avoids one rejected rule shadowing an
           otherwise applicable rule, while retaining one split per call. *)
      in
        first_success packs tm
      end
  end

fun split_concl_tac thms = CONV_TAC (SPLIT_CONV thms)

fun contains_head heads tm =
  can (find_term
        (fn subtm =>
            is_const subtm andalso
            List.exists (fn head => same_const head subtm) heads)) tm

fun clean_asm_eq th =
  let
    val not_not = CONJUNCT1 boolTheory.NOT_CLAUSES
    val cancel = REWR_CONV not_not
    val negated = AP_TERM boolSyntax.negation th
    val cleanup =
      LAND_CONV cancel THENC
      RAND_CONV cancel THENC
      RAND_CONV (REDEPTH_CONV cancel)
  in
    (* Cancel the two outer negations without simplifying inside the
       original assumption.  Then remove the double negations generated
       in the case hypotheses.  This is the small fragment of the usual
       NOT_CLAUSES/DE_MORGAN_THM cleanup needed here. *)
    CONV_RULE cleanup negated
  end

fun asm_eq cmap asm =
  let
    val packs = sort pack_le (scan true cmap (mk_neg asm))
  in
    clean_asm_eq (first_success packs (mk_neg asm))
  end

fun SPLIT_ASM_TAC thms =
  let
    val cmap = cmap_of_rules thms
    val heads =
      map (#head o #1)
        (List.filter (fn ({asm,...}, _) => asm) cmap)

    fun tac (asms, goal) =
      case List.find (contains_head heads) asms of
          NONE =>
            raise ERR "SPLIT_ASM_TAC" "no assumption contains a split key"
        | SOME asm =>
            let
              val eq = asm_eq cmap asm
              val cases = EQ_MP eq (ASSUME asm)
            in
              PRED_ASSUM (aconv asm) (K (STRIP_ASSUME_TAC cases))
                (asms, goal)
            end
  in
    tac
  end

fun SPLIT_TAC thms =
  CHANGED_TAC (split_concl_tac thms) ORELSE
  CHANGED_TAC (SPLIT_ASM_TAC thms)

end
