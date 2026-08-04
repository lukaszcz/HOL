structure hhProblemGen :> hhProblemGen =
struct

  open HolKernel boolSyntax

  type term = Term.term
  type thm = Thm.thm
  type named_terms = {conjecture : term, facts : (string * term) list}

  datatype hol_formula =
      HQuant of bool * term list * hol_formula
    | HConn of hhTptpProblem.conn * hol_formula list
    | HAtom of term
  type formula_ir = {conjecture : hol_formula,
                     facts : (string * hol_formula) list}
  type proxy_ir = {conjecture : hol_formula,
                   facts : (string * hol_formula) list,
                   proxies : string list}

  datatype fo_term =
      FOHead of term * fo_term list
    | FOApp of fo_term * fo_term
    | FOPred of fo_term
    | FOAbs of term * fo_term
  datatype fo_formula =
      FOQuant of bool * term list * fo_formula
    | FOConn of hhTptpProblem.conn * fo_formula list
    | FOAtom of fo_term
  type fo_ir = {conjecture : fo_formula, facts : (string * fo_formula) list,
                used_app : bool, used_pp : bool}

  fun fail message = raise Fail ("hhProblemGen: " ^ message)

  fun syntax_of hhTptpProblem.FOF = {with_ite = false, with_let = false}
    | syntax_of (hhTptpProblem.TFF {fool = hhTptpProblem.NoFool, ...}) =
        {with_ite = false, with_let = false}
    | syntax_of (hhTptpProblem.TFF {fool = hhTptpProblem.Fool syntax, ...}) =
        syntax
    | syntax_of (hhTptpProblem.THF {syntax, ...}) = syntax

  fun is_full_ho (hhTptpProblem.THF _) = true
    | is_full_ho _ = false

  fun is_fool (hhTptpProblem.TFF {fool = hhTptpProblem.Fool _, ...}) = true
    | is_fool _ = false

  (* This is deliberately a term operation rather than a simplifier: the
     generator must retain non-$ite COND for TASK_07's helper facts. *)
  fun beta_eta_contract unfold_let tm =
    let
      fun recurse body =
        if is_abs body then
          let
            val (var, matrix) = dest_abs body
            val matrix' = recurse matrix
          in
            if is_comb matrix' andalso aconv (rand matrix') var andalso
               not (List.exists (fn other => aconv var other)
                 (free_vars_lr (rator matrix'))) then
              recurse (rator matrix')
            else mk_abs (var, matrix')
          end
        else if unfold_let andalso is_let body then
          let val (func, arg) = dest_let body in recurse (mk_comb (func, arg)) end
        else if is_comb body then
          let
            val left = recurse (rator body)
            val right = recurse (rand body)
            val combined = mk_comb (left, right)
          in
            if is_abs left then recurse (beta_conv combined) else combined
          end
        else body
    in
      recurse tm
    end

  fun presimp format ({conjecture, facts} : named_terms) =
    let
      val {with_let, ...} = syntax_of format
      val simplify = beta_eta_contract (not with_let)
    in
      {conjecture = simplify conjecture,
       facts = map (fn (name, tm) => (name, simplify tm)) facts}
    end

  fun pass_lambda format mode ({conjecture, facts} : named_terms) =
    let
      val mode' = if mode = "keep_lams" andalso not (is_full_ho format)
                    then "lifting" else mode
      val formulas = conjecture :: map #2 facts
      val (rewritten, definitions) = hhLamTrans.translate mode' formulas
    in
      {conjecture = hd rewritten,
       facts = ListPair.zip (map #1 facts, tl rewritten) @ definitions}
    end

  fun is_monomorphic (hhTypeEnc.Native {poly = false, ...}) = true
    | is_monomorphic (hhTypeEnc.Guards {poly = false, ...}) = true
    | is_monomorphic _ = false

  fun pass_monomorph encoding caps ({conjecture, facts} : named_terms) =
    if is_monomorphic encoding then
      {conjecture = conjecture,
       facts = hhMonomorph.monomorph caps conjecture facts}
    else {conjecture = conjecture, facts = facts}

  fun skeleton tm =
    if is_forall tm then
      let val (var, body) = dest_forall tm in HQuant (true, [var], skeleton body) end
    else if is_exists tm then
      let val (var, body) = dest_exists tm in HQuant (false, [var], skeleton body) end
    else if is_neg tm then HConn (hhTptpProblem.Not, [skeleton (dest_neg tm)])
    else if is_conj tm then
      HConn (hhTptpProblem.And, [skeleton (lhand tm), skeleton (rand tm)])
    else if is_disj tm then
      HConn (hhTptpProblem.Or, [skeleton (lhand tm), skeleton (rand tm)])
    else if is_imp_only tm then
      let val (left, right) = dest_imp tm in
        HConn (hhTptpProblem.Implies, [skeleton left, skeleton right])
      end
    else if is_eq tm andalso type_of (lhand tm) = Type.bool then
      HConn (hhTptpProblem.Iff, [skeleton (lhand tm), skeleton (rand tm)])
    else HAtom tm

  fun formula_skeleton ({conjecture, facts} : named_terms) =
    {conjecture = skeleton conjecture,
     facts = map (fn (name, tm) => (name, skeleton tm)) facts}

  fun logical_info head =
    if same_const head negation then SOME ("not", 1, "$not")
    else if same_const head conjunction then SOME ("conj", 2, "$and")
    else if same_const head disjunction then SOME ("disj", 2, "$or")
    else if same_const head implication then SOME ("imp", 2, "$implies")
    else if same_const head equality then SOME ("eq", 2, "$equal")
    else if same_const head universal then SOME ("all", 1, "$forall")
    else if same_const head existential then SOME ("ex", 1, "$exists")
    else if same_const head T then SOME ("true", 0, "$true")
    else if same_const head F then SOME ("false", 0, "$false")
    else NONE

  fun rebuild head args = List.foldl (fn (arg, fun_tm) => mk_comb (fun_tm, arg))
    head args
  fun proxy_head name head = mk_var ("pxy." ^ name, type_of head)
  fun builtin_head name head = mk_var (name, type_of head)
  fun is_cond_head head = same_const head conditional

  fun transform_term format seen tm =
    let
      val (head, args) = strip_comb tm
      val args' = map (transform_term format seen) args
      val argc = length args
      val {with_ite, ...} = syntax_of format
      fun use_proxy name =
        (if List.exists (fn old => old = name) (!seen) then ()
         else seen := !seen @ [name];
         rebuild (proxy_head name head) args')
      fun use_builtin name = rebuild (builtin_head name head) args'
    in
      if is_cond_head head andalso with_ite andalso argc >= 3 then
        use_builtin "$ite"
      else
        case logical_info head of
            NONE =>
              if is_abs tm then
                let val (var, body) = dest_abs tm in
                  mk_abs (var, transform_term format seen body)
                end
              else if null args then head
              else rebuild (transform_term format seen head) args'
          | SOME (name, card, builtin) =>
              if is_full_ho format then use_builtin builtin
              else if is_fool format andalso argc = card then use_builtin builtin
              else use_proxy name
    end

  fun introduce_proxies format ({conjecture, facts} : formula_ir) =
    let
      val seen = ref []
      fun formula (HQuant (all, vars, body)) = HQuant (all, vars, formula body)
        | formula (HConn (conn, bodies)) = HConn (conn, map formula bodies)
        | formula (HAtom tm) = HAtom (transform_term format seen tm)
    in
      {conjecture = formula conjecture,
       facts = map (fn (name, body) => (name, formula body)) facts,
       proxies = !seen}
    end

  fun translate_front {format, type_enc, lam_trans, mono_iters,
                       mono_instances} terms =
    introduce_proxies format
      (formula_skeleton
        (pass_monomorph type_enc
          {max_iters = mono_iters, max_new_instances = mono_instances}
          (pass_lambda format lam_trans (presimp format terms))))

  fun type_is_fun ty = (ignore (Type.dom_rng ty); true) handle HOL_ERR _ => false
  fun dom_rng ty = SOME (Type.dom_rng ty) handle HOL_ERR _ => NONE

  fun term_head tm = fst (strip_comb tm)
  fun is_generated_var tm =
    is_var tm andalso
    let val name = fst (dest_var tm) in
      String.isPrefix "pxy." name orelse String.isPrefix "$" name
    end
  fun is_symbol tm = is_const tm orelse is_generated_var tm

  fun same_head left right = aconv left right
  fun find_head head [] = NONE
    | find_head head ((other, value) :: rest) =
        if same_head head other then SOME value else find_head head rest

  fun add_head head arity table =
    if not (is_symbol head) then table
    else
      let
        fun update [] = [(head, [arity])]
          | update ((old, arities) :: rest) =
              if same_head head old then (old, arity :: arities) :: rest
              else (old, arities) :: update rest
      in
        update table
      end

  fun heads_of_term tm table =
    let val (head, args) = strip_comb tm in
      List.foldl (fn (arg, result) => heads_of_term arg result)
        (add_head head (length args) table) args
    end

  fun heads_of_formula (HQuant (_, _, body)) table = heads_of_formula body table
    | heads_of_formula (HConn (_, bodies)) table =
        List.foldl (fn (body, result) => heads_of_formula body result)
          table bodies
    | heads_of_formula (HAtom tm) table = heads_of_term tm table

  fun vars_of_formula (HQuant (_, vars, body)) result =
        vars_of_formula body
          (List.filter (not o is_generated_var) vars @ result)
    | vars_of_formula (HConn (_, bodies)) result =
        List.foldl (fn (body, acc) => vars_of_formula body acc) result bodies
    | vars_of_formula (HAtom _) result = result

  fun result_after ty 0 = SOME ty
    | result_after ty count =
        (case dom_rng ty of
           SOME (_, range) => result_after range (count - 1)
         | NONE => NONE)

  fun min_arity vars (head, arities) =
    let
      val ordinary = List.foldl Int.min (hd arities) (tl arities)
      fun useful count =
        case result_after (type_of head) count of
            NONE => false
          | SOME result => type_is_fun result andalso
              List.exists (fn var => type_of var = result) vars
      fun lower count best =
        if count >= ordinary then best
        else lower (count + 1) (if useful count then count else best)
    in
      lower 0 ordinary
    end

  (* Pass 6.  Sufficient_App_Op retains direct applications unless a
     function-typed variable can consume a partial result.  Isabelle's
     45-fact poly-native cut-over uses Min_App_Op: direct symbols then keep
     their largest observed spine, trading a few partial applications for a
     smaller declaration/application vocabulary. *)
  fun app_arities encoding nfacts variables table =
    map (fn item as (_, arities) =>
      let
        val minimum = min_arity variables item
        val maximum = List.foldl Int.max (hd arities) (tl arities)
        val use_min =
          case encoding of
              hhTypeEnc.Native {poly = true, ...} => nfacts >= 45
            | _ => false
      in
        (fst item, if use_min then maximum else minimum)
      end) table

  fun arity_for head arities =
    case find_head head arities of SOME arity => arity | NONE => 0

  fun firstorderize format encoding ({conjecture, facts, ...} : proxy_ir) =
    if is_full_ho format then
      let
        fun term in_position tm =
          if is_abs tm then
            let val (var, body) = dest_abs tm in FOAbs (var, term false body) end
          else
            let val (head, args) = strip_comb tm in
              FOHead (head, map (term true) args)
            end
        fun formula (HQuant (all, vars, body)) = FOQuant (all, vars, formula body)
          | formula (HConn (conn, bodies)) = FOConn (conn, map formula bodies)
          | formula (HAtom tm) = FOAtom (term false tm)
      in
        {conjecture = formula conjecture,
         facts = map (fn (name, body) => (name, formula body)) facts,
         used_app = false, used_pp = false}
      end
    else
      let
        val table = heads_of_formula conjecture
          (List.foldl (fn ((_, formula), result) => heads_of_formula formula result)
            [] facts)
        val variables = vars_of_formula conjecture
          (List.foldl (fn ((_, formula), result) => vars_of_formula formula result)
            [] facts)
        val arities = app_arities encoding (length facts) variables table
        val used_app = ref false
        val used_pp = ref false
        fun term in_position tm =
          if is_abs tm then fail "lambda survived first-order lambda handling"
          else
            let
              val (head, args) = strip_comb tm
              val minimum = if is_symbol head then arity_for head arities else 0
              val direct_arity = if length args < minimum then 0 else minimum
              val direct = FOHead (head, map (term true)
                (List.take (args, direct_arity)))
              val applied = List.foldl (fn (arg, result) =>
                (used_app := true; FOApp (result, term true arg))) direct
                (List.drop (args, direct_arity))
              val boolean = type_of tm = Type.bool
            in
              if in_position andalso boolean andalso not (is_fool format) then
                (used_pp := true; FOPred applied)
              else applied
            end
        fun formula (HQuant (all, vars, body)) = FOQuant (all, vars, formula body)
          | formula (HConn (conn, bodies)) = FOConn (conn, map formula bodies)
          | formula (HAtom tm) = FOAtom (term false tm)
      in
        {conjecture = formula conjecture,
         facts = map (fn (name, body) => (name, formula body)) facts,
         used_app = !used_app, used_pp = !used_pp}
      end

  fun add_once equal value values =
    if List.exists (equal value) values then values else values @ [value]
  fun same_value left right = left = right
  fun types_of_type ty =
    if is_vartype ty then [ty]
    else let val {Args, ...} = Type.dest_thy_type ty in ty :: List.concat (map types_of_type Args) end
  fun types_of_term tm = types_of_type (type_of tm) @
    List.concat (map types_of_term (snd (strip_comb tm)))
  fun types_of_formula (FOQuant (_, vars, body)) =
        List.concat (map (types_of_type o type_of) vars) @ types_of_formula body
    | types_of_formula (FOConn (_, bodies)) = List.concat (map types_of_formula bodies)
    | types_of_formula (FOAtom tm) = types_of_fo_term tm
  and types_of_fo_term (FOHead (head, args)) =
        types_of_type (type_of head) @ List.concat (map types_of_fo_term args)
    | types_of_fo_term (FOApp (left, right)) =
        types_of_fo_term left @ types_of_fo_term right
    | types_of_fo_term (FOPred body) = types_of_fo_term body
    | types_of_fo_term (FOAbs (var, body)) =
        types_of_type (type_of var) @ types_of_fo_term body

  fun raw_mangle_type ty =
    if is_vartype ty then "var." ^ dest_vartype ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty in
        Thy ^ "." ^ Tyop ^
        (if null Args then "" else "(" ^
          String.concatWith "," (map raw_mangle_type Args) ^ ")")
      end
  fun mangle_type ty = aiLib.escape ("ty." ^ raw_mangle_type ty)

  fun native_type ty =
    if is_vartype ty then hhTptpProblem.TyVar ("A" ^ aiLib.escape (dest_vartype ty))
    else
      let
        val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in
        if Thy = "min" andalso Tyop = "fun" then
          (case Args of
             [domain, range] => hhTptpProblem.TyFun (native_type domain,
               native_type range)
           | _ => fail "malformed function type")
        else if Thy = "min" andalso Tyop = "bool" then
          hhTptpProblem.TyCon ("$o", [])
        else hhTptpProblem.TyCon
          (aiLib.escape ("ty." ^ Thy ^ "." ^ Tyop), map native_type Args)
      end

  fun type_for (hhTypeEnc.Native {poly = true, ...}) = native_type
    | type_for _ = fn ty => hhTptpProblem.TyCon (mangle_type ty, [])

  fun const_type_args tm =
    if not (is_const tm) then []
    else
      let
        val {Thy, Name, Ty} = dest_thy_const tm
        val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
        val (subst, unmatched) = raw_match_type generic Ty ([], [])
        fun image variable =
          case List.find (fn entry => #redex entry = variable) subst of
              SOME entry => #residue entry
            | NONE => variable
      in
        map image (Type.type_vars generic @ unmatched)
      end

  fun raw_symbol head =
    if is_const head then
      let val {Thy, Name, ...} = dest_thy_const head in "c." ^ Thy ^ "." ^ Name end
    else if is_var head then fst (dest_var head)
    else fail "term head is neither a constant nor a variable"

  fun variable_name name =
    if size name > 0 andalso Char.isUpper (String.sub (name, 0)) then
      aiLib.escape name
    else "V_" ^ aiLib.escape name

  fun encoded_symbol encoding head =
    if is_var head andalso not (is_generated_var head) then
      variable_name (raw_symbol head)
    else
      case encoding of
          hhTypeEnc.Native {poly = true, ...} => aiLib.escape (raw_symbol head)
        | _ =>
            let val args = const_type_args head in
              if null args then aiLib.escape (raw_symbol head)
              else aiLib.escape (raw_symbol head ^ "." ^
                String.concatWith "." (map raw_mangle_type args))
            end

  fun encode_term encoding (FOHead (head, args)) =
        hhTptpProblem.Tm ((encoded_symbol encoding head,
          (case encoding of
             hhTypeEnc.Native {poly = true, ...} => map native_type (const_type_args head)
           | _ => [])), map (encode_term encoding) args)
    | encode_term encoding (FOApp (left, right)) =
        hhTptpProblem.Tm (("app_2E", []),
          [encode_term encoding left, encode_term encoding right])
    | encode_term encoding (FOPred body) =
        hhTptpProblem.Tm (("pp_2E", []), [encode_term encoding body])
    | encode_term encoding (FOAbs (var, body)) =
        hhTptpProblem.TmAbs ((variable_name (fst (dest_var var)),
          type_for encoding (type_of var)), encode_term encoding body)

  fun type_vars_of_formula formula =
    let
      fun collect_ty ty result =
        if is_vartype ty then add_once same_value ty result
        else let val {Args, ...} = Type.dest_thy_type ty in
          List.foldl (fn (arg, acc) => collect_ty arg acc) result Args
        end
      fun collect_term (FOHead (head, args)) result =
            List.foldl (fn (arg, acc) => collect_term arg acc)
              (collect_ty (type_of head) result) args
        | collect_term (FOApp (left, right)) result =
            collect_term right (collect_term left result)
        | collect_term (FOPred body) result = collect_term body result
        | collect_term (FOAbs (var, body)) result =
            collect_term body (collect_ty (type_of var) result)
      fun collect (FOQuant (_, vars, body)) result =
            collect body (List.foldl (fn (var, acc) =>
              collect_ty (type_of var) acc) result vars)
        | collect (FOConn (_, bodies)) result =
            List.foldl (fn (body, acc) => collect body acc) result bodies
        | collect (FOAtom tm) result = collect_term tm result
    in
      collect formula []
    end

  fun guard_name ty = aiLib.escape ("gd." ^ mangle_type ty)
  fun guard_atom encoding ty tm =
    hhTptpProblem.Atom (hhTptpProblem.Tm ((guard_name ty, []), [tm]))

  fun guarded_type (hhTypeEnc.Guards {level = hhTypeEnc.AllTypes, ...}) _ _ = true
    | guarded_type (hhTypeEnc.Guards {level = hhTypeEnc.NonmonoNonUniform, ...})
        needs ty = List.exists (fn other => other = ty) needs
    | guarded_type _ _ _ = false

  (* Pass 8 soundness argument.  Mangled native symbols interpret every
     ground HOL instance in its own nonempty sort (leftover variables name
     opaque nonempty sorts).  TF1 keeps exactly HOL's parametric type
     arguments and binds all formula type variables.  Guards restrict every
     guarded quantifier and gsy result to its HOL carrier; wit witnesses make
     each such carrier inhabited.  Thus each family extends a HOL model and
     cannot prove a non-theorem merely by confusing types. *)
  fun encode_formula format encoding needs formula =
    let
      fun encode (FOQuant (all, vars, body)) =
            List.foldr (fn (var, result) =>
              let
                val ty = type_of var
                val var_name = variable_name (fst (dest_var var))
                val bound = (var_name, SOME (type_for encoding ty))
                val result' =
                  if guarded_type encoding needs ty then
                    if all then hhTptpProblem.Conn (hhTptpProblem.Implies,
                      [guard_atom encoding ty
                        (hhTptpProblem.Tm ((var_name, []), [])), result])
                    else hhTptpProblem.Conn (hhTptpProblem.And,
                      [guard_atom encoding ty
                        (hhTptpProblem.Tm ((var_name, []), [])), result])
                  else result
              in
                hhTptpProblem.Quant (all, [bound], result')
              end) (encode body) vars
        | encode (FOConn (conn, bodies)) =
            hhTptpProblem.Conn (conn, map encode bodies)
        | encode (FOAtom tm) = hhTptpProblem.Atom (encode_term encoding tm)
      val result = encode formula
      val tvars = type_vars_of_formula formula
    in
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            if null tvars then result
            else hhTptpProblem.TyQuant (true,
              map (fn ty => "A" ^ aiLib.escape (dest_vartype ty)) tvars, result)
        | _ => result
    end

  fun heads_of_fo_term (FOHead (head, args), heads) =
        List.foldl heads_of_fo_term (if is_symbol head then
          add_once (fn left => fn right => same_head left right) head heads else heads) args
    | heads_of_fo_term (FOApp (left, right), heads) =
        heads_of_fo_term (right, heads_of_fo_term (left, heads))
    | heads_of_fo_term (FOPred body, heads) = heads_of_fo_term (body, heads)
    | heads_of_fo_term (FOAbs (_, body), heads) = heads_of_fo_term (body, heads)
  fun heads_of_fo_formula (FOQuant (_, _, body), heads) =
        heads_of_fo_formula (body, heads)
    | heads_of_fo_formula (FOConn (_, bodies), heads) =
        List.foldl heads_of_fo_formula heads bodies
    | heads_of_fo_formula (FOAtom tm, heads) = heads_of_fo_term (tm, heads)

  fun type_parts ty =
    case dom_rng ty of
        SOME (domain, range) =>
          let val (domains, result) = type_parts range in (domain :: domains, result) end
      | NONE => ([], ty)

  fun declaration_type encoding head =
    let
      val (domains, result) = type_parts (type_of head)
      val ty = List.foldr (fn (domain, range) =>
        hhTptpProblem.TyFun (type_for encoding domain, range))
        (type_for encoding result) domains
    in
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            let val vars = Type.type_vars (type_of head) in
              if null vars then ty else hhTptpProblem.TyPi
                (map (fn var => "A" ^ aiLib.escape (dest_vartype var)) vars, ty)
            end
        | _ => ty
    end

  fun type_declarations encoding types =
    let
      fun native_op ty result =
        if is_vartype ty then result
        else
          let
            val {Thy, Tyop, Args} = Type.dest_thy_type ty
            val symbol = aiLib.escape ("ty." ^ Thy ^ "." ^ Tyop)
          in
            add_once same_value (symbol, length Args) result
          end
      fun mono_sort ty result = add_once same_value (mangle_type ty) result
    in
      case encoding of
          hhTypeEnc.Native {poly = true, ...} =>
            map (fn (symbol, arity) => hhTptpProblem.TypeDecl
              (aiLib.escape ("ty." ^ symbol), symbol, arity))
              (List.foldl (fn (ty, result) => native_op ty result) [] types)
        | _ =>
            map (fn symbol => hhTptpProblem.TypeDecl
              (aiLib.escape ("ty." ^ symbol), symbol, 0))
              (List.foldl (fn (ty, result) => mono_sort ty result) [] types)
    end

  fun gsy_line encoding needs head =
    let
      val (domains, result) = type_parts (type_of head)
    in
      if not (guarded_type encoding needs result) then NONE
      else
        let
          val variables = ListPair.zip
            (map (fn index => "G" ^ Int.toString index)
               (List.tabulate (length domains, fn index => index)),
             map (type_for encoding) domains)
          val application = hhTptpProblem.Tm ((encoded_symbol encoding head, []),
            map (fn (name, _) => hhTptpProblem.Tm ((name, []), [])) variables)
          val body = guard_atom encoding result application
          val formula = if null variables then body else hhTptpProblem.Quant
            (true, map (fn (name, ty) => (name, SOME ty)) variables, body)
        in
          SOME (hhTptpProblem.FormLine
            (aiLib.escape ("gsy." ^ encoded_symbol encoding head),
             hhTptpProblem.Axiom, formula))
        end
    end

  fun witness_line encoding ty =
    let
      val witness = aiLib.escape ("wit." ^ mangle_type ty)
      val term = hhTptpProblem.Tm ((witness, []), [])
    in
      hhTptpProblem.FormLine (aiLib.escape ("wit." ^ mangle_type ty),
        hhTptpProblem.Axiom, guard_atom encoding ty term)
    end

  fun generated_problem format encoding needs ({conjecture, facts, used_app,
                                                used_pp} : fo_ir) =
    let
      val all_formulas = conjecture :: map #2 facts
      val heads = List.foldl heads_of_fo_formula [] all_formulas
      val all_types = List.foldl (fn (formula, result) =>
        types_of_formula formula @ result) [] all_formulas
      val decls =
        if format = hhTptpProblem.FOF then []
        else
          let
            val sym_decls = map (fn head => hhTptpProblem.SymDecl
              (aiLib.escape ("sy." ^ encoded_symbol encoding head),
               encoded_symbol encoding head, declaration_type encoding head)) heads
            val app_decls = if used_app then [hhTptpProblem.SymDecl
              ("sy_2Eapp", "app_2E", hhTptpProblem.TyFun
                (hhTptpProblem.TyCon ("$i", []), hhTptpProblem.TyFun
                  (hhTptpProblem.TyCon ("$i", []), hhTptpProblem.TyCon ("$i", []))))]
              else []
            val pp_decls = if used_pp then [hhTptpProblem.SymDecl
              ("sy_2Epp", "pp_2E", hhTptpProblem.TyFun
                (hhTptpProblem.TyCon ("$i", []), hhTptpProblem.TyCon ("$o", [])))]
              else []
          in
            type_declarations encoding all_types @ sym_decls @ app_decls @ pp_decls
          end
      val gsy = List.mapPartial (gsy_line encoding needs) heads
      val guard_types = List.foldl (fn (ty, result) =>
        if guarded_type encoding needs ty then add_once same_value ty result else result)
        [] all_types
      val witnesses = map (witness_line encoding) guard_types
      val facts' = map (fn (name, formula) => hhTptpProblem.FormLine
        (aiLib.escape ("thm." ^ name), hhTptpProblem.Axiom,
         encode_formula format encoding needs formula)) facts
      val conjecture' = hhTptpProblem.FormLine ("conjecture",
        hhTptpProblem.Conjecture, encode_formula format encoding needs conjecture)
    in
      [("Declarations", decls @ gsy @ witnesses),
       ("Helpers", []), ("Facts", facts'), ("Conjecture", [conjecture'])]
    end

  fun generate_problem options ({conjecture, facts} : named_terms) =
    let
      val {format, type_enc, lam_trans, mono_iters, mono_instances} = options
      val terms = pass_monomorph type_enc
        {max_iters = mono_iters, max_new_instances = mono_instances}
        (pass_lambda format lam_trans
          (presimp format {conjecture = conjecture, facts = facts}))
      val proxy = introduce_proxies format (formula_skeleton terms)
      val needs =
        case type_enc of
            hhTypeEnc.Guards {level = hhTypeEnc.NonmonoNonUniform, ...} =>
              hhTypeEnc.types_needing_encoding
                (#conjecture terms :: map #2 (#facts terms))
          | _ => []
    in
      generated_problem format type_enc needs (firstorderize format type_enc proxy)
    end

  fun export_pb _ _ _ =
    fail "export_pb is not yet wired (TASK_07 completes problem printing)"

end
