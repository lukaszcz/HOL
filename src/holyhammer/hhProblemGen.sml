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
          let
            val (func, arg) = dest_let body
          in
            recurse (mk_comb (func, arg))
          end
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
      val conjecture' = hd rewritten
      val fact_terms = tl rewritten
    in
      {conjecture = conjecture',
       facts = ListPair.zip (map #1 facts, fact_terms) @ definitions}
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
      let val (var, body) = dest_forall tm in
        HQuant (true, [var], skeleton body)
      end
    else if is_exists tm then
      let val (var, body) = dest_exists tm in
        HQuant (false, [var], skeleton body)
      end
    else if is_neg tm then HConn (hhTptpProblem.Not, [skeleton (dest_neg tm)])
    else if is_conj tm then
      HConn (hhTptpProblem.And, [skeleton (lhand tm), skeleton (rand tm)])
    else if is_disj tm then
      HConn (hhTptpProblem.Or, [skeleton (lhand tm), skeleton (rand tm)])
    else if is_imp_only tm then
      let val (left, right) = dest_imp tm in
        HConn (hhTptpProblem.Implies, [skeleton left, skeleton right])
      end
    else if is_eq tm andalso type_of tm = Type.bool then
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

  fun rebuild head args = List.foldl (fn (arg, fn_tm) => mk_comb (fn_tm, arg))
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

  fun export_pb _ _ _ =
    fail "export_pb is not yet wired (TASK_07 completes problem printing)"

end
