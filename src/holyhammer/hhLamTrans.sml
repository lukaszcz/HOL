structure hhLamTrans :> hhLamTrans =
struct

  open HolKernel boolSyntax

  fun fail message = raise Fail ("hhLamTrans: " ^ message)

  fun has_var variable tm =
    List.exists (fn other => aconv variable other) (free_vars_lr tm)

  fun mk_fun domain range = Type.mk_type ("fun", [domain, range])

  fun close_formula tm = list_mk_forall (free_vars_lr tm, tm)

  fun strip_abs tm =
    let
      fun loop vars body =
        if is_abs body then
          let val (var, next) = dest_abs body in loop (vars @ [var]) next end
        else (vars, body)
    in
      loop [] tm
    end

  fun strip_foralls tm =
    let
      fun loop vars body =
        if is_forall body then
          let val (var, next) = dest_forall body in loop (vars @ [var]) next end
        else (vars, body)
    in
      loop [] tm
    end

  fun logical_map recurse tm =
    if is_forall tm then
      let val (var, body) = dest_forall tm in mk_forall (var, recurse body) end
    else if is_exists tm then
      let val (var, body) = dest_exists tm in mk_exists (var, recurse body) end
    else if is_neg tm then mk_neg (recurse (dest_neg tm))
    else if is_conj tm then
      mk_conj (recurse (lhand tm), recurse (rand tm))
    else if is_disj tm then
      mk_disj (recurse (lhand tm), recurse (rand tm))
    else if is_imp_only tm then
      let
        val (left, right) = dest_imp tm
      in
        mk_imp (recurse left, recurse right)
      end
    else if is_eq tm then
      mk_eq (recurse (lhand tm), recurse (rand tm))
    else if is_comb tm then
      mk_comb (recurse (rator tm), recurse (rand tm))
    else tm

  (* Do not open the combin theory: doing so changes the session grammar.
     Constants are looked up only when combs is selected.  HOL4 calls the B
     combinator "o"; it has B's defining equation o f g x = f (g x). *)
  fun combin name =
    gen_tyvarify (prim_mk_const {Thy = "combin", Name = name})

  fun ucomb f x = mk_ucomb (f, x)

  fun apply2 f x y = ucomb (ucomb f x) y

  (* Instantiation of a polymorphic combinator is fixed by its final
     argument.  Peel that application back off to obtain the required
     function-valued combinator term. *)
  fun as_function variable tm = rator (ucomb tm variable)

  fun abstract variable tm =
    if aconv variable tm then as_function variable (combin "I")
    else if not (has_var variable tm) then
      as_function variable (ucomb (combin "K") tm)
    else if is_comb tm then
      let
        val left = rator tm
        val right = rand tm
        val left_has = has_var variable left
        val right_has = has_var variable right
      in
        if left_has andalso right_has then
          as_function variable
            (apply2 (combin "S") (abstract variable left)
              (abstract variable right))
        else if left_has then
          as_function variable
            (apply2 (combin "C") (abstract variable left) right)
        else if right_has then
          as_function variable
            (apply2 (combin "o") left (abstract variable right))
        else as_function variable (ucomb (combin "K") tm)
      end
    else as_function variable (ucomb (combin "K") tm)

  fun eliminate_abs tm =
    let
      fun recurse body =
        if is_abs body then
          let
            val (vars, matrix) = strip_abs body
            val matrix' = recurse matrix
          in
            List.foldr (fn (var, result) => abstract var result) matrix' vars
          end
        else logical_map recurse body
    in
      recurse tm
    end

  fun eta_contract tm =
    let
      fun recurse body =
        if is_abs body then
          let
            val (var, matrix) = dest_abs body
            val matrix' = recurse matrix
          in
            if is_comb matrix' andalso aconv (rand matrix') var andalso
               not (has_var var (rator matrix')) then recurse (rator matrix')
            else mk_abs (var, matrix')
          end
        else logical_map recurse body
    in
      recurse tm
    end

  fun lift formulas =
    let
      val next = ref 0
      val definitions = ref []

      fun fresh_name () =
        let
          val index = !next
          val _ = next := index + 1
        in
          "lam." ^ Int.toString index
        end

      fun recurse tm =
        if is_abs tm then lift_abs tm else logical_map recurse tm
      and lift_abs tm =
        let
          val (bound, matrix) = strip_abs tm
          val captured = free_vars_lr tm
          val matrix' = recurse matrix
          val lam_type =
            List.foldr (fn (var, result) => mk_fun (type_of var) result)
              (type_of tm) captured
          val lam = mk_var (fresh_name (), lam_type)
          val replacement = list_mk_comb (lam, captured)
          val lhs = list_mk_comb (replacement, bound)
          val definition = list_mk_forall (captured @ bound,
            mk_eq (lhs, matrix'))
          val _ =
            definitions := (fst (dest_var lam), definition) :: !definitions
        in
          replacement
        end

      val rewritten = map (recurse o close_formula) formulas
    in
      (rewritten, List.rev (!definitions))
    end

  fun intentionalize definition =
    let
      val (_, equation) = strip_foralls definition
      val (left, right) = dest_eq equation
      val (head, args) = strip_comb left
    in
      mk_eq (head, list_mk_abs (args, right))
    end

  fun translate "lifting" formulas = lift formulas
    | translate "combs" formulas =
        (map (eliminate_abs o close_formula) formulas, [])
    | translate "combs_and_lifting" formulas =
        let
          val (rewritten, definitions) = lift formulas
          val combinator_definitions = map (fn (name, definition) =>
            (name ^ ".combs", eliminate_abs (intentionalize definition)))
            definitions
        in
          (rewritten, definitions @ combinator_definitions)
        end
    | translate "keep_lams" formulas =
        (map (eta_contract o close_formula) formulas, [])
    | translate "" _ = fail "the empty lambda mode belongs to the legacy path"
    | translate mode _ = fail ("unknown lambda mode " ^ String.toString mode)

end
