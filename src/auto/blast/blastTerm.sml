structure blastTerm :> blastTerm =
struct

  datatype term =
      Const of string * term list
    | Skolem of string * term option ref list
    | Free of string
    | Var of term option ref
    | Bound of int
    | Abs of string * term
    | $ of term * term

  infix 9 $

  type var = term option ref

  datatype state = State of
    {trail : var list ref,
     ntrail : int ref}

  val goal_name = "*Goal*"
  val false_name = "*False*"

  fun const_name {Thy, Name} = Thy ^ "$" ^ Name

  fun mkGoal p = Const (goal_name, []) $ p

  fun isGoal (Const (name, _) $ _) = name = goal_name
    | isGoal _ = false

  fun newState () = State {trail = ref [], ntrail = ref 0}

  fun trailSize (State {ntrail, ...}) = !ntrail

  fun trailVars (State {trail, ...}) = !trail

  fun is_Var (Var _) = true
    | is_Var _ = false

  fun dest_Var (Var v) = v
    | dest_Var _ = raise Fail "blastTerm.dest_Var"

  fun rand (_ $ x) = x
    | rand _ = raise Fail "blastTerm.rand"

  fun list_comb (f, []) = f
    | list_comb (f, x :: xs) = list_comb (f $ x, xs)

  fun strip_comb term =
    let
      fun strip (f $ x, xs) = strip (f, x :: xs)
        | strip result = result
    in
      strip (term, [])
    end

  fun head_of (f $ _) = head_of f
    | head_of term = term

  fun aconv (Const (a, ts), Const (b, us)) =
        a = b andalso aconvs (ts, us)
    | aconv (Skolem (a, _), Skolem (b, _)) = a = b
    | aconv (Free a, Free b) = a = b
    | aconv (Var v, u) =
        (case !v of
             SOME t => aconv (t, u)
           | NONE =>
               (case u of
                    Var w =>
                      (case !w of
                           SOME t => aconv (Var v, t)
                         | NONE => v = w)
                  | _ => false))
    | aconv (t, Var v) =
        (case !v of
             SOME u => aconv (t, u)
           | NONE => false)
    | aconv (Bound i, Bound j) = i = j
    | aconv (Abs (_, t), Abs (_, u)) = aconv (t, u)
    | aconv (f $ t, g $ u) = aconv (f, g) andalso aconv (t, u)
    | aconv _ = false

  and aconvs ([], []) = true
    | aconvs (t :: ts, u :: us) =
        aconv (t, u) andalso aconvs (ts, us)
    | aconvs _ = false

  fun mem_term (_, []) = false
    | mem_term (term, other :: terms) =
        aconv (term, other) orelse mem_term (term, terms)

  fun ins_term (term, terms) =
    if mem_term (term, terms) then terms else term :: terms

  fun mem_var (_, []) = false
    | mem_var (v, w :: ws) = v = w orelse mem_var (v, ws)

  fun ins_var (v, vars) =
    if mem_var (v, vars) then vars else v :: vars

  fun add_term_vars (Skolem (_, args), vars) =
        add_vars_vars (args, vars)
    | add_term_vars (Var v, vars) =
        (case !v of
             NONE => ins_var (v, vars)
           | SOME term => add_term_vars (term, vars))
    | add_term_vars (Const (_, terms), vars) =
        add_terms_vars (terms, vars)
    | add_term_vars (Abs (_, body), vars) = add_term_vars (body, vars)
    | add_term_vars (f $ x, vars) =
        add_term_vars (f, add_term_vars (x, vars))
    | add_term_vars (_, vars) = vars

  and add_terms_vars ([], vars) = vars
    | add_terms_vars (term :: terms, vars) =
        add_terms_vars (terms, add_term_vars (term, vars))

  and add_vars_vars ([], vars) = vars
    | add_vars_vars (v :: vs, vars) =
        (case !v of
             SOME term => add_vars_vars (vs, add_term_vars (term, vars))
           | NONE => add_vars_vars (vs, ins_var (v, vars)))

  fun vars_in_vars vars = add_vars_vars (vars, [])

  fun incr_bv increment =
    let
      fun inc level (term as Bound i) =
            if i >= level then Bound (i + increment) else term
        | inc level (Abs (name, body)) =
            Abs (name, inc (level + 1) body)
        | inc level (f $ x) = inc level f $ inc level x
        | inc _ term = term
    in
      inc
    end

  fun incr_boundvars 0 term = term
    | incr_boundvars increment term = incr_bv increment 0 term

  fun add_loose_bnos (Bound i, level, js) =
        if i < level then js
        else if List.exists (fn j => j = i - level) js then js
        else i - level :: js
    | add_loose_bnos (Abs (_, body), level, js) =
        add_loose_bnos (body, level + 1, js)
    | add_loose_bnos (f $ x, level, js) =
        add_loose_bnos (f, level, add_loose_bnos (x, level, js))
    | add_loose_bnos (_, _, js) = js

  fun loose_bnos term = add_loose_bnos (term, 0, [])

  fun subst_bound (arg, term) =
    let
      fun subst (body as Bound i, level) =
            if i < level then body
            else if i = level then incr_boundvars level arg
            else Bound (i - 1)
        | subst (Abs (name, body), level) =
            Abs (name, subst (body, level + 1))
        | subst (f $ x, level) =
            subst (f, level) $ subst (x, level)
        | subst (body, _) = body
    in
      subst (term, 0)
    end

  fun norm term =
    case term of
        Skolem (name, args) => Skolem (name, vars_in_vars args)
      | Const (name, terms) => Const (name, map norm terms)
      | Var v =>
          (case !v of
               NONE => term
             | SOME body => norm body)
      | f $ x =>
          (case norm f of
               Abs (_, body) => norm (subst_bound (x, body))
             | nf => nf $ norm x)
      | _ => term

  fun wkNormAux term =
    case term of
        Var v =>
          (case !v of
               SOME body => wkNorm body
             | NONE => term)
      | f $ x =>
          (case wkNormAux f of
               Abs (_, body) => wkNorm (subst_bound (x, body))
             | nf => nf $ x)
      | Abs (name, body) =>
          (case wkNormAux body of
               nb as (f $ x) =>
                 if List.exists (fn i => i = 0) (loose_bnos f)
                    orelse not (aconv (wkNorm x, Bound 0))
                 then Abs (name, nb)
                 else wkNorm (incr_boundvars ~1 f)
             | nb => Abs (name, nb))
      | _ => term

  and wkNorm term =
    case head_of term of
        Const _ => term
      | Skolem _ => term
      | Free _ => term
      | _ => wkNormAux term

  fun varOccur v =
    let
      fun occs _ [] = false
        | occs level (term :: terms) =
            occ level term orelse occs level terms
      and occ level (Var w) =
            v = w orelse
            (case !w of
                 NONE => false
               | SOME term => occ level term)
        | occ level (Skolem (_, args)) =
            occs level (map Var args)
        | occ level (Bound i) = level <= i
        | occ level (Abs (_, body)) = occ (level + 1) body
        | occ level (f $ x) = occ level x orelse occ level f
        | occ _ _ = false
    in
      occ 0
    end

  exception UNIFY

  fun clearTo (State {ntrail, trail}) mark =
    while !ntrail <> mark do
      case !trail of
          [] => raise Fail "blastTerm.clearTo: invalid trail mark"
        | v :: vs =>
            (v := NONE;
             trail := vs;
             ntrail := !ntrail - 1)

  fun unify state (vars, left, right) =
    let
      val State {ntrail, trail} = state
      val mark = !ntrail

      fun update (term as Var v, other) =
            if aconv (term, other) then ()
            else if varOccur v other then raise UNIFY
            else if mem_var (v, vars) then v := SOME other
            else if is_Var other andalso
                    mem_var (dest_Var other, vars)
            then dest_Var other := SOME term
            else
              (v := SOME other;
               trail := v :: !trail;
               ntrail := !ntrail + 1)
        | update _ = raise UNIFY

      fun unifyAux (t, u) =
        case (wkNorm t, wkNorm u) of
            (nt as Var _, nu) => update (nt, nu)
          | (nu, nt as Var _) => update (nt, nu)
          | (Const (a, ats), Const (b, bts)) =>
              if a = b then unifysAux (ats, bts) else raise UNIFY
          | (Abs (_, t'), Abs (_, u')) => unifyAux (t', u')
          | (f $ t', g $ u') =>
              (unifyAux (f, g); unifyAux (t', u'))
          | (nt, nu) =>
              if aconv (nt, nu) then () else raise UNIFY

      and unifysAux ([], []) = ()
        | unifysAux (t :: ts, u :: us) =
            (unifyAux (t, u); unifysAux (ts, us))
        | unifysAux _ = raise UNIFY
    in
      (unifyAux (left, right); true)
      handle UNIFY => (clearTo state mark; false)
    end

end
