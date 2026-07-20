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

  fun aconvMeasured checkpoint =
    let
      fun equal (left, right) =
        (checkpoint ();
         case (left, right) of
             (Const (a, ts), Const (b, us)) =>
               a = b andalso equals (ts, us)
           | (Skolem (a, _), Skolem (b, _)) => a = b
           | (Free a, Free b) => a = b
           | (Var v, u) =>
               (case !v of
                    SOME t => equal (t, u)
                  | NONE =>
                      (case u of
                           Var w =>
                             (case !w of
                                  SOME t => equal (Var v, t)
                                | NONE => v = w)
                         | _ => false))
           | (t, Var v) =>
               (case !v of SOME u => equal (t, u) | NONE => false)
           | (Bound i, Bound j) => i = j
           | (Abs (_, t), Abs (_, u)) => equal (t, u)
           | (f $ t, g $ u) => equal (f, g) andalso equal (t, u)
           | _ => false)
      and equals ([], []) = true
        | equals (t :: ts, u :: us) =
            (checkpoint (); equal (t, u) andalso equals (ts, us))
        | equals _ = false
    in
      equal
    end

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

  fun add_term_vars_measured checkpoint (term, vars) =
    let
      fun add_term (item, accumulated) =
        (checkpoint ();
         case item of
             Skolem (_, args) => add_vars (args, accumulated)
           | Var v =>
               (case !v of
                    NONE => add_var (v, accumulated)
                  | SOME body => add_term (body, accumulated))
           | Const (_, terms) => add_terms (terms, accumulated)
           | Abs (_, body) => add_term (body, accumulated)
           | f $ x => add_term (f, add_term (x, accumulated))
           | _ => accumulated)
      and add_terms ([], accumulated) = accumulated
        | add_terms (item :: items, accumulated) =
            (checkpoint ();
             add_terms (items, add_term (item, accumulated)))
      and add_vars ([], accumulated) = accumulated
        | add_vars (v :: vs, accumulated) =
            (checkpoint ();
             case !v of
                 SOME body => add_vars (vs, add_term (body, accumulated))
               | NONE => add_vars (vs, add_var (v, accumulated)))
      and add_var (v, []) = [v]
        | add_var (v, w :: ws) =
            (checkpoint ();
             if v = w then w :: ws else w :: add_var (v, ws))
    in
      add_term (term, vars)
    end

  fun add_terms_vars_measured checkpoint (terms, vars) =
    let
      fun add ([], accumulated) = accumulated
        | add (term :: rest, accumulated) =
            (checkpoint ();
             add (rest,
                  add_term_vars_measured checkpoint (term, accumulated)))
    in
      add (terms, vars)
    end

  fun vars_in_vars_measured checkpoint vars =
    let
      fun add ([], accumulated) = accumulated
        | add (v :: vs, accumulated) =
            (checkpoint ();
             case !v of
                 SOME term =>
                   add
                     (vs,
                      add_term_vars_measured checkpoint
                        (term, accumulated))
               | NONE =>
                   add
                     (vs,
                      add_term_vars_measured checkpoint
                        (Var v, accumulated)))
    in
      add (vars, [])
    end

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

  (* These are separate from the ordinary de-Bruijn operations so production
     normalization remains callback-free.  Every recursive term or accumulator
     item is a cooperative boundary. *)
  fun incr_boundvars_measured checkpoint increment term =
    if increment = 0 then term
    else
      let
        fun inc level item =
          (checkpoint ();
           case item of
               Bound i =>
                 if i >= level then Bound (i + increment) else item
             | Abs (name, body) => Abs (name, inc (level + 1) body)
             | f $ x => inc level f $ inc level x
             | _ => item)
      in
        inc 0 term
      end

  fun loose_bnos_measured checkpoint term =
    let
      fun member _ [] = false
        | member value (item :: items) =
            (checkpoint ();
             value = item orelse member value items)
      fun add (item, level, values) =
        (checkpoint ();
         case item of
             Bound i =>
               if i < level orelse member (i - level) values then values
               else i - level :: values
           | Abs (_, body) => add (body, level + 1, values)
           | f $ x => add (f, level, add (x, level, values))
           | _ => values)
    in
      add (term, 0, [])
    end

  fun subst_bound_measured checkpoint (arg, term) =
    let
      fun subst (item, level) =
        (checkpoint ();
         case item of
             Bound i =>
               if i < level then item
               else if i = level then
                 incr_boundvars_measured checkpoint level arg
               else Bound (i - 1)
           | Abs (name, body) => Abs (name, subst (body, level + 1))
           | f $ x => subst (f, level) $ subst (x, level)
           | _ => item)
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

  fun normMeasured checkpoint term =
    let
      fun increment amount tm =
        let
          fun inc level item =
            (checkpoint ();
             case item of
                 Bound i =>
                   if i >= level then Bound (i + amount) else item
               | Abs (name, body) => Abs (name, inc (level + 1) body)
               | f $ x => inc level f $ inc level x
               | _ => item)
        in
          inc 0 tm
        end

      fun substitute (argument, tm) =
        let
          fun subst (item, level) =
            (checkpoint ();
             case item of
                 Bound i =>
                   if i < level then item
                   else if i = level then increment level argument
                   else Bound (i - 1)
               | Abs (name, body) =>
                   Abs (name, subst (body, level + 1))
               | f $ x => subst (f, level) $ subst (x, level)
               | _ => item)
        in
          subst (tm, 0)
        end

      fun normalize item =
        (checkpoint ();
         case item of
             Skolem (name, args) =>
               Skolem (name, vars_in_vars_measured checkpoint args)
           | Const (name, terms) =>
               let
                 fun map_terms [] = []
                   | map_terms (tm :: rest) =
                       (checkpoint (); normalize tm :: map_terms rest)
               in
                 Const (name, map_terms terms)
               end
           | Var v =>
               (case !v of NONE => item | SOME body => normalize body)
           | f $ x =>
               (case normalize f of
                    Abs (_, body) => normalize (substitute (x, body))
                  | nf => nf $ normalize x)
           | _ => item)
    in
      normalize term
    end

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

  fun varOccurMeasured checkpoint v =
    let
      fun occs _ [] = false
        | occs level (term :: terms) =
            (checkpoint ();
             occ level term orelse occs level terms)
      and occ level term =
        (checkpoint ();
         case term of
             Var w =>
               v = w orelse
               (case !w of
                    NONE => false
                  | SOME body => occ level body)
           | Skolem (_, args) => occ_vars level args
           | Bound i => level <= i
           | Abs (_, body) => occ (level + 1) body
           | f $ x => occ level x orelse occ level f
           | _ => false)
      and occ_vars _ [] = false
        | occ_vars level (variable :: variables) =
            (checkpoint ();
             occ level (Var variable) orelse occ_vars level variables)
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

  fun clearToMeasured checkpoint (state as State {ntrail, trail}) mark =
    let
      fun clear () =
        if !ntrail = mark then ()
        else
          (checkpoint ();
           case !trail of
               [] => raise Fail "blastTerm.clearToMeasured: invalid trail mark"
             | v :: vs =>
                 (v := NONE;
                  trail := vs;
                  ntrail := !ntrail - 1;
                  clear ()))
    in
      clear ()
      handle exn => (clearTo state mark; raise exn)
    end

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

  fun unifyMeasured checkpoint state (vars, left, right) =
    let
      val State {ntrail, trail} = state
      val mark = !ntrail

      fun increment amount tm =
        let
          fun inc level item =
            (checkpoint ();
             case item of
                 Bound i =>
                   if i >= level then Bound (i + amount) else item
               | Abs (name, body) => Abs (name, inc (level + 1) body)
               | f $ x => inc level f $ inc level x
               | _ => item)
        in
          inc 0 tm
        end

      fun substitute (argument, tm) =
        let
          fun subst (item, level) =
            (checkpoint ();
             case item of
                 Bound i =>
                   if i < level then item
                   else if i = level then increment level argument
                   else Bound (i - 1)
               | Abs (name, body) =>
                   Abs (name, subst (body, level + 1))
               | f $ x => subst (f, level) $ subst (x, level)
               | _ => item)
        in
          subst (tm, 0)
        end

      fun loose tm =
        let
          fun add (Bound i, level, values) =
                (checkpoint ();
                 if i < level then values
                 else insert (i - level) values)
            | add (Abs (_, body), level, values) =
                (checkpoint (); add (body, level + 1, values))
            | add (f $ x, level, values) =
                (checkpoint ();
                 add (f, level, add (x, level, values)))
            | add (_, _, values) = (checkpoint (); values)
          and insert value [] = [value]
            | insert value (item :: items) =
                (checkpoint ();
                 if value = item then item :: items
                 else item :: insert value items)
        in
          add (tm, 0, [])
        end

      fun contains_zero [] = false
        | contains_zero (i :: rest) =
            (checkpoint (); i = 0 orelse contains_zero rest)

      fun head item =
        (checkpoint ();
         case item of f $ _ => head f | _ => item)

      fun weak_aux item =
        (checkpoint ();
         case item of
             Var v =>
               (case !v of SOME body => weak body | NONE => item)
           | f $ x =>
               (case weak_aux f of
                    Abs (_, body) => weak (substitute (x, body))
                  | nf => nf $ x)
           | Abs (name, body) =>
               (case weak_aux body of
                    nb as (f $ x) =>
                      if contains_zero (loose f) orelse
                         not
                           (aconvMeasured checkpoint
                              (weak x, Bound 0))
                      then Abs (name, nb)
                      else weak (increment ~1 f)
                  | nb => Abs (name, nb))
           | _ => item)

      and weak item =
        (checkpoint ();
         case head item of
             Const _ => item
           | Skolem _ => item
           | Free _ => item
           | _ => weak_aux item)

      fun member_var _ [] = false
        | member_var v (w :: ws) =
            (checkpoint (); v = w orelse member_var v ws)

      fun occurs variable =
        let
          fun occs _ [] = false
            | occs level (item :: items) =
                (checkpoint ();
                 occ level item orelse occs level items)
          and occ level item =
            (checkpoint ();
             case item of
                 Var other =>
                   variable = other orelse
                   (case !other of
                        NONE => false
                      | SOME body => occ level body)
               | Skolem (_, args) =>
                   let
                     fun terms [] = []
                       | terms (v :: vs) =
                           (checkpoint (); Var v :: terms vs)
                   in
                     occs level (terms args)
                   end
               | Bound i => level <= i
               | Abs (_, body) => occ (level + 1) body
               | f $ x => occ level x orelse occ level f
               | _ => false)
        in
          occ 0
        end

      fun update (term as Var v, other) =
            (checkpoint ();
             if aconvMeasured checkpoint (term, other) then ()
             else if occurs v other then raise UNIFY
             else if member_var v vars then v := SOME other
             else if is_Var other andalso
                     member_var (dest_Var other) vars
             then dest_Var other := SOME term
             else
               (v := SOME other;
                trail := v :: !trail;
                ntrail := !ntrail + 1))
        | update _ = raise UNIFY

      fun unifyAux polled (t, u) =
        let
          val _ = if polled then checkpoint () else ()
        in
          case (weak t, weak u) of
              (nt as Var _, nu) => update (nt, nu)
            | (nu, nt as Var _) => update (nt, nu)
            | (Const (a, ats), Const (b, bts)) =>
                if a = b then unifysAux (ats, bts) else raise UNIFY
            | (Abs (_, t'), Abs (_, u')) => unifyAux true (t', u')
            | (f $ t', g $ u') =>
                (unifyAux true (f, g); unifyAux true (t', u'))
            | (nt, nu) =>
                if aconvMeasured checkpoint (nt, nu) then ()
                else raise UNIFY
        end

      and unifysAux ([], []) = ()
        | unifysAux (t :: ts, u :: us) =
            (checkpoint ();
             unifyAux true (t, u);
             unifysAux (ts, us))
        | unifysAux _ = raise UNIFY
    in
      ((unifyAux false (left, right); true)
       handle UNIFY => (clearToMeasured checkpoint state mark; false)
            | exn => (clearTo state mark; raise exn))
    end

end
