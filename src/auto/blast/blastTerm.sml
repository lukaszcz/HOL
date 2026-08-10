structure blastTerm :> blastTerm =
struct

  datatype term =
      Const of KernelSig.kernelname * term list
    | Skolem of string * term option ref list
    | Fvar of string
    | Goal
    | False
    | Var of term option ref
    | Bound of int
    | Abs of string * term
    | $ of term * term

  infix 9 $

  type var = term option ref

  fun mapMeasured checkpoint f [] = []
    | mapMeasured checkpoint f (item :: items) =
        (checkpoint (); f item :: mapMeasured checkpoint f items)

  fun appMeasured checkpoint f [] = ()
    | appMeasured checkpoint f (item :: items) =
        (checkpoint (); f item; appMeasured checkpoint f items)

  fun existsMeasured checkpoint pred [] = false
    | existsMeasured checkpoint pred (item :: items) =
        (checkpoint ();
         pred item orelse existsMeasured checkpoint pred items)

  fun findMeasured checkpoint pred [] = NONE
    | findMeasured checkpoint pred (item :: items) =
        (checkpoint ();
         if pred item then SOME item else findMeasured checkpoint pred items)

  fun appendMeasured checkpoint [] right = right
    | appendMeasured checkpoint (item :: items) right =
        (checkpoint (); item :: appendMeasured checkpoint items right)

  fun partitionMeasured checkpoint pred [] = ([], [])
    | partitionMeasured checkpoint pred (item :: items) =
        let
          val _ = checkpoint ()
          val (yes, no) = partitionMeasured checkpoint pred items
        in
          if pred item then (item :: yes, no) else (yes, item :: no)
        end

  fun mapPartialMeasured checkpoint f [] = []
    | mapPartialMeasured checkpoint f (item :: items) =
        let
          val _ = checkpoint ()
          val result = f item
          val rest = mapPartialMeasured checkpoint f items
        in
          case result of NONE => rest | SOME value => value :: rest
        end

  datatype state = State of
    {trail : var list ref,
     ntrail : int ref}

  fun mkGoal p = Goal $ p

  fun isGoal (Goal $ _) = true
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
    | aconv (Fvar a, Fvar b) = a = b
    | aconv (Goal, Goal) = true
    | aconv (False, False) = true
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
           | (Fvar a, Fvar b) => a = b
           | (Goal, Goal) => true
           | (False, False) => true
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
      and add_var (v, values) =
        let
          fun member [] = false
            | member (w :: ws) =
                (checkpoint ();
                 v = w orelse member ws)
        in
          if member values then values else v :: values
        end
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
      val substitute = subst_bound_measured checkpoint

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
      | Fvar _ => term
      | Goal => term
      | False => term
      | _ => wkNormAux term

  fun wkNormMeasured checkpoint term =
    let
      val increment = incr_boundvars_measured checkpoint
      val substitute = subst_bound_measured checkpoint

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
                      if existsMeasured checkpoint (fn i => i = 0)
                           (loose_bnos_measured checkpoint f) orelse
                         not (aconvMeasured checkpoint (weak x, Bound 0))
                      then Abs (name, nb)
                      else weak (increment ~1 f)
                  | nb => Abs (name, nb))
           | _ => item)

      and weak item =
        (checkpoint ();
         case head item of
             Const _ => item
           | Skolem _ => item
           | Fvar _ => item
           | Goal => item
           | False => item
           | _ => weak_aux item)
    in
      weak term
    end

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

  (* The Skolem case polls once per dependency argument, in occ_vars. *)
  fun varOccurMeasured checkpoint v =
    let
      fun occ level term =
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

  fun noHook () = ()

  (* [poll] runs before each trail item is inspected, [note] after its
     assignment has been restored. *)
  fun clearTrail (poll, note, message) (State {ntrail, trail}) mark =
    while !ntrail <> mark do
      (poll ();
       case !trail of
           [] => raise Fail message
         | v :: vs =>
             (v := NONE;
              trail := vs;
              ntrail := !ntrail - 1;
              note ()))

  fun clearTo state mark =
    clearTrail (noHook, noHook, "blastTerm.clearTo: invalid trail mark")
      state mark

  fun clearToWith note state mark =
    clearTrail (noHook, note, "blastTerm.clearToWith: invalid trail mark")
      state mark

  fun clearToMeasuredWith cleanup checkpoint state mark =
    (clearTrail
       (checkpoint, noHook,
        "blastTerm.clearToMeasured: invalid trail mark")
       state mark
     handle exn => (cleanup exn state mark; raise exn))

  fun clearToMeasured checkpoint state mark =
    clearToMeasuredWith
      (fn _ => fn cleanup_state => fn cleanup_mark =>
         clearTo cleanup_state cleanup_mark)
      checkpoint state mark

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

  fun unifyMeasuredWith cleanup checkpoint state (vars, left, right) =
    let
      val State {ntrail, trail} = state
      val mark = !ntrail

      val weak = wkNormMeasured checkpoint

      fun member_var value =
        existsMeasured checkpoint (fn other => value = other)

      val occurs = varOccurMeasured checkpoint

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
       handle UNIFY =>
                (clearToMeasuredWith cleanup checkpoint state mark; false)
            | exn => (cleanup exn state mark; raise exn))
    end

end
