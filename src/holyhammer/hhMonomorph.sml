structure hhMonomorph :> hhMonomorph =
struct

  open HolKernel

  type term = Term.term
  type hol_type = Type.hol_type
  type subst = (hol_type, hol_type) Lib.subst

  val max_thm_instances = 10
  val max_schematic_occurrences = 20
  val privileged_facts = 10

  datatype fact_info =
      Ground of string * term
    | Ignored
    | Schematic of {
        nickname : string,
        theorem : term,
        tvars : hol_type list,
        schematics : (string * hol_type) list,
        initial_round : int,
        instances : (int * subst * term) list ref
      }

  fun insert cmp x [] = [x]
    | insert cmp x (y :: ys) =
        if cmp (x, y) = GREATER then y :: insert cmp x ys
        else x :: y :: ys

  fun sort cmp = List.foldl (fn (x, xs) => insert cmp x xs) []

  fun mem_type ty = List.exists (fn other => other = ty)

  fun insert_type ty tys =
    if mem_type ty tys then tys else sort Type.compare (ty :: tys)

  fun lookup name table =
    case List.find (fn (other, _) => other = name) table of
        SOME (_, value) => value
      | NONE => []

  fun has_name name table = List.exists (fn (other, _) => other = name) table

  fun update name value table =
    map (fn (other, old) => if other = name then (other, value)
                            else (other, old)) table

  fun all_consts tm =
    let
      fun walk current result =
        if is_const current then dest_const current :: result
        else if is_comb current then
          walk (rand current) (walk (rator current) result)
        else if is_abs current then
          walk (body current) (walk (bvar current) result)
        else result
    in
      walk tm []
    end

  fun schematic_consts tm =
    List.filter (Type.polymorphic o snd) (all_consts tm)

  fun all_ground_consts tm =
    List.filter (not o Type.polymorphic o snd) (all_consts tm)

  fun tvar_is_bound tvars ty = mem_type ty tvars

  fun groundable tvars schematics =
    let
      val schematic_tvars =
        List.foldl (fn ((_, ty), result) =>
          List.foldl (fn (tvar, vars) =>
            if tvar_is_bound vars tvar then vars else tvar :: vars)
            result (Type.type_vars ty)) [] schematics
    in
      List.all (tvar_is_bound schematic_tvars) tvars
    end

  fun classify rank (nickname, theorem) =
    let
      val tvars = Term.type_vars_in_term theorem
      val schematics = schematic_consts theorem
    in
      if null tvars then Ground (nickname, theorem)
      else if not (groundable tvars schematics) then Ignored
      else Schematic {
        nickname = nickname,
        theorem = theorem,
        tvars = tvars,
        schematics = schematics,
        initial_round = if rank < privileged_facts then 1 else 2,
        instances = ref []
      }
    end

  fun schema_names infos =
    let
      fun add (Schematic {schematics, ...}, names) =
            List.foldl (fn ((name, _), result) =>
              if has_name name result then result else (name, []) :: result)
              names schematics
        | add (_, names) = names
    in
      List.rev (List.foldl add [] infos)
    end

  fun add_ground (name, ty) table =
    if has_name name table then
      update name (insert_type ty (lookup name table)) table
    else table

  fun add_grounds tm table =
    List.foldl (fn (constant, result) => add_ground constant result)
      table (all_ground_consts tm)

  fun merge_grounds left right =
    map (fn (name, tys) =>
      (name, List.foldl (fn (ty, result) => insert_type ty result)
        tys (lookup name right))) left

  fun type_size ty = Type.type_size ty

  fun subst_pairs subst =
    sort (fn ({redex = left, ...}, {redex = right, ...}) =>
      Type.compare (left, right)) subst

  fun subst_compare (left, right) =
    let
      fun size subst =
        List.foldl (fn ({residue, ...}, total) => type_size residue + total)
          0 subst
      fun compare_pairs ([], []) = EQUAL
        | compare_pairs ([], _) = LESS
        | compare_pairs (_, []) = GREATER
        | compare_pairs ((lvar, lty) :: ls, (rvar, rty) :: rs) =
            (case Type.compare (lvar, rvar) of
                 EQUAL =>
                   (case Type.compare (lty, rty) of
                        EQUAL => compare_pairs (ls, rs)
                      | result => result)
               | result => result)
      val size_order = Int.compare (size left, size right)
    in
      if size_order = EQUAL then
        compare_pairs (map (fn {redex, residue} => (redex, residue))
          (subst_pairs left),
          map (fn {redex, residue} => (redex, residue)) (subst_pairs right))
      else size_order
    end

  fun complete tvars subst =
    List.all (fn tvar =>
      List.exists (fn {redex, ...} => redex = tvar) subst) tvars

  fun match ty ground subst =
    SOME (Type.match_type_in_context ty ground subst)
      handle HOL_ERR _ => NONE

  fun matching_grounds name ty subst known new =
    let
      fun try_one is_new ground =
        case match ty ground subst of
            SOME refined => [(is_new, refined)]
          | NONE => []
    in
      List.concat (map (try_one true) (lookup name new)) @
      List.concat (map (try_one false) (lookup name known))
    end

  fun substitutions tvars schematics known new require_new =
    let
      fun search [] subst used_new =
            if complete tvars subst andalso (not require_new orelse used_new)
            then [subst] else []
        | search ((name, ty) :: rest) subst used_new =
            let
              val matched = matching_grounds name ty subst known new
              val refined = List.concat (map (fn (is_new, subst') =>
                search rest subst' (used_new orelse is_new)) matched)
            in
              refined @ search rest subst used_new
            end
      fun same_subst left right = subst_compare (left, right) = EQUAL
      fun unique [] result = List.rev result
        | unique (subst :: rest) result =
            if List.exists (fn old => same_subst subst old) result then
              unique rest result
            else unique rest (subst :: result)
    in
      unique (sort subst_compare (search schematics [] false)) []
    end

  fun unique_terms candidates old =
    let
      fun seen tm = List.exists (fn (_, _, prior) => aconv tm prior) old
      fun loop [] _ result = List.rev result
        | loop ((round, subst, tm) :: rest) seen_now result =
            if seen tm orelse
               List.exists (fn (_, _, prior) => aconv tm prior) seen_now then
              loop rest seen_now result
            else loop rest ((round, subst, tm) :: seen_now)
              ((round, subst, tm) :: result)
    in
      loop candidates [] []
    end

  fun take 0 _ = []
    | take _ [] = []
    | take count (item :: items) = item :: take (count - 1) items

  fun grounds_from_instances instances table =
    List.foldl (fn ((_, _, theorem), result) => add_grounds theorem result)
      table instances

  fun process_fact round known new remaining fact next_new =
    case fact of
        Schematic {theorem, tvars, schematics, initial_round, instances, ...} =>
          if round < initial_round orelse !remaining <= 0 orelse
             length schematics > max_schematic_occurrences then next_new
          else
            let
              val (old, fresh, require_new) =
                if round = initial_round then ([], merge_grounds known new, false)
                else (known, new, true)
              val candidates = map (fn subst =>
                (round, subst, Term.inst subst theorem))
                (substitutions tvars schematics old fresh require_new)
              val candidates = unique_terms candidates (!instances)
              val room = Int.min (max_thm_instances - length (!instances),
                !remaining)
              val selected = if room <= 0 then [] else take room candidates
              val _ = instances := !instances @ selected
              val _ = remaining := !remaining - length selected
            in
              grounds_from_instances selected next_new
            end
      | _ => next_new

  fun result_of (Ground (nickname, theorem)) = [(nickname, theorem)]
    | result_of Ignored = []
    | result_of (Schematic {nickname, instances, ...}) =
        map (fn (_, _, theorem) => (nickname, theorem)) (!instances)

  fun monomorph {max_iters, max_new_instances} goal premises =
    let
      val infos = ListPair.mapEq (fn (rank, premise) =>
        classify rank premise)
        (List.tabulate (length premises, fn index => index), premises)
      val names = schema_names infos
      val initial = add_grounds goal
        (List.foldl (fn (Ground (_, theorem), result) =>
                       add_grounds theorem result
                      | (_, result) => result) names infos)
      val remaining = ref (Int.max (0, max_new_instances))

      fun rounds round known new =
        if round > Int.max (0, max_iters) orelse !remaining <= 0 then ()
        else
          let
            val next = List.foldl
              (fn (fact, result) =>
                process_fact round known new remaining fact result) names infos
          in
            rounds (round + 1) (merge_grounds known new) next
          end

      val _ = rounds 1 names initial
    in
      List.concat (map result_of infos)
    end

  val monomorphize = monomorph

end
