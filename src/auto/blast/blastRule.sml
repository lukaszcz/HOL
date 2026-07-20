structure blastRule :> blastRule =
struct

open HolKernel boolSyntax blastTerm

infix 9 $
infix |->

type hol_term = Term.term
type thm = Thm.thm
type goal = Abbrev.goal
type pterm = blastTerm.term
type var = blastTerm.var

datatype origin =
    Stored of {is_elim : bool, theorem : thm}
  | ImpIntro
  | AllIntro

type tableau_rule =
  {origin : origin,
   pattern : pterm,
   premises : pterm list list}

type monitor =
  {candidate : unit -> unit,
   conversion : unit -> unit,
   checkpoint : unit -> unit}

type entry =
  {formula : pterm,
   safe : bool,
   vars : var list,
   rules : tableau_rule list}

fun containsZeroMeasured checkpoint [] = false
  | containsZeroMeasured checkpoint (i :: rest) =
      (checkpoint ();
       i = 0 orelse containsZeroMeasured checkpoint rest)

datatype cache = Cache of
  {entries : entry list ref,
   conversions : int ref,
   hits : int ref}

fun newCache () =
  Cache {entries = ref [], conversions = ref 0, hits = ref 0}

fun conversionCount (Cache {conversions, ...}) = !conversions
fun hitCount (Cache {hits, ...}) = !hits

(* Skolem identity is name identity in blastTerm.  A session-global supply
   therefore prevents separate node caches from accidentally sharing one. *)
val skolem_names = ref 0

fun freshName _ prefix =
  (skolem_names := !skolem_names + 1;
   prefix ^ Int.toString (!skolem_names))

val blast_trace = ref 0
val _ = Feedback.register_trace ("blast", blast_trace, 7)

(* [const_name] is the identity stored in blast terms and decoded by
   [query_skeleton], so it is also the stable cache key. *)
val generic_cache :
  (string, hol_type * hol_type list) Redblackmap.dict ref =
  ref (Redblackmap.mkDict String.compare)

fun split_name encoded =
  let
    val (left, right) =
      Substring.position "$" (Substring.full encoded)
  in
    if Substring.isEmpty right then NONE
    else
      SOME (Substring.string left,
            Substring.string (Substring.slice (right, 1, NONE)))
  end

fun generic_info {Thy, Name} =
  let
    val encoded = const_name {Thy = Thy, Name = Name}
  in
    case Redblackmap.peek (!generic_cache, encoded) of
        SOME info => info
      | NONE =>
          let
            val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
            val info = (generic, Type.type_vars generic)
          in
            generic_cache :=
              Redblackmap.insert (!generic_cache, encoded, info);
            info
          end
  end

fun encode_type rigid type_map ty =
  if Type.is_vartype ty then
    if rigid then Free (Type.dest_vartype ty)
    else
      (case Redblackmap.peek (!type_map, ty) of
           SOME value => value
         | NONE =>
             let
               val value = Var (ref NONE)
             in
               type_map := Redblackmap.insert (!type_map, ty, value);
               value
             end)
  else
    let
      val {Thy, Tyop, Args} = Type.dest_thy_type ty
      val head = Const (const_name {Thy = Thy, Name = Tyop}, [])
    in
      list_comb (head, map (encode_type rigid type_map) Args)
    end

fun const_tyargs rigid type_map hol_const =
  let
    val {Thy, Name, Ty} = dest_thy_const hol_const
    val (generic, generic_vars) = generic_info {Thy = Thy, Name = Name}
    val subst = Type.match_type generic Ty
  in
    map (encode_type rigid type_map o Type.type_subst subst)
      generic_vars
  end

fun member_term tm = List.exists (fn other => Term.aconv tm other)

fun member_term_measured checkpoint tm =
  let
    fun member [] = false
      | member (other :: rest) =
          (checkpoint ();
           Term.aconv tm other orelse member rest)
  in
    member
  end

fun translator {rigid_types, goal_frees, rule_vars} =
  let
    (* Type.compare is structural equality on HOL types.  Term.compare is a
       total ordering that respects alpha-equivalence, matching the former
       [=] and [Term.aconv] association-list lookups respectively. *)
    val term_map : (hol_term, pterm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Term.compare)
    val type_map : (hol_type, pterm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Type.compare)

    fun fresh_variable tm make =
      case Redblackmap.peek (!term_map, tm) of
          SOME value => value
        | NONE =>
            let
              val value = make ()
            in
              term_map := Redblackmap.insert (!term_map, tm, value);
              value
            end

    fun variable depth bounds tm =
      case Redblackmap.peek (bounds, tm) of
          SOME binder_depth => Bound (depth - binder_depth)
        | NONE =>
            if member_term tm rule_vars then
              fresh_variable tm (fn () => Var (ref NONE))
            else if goal_frees then
              fresh_variable tm
                (fn () => Skolem (freshName () "*Free*", []))
            else
              let val (name, _) = dest_var tm in Free name end

    fun from depth bounds tm =
      if is_const tm then
        let
          val {Thy, Name, ...} = dest_thy_const tm
          val args = const_tyargs rigid_types type_map tm
        in
          Const (const_name {Thy = Thy, Name = Name}, args)
        end
      else if is_var tm then variable depth bounds tm
      else if is_abs tm then
        let
          val (binder, body) = dest_abs tm
          val (name, _) = dest_var binder
          val body_depth = depth + 1
          (* Persistent maps restore an outer binding when recursion returns.
             Storing absolute depth avoids rebuilding every outer binding. *)
          val body_bounds =
            Redblackmap.insert (bounds, binder, body_depth)
          val body' = from body_depth body_bounds body
        in
          case body' of
              f $ Bound 0 =>
                if List.exists (fn i => i = 0) (loose_bnos f) then
                  Abs (name, body')
                else incr_boundvars ~1 f
            | _ => Abs (name, body')
        end
      else
        let val (rator, rand) = dest_comb tm
        in from depth bounds rator $ from depth bounds rand end
  in
    fn hol_term =>
      from 0 (Redblackmap.mkDict Term.compare) hol_term
  end

(* A separate translator keeps ordinary rule conversion callback-free.  Each
   recursive HOL/type item is separated by a checkpoint; calls into the HOL
   kernel and persistent maps remain the indivisible units. *)
fun translatorMeasured checkpoint
      {rigid_types, goal_frees, rule_vars} =
  let
    val term_map : (hol_term, pterm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Term.compare)
    val type_map : (hol_type, pterm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Type.compare)

    fun member _ [] = false
      | member tm (other :: rest) =
          (checkpoint ();
           Term.aconv tm other orelse member tm rest)

    fun encode_type ty =
      let
        val _ = checkpoint ()
      in
        if Type.is_vartype ty then
          if rigid_types then Free (Type.dest_vartype ty)
          else
            (case Redblackmap.peek (!type_map, ty) of
                 SOME value => value
               | NONE =>
                   let val value = Var (ref NONE)
                   in
                     type_map :=
                       Redblackmap.insert (!type_map, ty, value);
                     value
                   end)
        else
          let
            val {Thy, Tyop, Args} = Type.dest_thy_type ty
            val head = Const (const_name {Thy = Thy, Name = Tyop}, [])
            fun encode [] = []
              | encode (arg :: args) =
                  (checkpoint (); encode_type arg :: encode args)
          in
            list_comb (head, encode Args)
          end
      end

    fun generic {Thy, Name} =
      let
        val encoded = const_name {Thy = Thy, Name = Name}
        val _ = checkpoint ()
      in
        case Redblackmap.peek (!generic_cache, encoded) of
            SOME info => info
          | NONE =>
              let
                val _ = checkpoint ()
                val generic =
                  type_of (prim_mk_const {Thy = Thy, Name = Name})
                val _ = checkpoint ()
                val info = (generic, Type.type_vars generic)
              in
                generic_cache :=
                  Redblackmap.insert (!generic_cache, encoded, info);
                info
              end
      end

    fun const_args hol_const =
      let
        val _ = checkpoint ()
        val {Thy, Name, Ty} = dest_thy_const hol_const
        val (generic_type, generic_vars) = generic {Thy = Thy, Name = Name}
        val _ = checkpoint ()
        val subst = Type.match_type generic_type Ty
        fun encode [] = []
          | encode (variable :: variables) =
              let
                val _ = checkpoint ()
                val instantiated = Type.type_subst subst variable
              in
                encode_type instantiated :: encode variables
              end
      in
        encode generic_vars
      end

    fun fresh_variable tm make =
      (checkpoint ();
       case Redblackmap.peek (!term_map, tm) of
           SOME value => value
         | NONE =>
             let val value = make ()
             in
               term_map := Redblackmap.insert (!term_map, tm, value);
               value
             end)

    fun variable depth bounds tm =
      (checkpoint ();
       case Redblackmap.peek (bounds, tm) of
           SOME binder_depth => Bound (depth - binder_depth)
         | NONE =>
             if member tm rule_vars then
               fresh_variable tm (fn () => Var (ref NONE))
             else if goal_frees then
               fresh_variable tm
                 (fn () => Skolem (freshName () "*Free*", []))
             else
               let val (name, _) = dest_var tm in Free name end)

    fun from depth bounds tm =
      let
        val _ = checkpoint ()
      in
        if is_const tm then
          let
            val {Thy, Name, ...} = dest_thy_const tm
            val args = const_args tm
          in
            Const (const_name {Thy = Thy, Name = Name}, args)
          end
        else if is_var tm then variable depth bounds tm
        else if is_abs tm then
          let
            val (binder, body) = dest_abs tm
            val (name, _) = dest_var binder
            val body_depth = depth + 1
            val body_bounds =
              Redblackmap.insert (bounds, binder, body_depth)
            val body' = from body_depth body_bounds body
          in
            case body' of
                f $ Bound 0 =>
                  (checkpoint ();
                   if containsZeroMeasured checkpoint
                        (loose_bnos_measured checkpoint f) then
                     Abs (name, body')
                   else incr_boundvars_measured checkpoint ~1 f)
              | _ => Abs (name, body')
          end
        else
          let
            val (rator, argument) = dest_comb tm
            val rator' = from depth bounds rator
            val argument' = from depth bounds argument
          in
            rator' $ argument'
          end
      end
  in
    fn hol_term =>
      from 0 (Redblackmap.mkDict Term.compare) hol_term
  end

fun fromGoalTerm tm =
  translator
    {rigid_types = true, goal_frees = true, rule_vars = []} tm

fun initialBranch (assumptions, conclusion) =
  let
    val from =
      translator
        {rigid_types = true, goal_frees = true, rule_vars = []}
  in
    map (fn formula => (formula, true))
      (mkGoal (from conclusion) :: map from assumptions)
  end

fun initialBranchMeasured checkpoint (assumptions, conclusion) =
  let
    val from =
      translatorMeasured checkpoint
        {rigid_types = true, goal_frees = true, rule_vars = []}
    fun translate [] = []
      | translate (formula :: formulas) =
          (checkpoint (); (from formula, true) :: translate formulas)
    val _ = checkpoint ()
    val conclusion' = from conclusion
  in
    (mkGoal conclusion', true) :: translate assumptions
  end

fun proto_imp term =
  case strip_comb term of
      (Const (name, _), [left, right]) =>
        if name = const_name {Thy = "min", Name = "==>"}
        then SOME (left, right)
        else NONE
    | _ => NONE

fun strip_imp term =
  case proto_imp term of
      SOME (premise, rest) =>
        let val (premises, conclusion) = strip_imp rest
        in (premise :: premises, conclusion) end
    | NONE => ([], term)

fun dest_forall_body term =
  case strip_comb term of
      (Const (name, _), [predicate]) =>
        if name = const_name {Thy = "bool", Name = "!"}
        then SOME predicate
        else NONE
    | _ => NONE

fun apply_predicate predicate argument =
  case predicate of
      Abs (_, body) => subst_bound (argument, body)
    | _ => predicate $ argument

fun apply_predicate_measured checkpoint predicate argument =
  (checkpoint ();
   case predicate of
       Abs (_, body) => subst_bound_measured checkpoint (argument, body)
     | _ => predicate $ argument)

fun skoPrem cache vars term =
  case dest_forall_body term of
      SOME predicate =>
        skoPrem cache vars
          (apply_predicate predicate
             (Skolem (freshName cache "S", vars)))
    | NONE => term

fun convertPrem term =
  let val (hypotheses, conclusion) = strip_imp term
  in mkGoal conclusion :: hypotheses end

fun skoPremMeasured checkpoint cache vars term =
  (checkpoint ();
   case dest_forall_body term of
       SOME predicate =>
         let
           val skolem = Skolem (freshName cache "S", vars)
           val _ = checkpoint ()
           val body = apply_predicate_measured checkpoint predicate skolem
         in
           skoPremMeasured checkpoint cache vars body
         end
     | NONE => term)

fun convertPremMeasured checkpoint term =
  let
    fun strip formula =
      (checkpoint ();
       case proto_imp formula of
           SOME (premise, rest) =>
             let val (hypotheses, conclusion) = strip rest
             in (premise :: hypotheses, conclusion) end
         | NONE => ([], formula))
    val (hypotheses, conclusion) = strip term
  in
    mkGoal conclusion :: hypotheses
  end

exception ElimBadConcl
exception ElimBadPrem

fun is_false_var term =
  case term of
      Var v =>
        (case !v of
             SOME (Const (name, _)) => name = false_name
           | _ => false)
    | _ => false

fun delete_concl [] = raise ElimBadPrem
  | delete_concl (formula :: formulas) =
      (case formula of
           Const (name, _) $ value =>
             if (name = goal_name orelse
                 name = const_name {Thy = "bool", Name = "~"}) andalso
                is_false_var value
             then formulas
             else formula :: delete_concl formulas
         | _ => formula :: delete_concl formulas)

fun canonical_data is_elim theorem =
  let
    val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
    val form = clasetRules.canonical_form_of kind theorem
    val (outer, _) = strip_forall (concl (#thm form))
    val from =
      translator
        {rigid_types = false, goal_frees = false, rule_vars = outer}
  in
    {outer = outer, hol_conclusion = #concl form,
     premises = map from (#prems form), conclusion = from (#concl form)}
  end

fun canonical_dataMeasured checkpoint is_elim theorem =
  let
    val kind = if is_elim then clasetRules.Elim else clasetRules.Intro
    val form =
      clasetRules.canonical_form_of_measured checkpoint kind theorem
    fun outer_vars tm =
      (checkpoint ();
       case total dest_forall tm of
           NONE => []
         | SOME (variable, body) => variable :: outer_vars body)
    val outer = outer_vars (concl (#thm form))
    val from =
      translatorMeasured checkpoint
        {rigid_types = false, goal_frees = false, rule_vars = outer}
    fun translate [] = []
      | translate (premise :: premises) =
          (checkpoint (); from premise :: translate premises)
    val premises = translate (#prems form)
    val _ = checkpoint ()
    val conclusion = from (#concl form)
  in
    {outer = outer, hol_conclusion = #concl form,
     premises = premises, conclusion = conclusion}
  end

fun countConversion (Cache {conversions, ...}) =
  conversions := !conversions + 1

fun convertIntro cache vars theorem =
  let
    val _ = countConversion cache
    val {premises, conclusion, ...} = canonical_data false theorem
    fun one premise = convertPrem (skoPrem cache vars premise)
  in
    {origin = Stored {is_elim = false, theorem = theorem},
     pattern = mkGoal conclusion,
     premises = map one premises}
  end

fun convertIntroMeasured checkpoint cache vars theorem =
  let
    val _ = countConversion cache
    val {premises, conclusion, ...} =
      canonical_dataMeasured checkpoint false theorem
    fun convert [] = []
      | convert (premise :: rest) =
          let
            val _ = checkpoint ()
            val skolemized = skoPremMeasured checkpoint cache vars premise
            val converted = convertPremMeasured checkpoint skolemized
          in
            converted :: convert rest
          end
  in
    {origin = Stored {is_elim = false, theorem = theorem},
     pattern = mkGoal conclusion,
     premises = convert premises}
  end

fun weak_warning theorem =
  if Feedback.current_trace "blast" >= 1 then
    HOL_WARNING "blastRule" "convertElim"
      ("Ignoring weak elimination rule\n" ^ Parse.thm_to_string theorem)
  else ()

fun bad_conclusion_message theorem =
  "Ignoring ill-formed elimination rule:\n" ^
  "conclusion should be a variable\n" ^ Parse.thm_to_string theorem

fun convertElim cache vars theorem =
  let
    val _ = countConversion cache
    val data = canonical_data true theorem
    val outer = #outer data
    val hol_conclusion = #hol_conclusion data
    val premises = #premises data
    val conclusion = #conclusion data
    val formula_variable =
      is_var hol_conclusion andalso
      type_of hol_conclusion = bool andalso
      member_term hol_conclusion outer
    val _ = if formula_variable then () else raise ElimBadConcl
    val false_var =
      case conclusion of
          Var variable => variable
        | _ => raise ElimBadConcl
    val (major, minors) =
      case premises of
          premise :: rest => (premise, rest)
        | [] => raise ElimBadConcl
    val _ = false_var := SOME (Const (false_name, []))
    fun one premise =
      delete_concl (convertPrem (skoPrem cache vars premise))
  in
    SOME
      {origin = Stored {is_elim = true, theorem = theorem},
       pattern = major,
       premises = map one minors}
  end
  handle ElimBadPrem => (weak_warning theorem; NONE)
       | ElimBadConcl =>
           (if Feedback.current_trace "blast" >= 1 then
              Feedback.HOL_MESG (bad_conclusion_message theorem)
            else ();
            NONE)

fun delete_concl_measured checkpoint [] =
      (checkpoint (); raise ElimBadPrem)
  | delete_concl_measured checkpoint (formula :: formulas) =
      (checkpoint ();
       case formula of
           Const (name, _) $ value =>
             if (name = goal_name orelse
                 name = const_name {Thy = "bool", Name = "~"}) andalso
                is_false_var value
             then formulas
             else formula :: delete_concl_measured checkpoint formulas
         | _ => formula :: delete_concl_measured checkpoint formulas)

fun convertElimMeasured checkpoint cache vars theorem =
  let
    val _ = countConversion cache
    val data = canonical_dataMeasured checkpoint true theorem
    val outer = #outer data
    val hol_conclusion = #hol_conclusion data
    val premises = #premises data
    val conclusion = #conclusion data
    val _ = checkpoint ()
    val formula_variable =
      is_var hol_conclusion andalso
      type_of hol_conclusion = bool andalso
      member_term_measured checkpoint hol_conclusion outer
    val _ = if formula_variable then () else raise ElimBadConcl
    val false_var =
      case conclusion of
          Var variable => variable
        | _ => raise ElimBadConcl
    val (major, minors) =
      case premises of
          premise :: rest => (premise, rest)
        | [] => raise ElimBadConcl
    val _ = false_var := SOME (Const (false_name, []))
    fun convert [] = []
      | convert (premise :: rest) =
          let
            val _ = checkpoint ()
            val skolemized = skoPremMeasured checkpoint cache vars premise
            val converted = convertPremMeasured checkpoint skolemized
            val minor = delete_concl_measured checkpoint converted
          in
            minor :: convert rest
          end
  in
    SOME
      {origin = Stored {is_elim = true, theorem = theorem},
       pattern = major,
       premises = convert minors}
  end
  handle ElimBadPrem => (weak_warning theorem; NONE)
       | ElimBadConcl =>
           (if Feedback.current_trace "blast" >= 1 then
              Feedback.HOL_MESG (bad_conclusion_message theorem)
            else ();
            NONE)

fun same_vars ([], []) = true
  | same_vars (left :: lefts, right :: rights) =
      left = right andalso same_vars (lefts, rights)
  | same_vars _ = false

fun cached (Cache {entries, hits, ...}) safe vars formula =
  case List.find
         (fn entry =>
            #safe entry = safe andalso
            same_vars (#vars entry, vars) andalso
            aconv (#formula entry, formula))
         (!entries) of
      NONE => NONE
    | SOME entry =>
        (hits := !hits + 1;
         SOME (#rules entry))

fun cachedMeasured checkpoint (Cache {entries, hits, ...})
      safe vars formula =
  let
    fun same ([], []) = true
      | same (left :: lefts, right :: rights) =
          (checkpoint ();
           left = right andalso same (lefts, rights))
      | same _ = false
    fun find [] = NONE
      | find (entry :: rest) =
          (checkpoint ();
           if #safe entry = safe andalso
              same (#vars entry, vars) andalso
              aconvMeasured checkpoint (#formula entry, formula)
           then SOME entry
           else find rest)
  in
    case find (!entries) of
        NONE => NONE
      | SOME entry =>
          (hits := !hits + 1;
           SOME (#rules entry))
  end

fun remember (Cache {entries, ...}) safe vars formula rules =
  entries :=
    {formula = formula, safe = safe, vars = vars, rules = rules} ::
    !entries

(* Rule variables are assigned destructively and off-trail by unify.  Keep
   pristine templates in a search cache, and give every acquisition fresh
   rule variables and fresh rule-local Skolems.  Variables and Skolems from
   the branch formula remain shared with the branch. *)
fun copyRules cache vars formula fresh_skolems rules =
  let
    val variable_copies = ref ([] : (var * var) list)
    val skolem_copies = ref ([] : (string * string) list)

    fun insert_string value values =
      if List.exists (fn other => other = value) values then values
      else value :: values

    fun add_skolems (Const (_, args)) names =
          List.foldl (fn (term, result) => add_skolems term result)
            names args
      | add_skolems (Skolem (name, arguments)) names =
          List.foldl
            (fn (variable, result) =>
               case !variable of
                   NONE => result
                 | SOME term => add_skolems term result)
            (insert_string name names) arguments
      | add_skolems (Var variable) names =
          (case !variable of
               NONE => names
             | SOME term => add_skolems term names)
      | add_skolems (Abs (_, body)) names = add_skolems body names
      | add_skolems (left $ right) names =
          add_skolems left (add_skolems right names)
      | add_skolems _ names = names

    val external_skolems =
      List.foldl
        (fn (variable, names) =>
           case !variable of
               NONE => names
             | SOME term => add_skolems term names)
        (add_skolems formula []) vars

    fun copy_variable variable =
      if mem_var (variable, vars) then variable
      else
        case List.find
               (fn (source, _) => source = variable) (!variable_copies) of
            SOME (_, copy) => copy
          | NONE =>
              let
                val copy = ref NONE
                val _ =
                  variable_copies :=
                    (variable, copy) :: !variable_copies
                val _ =
                  case !variable of
                      NONE => ()
                    | SOME term => copy := SOME (copy_term term)
              in
                copy
              end

    and copy_skolem name =
      if not fresh_skolems orelse
         List.exists (fn external => external = name) external_skolems
      then name
      else
        case List.find
               (fn (source, _) => source = name) (!skolem_copies) of
            SOME (_, copy) => copy
          | NONE =>
              let
                val copy = freshName cache "S"
              in
                skolem_copies := (name, copy) :: !skolem_copies;
                copy
              end

    and copy_term term =
      case term of
          Const (name, args) => Const (name, map copy_term args)
        | Skolem (name, arguments) =>
            Skolem (copy_skolem name, map copy_variable arguments)
        | Free name => Free name
        | Var variable => Var (copy_variable variable)
        | Bound index => Bound index
        | Abs (name, body) => Abs (name, copy_term body)
        | left $ right => copy_term left $ copy_term right

    fun copy_rule ({origin, pattern, premises} : tableau_rule) =
      {origin = origin,
       pattern = copy_term pattern,
       premises = map (map copy_term) premises}
  in
    map copy_rule rules
  end

fun query_skeleton formula =
  let
    val goal = isGoal formula
    val body = if goal then rand formula else formula
    val depth = if goal then 2 else 3
    val decoded = ref []

    fun decode term =
      case term of
          Free name => Type.mk_vartype name
        | Var variable =>
            (case !variable of
                 SOME value => decode value
               | NONE =>
                   (case List.find
                            (fn (key, _) => key = variable) (!decoded) of
                        SOME (_, ty) => ty
                      | NONE =>
                          let val ty = Type.gen_tyvar ()
                          in
                            decoded := (variable, ty) :: !decoded;
                            ty
                          end))
        | _ =>
            let
              val (head, args) = strip_comb term
            in
              case head of
                  Const (encoded, []) =>
                    (case split_name encoded of
                         SOME (thy, tyop) =>
                           Type.mk_thy_type
                             {Thy = thy, Tyop = tyop,
                              Args = map decode args}
                       | NONE => raise Fail "bad type encoding")
                | _ => raise Fail "bad type encoding"
            end

    fun constant (name, proto_args) =
      case split_name name of
          NONE => raise Fail "pseudo-constant in net query"
        | SOME (Thy, Name) =>
            let
              val (generic, generic_vars) =
                generic_info {Thy = Thy, Name = Name}
              val _ =
                if length generic_vars = length proto_args then ()
                else raise Fail "bad constant type arguments"
              val subst =
                ListPair.map (fn (variable, arg) => variable |-> decode arg)
                  (generic_vars, proto_args)
            in
              mk_thy_const
                {Thy = Thy, Name = Name,
                 Ty = Type.type_subst subst generic}
            end

    fun build expected 0 _ = genvar expected
      | build expected level term =
          (case strip_comb term of
               (Const (name, proto_args), actual_args) =>
                 let
                   fun apply (head, []) = head
                     | apply (head, arg :: args) =
                         let
                           val (domain, _) = Type.dom_rng (type_of head)
                           val arg' = build domain (level - 1) arg
                         in
                           apply (mk_comb (head, arg'), args)
                         end
                   val result =
                     apply (constant (name, proto_args), actual_args)
                 in
                   if type_of result = expected then result
                   else genvar expected
                 end
             | _ => genvar expected)
          handle HOL_ERR _ => genvar expected
               | Fail _ => genvar expected
  in
    build bool depth body
  end

fun query_skeleton_measured checkpoint formula =
  let
    val goal = isGoal formula
    val body = if goal then rand formula else formula
    val depth = if goal then 2 else 3
    val decoded = ref []

    fun strip term =
      let
        fun collect (left $ right, args) =
              (checkpoint (); collect (left, right :: args))
          | collect result = (checkpoint (); result)
      in
        collect (term, [])
      end

    fun find_decoded _ [] = NONE
      | find_decoded variable ((key, ty) :: rest) =
          (checkpoint ();
           if key = variable then SOME ty
           else find_decoded variable rest)

    fun decode term =
      (checkpoint ();
       case term of
           Free name => Type.mk_vartype name
         | Var variable =>
             (case !variable of
                  SOME value => decode value
                | NONE =>
                    (case find_decoded variable (!decoded) of
                         SOME ty => ty
                       | NONE =>
                           let val ty = Type.gen_tyvar ()
                           in
                             decoded := (variable, ty) :: !decoded;
                             ty
                           end))
         | _ =>
             let
               val (head, args) = strip term
               fun decode_args [] = []
                 | decode_args (arg :: rest) =
                     (checkpoint (); decode arg :: decode_args rest)
             in
               case head of
                   Const (encoded, []) =>
                     (case split_name encoded of
                          SOME (thy, tyop) =>
                            Type.mk_thy_type
                              {Thy = thy, Tyop = tyop,
                               Args = decode_args args}
                        | NONE => raise Fail "bad type encoding")
                 | _ => raise Fail "bad type encoding"
             end)

    fun constant (name, proto_args) =
      (checkpoint ();
       case split_name name of
           NONE => raise Fail "pseudo-constant in net query"
         | SOME (Thy, Name) =>
             let
               val (generic, generic_vars) =
                 generic_info {Thy = Thy, Name = Name}
               fun substitutions ([], []) = []
                 | substitutions (variable :: variables, arg :: args) =
                     (checkpoint ();
                      (variable |-> decode arg) ::
                        substitutions (variables, args))
                 | substitutions _ = raise Fail "bad constant type arguments"
               val subst = substitutions (generic_vars, proto_args)
               val _ = checkpoint ()
             in
               mk_thy_const
                 {Thy = Thy, Name = Name,
                  Ty = Type.type_subst subst generic}
             end)

    fun build expected 0 _ = (checkpoint (); genvar expected)
      | build expected level term =
          (checkpoint ();
           (case strip term of
                (Const (name, proto_args), actual_args) =>
                  let
                    fun apply (head, []) = head
                      | apply (head, arg :: args) =
                          let
                            val _ = checkpoint ()
                            val (domain, _) = Type.dom_rng (type_of head)
                            val arg' = build domain (level - 1) arg
                            val _ = checkpoint ()
                          in
                            apply (mk_comb (head, arg'), args)
                          end
                    val result =
                      apply (constant (name, proto_args), actual_args)
                    val _ = checkpoint ()
                  in
                    if type_of result = expected then result
                    else genvar expected
                  end
              | _ => genvar expected)
           handle HOL_ERR _ => genvar expected
                | Fail _ => genvar expected)
  in
    build bool depth body
  end

fun pseudoRules cache vars formula =
  if not (isGoal formula) then []
  else
    let
      val body = rand formula
    in
      case proto_imp body of
          SOME (premise, conclusion) =>
            [{origin = ImpIntro, pattern = formula,
              premises = [[mkGoal conclusion, premise]]}]
        | NONE =>
            (case dest_forall_body body of
                 SOME predicate =>
                   let
                     val skolem = Skolem (freshName cache "S", vars)
                   in
                     [{origin = AllIntro, pattern = formula,
                       premises = [[mkGoal
                         (apply_predicate predicate skolem)]]}]
                   end
               | NONE => [])
    end

fun pseudoRulesMeasured checkpoint cache vars formula =
  if not (isGoal formula) then []
  else
    let
      val _ = checkpoint ()
      val body = rand formula
    in
      case proto_imp body of
          SOME (premise, conclusion) =>
            [{origin = ImpIntro, pattern = formula,
              premises = [[mkGoal conclusion, premise]]}]
        | NONE =>
            (checkpoint ();
             case dest_forall_body body of
                 SOME predicate =>
                   let
                     val skolem = Skolem (freshName cache "S", vars)
                     val _ = checkpoint ()
                     val applied =
                       apply_predicate_measured checkpoint predicate skolem
                   in
                     [{origin = AllIntro, pattern = formula,
                       premises = [[mkGoal applied]]}]
                   end
               | NONE => [])
    end

fun isVarForm (Var _) = true
  | isVarForm (Const (name, _) $ Var _) =
      name = const_name {Thy = "bool", Name = "~"}
  | isVarForm _ = false

fun candidates claset safe formula =
  if not (isGoal formula) andalso isVarForm formula then []
  else let
    val query = query_skeleton formula
    fun intros part = clasetLib.unify_intro_candidates part query
    fun elims part = clasetLib.unify_elim_candidates part query
    val tagged =
      if safe then
        if isGoal formula then
          intros (clasetLib.safe0_part claset) @
          intros (clasetLib.safep_part claset)
        else
          elims (clasetLib.safe0_part claset) @
          elims (clasetLib.safep_part claset)
      else if isGoal formula then
        intros (clasetLib.unsafe_part claset)
      else elims (clasetLib.unsafe_part claset)
  in
    clasetRules.candidate_order tagged
  end

fun candidatesMeasured ({checkpoint, ...} : monitor) claset safe formula =
  if not (isGoal formula) andalso isVarForm formula then []
  else
    let
      val query = query_skeleton_measured checkpoint formula
      fun intros part =
        clasetLib.unify_intro_candidates_measured checkpoint part query
      fun elims part =
        clasetLib.unify_elim_candidates_measured checkpoint part query
      fun append [] right = right
        | append (item :: items) right =
            (checkpoint (); item :: append items right)
      val tagged =
        if safe then
          if isGoal formula then
            append (intros (clasetLib.safe0_part claset))
              (intros (clasetLib.safep_part claset))
          else
            append (elims (clasetLib.safe0_part claset))
              (elims (clasetLib.safep_part claset))
        else if isGoal formula then
          intros (clasetLib.unsafe_part claset)
        else elims (clasetLib.unsafe_part claset)
    in
      clasetRules.candidate_order_measured checkpoint tagged
    end

fun acquire cache claset safe vars formula =
  case cached cache safe vars formula of
      SOME rules => copyRules cache vars formula true rules
    | NONE =>
        let
          val tagged = candidates claset safe formula
          fun convert (_, (is_elim, theorem)) =
            if is_elim then convertElim cache vars theorem
            else SOME (convertIntro cache vars theorem)
          fun weight_at_most_one ({weight, ...} : clasetRules.tag, _) =
            weight <= 1
          val (early, late) = List.partition weight_at_most_one tagged
          val early_rules = List.mapPartial convert early
          val late_rules = List.mapPartial convert late
          val rules =
            if safe then
              early_rules @ pseudoRules cache vars formula @ late_rules
            else early_rules @ late_rules
          val _ =
            remember cache safe vars formula
              (copyRules cache vars formula false rules)
        in
          rules
        end

fun copyRulesMeasured ({checkpoint, ...} : monitor)
      cache vars formula fresh_skolems rules =
  let
    val variable_copies = ref ([] : (var * var) list)
    val skolem_copies = ref ([] : (string * string) list)

    fun string_member _ [] = false
      | string_member value (other :: rest) =
          (checkpoint ();
           value = other orelse string_member value rest)

    fun variable_member _ [] = false
      | variable_member value (other :: rest) =
          (checkpoint ();
           value = other orelse variable_member value rest)

    fun insert_string value values =
      if string_member value values then values else value :: values

    fun find_variable _ [] = NONE
      | find_variable variable ((source, copy) :: rest) =
          (checkpoint ();
           if source = variable then SOME copy
           else find_variable variable rest)

    fun find_skolem _ [] = NONE
      | find_skolem name ((source, copy) :: rest) =
          (checkpoint ();
           if source = name then SOME copy else find_skolem name rest)

    fun add_skolems term names =
      let
        val _ = checkpoint ()
      in
        case term of
            Const (_, args) =>
              fold_terms args names
          | Skolem (name, arguments) =>
              fold_vars arguments (insert_string name names)
          | Var variable =>
              (case !variable of
                   NONE => names
                 | SOME item => add_skolems item names)
          | Abs (_, body) => add_skolems body names
          | left $ right => add_skolems left (add_skolems right names)
          | _ => names
      end

    and fold_terms [] names = names
      | fold_terms (item :: items) names =
          (checkpoint (); fold_terms items (add_skolems item names))

    and fold_vars [] names = names
      | fold_vars (variable :: variables) names =
          (checkpoint ();
           fold_vars variables
             (case !variable of
                  NONE => names
                | SOME item => add_skolems item names))

    val external_skolems =
      List.foldl
        (fn (variable, names) =>
           (checkpoint ();
            case !variable of
                NONE => names
              | SOME term => add_skolems term names))
        (add_skolems formula []) vars

    fun copy_variable variable =
      (checkpoint ();
       if variable_member variable vars then variable
       else
         case find_variable variable (!variable_copies) of
             SOME copy => copy
           | NONE =>
               let
                 val copy = ref NONE
                 val _ =
                   variable_copies :=
                     (variable, copy) :: !variable_copies
                 val _ =
                   case !variable of
                       NONE => ()
                     | SOME term => copy := SOME (copy_term term)
               in
                 copy
               end)

    and copy_skolem name =
      (checkpoint ();
       if not fresh_skolems orelse
          string_member name external_skolems
       then name
       else
         case find_skolem name (!skolem_copies) of
             SOME copy => copy
           | NONE =>
               let
                 val copy = freshName cache "S"
               in
                 skolem_copies := (name, copy) :: !skolem_copies;
                 copy
               end)

    and copy_term term =
      (checkpoint ();
       case term of
           Const (name, args) => Const (name, copy_terms args)
         | Skolem (name, arguments) =>
             Skolem (copy_skolem name, copy_variables arguments)
         | Free name => Free name
         | Var variable => Var (copy_variable variable)
         | Bound index => Bound index
         | Abs (name, body) => Abs (name, copy_term body)
         | left $ right => copy_term left $ copy_term right)

    and copy_terms [] = []
      | copy_terms (term :: terms) =
          (checkpoint (); copy_term term :: copy_terms terms)

    and copy_variables [] = []
      | copy_variables (variable :: variables) =
          (checkpoint ();
           copy_variable variable :: copy_variables variables)

    fun copy_premise [] = []
      | copy_premise (term :: terms) =
          (checkpoint (); copy_term term :: copy_premise terms)

    fun copy_premises [] = []
      | copy_premises (premise :: premises) =
          (checkpoint ();
           copy_premise premise :: copy_premises premises)

    fun copy_rule ({origin, pattern, premises} : tableau_rule) =
      (checkpoint ();
       {origin = origin,
        pattern = copy_term pattern,
        premises = copy_premises premises})
    fun copy_rules [] = []
      | copy_rules (rule :: rest) =
          (checkpoint (); copy_rule rule :: copy_rules rest)
  in
    copy_rules rules
  end

fun acquireMeasured (monitor as {candidate, conversion, checkpoint})
      cache claset safe vars formula =
  case cachedMeasured checkpoint cache safe vars formula of
      SOME rules =>
        copyRulesMeasured monitor cache vars formula true rules
    | NONE =>
        let
          val tagged = candidatesMeasured monitor claset safe formula
          fun enumerate [] = ()
            | enumerate (_ :: rest) =
                (checkpoint (); candidate (); enumerate rest)
          val _ = enumerate tagged
          fun convert (_, (is_elim, theorem)) =
            let
              val _ = checkpoint ()
              val _ = conversion ()
              val result =
                if is_elim then
                  convertElimMeasured checkpoint cache vars theorem
                else
                  SOME
                    (convertIntroMeasured checkpoint cache vars theorem)
            in
              result
            end
          fun weight_at_most_one ({weight, ...} : clasetRules.tag, _) =
            weight <= 1
          fun partition [] = ([], [])
            | partition (item :: rest) =
                let
                  val _ = checkpoint ()
                  val (yes, no) = partition rest
                in
                  if weight_at_most_one item then (item :: yes, no)
                  else (yes, item :: no)
                end
          fun map_partial _ [] = []
            | map_partial f (item :: rest) =
                let
                  val _ = checkpoint ()
                  val result = f item
                in
                  case result of
                      NONE => map_partial f rest
                    | SOME value => value :: map_partial f rest
                end
          fun append [] right = right
            | append (item :: items) right =
                (checkpoint (); item :: append items right)
          val (early, late) = partition tagged
          val early_rules = map_partial convert early
          val late_rules = map_partial convert late
          val rules =
            if safe then
              append early_rules
                (append (pseudoRulesMeasured checkpoint cache vars formula)
                   late_rules)
            else append early_rules late_rules
          val _ = checkpoint ()
          val templates =
            copyRulesMeasured monitor cache vars formula false rules
          val _ = remember cache safe vars formula templates
        in
          rules
        end

fun safeRules cache claset vars formula =
  acquire cache claset true vars formula

fun unsafeRules cache claset vars formula =
  acquire cache claset false vars formula

fun safeRulesMeasured monitor cache claset vars formula =
  acquireMeasured monitor cache claset true vars formula

fun unsafeRulesMeasured monitor cache claset vars formula =
  acquireMeasured monitor cache claset false vars formula

fun replayTheorem
      ({origin = Stored {is_elim, theorem}, ...} : tableau_rule) dup =
      if dup andalso is_elim then
        SOME (clasetRules.REV_DUP_ELIM_RULE theorem)
      else SOME theorem
  | replayTheorem _ _ = NONE

end
