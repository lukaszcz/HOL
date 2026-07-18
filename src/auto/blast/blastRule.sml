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

type entry =
  {formula : pterm,
   safe : bool,
   vars : var list,
   rules : tableau_rule list}

datatype cache = Cache of
  {entries : entry list ref,
   conversions : int ref}

fun newCache () = Cache {entries = ref [], conversions = ref 0}

fun conversionCount (Cache {conversions, ...}) = !conversions

(* Skolem identity is name identity in blastTerm.  A session-global supply
   therefore prevents separate node caches from accidentally sharing one. *)
val skolem_names = ref 0

fun freshName _ prefix =
  (skolem_names := !skolem_names + 1;
   prefix ^ Int.toString (!skolem_names))

val blast_trace = ref 0
val _ = Feedback.register_trace ("blast", blast_trace, 7)

val generic_cache :
  (string * (hol_type * hol_type list)) list ref = ref []

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
    case List.find (fn (key, _) => key = encoded) (!generic_cache) of
        SOME (_, info) => info
      | NONE =>
          let
            val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
            val info = (generic, Type.type_vars generic)
          in
            generic_cache := (encoded, info) :: !generic_cache;
            info
          end
  end

fun lookup_type ty [] = NONE
  | lookup_type ty ((key, value) :: rest) =
      if key = ty then SOME value else lookup_type ty rest

fun encode_type rigid alist ty =
  if Type.is_vartype ty then
    if rigid then Free (Type.dest_vartype ty)
    else
      (case lookup_type ty (!alist) of
           SOME value => value
         | NONE =>
             let
               val value = Var (ref NONE)
             in
               alist := (ty, value) :: !alist;
               value
             end)
  else
    let
      val {Thy, Tyop, Args} = Type.dest_thy_type ty
      val head = Const (const_name {Thy = Thy, Name = Tyop}, [])
    in
      list_comb (head, map (encode_type rigid alist) Args)
    end

fun const_tyargs rigid type_alist hol_const =
  let
    val {Thy, Name, Ty} = dest_thy_const hol_const
    val (generic, generic_vars) = generic_info {Thy = Thy, Name = Name}
    val subst = Type.match_type generic Ty
  in
    map (encode_type rigid type_alist o Type.type_subst subst)
      generic_vars
  end

fun member_term tm = List.exists (fn other => Term.aconv tm other)

fun lookup_term tm [] = NONE
  | lookup_term tm ((key, value) :: rest) =
      if Term.aconv tm key then SOME value else lookup_term tm rest

fun translator {rigid_types, goal_frees, rule_vars} =
  let
    val term_alist = ref []
    val type_alist = ref []

    fun fresh_variable tm make =
      case lookup_term tm (!term_alist) of
          SOME value => value
        | NONE =>
            let
              val value = make ()
            in
              term_alist := (tm, value) :: !term_alist;
              value
            end

    fun variable bounds tm =
      case lookup_term tm bounds of
          SOME level => Bound level
        | NONE =>
            if member_term tm rule_vars then
              fresh_variable tm (fn () => Var (ref NONE))
            else if goal_frees then
              fresh_variable tm
                (fn () => Skolem (freshName () "*Free*", []))
            else
              let val (name, _) = dest_var tm in Free name end

    fun under_binder bounds =
      map (fn (tm, level) => (tm, level + 1)) bounds

    fun from bounds tm =
      if is_const tm then
        let
          val {Thy, Name, ...} = dest_thy_const tm
          val args = const_tyargs rigid_types type_alist tm
        in
          Const (const_name {Thy = Thy, Name = Name}, args)
        end
      else if is_var tm then variable bounds tm
      else if is_abs tm then
        let
          val (binder, body) = dest_abs tm
          val (name, _) = dest_var binder
          val body' = from ((binder, 0) :: under_binder bounds) body
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
        in from bounds rator $ from bounds rand end
  in
    fn hol_term => from [] hol_term
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

fun same_vars ([], []) = true
  | same_vars (left :: lefts, right :: rights) =
      left = right andalso same_vars (lefts, rights)
  | same_vars _ = false

fun cached (Cache {entries, ...}) safe vars formula =
  case List.find
         (fn entry =>
            #safe entry = safe andalso
            same_vars (#vars entry, vars) andalso
            aconv (#formula entry, formula))
         (!entries) of
      NONE => NONE
    | SOME entry => SOME (#rules entry)

fun remember (Cache {entries, ...}) safe vars formula rules =
  entries :=
    {formula = formula, safe = safe, vars = vars, rules = rules} ::
    !entries

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

fun acquire cache claset safe vars formula =
  case cached cache safe vars formula of
      SOME rules => rules
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
          val _ = remember cache safe vars formula rules
        in
          rules
        end

fun safeRules cache claset vars formula =
  acquire cache claset true vars formula

fun unsafeRules cache claset vars formula =
  acquire cache claset false vars formula

fun replayTheorem
      ({origin = Stored {is_elim, theorem}, ...} : tableau_rule) dup =
      if dup andalso is_elim then
        SOME (clasetRules.REV_DUP_ELIM_RULE theorem)
      else SOME theorem
  | replayTheorem _ _ = NONE

end
