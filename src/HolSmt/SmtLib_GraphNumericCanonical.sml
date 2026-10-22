(* Fixed stock conditional canonicalization: Source-only proposal. *)
structure SmtLib_GraphNumericCanonical :> SmtLib_GraphNumericCanonical =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure P = SmtReplayProof
  structure W = SmtReplayInvocationWork
  structure C = SmtLib_GraphNumericRewriteCatalogue
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumericCanonical"
  fun diagnostic work label describe =
    if not ((OS.Process.getEnv "HOL4_HOLSMT_REPLAY_DIAGNOSTICS" = SOME "1")
        handle _ => false) then () else
      ((let val audit = W.audit work
        in TextIO.output (TextIO.stdErr,
          "CANONICAL_WORK phase=" ^ label ^ " charged=" ^
          Int.toString (#charged audit) ^ " retired=" ^
          Bool.toString (#retired audit) ^ describe () ^ "\n");
          TextIO.flushOut TextIO.stdErr end) handle _ => ())
  fun guard_app work action rows =
    let fun visit [] = W.spend_guard_policy work 1
          | visit (row::rest) =
              (W.spend_guard_policy work 1;action row;visit rest)
    in visit rows end
  datatype phase = Fresh | Prepared | Executed | Retired
  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     original : C.catalogue,phase : phase ref,symbols : int,
     limits : W.limits,
     check_type : Type.hol_type -> unit,
     retained : G.closure_child list ref,
     validation_depth : int ref,validation_generation : IntInf.int ref,
     validated : IntInf.int ref,validated_retirement : IntInf.int ref}
  fun retire (Owner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected owner action = action () handle primary =>
    (retire owner;raise primary)
  (* Complete backing validation is retained under a genuine graph retirement
     witness. Exact owner/Type/Term/root checks still run every time. *)
  fun cheap (owner as Owner
      {work,graph,scope,sources,phase,symbols,limits,...}) =
    protected owner (fn () =>
      (if !phase = Retired then raise ERR "active" "canonical owner retired"
       else ();
       W.validate work graph scope sources limits;
       if Term.term_epoch () = symbols then () else
         raise ERR "active" "constant retirement epoch changed"))
  fun invalidate (Owner {validation_generation,...}) =
    validation_generation := !validation_generation + 1
  fun active (owner as Owner
      {work,graph,scope,original,retained,validation_generation,
       validated,validated_retirement,...}) =
    protected owner (fn () =>
      let val _ = cheap owner
          val observed = G.scope_retirement_epoch graph scope
          (* Frame/node/closure geometry is immutable after fresh creation.
             Every actual retirement changes this authentic graph witness.
             Type/Term and Work guards are never cached. *)
          val _ = if !validated_retirement = observed then () else
            (C.validate_for work original;
             guard_app work (fn child => ignore
               (G.closure_child_node graph scope child)) (!retained);
             cheap owner;
             if G.scope_retirement_epoch graph scope = observed then () else
               raise ERR "active" "scope retirement during backing pass";
             validated_retirement := observed)
      in validated := !validation_generation end)
  fun invalidate_backings (owner as Owner {validated_retirement,...}) =
    (validated_retirement := ~1;invalidate owner)
  fun transaction (owner as Owner {validation_depth,...}) operation =
    let val saved = !validation_depth
        val _ = active owner
        val _ = if saved = 0 then invalidate owner else ()
        val _ = validation_depth := saved+1
        fun restore () = validation_depth := saved
    in (let val _ = active owner
            val answer = operation ()
            val _ = restore ()
            val _ = active owner
        in answer end) handle primary => (restore ();raise primary)
    end
  (* Policies never reuse a pure-pass stamp. A returning child retirement
     changes the graph witness, forcing the full actual backing check. *)
  fun external (owner as Owner {validation_depth,...}) operation =
    let val saved = !validation_depth
        val _ = validation_depth := 0
        val _ = invalidate owner
        fun restore () = (validation_depth := saved;invalidate owner)
    in (let val _ = active owner
            val answer = operation ()
            val _ = active owner
            val _ = restore ()
        in answer end) handle primary => (restore ();raise primary)
    end
  (* spend authenticates the SAME active Work and only debits its private
     counter. There is no callback/native mutation between these guards. *)
  fun tick (owner as Owner {work,...}) =
    (active owner;W.spend work 1)
  fun begin work original {check_type} =
    let val _ = C.validate_for work original
        val sources = W.original_sources work
        val graph = S.owning_graph sources
        val scope = S.owning_scope sources
        val limits = W.semantic_limits work
    in Owner {work = work,graph = graph,scope = scope,sources = sources,
      original = original,phase = ref Fresh,symbols = Term.term_epoch (),
      limits = limits,check_type = check_type,retained = ref [],
      validation_depth = ref 0,validation_generation = ref 0,
      validated = ref (~1),validated_retirement = ref (~1)} end
    handle primary => (W.close work;raise primary)

  (* Types of FUTURE logical headers stay DATA until the complete quote.
     Actual original variable/constant types retain their declaration IDs. *)
  datatype ty = HeldType of Type.hol_type | Arrow of ty * ty
  datatype syntax = Held of Term.term * ty | Application of syntax * syntax
    | Abstraction of syntax * syntax
  datatype rule = Seed of P.closed_fact | SeedFixed of Thm.thm
    | Specialize of syntax * proof | Generalize of syntax * proof
    | TypeInstance of (Type.hol_type * ty) list * proof
    | TermInstance of (syntax * syntax) list * proof
    | EqualModusPonens of proof * proof
    | ApplyFunction of syntax * proof | ApplyArgument of proof * syntax
    | AbstractEquality of syntax * proof | ContractBeta of syntax
    | ChooseWitness of syntax * proof * proof
    | NegationEliminate of proof
    | SpecializeAll of syntax list * proof
    | SelectLeft of proof | SelectRight of proof
    | Undisch of proof | Discharge of syntax * proof
    | Assume of syntax | Conjoin of proof * proof
    | DisjLeft of proof * syntax | DisjRight of syntax * proof
    | ModusPonens of proof * proof | NotIntro of proof
    | ToTruth of proof | ToFalse of proof | Symmetry of proof
    | FlipLeftEquality of proof | QuantifyCondition of syntax * proof
    | ConjoinConditions of syntax list * proof
    | ExistsIntroduction of syntax * syntax * proof | NegatedSymmetry of proof
    | ExpandAbbrev of proof | AbbrevFunctionEquality of proof
    | ExpandRestrictedForall of proof
    | FalseEquality of syntax * proof
    | TruthFalseEquality of bool * syntax * proof
  and proof = Proof of {conclusion : syntax,hypotheses : syntax list,
                       rule : rule}
  type profile = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int}
  datatype plan = Plan of {owner : owner,
    rows : (int * Thm.thm * proof) list,used : bool ref}
  datatype catalogue = Catalogue of {owner : owner,
    origins : (int * Thm.thm) list,rules : Thm.thm list,
    facts : P.closed_fact list}
  fun statement (Proof {conclusion,...}) = conclusion
  fun hypotheses (Proof {hypotheses,...}) = hypotheses
  fun type_of (Held (_,ty)) = ty
    | type_of (Application (f,_)) =
        (case type_of f of Arrow (_,result) => result
         | HeldType ty => HeldType (#2 (Type.dom_rng ty)))
    | type_of (Abstraction (v,b)) = Arrow (type_of v,type_of b)
  val boolean = HeldType Type.bool
  fun constant term = Held (term,HeldType (Term.type_of term))
  fun unary term operand = Application (constant term,operand)
  fun binary term left right =
    Application (Application (constant term,left),right)
  fun implication a b = binary boolSyntax.implication a b
  fun conjunction a b = binary boolSyntax.conjunction a b
  fun disjunction a b = binary boolSyntax.disjunction a b
  fun negation a = unary boolSyntax.negation a
  (* Polymorphic equality headers use the exact operand type, not the
     pre-instantiated equality constant's generic type. *)
  fun equality a b =
    Application (Application
      (Held (boolSyntax.equality,
        Arrow (type_of a,Arrow (type_of a,boolean))),a),b)
  fun quantifier head v body = Application
    (Held (head,Arrow (Arrow (type_of v,boolean),boolean)),
     Abstraction (v,body))
  fun truth () = constant boolSyntax.T
  fun falsity () = constant boolSyntax.F

  fun parse owner term =
    let val _ = tick owner
        val ty = HeldType (Term.type_of term)
    in if Term.is_comb term then
         let val (f,x) = Term.dest_comb term
         in Application (parse owner f,parse owner x) end
       else if Term.is_abs term then
         let val (v,b) = Term.dest_abs term
         in Abstraction (parse owner v,parse owner b) end
       else Held (term,ty) end
  fun head_is owner thy name (Held (term,_)) =
        (tick owner;
         if Term.is_const term then
           let val value = Term.dest_thy_const term
           in #Thy value = thy andalso #Name value = name end
         else false)
    | head_is _ _ _ _ = false
  fun unary_view owner thy name (Application (f,x)) =
        if head_is owner thy name f then SOME x else NONE
    | unary_view _ _ _ _ = NONE
  fun binary_view owner thy name (Application (Application (f,x),y)) =
        if head_is owner thy name f then SOME (x,y) else NONE
    | binary_view _ _ _ _ = NONE
  fun is_variable owner (Held (term,_)) = (tick owner;Term.is_var term)
    | is_variable _ _ = false
  fun is_constant owner (Held (term,_)) = (tick owner;Term.is_const term)
    | is_constant _ _ = false
  (* Exact original VAR/type comparison after the complete source portfolio
     has been admitted. Bound variables are paired separately in alpha. *)
  fun variable_equal owner (Held (left,a),Held (right,b)) =
        (tick owner;Term.is_var left andalso Term.is_var right andalso
         #1 (Term.dest_var left) = #1 (Term.dest_var right) andalso
         type_equal owner (a,b))
    | variable_equal _ _ = false
  and type_equal owner (HeldType a,HeldType b) =
        (tick owner;Type.compare (a,b) = EQUAL)
    | type_equal owner (Arrow (a,b),Arrow (c,d)) =
        type_equal owner (a,c) andalso type_equal owner (b,d)
    | type_equal owner (HeldType a,b) =
        if Type.is_vartype a then false else
          let val shape = Type.dest_thy_type a
          in if #Thy shape = "min" andalso #Tyop shape = "fun" then
               let val (x,y) = Type.dom_rng a
               in type_equal owner (Arrow (HeldType x,HeldType y),b) end
             else false end
    | type_equal owner (a,HeldType b) = type_equal owner (HeldType b,a)
  fun alpha owner left right =
    let
      fun lookup _ [] = NONE
        | lookup value ((a,b)::rest) =
            if variable_equal owner (value,a) then SOME b
            else lookup value rest
      fun same bound a b =
        (tick owner;
         if not (type_equal owner (type_of a,type_of b)) then false else
         case (a,b) of
           (Application (f,x),Application (g,y)) =>
             same bound f g andalso same bound x y
         | (Abstraction (v,x),Abstraction (w,y)) => same ((v,w)::bound) x y
         | (Held (x,_),Held (y,_)) =>
             (case lookup a bound of SOME target =>
                variable_equal owner (target,b)
              | NONE => if Term.is_var x then variable_equal owner (a,b)
                else Term.is_const x andalso Term.is_const y andalso
                  KernelSig.id_compare
                    (#Name (Term.dest_thy_constid x),
                     #Name (Term.dest_thy_constid y)) = EQUAL)
         | _ => false)
    in same [] left right end
  fun member owner value values = List.exists (alpha owner value) values
  fun union owner left right = List.foldl (fn (v,acc) =>
    if member owner v acc then acc else v::acc) right left
  fun free owner value =
    let fun visit bound current found =
      (tick owner;case current of
         Application (f,x) => visit bound x (visit bound f found)
       | Abstraction (v,b) => visit (v::bound) b found
       | Held _ => if is_variable owner current andalso
           not (member owner current bound) andalso
           not (member owner current found) then current::found else found)
    in List.rev (visit [] value []) end
  fun free_hyp owner proof =
    List.foldl (fn (h,acc) => union owner (free owner h) acc) []
      (hypotheses proof)
  fun theorem conclusion hyps rule =
    Proof {conclusion = conclusion,hypotheses = hyps,rule = rule}
  fun assumption value = theorem value [value] (Assume value)
  fun discharge owner value proof = theorem
    (implication value (statement proof))
    (List.filter (fn h => not (alpha owner value h)) (hypotheses proof))
    (Discharge (value,proof))
  fun undisch owner proof =
    case binary_view owner "min" "==>" (statement proof) of
      SOME (ant,body) => theorem body
        (union owner [ant] (hypotheses proof)) (Undisch proof)
    | NONE => raise ERR "undisch" "private non-implication recipe"
  fun mp owner law argument =
    case binary_view owner "min" "==>" (statement law) of
      SOME (ant,body) => if alpha owner ant (statement argument) then
        theorem body (union owner (hypotheses law) (hypotheses argument))
          (ModusPonens (law,argument))
        else raise ERR "mp" "private antecedent recipe mismatch"
    | NONE => raise ERR "mp" "private rule is not implication"
  fun sym owner proof =
    case binary_view owner "min" "=" (statement proof) of
      SOME (left,right) => theorem (equality right left) (hypotheses proof)
        (Symmetry proof)
    | NONE => raise ERR "sym" "private non-equation recipe"
  fun eqt proof = theorem (equality (statement proof) (truth ()))
    (hypotheses proof) (ToTruth proof)
  fun eqf owner proof = case unary_view owner "bool" "~" (statement proof) of
      SOME value => theorem (equality value (falsity ())) (hypotheses proof)
        (ToFalse proof)
    | NONE => raise ERR "eqf" "private non-negation recipe"

  fun substitute owner variable replacement value =
    if variable_equal owner (variable,value) then replacement else
      (tick owner;case value of
         Application (f,x) => Application
           (substitute owner variable replacement f,
            substitute owner variable replacement x)
       | Abstraction (v,b) => if variable_equal owner (variable,v) then value
           else if member owner v (free owner replacement) andalso
                   member owner variable (free owner b) then
             let val avoid = union owner (free owner b)
                   (free owner replacement)
                 val term = case v of Held (t,_) => t
                   | _ => raise ERR "substitute" "private binder not atomic"
                 val terms = List.map (fn Held (t,_) => t
                   | _ => raise ERR "substitute" "private variable not atomic")
                   avoid
                 val _ = tick owner
                 val next = Held (Term.prim_variant terms term,type_of v)
                 val _ = active owner
                 val renamed = substitute owner v next b
             in Abstraction
               (next,substitute owner variable replacement renamed) end
           else Abstraction (v,substitute owner variable replacement b)
       | Held _ => value)
  fun actual_variable (Held (term,_)) = term
    | actual_variable _ = raise ERR "variable" "private non-held variable"
  fun ordered_variables owner values =
    Listsort.sort (fn (a,b) =>
      (tick owner;Term.compare (actual_variable a,actual_variable b))) values
  fun vary owner avoid variable =
    let val term = actual_variable variable
        val args = List.map actual_variable avoid
        val _ = tick owner
        (* Only a held original VAR type is reused. No theorem or type
           constructor is invoked here. The name-search work will be quoted
           from the actual finite avoidance portfolio before this call. *)
        val answer = Term.prim_variant args term
        val _ = active owner
    in Held (answer,type_of variable) end
  fun specialize_all owner proof =
    let
      fun collect value = case unary_view owner "bool" "!" value of
          SOME (Abstraction (v,b)) =>
            let val (vars,body) = collect b in (v::vars,body) end
        | SOME _ => raise ERR "specialize_all" "forall lacks a lambda"
        | NONE => ([],value)
      val (variables,body) = collect (statement proof)
      val avoid = ordered_variables owner (free_hyp owner proof) @
        ordered_variables owner (free owner (statement proof))
      val (_,variants) = List.foldr (fn (v,(held,chosen)) =>
        let val next = vary owner held v
        in (next::held,next::chosen) end) (avoid,[]) variables
      val answer = ListPair.foldlEq (fn (v,x,b) =>
        substitute owner v x b) body (variables,variants)
    in if null variables then proof else theorem answer (hypotheses proof)
      (SpecializeAll (variants,proof)) end
  fun select owner left proof =
    case binary_view owner "bool" "/\\" (statement proof) of
      SOME (a,b) => theorem (if left then a else b) (hypotheses proof)
        (if left then SelectLeft proof else SelectRight proof)
    | NONE => raise ERR "select" "private non-conjunction recipe"
  fun conj owner left right = theorem
    (conjunction (statement left) (statement right))
    (union owner (hypotheses left) (hypotheses right)) (Conjoin (left,right))
  fun not_intro owner proof =
    case binary_view owner "min" "==>" (statement proof) of
      SOME (ant,body) => if alpha owner body (falsity ()) then
        theorem (negation ant) (hypotheses proof) (NotIntro proof)
        else raise ERR "not_intro" "private consequent is not F"
    | NONE => raise ERR "not_intro" "private non-implication recipe"
  fun all_undisch owner proof =
    case binary_view owner "min" "==>" (statement proof) of
      SOME _ => all_undisch owner (undisch owner proof) | NONE => proof
  fun conditions owner proof =
    let fun collect value = case binary_view owner "min" "==>" value of
          SOME (a,b) => let val (ants,result) = collect b
                        in (a::ants,result) end
        | NONE => ([],value)
    in collect (statement proof) end
  fun conjoined_conditions owner ants proof =
    (* Cond_rewr.CONJ_DISCH uses itlist, making a RIGHT-associated ordered
       antecedent. Keep empty and singleton cases exact. *)
    case ants of [] => proof
    | [one] => discharge owner one proof
    | first::rest =>
        let val ant = List.foldr (fn (a,b) => conjunction a b)
              (List.last rest) (first::List.take (rest,length rest-1))
            val hyps = List.filter (fn h => not (member owner h ants))
              (hypotheses proof)
        in theorem (implication ant (statement proof)) hyps
          (ConjoinConditions (ants,proof)) end

  (* Every expanded recipe below is a kernel primitive, with its EXACT
     proposition and hypotheses retained before replay. SeedFixed is private
     and called only with the listed sealed bool/marker theorems. *)
  fun seed_fixed owner th =
    (tick owner;
     if null (Thm.hyp th) andalso Term.uptodate_term (Thm.concl th) then
       theorem (parse owner (Thm.concl th)) [] (SeedFixed th)
     else raise ERR "seed_fixed" "stale or non-closed fixed helper")
  fun spec owner arg p =
    case unary_view owner "bool" "!" (statement p) of
      SOME (Abstraction (v,b)) =>
        if type_equal owner (type_of v,type_of arg) then
          theorem (substitute owner v arg b) (hypotheses p)
            (Specialize (arg,p))
        else raise ERR "spec" "private specialization type differs"
    | _ => raise ERR "spec" "private helper has no leading forall"
  fun gen owner v p =
    if member owner v (free_hyp owner p) then
      raise ERR "gen" "private variable is free in hypotheses"
    else theorem (quantifier boolSyntax.universal v (statement p))
      (hypotheses p) (Generalize (v,p))
  fun eq_mp owner a b = case binary_view owner "min" "=" (statement a) of
      SOME (l,r) => if alpha owner l (statement b) then
        theorem r (union owner (hypotheses a) (hypotheses b))
          (EqualModusPonens (a,b))
        else raise ERR "eq_mp" "private proposition mismatch"
    | NONE => raise ERR "eq_mp" "private non-equation helper"
  fun not_elim owner p = case unary_view owner "bool" "~" (statement p) of
      SOME a => theorem (implication a (falsity ())) (hypotheses p)
        (NegationEliminate p)
    | NONE => raise ERR "not_elim" "private non-negation"
  fun substitute_type owner bindings shape =
    let fun actual ty =
      if Type.is_vartype ty then
        let fun find [] = HeldType ty
              | find ((a,b)::rest) =
                  (tick owner;if Type.compare (a,ty) = EQUAL then b
                   else find rest)
        in find bindings end
      else let val view = Type.dest_thy_type ty in
        if #Thy view = "min" andalso #Tyop view = "fun" then
          let val (a,b) = Type.dom_rng ty in Arrow (actual a,actual b) end
        else HeldType ty end
    in case shape of HeldType ty => actual ty
      | Arrow (a,b) => Arrow (substitute_type owner bindings a,
                              substitute_type owner bindings b) end
  fun inst_type owner bindings p =
    let fun visit value =
      (tick owner;case value of
         Held (term,ty) => Held (term,substitute_type owner bindings ty)
       | Application (f,x) => Application (visit f,visit x)
       | Abstraction (v,b) => Abstraction (visit v,visit b))
    in theorem (visit (statement p)) (List.map visit (hypotheses p))
      (TypeInstance (bindings,p)) end
  fun inst_term owner bindings p =
    let
      val avoid = List.foldl (fn ((_,range),acc) =>
        union owner (free owner range) acc) [] bindings
      fun lookup value [] = NONE
        | lookup value ((key,range)::rest) =
            if variable_equal owner (key,value) then SOME range
            else lookup value rest
      fun visit rows value = case lookup value rows of SOME range => range
        | NONE => (tick owner;case value of
            Application (f,x) => Application (visit rows f,visit rows x)
          | Abstraction (v,b) =>
              let val nested = List.filter
                    (fn (key,_) => not (variable_equal owner (key,v))) rows
                  val fresh = if member owner v avoid then
                    vary owner (union owner avoid (free owner b)) v else v
                  val body = if variable_equal owner (fresh,v) then b
                    else substitute owner v fresh b
              in Abstraction (fresh,visit nested body) end
          | Held _ => value)
    in theorem (visit bindings (statement p))
      (List.map (visit bindings) (hypotheses p)) (TermInstance (bindings,p))
    end
  fun apply_function owner f p =
    case binary_view owner "min" "=" (statement p) of
      SOME (a,b) => theorem
        (equality (Application (f,a)) (Application (f,b))) (hypotheses p)
        (ApplyFunction (f,p))
    | NONE => raise ERR "apply_function" "private helper is not equality"
  fun apply_argument owner p x =
    case binary_view owner "min" "=" (statement p) of
      SOME (a,b) => theorem
        (equality (Application (a,x)) (Application (b,x))) (hypotheses p)
        (ApplyArgument (p,x))
    | NONE => raise ERR "apply_argument" "private helper is not equality"
  fun abstract owner v p =
    case binary_view owner "min" "=" (statement p) of
      SOME (a,b) => theorem
        (equality (Abstraction (v,a)) (Abstraction (v,b))) (hypotheses p)
        (AbstractEquality (v,p))
    | NONE => raise ERR "abstract" "private helper is not equality"
  fun beta owner redex = case redex of
      Application (Abstraction (v,b),x) => theorem
        (equality redex (substitute owner v x b)) [] (ContractBeta redex)
    | _ => raise ERR "beta" "private non-beta expression"
  fun symmetry_conversion owner left right =
    let val basis = seed_fixed owner boolTheory.EQ_SYM_EQ
        val typed = inst_type owner [(Type.alpha,type_of left)] basis
    in spec owner right (spec owner left typed) end
  fun truth_basis owner negative =
    let val basis = seed_fixed owner boolTheory.EQ_CLAUSES
        val variable = case unary_view owner "bool" "!" (statement basis) of
            SOME (Abstraction (v,_)) => v
          | _ => raise ERR "truth_basis" "fixed EQ_CLAUSES shape changed"
        val all = spec owner variable basis
        fun fourth p = select owner false
          (select owner false (select owner false p))
        val chosen = if negative then fourth all
          else select owner true (select owner false all)
    in gen owner variable (sym owner chosen) end
  fun flatten_conjunction owner p =
    case binary_view owner "bool" "/\\" (statement p) of
      NONE => [p]
    | SOME _ => flatten_conjunction owner (select owner true p) @
        flatten_conjunction owner (select owner false p)
  fun conjunct_n owner n p = List.nth (flatten_conjunction owner p,n)
  fun primitive_conditions owner ants p = case ants of [] => p
    | [a] => discharge owner a p
    | a::rest =>
        let val tail = primitive_conditions owner rest p
            val current = discharge owner a tail
            val (b,c) = case binary_view owner "min" "==>"
                (statement tail) of SOME pair => pair
              | NONE => raise ERR "conditions" "private tail missing"
            val helper = List.foldl (fn (x,h) => spec owner x h)
              (seed_fixed owner boolTheory.AND_IMP_INTRO) [a,b,c]
        in eq_mp owner helper current end
  fun function_parts (Arrow (a,b)) = (a,b)
    | function_parts (HeldType ty) =
        let val (a,b) = Type.dom_rng ty in (HeldType a,HeldType b) end
  fun leading_variable owner p =
    case unary_view owner "bool" "!" (statement p) of
      SOME (Abstraction (v,_)) => v
    | _ => raise ERR "leading_variable" "private forall missing"
  fun function_equality owner p =
    let val (left,right) = case binary_view owner "min" "="
            (statement p) of SOME pair => pair
          | NONE => raise ERR "function_equality" "private equality missing"
    in case right of Abstraction _ =>
      let val (domain,range) = function_parts (type_of right)
          val law = inst_type owner
            [(Type.alpha,domain),(Type.beta,range)]
            (seed_fixed owner boolTheory.FUN_EQ_THM)
          val applied = eq_mp owner
            (spec owner right (spec owner left law)) p
          val variable = leading_variable owner applied
          val pointwise = spec owner variable applied
          val right_app = Application (right,variable)
          val left_app = Application (left,variable)
          val equality_function = Held (boolSyntax.equality,
            Arrow (range,Arrow (range,boolean)))
          val partial = Application (equality_function,left_app)
          val contracted = eq_mp owner
            (apply_function owner partial (beta owner right_app)) pointwise
      in gen owner variable (function_equality owner contracted) end
    | _ => sym owner p
    end
  fun abbrev_equality owner p =
    let val operand = case unary_view owner "marker" "Abbrev"
            (statement p) of SOME value => value
          | NONE => raise ERR "abbrev_equality" "Abbrev operand missing"
        val initial = seed_fixed owner markerTheory.Abbrev_def
        val helper = case unary_view owner "bool" "!" (statement initial) of
            SOME _ => spec owner operand initial
          | NONE => (case free owner (statement initial) of
              [variable] => inst_term owner [(variable,operand)] initial
            | _ => raise ERR "abbrev_equality" "fixed definition changed")
    in eq_mp owner helper p end
  fun restricted_forall owner p =
    let val (guard,predicate) = case binary_view owner "bool" "RES_FORALL"
            (statement p) of SOME pair => pair
          | NONE => raise ERR "restricted_forall" "restricted forall missing"
        val (domain,_) = function_parts (type_of predicate)
        val basis = inst_type owner [(Type.alpha,domain)]
          (seed_fixed owner boolTheory.RES_FORALL_THM)
        val helper = spec owner predicate (spec owner guard basis)
        val generalized = eq_mp owner helper p
        val variable = leading_variable owner generalized
        val pointwise = spec owner variable generalized
        val test = Application (guard,variable)
        val partial = Application (constant boolSyntax.implication,test)
        val contracted = eq_mp owner
          (apply_function owner partial
            (beta owner (Application (predicate,variable)))) pointwise
    in gen owner variable contracted end
  fun expand owner value =
    let val Proof {conclusion,hypotheses=held_hypotheses,rule} = value
        fun unary make p = make (expand owner p)
    in case rule of
      Seed _ => value | SeedFixed _ => value
    | SpecializeAll (variants,p) => List.foldl
        (fn (v,h) => spec owner v h) (expand owner p) variants
    | SelectLeft p => select owner true (expand owner p)
    | SelectRight p => select owner false (expand owner p)
    | Undisch p =>
        let val base = expand owner p
            val ant = case binary_view owner "min" "==>" (statement base) of
                SOME (a,_) => a
              | NONE => raise ERR "expand" "missing antecedent"
        in mp owner base (assumption ant) end
    | Discharge (ant,p) => discharge owner ant (expand owner p)
    | Assume _ => value
    | Conjoin (a,b) => conj owner (expand owner a) (expand owner b)
    | DisjLeft (p,b) => theorem conclusion held_hypotheses
        (DisjLeft (expand owner p,b))
    | DisjRight (a,p) => theorem conclusion held_hypotheses
        (DisjRight (a,expand owner p))
    | ModusPonens (a,b) => mp owner (expand owner a) (expand owner b)
    | NotIntro p => not_intro owner (expand owner p)
    | ToTruth p => let val base = expand owner p
        in eq_mp owner (spec owner (statement base) (truth_basis owner false))
          base end
    | ToFalse p =>
        let val base = expand owner p
            val body = case unary_view owner "bool" "~" (statement base) of
                SOME b => b | NONE => raise ERR "expand" "negation missing"
        in eq_mp owner (spec owner body (truth_basis owner true)) base end
    | Symmetry p => sym owner (expand owner p)
    | ConjoinConditions (ants,p) =>
        primitive_conditions owner ants (expand owner p)
    | FlipLeftEquality p =>
        let val base = expand owner p
            val (inner,r) = case binary_view owner "min" "="
                (statement base) of SOME pair => pair
              | NONE => raise ERR "expand" "outer equality missing"
            val (a,b) = case binary_view owner "min" "=" inner of
                SOME pair => pair
              | NONE => raise ERR "expand" "inner equality missing"
            val function = Held (boolSyntax.equality,
              Arrow (boolean,Arrow (boolean,boolean)))
            val converted = apply_argument owner
              (apply_function owner function (symmetry_conversion owner a b)) r
        in eq_mp owner converted base end
    | NegatedSymmetry p =>
        let val base = expand owner p
            val inner = case unary_view owner "bool" "~" (statement base) of
                SOME b => b | NONE => raise ERR "expand" "negation missing"
            val (a,b) = case binary_view owner "min" "=" inner of
                SOME pair => pair
              | NONE => raise ERR "expand" "negative equality missing"
        in eq_mp owner (apply_function owner (constant boolSyntax.negation)
          (symmetry_conversion owner a b)) base end
    | ExistsIntroduction (ant,witness,p) => theorem conclusion held_hypotheses
        (ExistsIntroduction (ant,witness,expand owner p))
    | QuantifyCondition (v,p) =>
        let val base = expand owner p
            val (ant,result) = case binary_view owner "min" "==>"
                (statement base) of SOME pair => pair
              | NONE => raise ERR "expand" "condition missing"
            val ex = quantifier boolSyntax.existential v ant
            val consequent = mp owner base (assumption ant)
            val chosen = theorem result
              (union owner (hypotheses base) [ex])
              (ChooseWitness (v,assumption ex,consequent))
        in discharge owner ex chosen end
    | ExpandAbbrev p => abbrev_equality owner (expand owner p)
    | AbbrevFunctionEquality p =>
        expand owner
          (specialize_all owner (function_equality owner (expand owner p)))
    | ExpandRestrictedForall p => restricted_forall owner (expand owner p)
    | FalseEquality (v,p) =>
        let val base = expand owner p
            val helper = spec owner (equality v (falsity ()))
              (seed_fixed owner boolTheory.FALSITY)
        in mp owner helper base end
    | TruthFalseEquality (left_true,v,p) =>
        let val base = expand owner p
            val distinct = select owner left_true
              (seed_fixed owner boolTheory.BOOL_EQ_DISTINCT)
            val contradiction = mp owner (not_elim owner distinct) base
            val helper = spec owner (equality v (falsity ()))
              (seed_fixed owner boolTheory.FALSITY)
        in mp owner helper contradiction end
    | _ => value
    end


  (* Exact ordered work-list/accumulator structure of Cond_rewr.IMP_CANON.
     In particular its final two reversals preserve branch and stock order. *)
  fun implication_canonical owner initial =
    let
      fun finish acc [] = acc
        | finish acc ((ants,proof)::rest) = finish
            (List.foldl (fn (ant,p) => discharge owner ant p) proof ants::acc)
            rest
      fun loop acc [] = finish [] acc
        | loop acc ((ants,proof)::rest) =
          let val value = statement proof in
            case binary_view owner "bool" "/\\" value of
              SOME _ => loop acc ((ants,select owner true proof)::
                                 (ants,select owner false proof)::rest)
            | NONE => (case binary_view owner "min" "==>" value of
                SOME (ant,body) =>
                  (case binary_view owner "bool" "/\\" ant of
                     SOME (a,b) =>
                       let val combined = conj owner (assumption a)
                             (assumption b)
                           val next = discharge owner a
                             (discharge owner b (mp owner proof combined))
                       in loop acc ((ants,next)::rest) end
                   | NONE => (case binary_view owner "bool" "\\/" ant of
                       SOME (a,b) =>
                         let val left = theorem (disjunction a b) [a]
                               (DisjLeft (assumption a,b))
                             val right = theorem (disjunction a b) [b]
                               (DisjRight (a,assumption b))
                             val first = discharge owner a
                               (mp owner proof left)
                             val second = discharge owner b
                               (mp owner proof right)
                         in loop acc ((ants,first)::(ants,second)::rest) end
                     | NONE => (case unary_view owner "bool" "?" ant of
                         SOME (Abstraction (v,b)) =>
                           let val all = ordered_variables owner
                                 (union owner (free_hyp owner proof)
                                   (free owner value))
                               val variant = vary owner all v
                               val instance = substitute owner v variant b
                               val witness = theorem ant [instance]
                                 (ExistsIntroduction
                                   (ant,variant,assumption instance))
                               val next = discharge owner instance
                                 (mp owner proof witness)
                           in loop acc ((ants,next)::rest) end
                       | SOME _ => raise ERR "implication_canonical"
                           "existential lacks genuine lambda"
                       | NONE => if alpha owner body (falsity ()) then
                           loop ((ants,not_intro owner proof)::acc) rest
                         else loop acc ((ant::ants,undisch owner proof)::rest))))
              | NONE => (case unary_view owner "bool" "!" value of
                  SOME _ => loop acc
                    ((ants,specialize_all owner proof)::rest)
                | NONE => if Option.isSome
                    (binary_view owner "bool" "RES_FORALL" value) then
                    loop acc ((ants,restricted_forall owner proof)::rest)
                  else loop ((ants,proof)::acc) rest))
          end
    in loop [] [([],initial)] end

  fun occurs owner needle value = alpha owner needle value orelse
    (tick owner;case value of
       Application (f,x) => occurs owner needle f orelse occurs owner needle x
     | Abstraction (_,b) => occurs owner needle b | Held _ => false)
  fun simple_right owner value =
    case binary_view owner "min" "=" value of
      NONE => true
    | SOME (l,r) => (is_variable owner l andalso is_constant owner r) orelse
        (is_constant owner l andalso is_variable owner r)
  fun flip_left owner proof =
    case binary_view owner "min" "=" (statement proof) of
      SOME (left,right) =>
        (case binary_view owner "min" "=" left of
           SOME (a,b) => theorem (equality (equality b a) right)
             (hypotheses proof) (FlipLeftEquality proof)
         | NONE => raise ERR "flip_left" "inner equation missing")
    | NONE => raise ERR "flip_left" "outer equation missing"

  fun equality_canonical owner proof =
    let
      val (ants,_) = conditions owner proof
      val hypfvs = free_hyp owner proof
      val opened = all_undisch owner proof
      val value = statement opened
      fun finish rows = List.map (conjoined_conditions owner ants) rows
      fun conditional_safe left right =
        let val available = union owner (free owner left) hypfvs
        in List.all (fn v => member owner v available) (free owner right)
        end
      val rewritten = case binary_view owner "min" "=" value of
        SOME (left,right) =>
          if occurs owner left right then [eqt opened,eqt (sym owner opened)]
          else if alpha owner left (truth ()) then
            if alpha owner right (falsity ()) then
              let val _ = tick owner
                  val variable = Held (Term.genvar Type.bool,boolean)
              in [theorem (equality variable (falsity ()))
                (hypotheses opened)
                (TruthFalseEquality (true,variable,opened))] end
            else [sym owner opened]
          else if alpha owner left (falsity ()) then
            if alpha owner right (truth ()) then
              let val _ = tick owner
                  val variable = Held (Term.genvar Type.bool,boolean)
              in [theorem (equality variable (falsity ()))
                (hypotheses opened)
                (TruthFalseEquality (false,variable,opened))] end
            else [sym owner opened]
          else let
            val safe = not (is_variable owner left) orelse
              not (type_equal owner (type_of left,boolean)) orelse
              member owner left hypfvs
            val base = if conditional_safe left right andalso safe then opened
              else eqt opened
            val flip = case binary_view owner "min" "=" (statement base) of
                SOME (l,r) => Option.isSome (binary_view owner "min" "=" l)
                  andalso simple_right owner r
              | NONE => false
          in if flip then [base,flip_left owner base] else [base] end
      | NONE => (case unary_view owner "bool" "~" value of
          SOME negative =>
            if Option.isSome (binary_view owner "min" "=" negative) then
              (case binary_view owner "min" "=" negative of
                 SOME (a,b) =>
                   let val mirror = theorem (negation (equality b a))
                         (hypotheses opened) (NegatedSymmetry opened)
                   in [eqf owner opened,eqf owner mirror] end
               | NONE => raise ERR "equality_canonical" "equation missing")
            else if is_variable owner negative andalso
                not (member owner negative hypfvs) then []
              else [eqf owner opened]
        | NONE => if alpha owner value (truth ()) then []
          else if alpha owner value (falsity ()) then
            (* Cond_rewr's fixed x_eq_false uses a private fresh boolean x.
               The exact arbitrary variable will be retained with its quote
               in the false-elimination operation before replay. *)
            let val _ = tick owner
                val variable = Held (Term.genvar Type.bool,boolean)
                val _ = active owner
            in [theorem (equality variable (falsity ())) (hypotheses opened)
              (FalseEquality (variable,opened))] end
          else if Option.isSome (unary_view owner "marker" "Abbrev" value)
            then
              let val decoded = abbrev_equality owner opened
              in case binary_view owner "min" "=" (statement decoded) of
                NONE => []
              | SOME (_,right) =>
                  let val base = equality_canonical owner (sym owner decoded)
                  in case right of Abstraction _ => base @
                    equality_canonical owner (specialize_all owner
                      (function_equality owner decoded))
                    | _ => base end
              end
          else if is_variable owner value andalso not
              (member owner value hypfvs) then [] else [eqt opened])
    in finish rewritten end

  fun quantify_conditions owner proof =
    case binary_view owner "min" "==>" (statement proof) of NONE => proof
    | SOME (_,body) =>
        let val excluded = union owner (free owner body) (free_hyp owner proof)
            val variables = ordered_variables owner (List.filter
              (fn v => not (member owner v excluded))
              (free owner (statement proof)))
            fun quantify (v,p) =
              case binary_view owner "min" "==>" (statement p) of
                SOME (ant,result) => theorem
                  (implication (quantifier boolSyntax.existential v ant) result)
                  (hypotheses p) (QuantifyCondition (v,p))
              | NONE => raise ERR "quantify" "private condition disappeared"
        in List.foldr quantify proof variables end

  (* Repeated annotations include the VARIABLE slot of every abstraction.
     Future arrow types remain symbolic; this pass calls no Type constructor
     and no supplied policy. Work is the invocation's independent type work,
     not an annotation <= syntax/template cutoff. *)
  fun type_weight owner ty =
    (tick owner;case ty of Arrow (a,b) =>
       1 + type_weight owner a + type_weight owner b
     | HeldType actual =>
         if not (Type.uptodate_type actual) then
           raise ERR "type_weight" "retired actual type"
         else if Type.is_vartype actual then 1
         else List.foldl (fn (a,n) => n+type_weight owner (HeldType a))
           (1 : IntInf.int) (#Args (Type.dest_thy_typeid actual)))
  fun plus ({raw=a,inc=b,ann=c}:profile) ({raw=d,inc=e,ann=f}:profile) =
    {raw=a+d,inc=b+e,ann=c+f}:profile
  fun syntax_profile_with_weight owner weight types value =
    let val _ = tick owner
        val ty = type_of value
        val annotation = weight ty
        val _ = types := ty:: !types
    in case value of
      Held _ => {raw=1,inc=1,ann=annotation}:profile
    | Application (f,x) => plus {raw=1,inc=1,ann=annotation}
        (plus (syntax_profile_with_weight owner weight types f)
          (syntax_profile_with_weight owner weight types x))
    | Abstraction (v,b) =>
        let val bt = type_of v val bw = weight bt
            val _ = types := bt:: !types
        in plus {raw=1,inc=2,ann=annotation+bw}
          (syntax_profile_with_weight owner weight types b) end
    end
  fun syntax_profile owner =
    syntax_profile_with_weight owner (type_weight owner)

  (* Genuine helper programs still require complete intermediate instances,
     not just the final clause profile. These descriptors are being filled
     from the exact public Drule/Conv grammar before execute is exposed. *)
  fun immediate_dependencies (Proof {rule,...}) = case rule of
      Seed _ => [] | SeedFixed _ => [] | Specialize (_,p) => [p]
    | Generalize (_,p) => [p] | TypeInstance (_,p) => [p]
    | TermInstance (_,p) => [p]
    | EqualModusPonens (a,b) => [a,b] | ApplyFunction (_,p) => [p]
    | ApplyArgument (p,_) => [p] | AbstractEquality (_,p) => [p]
    | ContractBeta _ => []
    | ChooseWitness (_,a,b) => [a,b]
    | NegationEliminate p => [p]
    | SpecializeAll (_,p) => [p] | SelectLeft p => [p]
    | SelectRight p => [p] | Undisch p => [p] | Discharge (_,p) => [p]
    | Assume _ => [] | Conjoin (a,b) => [a,b] | DisjLeft (p,_) => [p]
    | DisjRight (_,p) => [p] | ModusPonens (a,b) => [a,b]
    | NotIntro p => [p] | ToTruth p => [p] | ToFalse p => [p]
    | Symmetry p => [p] | FlipLeftEquality p => [p]
    | QuantifyCondition (_,p) => [p] | ConjoinConditions (_,p) => [p]
    | ExistsIntroduction (_,_,p) => [p] | NegatedSymmetry p => [p]
    | ExpandAbbrev p => [p] | AbbrevFunctionEquality p => [p]
    | ExpandRestrictedForall p => [p] | FalseEquality (_,p) => [p]
    | TruthFalseEquality (_,_,p) => [p]

  fun materialize_type (HeldType ty) = ty
    | materialize_type (Arrow (a,b)) =
        Type.--> (materialize_type a,materialize_type b)
  fun materialize owner value =
    let val _ = active owner
        val answer = case value of
          Held (term,ty) =>
            let val actual = materialize_type ty in
              if Type.compare (Term.type_of term,actual) = EQUAL then term
              else if Term.is_var term then
                Term.mk_var (#1 (Term.dest_var term),actual)
              else if Term.is_const term then
                let val {Thy,Name,...} = Term.dest_thy_const term
                in Term.mk_thy_const {Thy=Thy,Name=Name,Ty=actual} end
              else raise ERR "materialize" "private leaf is not atomic"
            end
        | Application (f,x) =>
            Term.mk_comb (materialize owner f,materialize owner x)
        | Abstraction (v,b) =>
            Term.mk_abs (materialize owner v,materialize owner b)
        val _ = active owner
    in answer end
  fun invoke owner operation =
    (active owner;let val answer = operation ()
                 in active owner;answer end)
  fun retain_closure (owner as Owner {graph,scope,retained,...}) node =
    let
      val seen = ref ([] : G.node list)
      val pending = ref ([] : G.closure_child list)
      fun walk child =
        let val _ = active owner
            val n = G.closure_child_node graph scope child
        in if List.exists (fn old => n = old) (!seen) then () else
          (seen := n:: !seen;pending := child:: !pending;
           case G.view graph n of
             G.Application _ =>
               let val (f,x) = G.closure_application_children graph scope child
               in walk f;walk x end
           | G.AdmittedBinder _ =>
               let val binder = G.closure_child_binder graph scope child
               in walk (G.binder_closure_body graph scope binder) end
           | G.OpaqueRetained => raise ERR "retain_closure"
               "fixed rule requires a genuine complete opened recipe"
           | _ => ())
        end
    in walk (G.closure_root graph scope node);
       retained := !pending @ !retained;
       invalidate_backings owner;active owner end

  (* Quiet replay of ONLY the private recipe. No supplied normalizer, public
     Cond_rewr construction/application, Trace listener, HOL_ERR fallback or
     arbitrary theorem/node input is accepted. Library rules are fixed. *)
  fun replay owner memo value =
    let
      fun lookup [] = NONE
        | lookup ((held,result)::rest) =
            if Portable.pointer_eq (held,value) then SOME result
            else lookup rest
      val _ = active owner
      fun compute () =
    let
      val Proof {rule,...} = value
    in case rule of
      Seed fact => invoke owner (fn () => P.closed_original fact)
    | SeedFixed theorem => theorem
    | Specialize (v,p) => invoke owner (fn () =>
        Thm.SPEC (materialize owner v) (replay owner memo p))
    | Generalize (v,p) => invoke owner (fn () =>
        Thm.GEN (materialize owner v) (replay owner memo p))
    | TypeInstance (bindings,p) => invoke owner (fn () => Thm.INST_TYPE
        (List.map (fn (a,b) => {redex=a,residue=materialize_type b}) bindings)
        (replay owner memo p))
    | TermInstance (bindings,p) => invoke owner (fn () => Thm.INST
        (List.map (fn (a,b) =>
          {redex=materialize owner a,residue=materialize owner b}) bindings)
        (replay owner memo p))
    | EqualModusPonens (a,b) => invoke owner (fn () =>
        Thm.EQ_MP (replay owner memo a) (replay owner memo b))
    | ApplyFunction (f,p) => invoke owner (fn () =>
        Thm.AP_TERM (materialize owner f) (replay owner memo p))
    | ApplyArgument (p,x) => invoke owner (fn () =>
        Thm.AP_THM (replay owner memo p) (materialize owner x))
    | AbstractEquality (v,p) => invoke owner (fn () =>
        Thm.ABS (materialize owner v) (replay owner memo p))
    | ContractBeta redex => invoke owner (fn () =>
        Thm.BETA_CONV (materialize owner redex))
    | ChooseWitness (v,a,b) => invoke owner (fn () =>
        Thm.CHOOSE (materialize owner v,replay owner memo a) (replay owner memo b))
    | NegationEliminate p => invoke owner
        (fn () => Thm.NOT_ELIM (replay owner memo p))
    | SelectLeft p => invoke owner (fn () => Thm.CONJUNCT1 (replay owner memo p))
    | SelectRight p => invoke owner (fn () => Thm.CONJUNCT2 (replay owner memo p))
    | Discharge (ant,p) => invoke owner (fn () =>
        Thm.DISCH (materialize owner ant) (replay owner memo p))
    | Assume ant => invoke owner (fn () => Thm.ASSUME (materialize owner ant))
    | Conjoin (a,b) => invoke owner (fn () =>
        Thm.CONJ (replay owner memo a) (replay owner memo b))
    | DisjLeft (p,b) => invoke owner (fn () =>
        Thm.DISJ1 (replay owner memo p) (materialize owner b))
    | DisjRight (a,p) => invoke owner (fn () =>
        Thm.DISJ2 (materialize owner a) (replay owner memo p))
    | ModusPonens (a,b) => invoke owner (fn () =>
        Thm.MP (replay owner memo a) (replay owner memo b))
    | NotIntro p => invoke owner (fn () => Thm.NOT_INTRO (replay owner memo p))
    | Symmetry p => invoke owner (fn () => Thm.SYM (replay owner memo p))
    | ExistsIntroduction (ant,witness,p) => invoke owner (fn () =>
        Thm.EXISTS (materialize owner ant,materialize owner witness)
          (replay owner memo p))
    | _ => raise ERR "replay" "unexpanded private recipe"
    end
      val result = case lookup (!memo) of SOME answer => answer
        | NONE => let val answer = compute ()
                      val _ = active owner
                      val _ = memo := (value,answer):: !memo
                  in answer end
      val _ = active owner
    in result end

  fun prepare (owner as Owner {work,scope,graph,original,phase,check_type,...}) =
    protected owner (fn () => W.with_step work (fn () =>
      transaction owner (fn () =>
    let
      val _ = active owner
      val _ = if !phase = Fresh then phase := Prepared else
        raise ERR "prepare" "canonicalization attempt consumed"
      val original_rules = C.originals original
      val original_facts = C.checked_rules original
      val cap = IntInf.fromInt (#template_limit (W.semantic_limits work))
      val types = ref ([] : ty list)
      (* Private pointer membership only: no proof, Type-validator result,
         permission or future native quotation is cached by this index. *)
      val _ = active owner
      val _ = W.spend work 128
      val seen = Array.array (127,[] : proof list)
      val total = ref (0 : IntInf.int)
      (* One callback-free planning pass only. Cache successful immutable
         compound-Type weights, never annotation incidences, allowances or
         validator outcomes. Leaf weights retain their original direct
         inspection. Every annotation is still appended below, in order;
         policy calls and native Type materialization remain unchanged. *)
      (* Each basic block below is callback/native-effect free. Authenticate
         the owner before its reads and pay every performed operation; the
         miss transition can then debit its actual local index work without
         repeating the complete backing guard between those pure events. *)
      fun metadata amount = (active owner;W.spend work amount)
      val _ = metadata 9
      val weights = Array.array
        (8,NONE:(ty * IntInf.int) option)
      val _ = metadata 2
      val position = ref (0,0)
      val recent = ref (NONE:(ty * IntInf.int) option)
      (* The next overwritten slot is the oldest retained miss. Lookup
         visits the same last eight misses, newest first; hits do not move
         history. No prefix cells are copied on a successful miss. *)
      fun same_pointer (HeldType left,HeldType right) =
            Portable.pointer_eq (left,right)
        | same_pointer (left,right) = Portable.pointer_eq (left,right)
      fun weight value =
        let
          val _ = tick owner
          fun valid actual = if Type.uptodate_type actual then () else
            raise ERR "type_weight" "retired actual type"
          fun cached compute =
            let
              fun lookup () =
                let
                  (* State read and the initial newest-slot index. *)
                  val _ = metadata 3
                  val (next,count) = !position
                  val newest = if next=0 then 7 else next-1
                  fun scan 0 _ = (metadata 1;NONE)
                    | scan remaining index =
                        let
                          (* Actual indexed read, option selection and
                             exact-pointer comparison share one guard. *)
                          val _ = metadata 4
                          val (held,result) = case Array.sub (weights,index) of
                              SOME entry => entry
                            | NONE => raise ERR "prepare"
                                "unfilled type-weight history"
                        in if same_pointer (held,value) then
                             (active owner;SOME result)
                           else
                             let
                               (* The preceding owner guard still holds:
                                  only pure local metadata intervenes. *)
                               val _ = W.spend work 3
                               val previous = if index=0 then 7 else index-1
                             in scan (remaining-1) previous end
                        end
                in scan count newest end
              val found = case !recent of SOME (held,result) =>
                    if same_pointer (held,value) then SOME result else
                      lookup ()
                | NONE => lookup ()
            in case found of SOME result =>
                (active owner;recent := SOME (value,result);result)
              | NONE =>
                let val result = compute ()
                    (* Actual state read, pair/slot write, cursor and count
                       arithmetic, then state write; no native callback. *)
                    val _ = metadata 6
                    val (next,count) = !position
                    val _ = Array.update (weights,next,SOME (value,result))
                    val following = if next=7 then 0 else next+1
                    val _ = position := (following,Int.min (8,count+1))
                    val _ = active owner
                    val _ = recent := SOME (value,result)
                in result end
            end
        in case value of Arrow (left,right) =>
            cached (fn () => 1+weight left+weight right)
          | HeldType actual =>
            if Type.is_vartype actual then (valid actual;1)
            else case #Args (Type.dest_thy_typeid actual) of
                [] => (valid actual;1)
              | arguments => cached (fn () =>
                  (valid actual;List.foldl (fn (argument,total) =>
                    total+weight (HeldType argument))
                    (1:IntInf.int) arguments))
        end
      (* This callback-free pass frequently admits the very same bridge
         three times. Retain only its successful immutable syntax profile
         and its exact Type-incidence prefix. Every repeated native quote
         and every later Type callback remains in the original order. *)
      val previous_profile = ref
        (NONE : (syntax * profile * ty list * ty list) option)
      fun copy_annotations current stop tail =
        (tick owner;
         if Portable.pointer_eq (current,stop) then tail else
           case current of annotation::rest =>
             (tick owner;
              annotation::copy_annotations rest stop tail)
           | [] => raise ERR "prepare" "disconnected annotation prefix")
      fun admit value =
        let
          val _ = tick owner
          val prior_types = !types
          val cached = case !previous_profile of
              SOME (held,result,start,stop) =>
                if Portable.pointer_eq (held,value) then
                  let val copied = copy_annotations start stop prior_types
                      val _ = active owner
                      val _ = types := copied
                  in SOME result end
                else NONE
            | NONE => NONE
          val profile = case cached of SOME result => result
            | NONE => syntax_profile_with_weight owner weight types value
          val _ = if #raw profile <= cap andalso #inc profile <= cap then ()
            else raise ERR "prepare" "primitive rule result exceeds template"
          val _ = tick owner
          val _ = previous_profile := SOME (value,profile,!types,prior_types)
        in total := !total + #raw profile + #inc profile + #ann profile end
      (* This hint reads only the bounded private rule constructors. It
         cannot classify a theorem or authorize skipping a native quote.
         Every collision still checks the actual immutable proof pointer.
         No symbolic/native operand or binder body is copied or inspected. *)
      fun proof_hint value =
        let
          val _ = active owner
          (* No external callback/native mutation occurs in this metadata
             programme. Direct spends retain the original active Work. *)
          fun pay amount = W.spend work amount
          fun leaf code = (pay 1;(code,NONE,NONE))
          fun unary code child = (pay 2;(code,SOME child,NONE))
          fun binary code left right =
            (pay 3;(code,SOME left,SOME right))
          fun descriptor (Proof {rule,...}) =
            (pay 2;case rule of
                Seed _ => leaf 0 | SeedFixed _ => leaf 1
              | Specialize (_,p) => unary 2 p
              | Generalize (_,p) => unary 3 p
              | TypeInstance (_,p) => unary 4 p
              | TermInstance (_,p) => unary 5 p
              | EqualModusPonens (a,b) => binary 6 a b
              | ApplyFunction (_,p) => unary 7 p
              | ApplyArgument (p,_) => unary 8 p
              | AbstractEquality (_,p) => unary 9 p
              | ContractBeta _ => leaf 10
              | ChooseWitness (_,a,b) => binary 11 a b
              | NegationEliminate p => unary 12 p
              | SpecializeAll (_,p) => unary 13 p
              | SelectLeft p => unary 14 p | SelectRight p => unary 15 p
              | Undisch p => unary 16 p | Discharge (_,p) => unary 17 p
              | Assume _ => leaf 18 | Conjoin (a,b) => binary 19 a b
              | DisjLeft (p,_) => unary 20 p
              | DisjRight (_,p) => unary 21 p
              | ModusPonens (a,b) => binary 22 a b
              | NotIntro p => unary 23 p | ToTruth p => unary 24 p
              | ToFalse p => unary 25 p | Symmetry p => unary 26 p
              | FlipLeftEquality p => unary 27 p
              | QuantifyCondition (_,p) => unary 28 p
              | ConjoinConditions (_,p) => unary 29 p
              | ExistsIntroduction (_,_,p) => unary 30 p
              | NegatedSymmetry p => unary 31 p
              | ExpandAbbrev p => unary 32 p
              | AbbrevFunctionEquality p => unary 33 p
              | ExpandRestrictedForall p => unary 34 p
              | FalseEquality (_,p) => unary 35 p
              | TruthFalseEquality (_,_,p) => unary 36 p)
          fun sample depth proof =
            let val (code,left,right)=descriptor proof val _=pay 1
            in if depth=0 then (pay 1;code mod 127) else
              let fun child NONE=(pay 1;0)
                    | child(SOME held)=(pay 2;sample(depth-1)held)
                  val a=child left val b=child right val _=pay 5
              in (code+37*a+17*b) mod 127 end
            end
          val answer=sample 2 value
          val _=active owner
        in answer end
      fun visited value =
        let val index=proof_hint value
            val _=tick owner
            val rows=Array.sub(seen,index)
            fun lookup []=(active owner;false)
              | lookup(p::rest)=
                  (tick owner;Portable.pointer_eq(value,p)orelse lookup rest)
            val found=lookup rows
            val _=active owner
        in (index,found) end
      fun quote value =
        let val (bucket,known)=visited value
        in if known then () else
        let val Proof {rule,...} = value
            val _ = (case rule of
              SpecializeAll _ => raise ERR "quote" "unexpanded specialization"
            | Undisch _ => raise ERR "quote" "unexpanded undisch"
            | ToTruth _ => raise ERR "quote" "unexpanded EQT"
            | ToFalse _ => raise ERR "quote" "unexpanded EQF"
            | FlipLeftEquality _ => raise ERR "quote" "unexpanded left symmetry"
            | NegatedSymmetry _ => raise ERR "quote" "unexpanded negation"
            | ConjoinConditions _ => raise ERR "quote" "unexpanded conditions"
            | QuantifyCondition _ => raise ERR "quote" "unexpanded quantification"
            | ExpandAbbrev _ => raise ERR "quote" "unexpanded Abbrev"
            | AbbrevFunctionEquality _ => raise ERR "quote" "unexpanded FUN_EQ"
            | ExpandRestrictedForall _ => raise ERR "quote" "unexpanded restriction"
            | FalseEquality _ => raise ERR "quote" "unexpanded falsity"
            | TruthFalseEquality _ => raise ERR "quote" "unexpanded distinctness"
            | _ => ())
            val _ = List.app quote (immediate_dependencies value)
            val _ = admit (statement value)
            val _ = List.app admit (hypotheses value)
            (* SPEC/INST can discard an operand. Its full actual syntax and
               repeated types must still precede that public operation. *)
            val _ = (case rule of
              Specialize (v,_) => admit v
            | Generalize (v,_) => admit v
            | TypeInstance (bindings,_) => List.app (fn (a,b) =>
                let val x = weight (HeldType a)
                    val y = weight b
                in types := HeldType a::b:: !types;
                   total := !total+x+y end) bindings
            | TermInstance (bindings,_) => List.app
                (fn (a,b) => (admit a;admit b)) bindings
            | ApplyFunction (f,_) => admit f
            | ApplyArgument (_,x) => admit x
            | AbstractEquality (v,_) => admit v
            | ContractBeta redex => admit redex
            | ChooseWitness (v,_,_) => admit v
            | ExistsIntroduction (ant,v,_) => (admit ant;admit v)
            | _ => ())
            val _ = active owner
            val _ = W.spend work 4
            val _ = Array.update (seen,bucket,value::Array.sub (seen,bucket))
            val _ = active owner
        in () end end
      fun rows [] [] _ = []
        | rows (rule::rest) (fact::more) index =
            let fun phase label = diagnostic work label
                  (fn () => " row=" ^ Int.toString index)
                val _ = phase "row.before"
                val _ = tick owner
                val _ = P.validate_closed_fact graph scope
                  (IntInf.toInt cap) fact
                val _ = if Portable.pointer_eq (rule,P.closed_original fact)
                  then () else raise ERR "prepare" "stock original changed"
                val _ = retain_closure owner (P.closed_node fact)
                val seed = theorem (parse owner (Thm.concl rule)) [] (Seed fact)
                val _ = phase "row.seed.after"
                val implications = implication_canonical owner seed
                val equalities = List.concat
                  (List.map (equality_canonical owner) implications)
                val complete = List.map
                  (expand owner o quantify_conditions owner) equalities
                val _ = phase "row.canonical.after"
                fun record p =
                  let val _ = phase "clause.before"
                      val _ = quote p
                      (* Whole import/opened ALPHA correspondence, its
                         TRANS and closed EQ_MP result. No source ASSUME. *)
                      val bridge = equality (statement p) (statement p)
                      val _ = List.app admit [bridge,bridge,bridge,statement p]
                      val _ = if null (hypotheses p) then () else
                        raise ERR "prepare" "canonical stock clause not closed"
                      val _ = phase "clause.profile.after"
                  in (index,rule,p) end
            in List.map record complete @ rows rest more (index+1) end
        | rows _ _ _ = raise ERR "prepare" "stock catalogue incidence differs"
      val prepared = rows original_rules original_facts 0
      val _ = diagnostic work "rows.after" (fn () =>
        " quote=" ^ IntInf.toString (!total) ^
        " callbacks=" ^ Int.toString (List.length (!types)))
      val _ = if !total <= IntInf.fromInt (W.work_limit work) then
          W.spend work (IntInf.toInt (!total))
        else raise ERR "prepare" "primitive portfolio exceeds original Work"
      val _ = diagnostic work "quote.debit.after" (fn () => "")
      fun policy ty =
        let val _ = active owner
            val actual = materialize_type ty
            val _ = active owner
            val _ = external owner (fn () => check_type actual)
            val _ = active owner
        in () end
      val _ = List.app policy (List.rev (!types))
      val _ = diagnostic work "policies.after" (fn () => "")
      val _ = active owner
    in Plan {owner=owner,rows=prepared,used=ref false} end)))

  fun execute (Plan {owner=owner as Owner
      {work,graph,scope,phase,check_type,...},rows,used}) =
    protected owner (fn () => W.with_step work (fn () =>
      transaction owner (fn () =>
    let
      val _ = active owner
      val _ = if !phase = Prepared andalso not (!used) then
        (used := true;phase := Executed)
        else raise ERR "execute" "canonicalization plan consumed"
      val cap = #template_limit (W.semantic_limits work)
      val memo = ref ([] : (proof * Thm.thm) list)
      (* Only completed private proofs are memoized; active guards run before
         and after every hit. Nothing is cached across a policy without
         owner/epochs/all retained input and output frame revalidation. *)
      fun policy ty = external owner (fn () => check_type ty)
      fun close (_,_,p) =
        let val theorem = invoke owner (fn () => replay owner memo p)
            val _ = if null (Thm.hyp theorem) then () else
              raise ERR "execute" "canonical clause acquired hypotheses"
            val source = invoke owner (fn () =>
              G.import graph scope cap (Thm.concl theorem))
            val opened = invoke owner (fn () =>
              G.record_opened_view graph scope cap (#node source))
            val _ = retain_closure owner (#node opened)
            val fact = invoke owner (fn () => P.record_closed_from_import
              graph scope {node= #node opened,theorem=theorem,
                template_limit=cap,check_type=policy})
        in (theorem,fact) end
      val results = List.map close rows
    in Catalogue {owner=owner,origins=List.map
      (fn (index,original,_) => (index,original)) rows,
      rules=List.map #1 results,facts=List.map #2 results} end)))
  fun validate_for expected
      (Catalogue {owner=owner as Owner {work,...},...}) =
    ((ignore (W.original_sources expected);
      if Portable.pointer_eq (expected,work) then active owner else
        raise ERR "validate_for" "foreign canonical catalogue")
     handle primary => (W.close expected;raise primary))
  fun originals (Catalogue {owner,rules,...}) = (active owner;rules)
  fun checked_rules (Catalogue {owner,facts,...}) = (active owner;facts)
  fun origins (Catalogue {owner,origins,...}) = (active owner;origins)
  structure RP=SmtReplayResourcePolicy
  structure NC=SmtReplayNativeContract
  datatype phase = Fresh | Prepared | Executed | Retired
  datatype policy_owner = PolicyOwner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     original : C.policy_catalogue,phase : phase ref,symbols : int,
     check_type : Type.hol_type -> unit,
     retained : G.closure_child list ref,
     validation_depth : int ref,validation_generation : IntInf.int ref,
     validated : IntInf.int ref,validated_retirement : IntInf.int ref,
     native_contract:NC.contract,native_events:IntInf.int ref}
  fun retire (PolicyOwner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected policy_owner action = action () handle primary =>
    (retire policy_owner;raise primary)
  (* Complete backing validation is retained under a genuine graph retirement
     witness. Exact policy_owner/Type/Term/root checks still run every time. *)
  fun cheap (policy_owner as PolicyOwner
      {work,graph,scope,sources,phase,symbols,native_contract,...}) =
    protected policy_owner (fn () =>
      (if !phase = Retired then raise ERR "active"
        "canonical policy_owner retired"
       else ();
       W.validate_policy work graph scope sources (W.semantic_policy work);
       NC.validate_for work native_contract;
       if Term.term_epoch () = symbols then () else
         raise ERR "active" "constant retirement epoch changed"))
  fun invalidate (PolicyOwner {validation_generation,...}) =
    validation_generation := !validation_generation + 1
  fun active (policy_owner as PolicyOwner
      {work,graph,scope,original,retained,validation_generation,
       validated,validated_retirement,...}) =
    protected policy_owner (fn () =>
      let val _ = cheap policy_owner
          val observed = G.scope_retirement_epoch graph scope
          (* Frame/node/closure geometry is immutable after fresh creation.
             Every actual retirement changes this authentic graph witness.
             Type/Term and Work guards are never cached. *)
          val _ = if !validated_retirement = observed then () else
            (C.validate_with_policy_for work original;
             guard_app work (fn child => ignore
               (G.closure_child_node graph scope child)) (!retained);
             cheap policy_owner;
             if G.scope_retirement_epoch graph scope = observed then () else
               raise ERR "active" "scope retirement during backing pass";
             validated_retirement := observed)
      in validated := !validation_generation end)
  fun invalidate_backings (policy_owner as PolicyOwner
    {validated_retirement,...}) =
    (validated_retirement := ~1;invalidate policy_owner)
  fun transaction (policy_owner as PolicyOwner {validation_depth,...})
    operation =
    let val saved = !validation_depth
        val _ = active policy_owner
        val _ = if saved = 0 then invalidate policy_owner else ()
        val _ = validation_depth := saved+1
        fun restore () = validation_depth := saved
    in (let val _ = active policy_owner
            val answer = operation ()
            val _ = restore ()
            val _ = active policy_owner
        in answer end) handle primary => (restore ();raise primary)
    end
  (* Policies never reuse a pure-pass stamp. A returning child retirement
     changes the graph witness, forcing the full actual backing check. *)
  fun external (policy_owner as PolicyOwner {validation_depth,...}) operation =
    let val saved = !validation_depth
        val _ = validation_depth := 0
        val _ = invalidate policy_owner
        fun restore () = (validation_depth := saved;invalidate policy_owner)
    in (let val _ = active policy_owner
            val answer = operation ()
            val _ = active policy_owner
            val _ = restore ()
        in answer end) handle primary => (restore ();raise primary)
    end
  fun tick (policy_owner as PolicyOwner
      {work,native_contract,native_events,...}) =
    (active policy_owner;
     if !native_events<IntInf.fromInt
         (#type_work_limit (NC.for_work work native_contract)) then () else
       raise ERR "tick" "native planning allowance exhausted";
     native_events:= !native_events+1;
     W.spend_policy work 1;active policy_owner)
  fun begin_with_policy work original {check_type} =
    let val _ = C.validate_with_policy_for work original
        val native_contract=C.native_contract_for work original
        val sources = W.original_sources work
        val graph = S.owning_graph sources
        val scope = S.owning_scope sources
    in PolicyOwner {work = work,graph = graph,scope = scope,sources = sources,
      original = original,phase = ref Fresh,symbols = Term.term_epoch (),
      check_type = check_type,retained = ref [],
      validation_depth = ref 0,validation_generation = ref 0,
      validated = ref (~1),validated_retirement = ref (~1),
      native_contract=native_contract,native_events=ref 0} end
    handle primary => (W.close work;raise primary)

  (* Types of FUTURE logical headers stay DATA until the complete quote.
     Actual original variable/constant types retain their declaration IDs. *)
  datatype ty = HeldType of Type.hol_type | Arrow of ty * ty
  datatype syntax = Held of Term.term * ty | Application of syntax * syntax
    | Abstraction of syntax * syntax
  datatype rule = Seed of P.closed_fact | SeedFixed of Thm.thm
    | Specialize of syntax * proof | Generalize of syntax * proof
    | TypeInstance of (Type.hol_type * ty) list * proof
    | TermInstance of (syntax * syntax) list * proof
    | EqualModusPonens of proof * proof
    | ApplyFunction of syntax * proof | ApplyArgument of proof * syntax
    | AbstractEquality of syntax * proof | ContractBeta of syntax
    | ChooseWitness of syntax * proof * proof
    | NegationEliminate of proof
    | SpecializeAll of syntax list * proof
    | SelectLeft of proof | SelectRight of proof
    | Undisch of proof | Discharge of syntax * proof
    | Assume of syntax | Conjoin of proof * proof
    | DisjLeft of proof * syntax | DisjRight of syntax * proof
    | ModusPonens of proof * proof | NotIntro of proof
    | ToTruth of proof | ToFalse of proof | Symmetry of proof
    | FlipLeftEquality of proof | QuantifyCondition of syntax * proof
    | ConjoinConditions of syntax list * proof
    | ExistsIntroduction of syntax * syntax * proof | NegatedSymmetry of proof
    | ExpandAbbrev of proof | AbbrevFunctionEquality of proof
    | ExpandRestrictedForall of proof
    | FalseEquality of syntax * proof
    | TruthFalseEquality of bool * syntax * proof
  and proof = Proof of {conclusion : syntax,hypotheses : syntax list,
                       rule : rule}
  type profile = {raw : IntInf.int,inc : IntInf.int,ann : IntInf.int}
  datatype policy_plan = PolicyPlan of {policy_owner : policy_owner,
    rows : (int * Thm.thm * proof) list,used : bool ref}
  datatype policy_catalogue = PolicyCatalogue of {policy_owner : policy_owner,
    origins_with_policy : (int * Thm.thm) list,rules : Thm.thm list,
    facts : P.closed_fact list}
  fun statement (Proof {conclusion,...}) = conclusion
  fun hypotheses (Proof {hypotheses,...}) = hypotheses
  fun type_of (Held (_,ty)) = ty
    | type_of (Application (f,_)) =
        (case type_of f of Arrow (_,result) => result
         | HeldType ty => HeldType (#2 (Type.dom_rng ty)))
    | type_of (Abstraction (v,b)) = Arrow (type_of v,type_of b)
  val boolean = HeldType Type.bool
  fun constant term = Held (term,HeldType (Term.type_of term))
  fun unary term operand = Application (constant term,operand)
  fun binary term left right =
    Application (Application (constant term,left),right)
  fun implication a b = binary boolSyntax.implication a b
  fun conjunction a b = binary boolSyntax.conjunction a b
  fun disjunction a b = binary boolSyntax.disjunction a b
  fun negation a = unary boolSyntax.negation a
  (* Polymorphic equality headers use the exact operand type, not the
     pre-instantiated equality constant's generic type. *)
  fun equality a b =
    Application (Application
      (Held (boolSyntax.equality,
        Arrow (type_of a,Arrow (type_of a,boolean))),a),b)
  fun quantifier head v body = Application
    (Held (head,Arrow (Arrow (type_of v,boolean),boolean)),
     Abstraction (v,body))
  fun truth () = constant boolSyntax.T
  fun falsity () = constant boolSyntax.F

  fun parse policy_owner term =
    let val _ = tick policy_owner
        val ty = HeldType (Term.type_of term)
    in if Term.is_comb term then
         let val (f,x) = Term.dest_comb term
         in Application (parse policy_owner f,parse policy_owner x) end
       else if Term.is_abs term then
         let val (v,b) = Term.dest_abs term
         in Abstraction (parse policy_owner v,parse policy_owner b) end
       else Held (term,ty) end
  fun head_is policy_owner thy name (Held (term,_)) =
        (tick policy_owner;
         if Term.is_const term then
           let val value = Term.dest_thy_const term
           in #Thy value = thy andalso #Name value = name end
         else false)
    | head_is _ _ _ _ = false
  fun unary_view policy_owner thy name (Application (f,x)) =
        if head_is policy_owner thy name f then SOME x else NONE
    | unary_view _ _ _ _ = NONE
  fun binary_view policy_owner thy name (Application (Application (f,x),y)) =
        if head_is policy_owner thy name f then SOME (x,y) else NONE
    | binary_view _ _ _ _ = NONE
  fun is_variable policy_owner (Held (term,_)) = (tick
    policy_owner;Term.is_var term)
    | is_variable _ _ = false
  fun is_constant policy_owner (Held (term,_)) = (tick
    policy_owner;Term.is_const term)
    | is_constant _ _ = false
  (* Exact original VAR/type comparison after the complete source portfolio
     has been admitted. Bound variables are paired separately in alpha. *)
  fun variable_equal policy_owner (Held (left,a),Held (right,b)) =
        (tick policy_owner;Term.is_var left andalso Term.is_var right andalso
         #1 (Term.dest_var left) = #1 (Term.dest_var right) andalso
         type_equal policy_owner (a,b))
    | variable_equal _ _ = false
  and type_equal policy_owner (HeldType a,HeldType b) =
        (tick policy_owner;Type.compare (a,b) = EQUAL)
    | type_equal policy_owner (Arrow (a,b),Arrow (c,d)) =
        type_equal policy_owner (a,c) andalso type_equal policy_owner (b,d)
    | type_equal policy_owner (HeldType a,b) =
        if Type.is_vartype a then false else
          let val shape = Type.dest_thy_type a
          in if #Thy shape = "min" andalso #Tyop shape = "fun" then
               let val (x,y) = Type.dom_rng a
               in type_equal policy_owner (Arrow (HeldType x,HeldType y),b) end
             else false end
    | type_equal policy_owner (a,HeldType b) = type_equal policy_owner
      (HeldType b,a)
  fun alpha policy_owner left right =
    let
      fun lookup _ [] = NONE
        | lookup value ((a,b)::rest) =
            if variable_equal policy_owner (value,a) then SOME b
            else lookup value rest
      fun same bound a b =
        (tick policy_owner;
         if not (type_equal policy_owner (type_of a,type_of b)) then false else
         case (a,b) of
           (Application (f,x),Application (g,y)) =>
             same bound f g andalso same bound x y
         | (Abstraction (v,x),Abstraction (w,y)) => same ((v,w)::bound) x y
         | (Held (x,_),Held (y,_)) =>
             (case lookup a bound of SOME target =>
                variable_equal policy_owner (target,b)
              | NONE => if Term.is_var x then variable_equal policy_owner (a,b)
                else Term.is_const x andalso Term.is_const y andalso
                  KernelSig.id_compare
                    (#Name (Term.dest_thy_constid x),
                     #Name (Term.dest_thy_constid y)) = EQUAL)
         | _ => false)
    in same [] left right end
  fun member policy_owner value values = List.exists (alpha policy_owner
    value) values
  fun union policy_owner left right = List.foldl (fn (v,acc) =>
    if member policy_owner v acc then acc else v::acc) right left
  fun free policy_owner value =
    let fun visit bound current found =
      (tick policy_owner;case current of
         Application (f,x) => visit bound x (visit bound f found)
       | Abstraction (v,b) => visit (v::bound) b found
       | Held _ => if is_variable policy_owner current andalso
           not (member policy_owner current bound) andalso
           not (member policy_owner current found) then current::found else
             found)
    in List.rev (visit [] value []) end
  fun free_hyp policy_owner proof =
    List.foldl (fn (h,acc) => union policy_owner (free policy_owner h) acc) []
      (hypotheses proof)
  fun theorem conclusion hyps rule =
    Proof {conclusion = conclusion,hypotheses = hyps,rule = rule}
  fun assumption value = theorem value [value] (Assume value)
  fun discharge policy_owner value proof = theorem
    (implication value (statement proof))
    (List.filter (fn h => not (alpha policy_owner value h)) (hypotheses proof))
    (Discharge (value,proof))
  fun undisch policy_owner proof =
    case binary_view policy_owner "min" "==>" (statement proof) of
      SOME (ant,body) => theorem body
        (union policy_owner [ant] (hypotheses proof)) (Undisch proof)
    | NONE => raise ERR "undisch" "private non-implication recipe"
  fun mp policy_owner law argument =
    case binary_view policy_owner "min" "==>" (statement law) of
      SOME (ant,body) => if alpha policy_owner ant (statement argument) then
        theorem body (union policy_owner (hypotheses law) (hypotheses
          argument))
          (ModusPonens (law,argument))
        else raise ERR "mp" "private antecedent recipe mismatch"
    | NONE => raise ERR "mp" "private rule is not implication"
  fun sym policy_owner proof =
    case binary_view policy_owner "min" "=" (statement proof) of
      SOME (left,right) => theorem (equality right left) (hypotheses proof)
        (Symmetry proof)
    | NONE => raise ERR "sym" "private non-equation recipe"
  fun eqt proof = theorem (equality (statement proof) (truth ()))
    (hypotheses proof) (ToTruth proof)
  fun eqf policy_owner proof = case unary_view policy_owner "bool" "~"
    (statement proof) of
      SOME value => theorem (equality value (falsity ())) (hypotheses proof)
        (ToFalse proof)
    | NONE => raise ERR "eqf" "private non-negation recipe"

  fun substitute policy_owner variable replacement value =
    if variable_equal policy_owner (variable,value) then replacement else
      (tick policy_owner;case value of
         Application (f,x) => Application
           (substitute policy_owner variable replacement f,
            substitute policy_owner variable replacement x)
       | Abstraction (v,b) => if variable_equal policy_owner (variable,v) then
         value
           else if member policy_owner v (free policy_owner replacement)
             andalso
                   member policy_owner variable (free policy_owner b) then
             let val avoid = union policy_owner (free policy_owner b)
                   (free policy_owner replacement)
                 val term = case v of Held (t,_) => t
                   | _ => raise ERR "substitute" "private binder not atomic"
                 val terms = List.map (fn Held (t,_) => t
                   | _ => raise ERR "substitute" "private variable not atomic")
                   avoid
                 val _ = tick policy_owner
                 val next = Held (Term.prim_variant terms term,type_of v)
                 val _ = active policy_owner
                 val renamed = substitute policy_owner v next b
             in Abstraction
               (next,substitute policy_owner variable replacement renamed) end
           else Abstraction (v,substitute policy_owner variable replacement b)
       | Held _ => value)
  fun actual_variable (Held (term,_)) = term
    | actual_variable _ = raise ERR "variable" "private non-held variable"
  fun ordered_variables policy_owner values =
    Listsort.sort (fn (a,b) =>
      (tick policy_owner;Term.compare (actual_variable a,actual_variable b)))
        values
  fun vary policy_owner avoid variable =
    let val term = actual_variable variable
        val args = List.map actual_variable avoid
        val _ = tick policy_owner
        (* Only a held original VAR type is reused. No theorem or type
           constructor is invoked here. The name-search work will be quoted
           from the actual finite avoidance portfolio before this call. *)
        val answer = Term.prim_variant args term
        val _ = active policy_owner
    in Held (answer,type_of variable) end
  fun specialize_all policy_owner proof =
    let
      fun collect value = case unary_view policy_owner "bool" "!" value of
          SOME (Abstraction (v,b)) =>
            let val (vars,body) = collect b in (v::vars,body) end
        | SOME _ => raise ERR "specialize_all" "forall lacks a lambda"
        | NONE => ([],value)
      val (variables,body) = collect (statement proof)
      val avoid = ordered_variables policy_owner (free_hyp policy_owner proof)
        @
        ordered_variables policy_owner (free policy_owner (statement proof))
      val (_,variants) = List.foldr (fn (v,(held,chosen)) =>
        let val next = vary policy_owner held v
        in (next::held,next::chosen) end) (avoid,[]) variables
      val answer = ListPair.foldlEq (fn (v,x,b) =>
        substitute policy_owner v x b) body (variables,variants)
    in if null variables then proof else theorem answer (hypotheses proof)
      (SpecializeAll (variants,proof)) end
  fun select policy_owner left proof =
    case binary_view policy_owner "bool" "/\\" (statement proof) of
      SOME (a,b) => theorem (if left then a else b) (hypotheses proof)
        (if left then SelectLeft proof else SelectRight proof)
    | NONE => raise ERR "select" "private non-conjunction recipe"
  fun conj policy_owner left right = theorem
    (conjunction (statement left) (statement right))
    (union policy_owner (hypotheses left) (hypotheses right)) (Conjoin
      (left,right))
  fun not_intro policy_owner proof =
    case binary_view policy_owner "min" "==>" (statement proof) of
      SOME (ant,body) => if alpha policy_owner body (falsity ()) then
        theorem (negation ant) (hypotheses proof) (NotIntro proof)
        else raise ERR "not_intro" "private consequent is not F"
    | NONE => raise ERR "not_intro" "private non-implication recipe"
  fun all_undisch policy_owner proof =
    case binary_view policy_owner "min" "==>" (statement proof) of
      SOME _ => all_undisch policy_owner (undisch policy_owner proof) | NONE
        => proof
  fun conditions policy_owner proof =
    let fun collect value = case binary_view policy_owner "min" "==>" value of
          SOME (a,b) => let val (ants,result) = collect b
                        in (a::ants,result) end
        | NONE => ([],value)
    in collect (statement proof) end
  fun conjoined_conditions policy_owner ants proof =
    (* Cond_rewr.CONJ_DISCH uses itlist, making a RIGHT-associated ordered
       antecedent. Keep empty and singleton cases exact. *)
    case ants of [] => proof
    | [one] => discharge policy_owner one proof
    | first::rest =>
        let val ant = List.foldr (fn (a,b) => conjunction a b)
              (List.last rest) (first::List.take (rest,length rest-1))
            val hyps = List.filter (fn h => not (member policy_owner h ants))
              (hypotheses proof)
        in theorem (implication ant (statement proof)) hyps
          (ConjoinConditions (ants,proof)) end

  (* Every expanded recipe below is a kernel primitive, with its EXACT
     proposition and hypotheses retained before replay. SeedFixed is private
     and called only with the listed sealed bool/marker theorems. *)
  fun seed_fixed policy_owner th =
    (tick policy_owner;
     if null (Thm.hyp th) andalso Term.uptodate_term (Thm.concl th) then
       theorem (parse policy_owner (Thm.concl th)) [] (SeedFixed th)
     else raise ERR "seed_fixed" "stale or non-closed fixed helper")
  fun spec policy_owner arg p =
    case unary_view policy_owner "bool" "!" (statement p) of
      SOME (Abstraction (v,b)) =>
        if type_equal policy_owner (type_of v,type_of arg) then
          theorem (substitute policy_owner v arg b) (hypotheses p)
            (Specialize (arg,p))
        else raise ERR "spec" "private specialization type differs"
    | _ => raise ERR "spec" "private helper has no leading forall"
  fun gen policy_owner v p =
    if member policy_owner v (free_hyp policy_owner p) then
      raise ERR "gen" "private variable is free in hypotheses"
    else theorem (quantifier boolSyntax.universal v (statement p))
      (hypotheses p) (Generalize (v,p))
  fun eq_mp policy_owner a b = case binary_view policy_owner "min" "="
    (statement a) of
      SOME (l,r) => if alpha policy_owner l (statement b) then
        theorem r (union policy_owner (hypotheses a) (hypotheses b))
          (EqualModusPonens (a,b))
        else raise ERR "eq_mp" "private proposition mismatch"
    | NONE => raise ERR "eq_mp" "private non-equation helper"
  fun not_elim policy_owner p = case unary_view policy_owner "bool" "~"
    (statement p) of
      SOME a => theorem (implication a (falsity ())) (hypotheses p)
        (NegationEliminate p)
    | NONE => raise ERR "not_elim" "private non-negation"
  fun substitute_type policy_owner bindings shape =
    let fun actual ty =
      if Type.is_vartype ty then
        let fun find [] = HeldType ty
              | find ((a,b)::rest) =
                  (tick policy_owner;if Type.compare (a,ty) = EQUAL then b
                   else find rest)
        in find bindings end
      else let val view = Type.dest_thy_type ty in
        if #Thy view = "min" andalso #Tyop view = "fun" then
          let val (a,b) = Type.dom_rng ty in Arrow (actual a,actual b) end
        else HeldType ty end
    in case shape of HeldType ty => actual ty
      | Arrow (a,b) => Arrow (substitute_type policy_owner bindings a,
                              substitute_type policy_owner bindings b) end
  fun inst_type policy_owner bindings p =
    let fun visit value =
      (tick policy_owner;case value of
         Held (term,ty) => Held (term,substitute_type policy_owner bindings ty)
       | Application (f,x) => Application (visit f,visit x)
       | Abstraction (v,b) => Abstraction (visit v,visit b))
    in theorem (visit (statement p)) (List.map visit (hypotheses p))
      (TypeInstance (bindings,p)) end
  fun inst_term policy_owner bindings p =
    let
      val avoid = List.foldl (fn ((_,range),acc) =>
        union policy_owner (free policy_owner range) acc) [] bindings
      fun lookup value [] = NONE
        | lookup value ((key,range)::rest) =
            if variable_equal policy_owner (key,value) then SOME range
            else lookup value rest
      fun visit rows value = case lookup value rows of SOME range => range
        | NONE => (tick policy_owner;case value of
            Application (f,x) => Application (visit rows f,visit rows x)
          | Abstraction (v,b) =>
              let val nested = List.filter
                    (fn (key,_) => not (variable_equal policy_owner (key,v)))
                      rows
                  val fresh = if member policy_owner v avoid then
                    vary policy_owner (union policy_owner avoid (free
                      policy_owner b)) v else v
                  val body = if variable_equal policy_owner (fresh,v) then b
                    else substitute policy_owner v fresh b
              in Abstraction (fresh,visit nested body) end
          | Held _ => value)
    in theorem (visit bindings (statement p))
      (List.map (visit bindings) (hypotheses p)) (TermInstance (bindings,p))
    end
  fun apply_function policy_owner f p =
    case binary_view policy_owner "min" "=" (statement p) of
      SOME (a,b) => theorem
        (equality (Application (f,a)) (Application (f,b))) (hypotheses p)
        (ApplyFunction (f,p))
    | NONE => raise ERR "apply_function" "private helper is not equality"
  fun apply_argument policy_owner p x =
    case binary_view policy_owner "min" "=" (statement p) of
      SOME (a,b) => theorem
        (equality (Application (a,x)) (Application (b,x))) (hypotheses p)
        (ApplyArgument (p,x))
    | NONE => raise ERR "apply_argument" "private helper is not equality"
  fun abstract policy_owner v p =
    case binary_view policy_owner "min" "=" (statement p) of
      SOME (a,b) => theorem
        (equality (Abstraction (v,a)) (Abstraction (v,b))) (hypotheses p)
        (AbstractEquality (v,p))
    | NONE => raise ERR "abstract" "private helper is not equality"
  fun beta policy_owner redex = case redex of
      Application (Abstraction (v,b),x) => theorem
        (equality redex (substitute policy_owner v x b)) [] (ContractBeta
          redex)
    | _ => raise ERR "beta" "private non-beta expression"
  fun symmetry_conversion policy_owner left right =
    let val basis = seed_fixed policy_owner boolTheory.EQ_SYM_EQ
        val typed = inst_type policy_owner [(Type.alpha,type_of left)] basis
    in spec policy_owner right (spec policy_owner left typed) end
  fun truth_basis policy_owner negative =
    let val basis = seed_fixed policy_owner boolTheory.EQ_CLAUSES
        val variable = case unary_view policy_owner "bool" "!" (statement
          basis) of
            SOME (Abstraction (v,_)) => v
          | _ => raise ERR "truth_basis" "fixed EQ_CLAUSES shape changed"
        val all = spec policy_owner variable basis
        fun fourth p = select policy_owner false
          (select policy_owner false (select policy_owner false p))
        val chosen = if negative then fourth all
          else select policy_owner true (select policy_owner false all)
    in gen policy_owner variable (sym policy_owner chosen) end
  fun flatten_conjunction policy_owner p =
    case binary_view policy_owner "bool" "/\\" (statement p) of
      NONE => [p]
    | SOME _ => flatten_conjunction policy_owner (select policy_owner true p) @
        flatten_conjunction policy_owner (select policy_owner false p)
  fun conjunct_n policy_owner n p = List.nth (flatten_conjunction policy_owner
    p,n)
  fun primitive_conditions policy_owner ants p = case ants of [] => p
    | [a] => discharge policy_owner a p
    | a::rest =>
        let val tail = primitive_conditions policy_owner rest p
            val current = discharge policy_owner a tail
            val (b,c) = case binary_view policy_owner "min" "==>"
                (statement tail) of SOME pair => pair
              | NONE => raise ERR "conditions" "private tail missing"
            val helper = List.foldl (fn (x,h) => spec policy_owner x h)
              (seed_fixed policy_owner boolTheory.AND_IMP_INTRO) [a,b,c]
        in eq_mp policy_owner helper current end
  fun function_parts (Arrow (a,b)) = (a,b)
    | function_parts (HeldType ty) =
        let val (a,b) = Type.dom_rng ty in (HeldType a,HeldType b) end
  fun leading_variable policy_owner p =
    case unary_view policy_owner "bool" "!" (statement p) of
      SOME (Abstraction (v,_)) => v
    | _ => raise ERR "leading_variable" "private forall missing"
  fun function_equality policy_owner p =
    let val (left,right) = case binary_view policy_owner "min" "="
            (statement p) of SOME pair => pair
          | NONE => raise ERR "function_equality" "private equality missing"
    in case right of Abstraction _ =>
      let val (domain,range) = function_parts (type_of right)
          val law = inst_type policy_owner
            [(Type.alpha,domain),(Type.beta,range)]
            (seed_fixed policy_owner boolTheory.FUN_EQ_THM)
          val applied = eq_mp policy_owner
            (spec policy_owner right (spec policy_owner left law)) p
          val variable = leading_variable policy_owner applied
          val pointwise = spec policy_owner variable applied
          val right_app = Application (right,variable)
          val left_app = Application (left,variable)
          val equality_function = Held (boolSyntax.equality,
            Arrow (range,Arrow (range,boolean)))
          val partial = Application (equality_function,left_app)
          val contracted = eq_mp policy_owner
            (apply_function policy_owner partial (beta policy_owner
              right_app)) pointwise
      in gen policy_owner variable (function_equality policy_owner contracted)
        end
    | _ => sym policy_owner p
    end
  fun abbrev_equality policy_owner p =
    let val operand = case unary_view policy_owner "marker" "Abbrev"
            (statement p) of SOME value => value
          | NONE => raise ERR "abbrev_equality" "Abbrev operand missing"
        val initial = seed_fixed policy_owner markerTheory.Abbrev_def
        val helper = case unary_view policy_owner "bool" "!" (statement
          initial) of
            SOME _ => spec policy_owner operand initial
          | NONE => (case free policy_owner (statement initial) of
              [variable] => inst_term policy_owner [(variable,operand)] initial
            | _ => raise ERR "abbrev_equality" "fixed definition changed")
    in eq_mp policy_owner helper p end
  fun restricted_forall policy_owner p =
    let val (guard,predicate) = case binary_view policy_owner "bool"
      "RES_FORALL"
            (statement p) of SOME pair => pair
          | NONE => raise ERR "restricted_forall" "restricted forall missing"
        val (domain,_) = function_parts (type_of predicate)
        val basis = inst_type policy_owner [(Type.alpha,domain)]
          (seed_fixed policy_owner boolTheory.RES_FORALL_THM)
        val helper = spec policy_owner predicate (spec policy_owner guard
          basis)
        val generalized = eq_mp policy_owner helper p
        val variable = leading_variable policy_owner generalized
        val pointwise = spec policy_owner variable generalized
        val test = Application (guard,variable)
        val partial = Application (constant boolSyntax.implication,test)
        val contracted = eq_mp policy_owner
          (apply_function policy_owner partial
            (beta policy_owner (Application (predicate,variable)))) pointwise
    in gen policy_owner variable contracted end
  fun expand policy_owner value =
    let val Proof {conclusion,hypotheses=held_hypotheses,rule} = value
        fun unary make p = make (expand policy_owner p)
    in case rule of
      Seed _ => value | SeedFixed _ => value
    | SpecializeAll (variants,p) => List.foldl
        (fn (v,h) => spec policy_owner v h) (expand policy_owner p) variants
    | SelectLeft p => select policy_owner true (expand policy_owner p)
    | SelectRight p => select policy_owner false (expand policy_owner p)
    | Undisch p =>
        let val base = expand policy_owner p
            val ant = case binary_view policy_owner "min" "==>" (statement
              base) of
                SOME (a,_) => a
              | NONE => raise ERR "expand" "missing antecedent"
        in mp policy_owner base (assumption ant) end
    | Discharge (ant,p) => discharge policy_owner ant (expand policy_owner p)
    | Assume _ => value
    | Conjoin (a,b) => conj policy_owner (expand policy_owner a) (expand
      policy_owner b)
    | DisjLeft (p,b) => theorem conclusion held_hypotheses
        (DisjLeft (expand policy_owner p,b))
    | DisjRight (a,p) => theorem conclusion held_hypotheses
        (DisjRight (a,expand policy_owner p))
    | ModusPonens (a,b) => mp policy_owner (expand policy_owner a) (expand
      policy_owner b)
    | NotIntro p => not_intro policy_owner (expand policy_owner p)
    | ToTruth p => let val base = expand policy_owner p
        in eq_mp policy_owner (spec policy_owner (statement base) (truth_basis
          policy_owner false))
          base end
    | ToFalse p =>
        let val base = expand policy_owner p
            val body = case unary_view policy_owner "bool" "~" (statement
              base) of
                SOME b => b | NONE => raise ERR "expand" "negation missing"
        in eq_mp policy_owner (spec policy_owner body (truth_basis
          policy_owner true)) base end
    | Symmetry p => sym policy_owner (expand policy_owner p)
    | ConjoinConditions (ants,p) =>
        primitive_conditions policy_owner ants (expand policy_owner p)
    | FlipLeftEquality p =>
        let val base = expand policy_owner p
            val (inner,r) = case binary_view policy_owner "min" "="
                (statement base) of SOME pair => pair
              | NONE => raise ERR "expand" "outer equality missing"
            val (a,b) = case binary_view policy_owner "min" "=" inner of
                SOME pair => pair
              | NONE => raise ERR "expand" "inner equality missing"
            val function = Held (boolSyntax.equality,
              Arrow (boolean,Arrow (boolean,boolean)))
            val converted = apply_argument policy_owner
              (apply_function policy_owner function (symmetry_conversion
                policy_owner a b)) r
        in eq_mp policy_owner converted base end
    | NegatedSymmetry p =>
        let val base = expand policy_owner p
            val inner = case unary_view policy_owner "bool" "~" (statement
              base) of
                SOME b => b | NONE => raise ERR "expand" "negation missing"
            val (a,b) = case binary_view policy_owner "min" "=" inner of
                SOME pair => pair
              | NONE => raise ERR "expand" "negative equality missing"
        in eq_mp policy_owner (apply_function policy_owner (constant
          boolSyntax.negation)
          (symmetry_conversion policy_owner a b)) base end
    | ExistsIntroduction (ant,witness,p) => theorem conclusion held_hypotheses
        (ExistsIntroduction (ant,witness,expand policy_owner p))
    | QuantifyCondition (v,p) =>
        let val base = expand policy_owner p
            val (ant,result) = case binary_view policy_owner "min" "==>"
                (statement base) of SOME pair => pair
              | NONE => raise ERR "expand" "condition missing"
            val ex = quantifier boolSyntax.existential v ant
            val consequent = mp policy_owner base (assumption ant)
            val chosen = theorem result
              (union policy_owner (hypotheses base) [ex])
              (ChooseWitness (v,assumption ex,consequent))
        in discharge policy_owner ex chosen end
    | ExpandAbbrev p => abbrev_equality policy_owner (expand policy_owner p)
    | AbbrevFunctionEquality p =>
        expand policy_owner
          (specialize_all policy_owner (function_equality policy_owner (expand
            policy_owner p)))
    | ExpandRestrictedForall p => restricted_forall policy_owner (expand
      policy_owner p)
    | FalseEquality (v,p) =>
        let val base = expand policy_owner p
            val helper = spec policy_owner (equality v (falsity ()))
              (seed_fixed policy_owner boolTheory.FALSITY)
        in mp policy_owner helper base end
    | TruthFalseEquality (left_true,v,p) =>
        let val base = expand policy_owner p
            val distinct = select policy_owner left_true
              (seed_fixed policy_owner boolTheory.BOOL_EQ_DISTINCT)
            val contradiction = mp policy_owner (not_elim policy_owner
              distinct) base
            val helper = spec policy_owner (equality v (falsity ()))
              (seed_fixed policy_owner boolTheory.FALSITY)
        in mp policy_owner helper contradiction end
    | _ => value
    end


  (* Exact ordered work-list/accumulator structure of Cond_rewr.IMP_CANON.
     In particular its final two reversals preserve branch and stock order. *)
  fun implication_canonical policy_owner initial =
    let
      fun finish acc [] = acc
        | finish acc ((ants,proof)::rest) = finish
            (List.foldl (fn (ant,p) => discharge policy_owner ant p) proof
              ants::acc)
            rest
      fun loop acc [] = finish [] acc
        | loop acc ((ants,proof)::rest) =
          let val value = statement proof in
            case binary_view policy_owner "bool" "/\\" value of
              SOME _ => loop acc ((ants,select policy_owner true proof)::
                                 (ants,select policy_owner false proof)::rest)
            | NONE => (case binary_view policy_owner "min" "==>" value of
                SOME (ant,body) =>
                  (case binary_view policy_owner "bool" "/\\" ant of
                     SOME (a,b) =>
                       let val combined = conj policy_owner (assumption a)
                             (assumption b)
                           val next = discharge policy_owner a
                             (discharge policy_owner b (mp policy_owner proof
                               combined))
                       in loop acc ((ants,next)::rest) end
                   | NONE => (case binary_view policy_owner "bool" "\\/" ant of
                       SOME (a,b) =>
                         let val left = theorem (disjunction a b) [a]
                               (DisjLeft (assumption a,b))
                             val right = theorem (disjunction a b) [b]
                               (DisjRight (a,assumption b))
                             val first = discharge policy_owner a
                               (mp policy_owner proof left)
                             val second = discharge policy_owner b
                               (mp policy_owner proof right)
                         in loop acc ((ants,first)::(ants,second)::rest) end
                     | NONE => (case unary_view policy_owner "bool" "?" ant of
                         SOME (Abstraction (v,b)) =>
                           let val all = ordered_variables policy_owner
                                 (union policy_owner (free_hyp policy_owner
                                   proof)
                                   (free policy_owner value))
                               val variant = vary policy_owner all v
                               val instance = substitute policy_owner v
                                 variant b
                               val witness = theorem ant [instance]
                                 (ExistsIntroduction
                                   (ant,variant,assumption instance))
                               val next = discharge policy_owner instance
                                 (mp policy_owner proof witness)
                           in loop acc ((ants,next)::rest) end
                       | SOME _ => raise ERR "implication_canonical"
                           "existential lacks genuine lambda"
                       | NONE => if alpha policy_owner body (falsity ()) then
                           loop ((ants,not_intro policy_owner proof)::acc) rest
                         else loop acc ((ant::ants,undisch policy_owner
                           proof)::rest))))
              | NONE => (case unary_view policy_owner "bool" "!" value of
                  SOME _ => loop acc
                    ((ants,specialize_all policy_owner proof)::rest)
                | NONE => if Option.isSome
                    (binary_view policy_owner "bool" "RES_FORALL" value) then
                    loop acc ((ants,restricted_forall policy_owner
                      proof)::rest)
                  else loop ((ants,proof)::acc) rest))
          end
    in loop [] [([],initial)] end

  fun occurs policy_owner needle value = alpha policy_owner needle value orelse
    (tick policy_owner;case value of
       Application (f,x) => occurs policy_owner needle f orelse occurs
         policy_owner needle x
     | Abstraction (_,b) => occurs policy_owner needle b | Held _ => false)
  fun simple_right policy_owner value =
    case binary_view policy_owner "min" "=" value of
      NONE => true
    | SOME (l,r) => (is_variable policy_owner l andalso is_constant
      policy_owner r) orelse
        (is_constant policy_owner l andalso is_variable policy_owner r)
  fun flip_left policy_owner proof =
    case binary_view policy_owner "min" "=" (statement proof) of
      SOME (left,right) =>
        (case binary_view policy_owner "min" "=" left of
           SOME (a,b) => theorem (equality (equality b a) right)
             (hypotheses proof) (FlipLeftEquality proof)
         | NONE => raise ERR "flip_left" "inner equation missing")
    | NONE => raise ERR "flip_left" "outer equation missing"

  fun equality_canonical policy_owner proof =
    let
      val (ants,_) = conditions policy_owner proof
      val hypfvs = free_hyp policy_owner proof
      val opened = all_undisch policy_owner proof
      val value = statement opened
      fun finish rows = List.map (conjoined_conditions policy_owner ants) rows
      fun conditional_safe left right =
        let val available = union policy_owner (free policy_owner left) hypfvs
        in List.all (fn v => member policy_owner v available) (free
          policy_owner right)
        end
      val rewritten = case binary_view policy_owner "min" "=" value of
        SOME (left,right) =>
          if occurs policy_owner left right then [eqt opened,eqt (sym
            policy_owner opened)]
          else if alpha policy_owner left (truth ()) then
            if alpha policy_owner right (falsity ()) then
              let val _ = tick policy_owner
                  val variable = Held (Term.genvar Type.bool,boolean)
              in [theorem (equality variable (falsity ()))
                (hypotheses opened)
                (TruthFalseEquality (true,variable,opened))] end
            else [sym policy_owner opened]
          else if alpha policy_owner left (falsity ()) then
            if alpha policy_owner right (truth ()) then
              let val _ = tick policy_owner
                  val variable = Held (Term.genvar Type.bool,boolean)
              in [theorem (equality variable (falsity ()))
                (hypotheses opened)
                (TruthFalseEquality (false,variable,opened))] end
            else [sym policy_owner opened]
          else let
            val safe = not (is_variable policy_owner left) orelse
              not (type_equal policy_owner (type_of left,boolean)) orelse
              member policy_owner left hypfvs
            val base = if conditional_safe left right andalso safe then opened
              else eqt opened
            val flip = case binary_view policy_owner "min" "=" (statement
              base) of
                SOME (l,r) => Option.isSome (binary_view policy_owner "min"
                  "=" l)
                  andalso simple_right policy_owner r
              | NONE => false
          in if flip then [base,flip_left policy_owner base] else [base] end
      | NONE => (case unary_view policy_owner "bool" "~" value of
          SOME negative =>
            if Option.isSome (binary_view policy_owner "min" "=" negative) then
              (case binary_view policy_owner "min" "=" negative of
                 SOME (a,b) =>
                   let val mirror = theorem (negation (equality b a))
                         (hypotheses opened) (NegatedSymmetry opened)
                   in [eqf policy_owner opened,eqf policy_owner mirror] end
               | NONE => raise ERR "equality_canonical" "equation missing")
            else if is_variable policy_owner negative andalso
                not (member policy_owner negative hypfvs) then []
              else [eqf policy_owner opened]
        | NONE => if alpha policy_owner value (truth ()) then []
          else if alpha policy_owner value (falsity ()) then
            (* Cond_rewr's fixed x_eq_false uses a private fresh boolean x.
               The exact arbitrary variable will be retained with its quote
               in the false-elimination operation before replay. *)
            let val _ = tick policy_owner
                val variable = Held (Term.genvar Type.bool,boolean)
                val _ = active policy_owner
            in [theorem (equality variable (falsity ())) (hypotheses opened)
              (FalseEquality (variable,opened))] end
          else if Option.isSome (unary_view policy_owner "marker" "Abbrev"
            value)
            then
              let val decoded = abbrev_equality policy_owner opened
              in case binary_view policy_owner "min" "=" (statement decoded) of
                NONE => []
              | SOME (_,right) =>
                  let val base = equality_canonical policy_owner (sym
                    policy_owner decoded)
                  in case right of Abstraction _ => base @
                    equality_canonical policy_owner (specialize_all
                      policy_owner
                      (function_equality policy_owner decoded))
                    | _ => base end
              end
          else if is_variable policy_owner value andalso not
              (member policy_owner value hypfvs) then [] else [eqt opened])
    in finish rewritten end

  fun quantify_conditions policy_owner proof =
    case binary_view policy_owner "min" "==>" (statement proof) of NONE =>
      proof
    | SOME (_,body) =>
        let val excluded = union policy_owner (free policy_owner body)
          (free_hyp policy_owner proof)
            val variables = ordered_variables policy_owner (List.filter
              (fn v => not (member policy_owner v excluded))
              (free policy_owner (statement proof)))
            fun quantify (v,p) =
              case binary_view policy_owner "min" "==>" (statement p) of
                SOME (ant,result) => theorem
                  (implication (quantifier boolSyntax.existential v ant)
                    result)
                  (hypotheses p) (QuantifyCondition (v,p))
              | NONE => raise ERR "quantify" "private condition disappeared"
        in List.foldr quantify proof variables end

  (* Repeated annotations include the VARIABLE slot of every abstraction.
     Future arrow types remain symbolic; this pass calls no Type constructor
     and no supplied policy. Work is the invocation's independent type work,
     not an annotation <= syntax/template cutoff. *)
  fun type_weight policy_owner ty =
    (tick policy_owner;case ty of Arrow (a,b) =>
       1 + type_weight policy_owner a + type_weight policy_owner b
     | HeldType actual =>
         if not (Type.uptodate_type actual) then
           raise ERR "type_weight" "retired actual type"
         else if Type.is_vartype actual then 1
         else List.foldl (fn (a,n) => n+type_weight policy_owner (HeldType a))
           (1 : IntInf.int) (#Args (Type.dest_thy_typeid actual)))
  fun plus ({raw=a,inc=b,ann=c}:profile) ({raw=d,inc=e,ann=f}:profile) =
    {raw=a+d,inc=b+e,ann=c+f}:profile
  fun syntax_profile policy_owner types value =
    let val _ = tick policy_owner
        val ty = type_of value
        val annotation = type_weight policy_owner ty
        val _ = types := ty:: !types
    in case value of
      Held _ => {raw=1,inc=1,ann=annotation}:profile
    | Application (f,x) => plus {raw=1,inc=1,ann=annotation}
        (plus (syntax_profile policy_owner types f) (syntax_profile
          policy_owner types x))
    | Abstraction (v,b) =>
        let val bt = type_of v val bw = type_weight policy_owner bt
            val _ = types := bt:: !types
        in plus {raw=1,inc=2,ann=annotation+bw}
          (syntax_profile policy_owner types b) end
    end

  (* Genuine helper programs still require complete intermediate instances,
     not just the final clause profile. These descriptors are being filled
     from the exact public Drule/Conv grammar before execute_with_policy is
       exposed. *)
  fun immediate_dependencies (Proof {rule,...}) = case rule of
      Seed _ => [] | SeedFixed _ => [] | Specialize (_,p) => [p]
    | Generalize (_,p) => [p] | TypeInstance (_,p) => [p]
    | TermInstance (_,p) => [p]
    | EqualModusPonens (a,b) => [a,b] | ApplyFunction (_,p) => [p]
    | ApplyArgument (p,_) => [p] | AbstractEquality (_,p) => [p]
    | ContractBeta _ => []
    | ChooseWitness (_,a,b) => [a,b]
    | NegationEliminate p => [p]
    | SpecializeAll (_,p) => [p] | SelectLeft p => [p]
    | SelectRight p => [p] | Undisch p => [p] | Discharge (_,p) => [p]
    | Assume _ => [] | Conjoin (a,b) => [a,b] | DisjLeft (p,_) => [p]
    | DisjRight (_,p) => [p] | ModusPonens (a,b) => [a,b]
    | NotIntro p => [p] | ToTruth p => [p] | ToFalse p => [p]
    | Symmetry p => [p] | FlipLeftEquality p => [p]
    | QuantifyCondition (_,p) => [p] | ConjoinConditions (_,p) => [p]
    | ExistsIntroduction (_,_,p) => [p] | NegatedSymmetry p => [p]
    | ExpandAbbrev p => [p] | AbbrevFunctionEquality p => [p]
    | ExpandRestrictedForall p => [p] | FalseEquality (_,p) => [p]
    | TruthFalseEquality (_,_,p) => [p]

  fun materialize_type (HeldType ty) = ty
    | materialize_type (Arrow (a,b)) =
        Type.--> (materialize_type a,materialize_type b)
  fun materialize policy_owner value =
    let val _ = active policy_owner
        val answer = case value of
          Held (term,ty) =>
            let val actual = materialize_type ty in
              if Type.compare (Term.type_of term,actual) = EQUAL then term
              else if Term.is_var term then
                Term.mk_var (#1 (Term.dest_var term),actual)
              else if Term.is_const term then
                let val {Thy,Name,...} = Term.dest_thy_const term
                in Term.mk_thy_const {Thy=Thy,Name=Name,Ty=actual} end
              else raise ERR "materialize" "private leaf is not atomic"
            end
        | Application (f,x) =>
            Term.mk_comb (materialize policy_owner f,materialize policy_owner
              x)
        | Abstraction (v,b) =>
            Term.mk_abs (materialize policy_owner v,materialize policy_owner b)
        val _ = active policy_owner
    in answer end
  fun invoke policy_owner operation =
    (active policy_owner;let val answer = operation ()
                 in active policy_owner;answer end)
  fun retain_closure (policy_owner as PolicyOwner {graph,scope,retained,...})
    node =
    let
      val seen = ref ([] : G.node list)
      val pending = ref ([] : G.closure_child list)
      fun walk child =
        let val _ = active policy_owner
            val n = G.closure_child_node graph scope child
        in if List.exists (fn old => n = old) (!seen) then () else
          (seen := n:: !seen;pending := child:: !pending;
           case G.view graph n of
             G.Application _ =>
               let val (f,x) = G.closure_application_children graph scope child
               in walk f;walk x end
           | G.AdmittedBinder _ =>
               let val binder = G.closure_child_binder graph scope child
               in walk (G.binder_closure_body graph scope binder) end
           | G.OpaqueRetained => raise ERR "retain_closure"
               "fixed rule requires a genuine complete opened recipe"
           | _ => ())
        end
    in walk (G.closure_root graph scope node);
       retained := !pending @ !retained;
       invalidate_backings policy_owner;active policy_owner end

  (* Quiet replay of ONLY the private recipe. No supplied normalizer, public
     Cond_rewr construction/application, Trace listener, HOL_ERR fallback or
     arbitrary theorem/node input is accepted. Library rules are fixed. *)
  fun replay policy_owner memo value =
    let
      fun lookup [] = NONE
        | lookup ((held,result)::rest) =
            if Portable.pointer_eq (held,value) then SOME result
            else lookup rest
      val _ = active policy_owner
      fun compute () =
    let
      val Proof {rule,...} = value
    in case rule of
      Seed fact => invoke policy_owner (fn () => P.closed_original fact)
    | SeedFixed theorem => theorem
    | Specialize (v,p) => invoke policy_owner (fn () =>
        Thm.SPEC (materialize policy_owner v) (replay policy_owner memo p))
    | Generalize (v,p) => invoke policy_owner (fn () =>
        Thm.GEN (materialize policy_owner v) (replay policy_owner memo p))
    | TypeInstance (bindings,p) => invoke policy_owner (fn () => Thm.INST_TYPE
        (List.map (fn (a,b) => {redex=a,residue=materialize_type b}) bindings)
        (replay policy_owner memo p))
    | TermInstance (bindings,p) => invoke policy_owner (fn () => Thm.INST
        (List.map (fn (a,b) =>
          {redex=materialize policy_owner a,residue=materialize policy_owner
            b}) bindings)
        (replay policy_owner memo p))
    | EqualModusPonens (a,b) => invoke policy_owner (fn () =>
        Thm.EQ_MP (replay policy_owner memo a) (replay policy_owner memo b))
    | ApplyFunction (f,p) => invoke policy_owner (fn () =>
        Thm.AP_TERM (materialize policy_owner f) (replay policy_owner memo p))
    | ApplyArgument (p,x) => invoke policy_owner (fn () =>
        Thm.AP_THM (replay policy_owner memo p) (materialize policy_owner x))
    | AbstractEquality (v,p) => invoke policy_owner (fn () =>
        Thm.ABS (materialize policy_owner v) (replay policy_owner memo p))
    | ContractBeta redex => invoke policy_owner (fn () =>
        Thm.BETA_CONV (materialize policy_owner redex))
    | ChooseWitness (v,a,b) => invoke policy_owner (fn () =>
        Thm.CHOOSE (materialize policy_owner v,replay policy_owner memo a)
          (replay policy_owner memo b))
    | NegationEliminate p => invoke policy_owner
        (fn () => Thm.NOT_ELIM (replay policy_owner memo p))
    | SelectLeft p => invoke policy_owner (fn () => Thm.CONJUNCT1 (replay
      policy_owner memo p))
    | SelectRight p => invoke policy_owner (fn () => Thm.CONJUNCT2 (replay
      policy_owner memo p))
    | Discharge (ant,p) => invoke policy_owner (fn () =>
        Thm.DISCH (materialize policy_owner ant) (replay policy_owner memo p))
    | Assume ant => invoke policy_owner (fn () => Thm.ASSUME (materialize
      policy_owner ant))
    | Conjoin (a,b) => invoke policy_owner (fn () =>
        Thm.CONJ (replay policy_owner memo a) (replay policy_owner memo b))
    | DisjLeft (p,b) => invoke policy_owner (fn () =>
        Thm.DISJ1 (replay policy_owner memo p) (materialize policy_owner b))
    | DisjRight (a,p) => invoke policy_owner (fn () =>
        Thm.DISJ2 (materialize policy_owner a) (replay policy_owner memo p))
    | ModusPonens (a,b) => invoke policy_owner (fn () =>
        Thm.MP (replay policy_owner memo a) (replay policy_owner memo b))
    | NotIntro p => invoke policy_owner (fn () => Thm.NOT_INTRO (replay
      policy_owner memo p))
    | Symmetry p => invoke policy_owner (fn () => Thm.SYM (replay policy_owner
      memo p))
    | ExistsIntroduction (ant,witness,p) => invoke policy_owner (fn () =>
        Thm.EXISTS (materialize policy_owner ant,materialize policy_owner
          witness)
          (replay policy_owner memo p))
    | _ => raise ERR "replay" "unexpanded private recipe"
    end
      val result = case lookup (!memo) of SOME answer => answer
        | NONE => let val answer = compute ()
                      val _ = active policy_owner
                      val _ = memo := (value,answer):: !memo
                  in answer end
      val _ = active policy_owner
    in result end

  fun prepare_with_policy (policy_owner as PolicyOwner
    {work,scope,graph,original,phase,check_type,native_contract,...}) =
    protected policy_owner (fn () => W.with_step work (fn () =>
      transaction policy_owner (fn () =>
    let
      val _ = active policy_owner
      val _ = if !phase = Fresh then phase := Prepared else
        raise ERR "prepare_with_policy" "canonicalization attempt consumed"
      val original_rules = C.originals_with_policy original
      val original_facts = C.checked_rules_with_policy original
      val cap = #template_limit (W.semantic_policy work)
      val native=NC.for_work work native_contract
      val native_cap=IntInf.fromInt
        (#template_limit (#semantic_limits native))
      val types = ref ([] : ty list)
      val seen = ref ([] : proof list)
      val total = ref (0 : IntInf.int)
      fun admit value =
        let val profile = syntax_profile policy_owner types value
            val _ = if RP.allows cap (#raw profile) andalso RP.allows cap
              (#inc profile)
              andalso #raw profile<=native_cap andalso #inc
                profile<=native_cap then ()
              else raise ERR "prepare_with_policy"
                "primitive rule result exceeds template"
        in total := !total + #raw profile + #inc profile + #ann profile end
      fun visited value [] = false
        | visited value (p::rest) =
            (tick policy_owner;Portable.pointer_eq (value,p) orelse visited
              value rest)
      fun quote value = if visited value (!seen) then () else
        let val Proof {rule,...} = value
            val _ = (case rule of
              SpecializeAll _ => raise ERR "quote" "unexpanded specialization"
            | Undisch _ => raise ERR "quote" "unexpanded undisch"
            | ToTruth _ => raise ERR "quote" "unexpanded EQT"
            | ToFalse _ => raise ERR "quote" "unexpanded EQF"
            | FlipLeftEquality _ => raise ERR "quote"
              "unexpanded left symmetry"
            | NegatedSymmetry _ => raise ERR "quote" "unexpanded negation"
            | ConjoinConditions _ => raise ERR "quote" "unexpanded conditions"
            | QuantifyCondition _ => raise ERR "quote"
              "unexpanded quantification"
            | ExpandAbbrev _ => raise ERR "quote" "unexpanded Abbrev"
            | AbbrevFunctionEquality _ => raise ERR "quote" "unexpanded FUN_EQ"
            | ExpandRestrictedForall _ => raise ERR "quote"
              "unexpanded restriction"
            | FalseEquality _ => raise ERR "quote" "unexpanded falsity"
            | TruthFalseEquality _ => raise ERR "quote"
              "unexpanded distinctness"
            | _ => ())
            val _ = List.app quote (immediate_dependencies value)
            val _ = admit (statement value)
            val _ = List.app admit (hypotheses value)
            (* SPEC/INST can discard an operand. Its full actual syntax and
               repeated types must still precede that public operation. *)
            val _ = (case rule of
              Specialize (v,_) => admit v
            | Generalize (v,_) => admit v
            | TypeInstance (bindings,_) => List.app (fn (a,b) =>
                let val x = type_weight policy_owner (HeldType a)
                    val y = type_weight policy_owner b
                in types := HeldType a::b:: !types;
                   total := !total+x+y end) bindings
            | TermInstance (bindings,_) => List.app
                (fn (a,b) => (admit a;admit b)) bindings
            | ApplyFunction (f,_) => admit f
            | ApplyArgument (_,x) => admit x
            | AbstractEquality (v,_) => admit v
            | ContractBeta redex => admit redex
            | ChooseWitness (v,_,_) => admit v
            | ExistsIntroduction (ant,v,_) => (admit ant;admit v)
            | _ => ())
            val _ = seen := value:: !seen
        in () end
      fun rows [] [] _ = []
        | rows (rule::rest) (fact::more) index =
            let val _ = tick policy_owner
                val _ = P.validate_closed_fact_with_policy graph scope cap fact
                val _ = if Portable.pointer_eq (rule,P.closed_original fact)
                  then () else raise ERR "prepare_with_policy"
                    "stock original changed"
                val _ = retain_closure policy_owner (P.closed_node fact)
                val seed = theorem (parse policy_owner (Thm.concl rule)) []
                  (Seed fact)
                val implications = implication_canonical policy_owner seed
                val equalities = List.concat
                  (List.map (equality_canonical policy_owner) implications)
                val complete = List.map
                  (expand policy_owner o quantify_conditions policy_owner)
                    equalities
                fun record p =
                  let val _ = quote p
                      (* Whole import/opened ALPHA correspondence, its
                         TRANS and closed EQ_MP result. No source ASSUME. *)
                      val bridge = equality (statement p) (statement p)
                      val _ = List.app admit [bridge,bridge,bridge,statement p]
                      val _ = if null (hypotheses p) then () else
                        raise ERR "prepare_with_policy"
                          "canonical stock clause not closed"
                  in (index,rule,p) end
            in List.map record complete @ rows rest more (index+1) end
        | rows _ _ _ = raise ERR "prepare_with_policy"
          "stock policy_catalogue incidence differs"
      val prepared = rows original_rules original_facts 0
      val _ = if !total<=IntInf.fromInt (#type_work_limit native) andalso
          RP.allows (W.remaining_policy work) (!total) then
          W.spend_policy work (!total)
        else raise ERR "prepare_with_policy"
          "primitive portfolio exceeds original Work"
      fun policy ty =
        let val _ = active policy_owner
            val actual = materialize_type ty
            val _ = active policy_owner
            val _ = external policy_owner (fn () => check_type actual)
            val _ = active policy_owner
        in () end
      val _ = List.app policy (List.rev (!types))
      val _ = active policy_owner
    in PolicyPlan {policy_owner=policy_owner,rows=prepared,used=ref false}
      end)))

  fun execute_with_policy (PolicyPlan {policy_owner=policy_owner as PolicyOwner
      {work,graph,scope,phase,check_type,native_contract,...},rows,used}) =
    protected policy_owner (fn () => W.with_step work (fn () =>
      transaction policy_owner (fn () =>
    let
      val _ = active policy_owner
      val _ = if !phase = Prepared andalso not (!used) then
        (used := true;phase := Executed)
        else raise ERR "execute_with_policy"
          "canonicalization policy_plan consumed"
      val cap = #template_limit (W.semantic_policy work)
      val native=NC.for_work work native_contract
      val native_cap=RP.AtMost (IntInf.fromInt
        (#template_limit (#semantic_limits native)))
      val import_cap=RP.AtMost (IntInf.fromInt (#import_limit native))
      val memo = ref ([] : (proof * Thm.thm) list)
      (* Only completed private proofs are memoized; active guards run before
         and after every hit. Nothing is cached across a policy without
         policy_owner/epochs/all retained input and output frame revalidation.
           *)
      fun policy ty = external policy_owner (fn () => check_type ty)
      fun close (_,_,p) =
        let val theorem = invoke policy_owner (fn () => replay policy_owner
          memo p)
            val _ = if null (Thm.hyp theorem) then () else
              raise ERR "execute_with_policy"
                "canonical clause acquired hypotheses"
            val source = invoke policy_owner (fn () =>
              G.import_with_policy graph scope import_cap (Thm.concl theorem))
            val opened = invoke policy_owner (fn () =>
              G.record_opened_view_with_policy graph scope native_cap (#node
                source))
            val _ = retain_closure policy_owner (#node opened)
            val fact = invoke policy_owner (fn () =>
              P.record_closed_from_import_with_policy
              graph scope {node= #node opened,theorem=theorem,
                template_limit=cap,check_type=policy})
        in (theorem,fact) end
      val results = List.map close rows
    in PolicyCatalogue {policy_owner=policy_owner,origins_with_policy=List.map
      (fn (index,original,_) => (index,original)) rows,
      rules=List.map #1 results,facts=List.map #2 results} end)))
  fun validate_with_policy_for expected
      (PolicyCatalogue {policy_owner=policy_owner as PolicyOwner
        {work,...},...}) =
    ((ignore (W.original_sources expected);
      if Portable.pointer_eq (expected,work) then active policy_owner else
        raise ERR "validate_with_policy_for"
          "foreign canonical policy_catalogue")
     handle primary => (W.close expected;raise primary))
  fun originals_with_policy (PolicyCatalogue {policy_owner,rules,...}) =
    (active policy_owner;rules)
  fun checked_rules_with_policy (PolicyCatalogue {policy_owner,facts,...}) =
    (active policy_owner;facts)
  fun origins_with_policy (PolicyCatalogue
    {policy_owner,origins_with_policy,...}) = (active
    policy_owner;origins_with_policy)
  fun native_contract_for expected
      (held as PolicyCatalogue {policy_owner=PolicyOwner
        {native_contract,...},...}) =
    (validate_with_policy_for expected held;native_contract)

end
