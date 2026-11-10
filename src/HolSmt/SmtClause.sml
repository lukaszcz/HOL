(* Ordered occurrences stay opaque, even when a literal is a disjunction.
   Hashes index terms; only typed alpha-equality and kernel rules prove
   facts. *)
structure SmtClause :> SmtClause =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtClause"
  type clause_statistics =
    {clause_objects:IntInf.int,clause_accesses:IntInf.int,
     selected_proof_returns:IntInf.int,inst_calls:IntInf.int,
     schema_raw_nodes:IntInf.int,index_hits:IntInf.int,index_misses:IntInf.int}
  type clause_meter =
    {clause_objects:IntInf.int ref,clause_accesses:IntInf.int ref,
     selected_proof_returns:IntInf.int ref,inst_calls:IntInf.int ref,
     schema_raw_nodes:IntInf.int ref,index_hits:IntInf.int ref,
     index_misses:IntInf.int ref}
  val clause_meter : clause_meter option ref = ref NONE
  fun observe select = case !clause_meter of NONE => ()
    | SOME fields => let val cell = select fields in cell := !cell+1 end
  fun with_clause_statistics action =
    let val _ = case !clause_meter of NONE => () | SOME _ =>
          raise ERR "with_clause_statistics" "observation reentry"
        val fields : clause_meter =
          {clause_objects=ref 0,clause_accesses=ref 0,
           selected_proof_returns=ref 0,inst_calls=ref 0,
           schema_raw_nodes=ref 0,index_hits=ref 0,index_misses=ref 0}
        val _ = clause_meter := SOME fields
        val outcome = Exn.capture action ()
        val _ = clause_meter := NONE
        val counts : clause_statistics =
          {clause_objects= !(#clause_objects fields),
           clause_accesses= !(#clause_accesses fields),
           selected_proof_returns= !(#selected_proof_returns fields),
           inst_calls= !(#inst_calls fields),
           schema_raw_nodes= !(#schema_raw_nodes fields),
           index_hits= !(#index_hits fields),
           index_misses= !(#index_misses fields)}
    in (Exn.release outcome,counts) end
  fun returned proof = (observe #selected_proof_returns;proof)
  fun rule1 operation argument = returned (operation argument)
  fun rule2 operation first second = returned (operation first second)
  fun rule3 operation first second third =
    returned (operation first second third)
  fun observed_inst substitutions proof =
    (case !clause_meter of NONE =>
        SmtReplayRuleObservation.INST substitutions proof
      | SOME fields =>
        let
          val profile = SmtReplayInstanceObservation.input_profile proof
          val _ = #inst_calls fields := !(#inst_calls fields)+1
          val _ = #schema_raw_nodes fields := !(#schema_raw_nodes fields)+
            #raw profile
        in returned (SmtReplayRuleObservation.INST substitutions proof) end)
  val bucket_count = 4093
  fun same left right = Portable.pointer_eq (left, right) orelse
    Term.aconv left right
  fun string_hash text = CharVector.foldl
    (fn (character, hash) =>
      (hash * 33 + Char.ord character) mod bucket_count) 17 text
  fun hash 0 tm =
        if Term.is_const tm then
          let val {Thy, Name, ...} = Term.dest_thy_const tm
          in (string_hash Thy * 37 + string_hash Name) mod bucket_count end
        else if Term.is_var tm then string_hash (#1 (Term.dest_var tm))
        else if Term.is_abs tm then 5 else 7
    | hash depth tm =
        if Term.is_comb tm then
          (hash (depth - 1) (Term.rator tm) * 41 +
           hash (depth - 1) (Term.rand tm) * 67 + 11) mod bucket_count
        else if Term.is_abs tm then 5
        else hash 0 tm
  type occurrence = {literal : Term.term, negative : bool, atom : Term.term}
  datatype clause = Clause of
    {occurrences : occurrence list, thm : Thm.thm,
     index : (int, (Term.term * int) list) Redblackmap.dict}
  fun term [] = boolSyntax.F
    | term [literal] = literal
    | term (literal :: rest) = boolSyntax.mk_disj (literal, term rest)
  fun literals (Clause {occurrences, ...}) =
    (observe #clause_accesses;List.map #literal occurrences)
  fun theorem (Clause {thm, ...}) = (observe #clause_accesses;thm)
  fun occurrence literal =
    case Lib.total boolSyntax.dest_neg literal of
      SOME atom => {literal = literal, negative = true, atom = atom}
    | NONE => {literal = literal, negative = false, atom = literal}
  fun from_literals literals thm =
    let
      val _ = List.all (fn tm => Term.type_of tm = Type.bool) literals orelse
        raise ERR "from_literals" "non-Boolean literal occurrence"
      val _ = same (term literals) (Thm.concl thm) orelse
        raise ERR "from_literals" "clause/theorem endpoint mismatch"
      val _ = Library.check_oracle_tags "SmtClause" "clause" thm
      val index = ref (Redblackmap.mkDict Int.compare)
      fun add [] _ = ()
        | add (literal :: rest) position =
            let val key = hash 6 literal
            in
              index := Redblackmap.insert (!index, key,
                (literal, position) ::
                Option.getOpt (Redblackmap.peek (!index, key), []));
              add rest (position + 1)
            end
      val _ = add literals 0
    in observe #clause_objects;
      Clause {occurrences = List.map occurrence literals,
      thm = thm, index = !index} end
  fun find literal (Clause {index, ...}) =
    let val key = hash 6 literal in
      (* Buckets are stored in reverse occurrence order.  Keep the first
         source occurrence, even when duplicates are separated by literals. *)
      let val _ = observe #clause_accesses
          val result = List.foldl (fn ((saved, position), chosen) =>
            if same saved literal then SOME position else chosen) NONE
            (Option.getOpt (Redblackmap.peek (index, key), []))
          val _ = case result of SOME _ => observe #index_hits
            | NONE => observe #index_misses
      in result end
    end
  fun contains literal clause = Option.isSome (find literal clause)

  val clause_tactic = Tactical.THEN
    (Tactical.REPEAT Tactic.GEN_TAC, tautLib.TAUT_TAC)
  val swap = Library.prove
    (``!(a:bool) b. (a \/ b) = (b \/ a)``, clause_tactic)
  val move = Library.prove
    (``!(a:bool) p b. (a \/ (p \/ b)) = (p \/ (a \/ b))``,
     clause_tactic)
  val associate = Library.prove
    (``!(a:bool) b c. ((a \/ b) \/ c) = (a \/ (b \/ c))``,
     clause_tactic)
  val right_false = Library.prove
    (``!(a:bool). (a \/ F) = a``, clause_tactic)
  val left_false = Library.prove
    (``!(a:bool). (F \/ a) = a``, clause_tactic)
  val positive_resolution = Library.prove
    (``!(p:bool) a b. (p \/ a) ==> (~p \/ b) ==> (a \/ b)``,
     clause_tactic)
  val negative_resolution = Library.prove
    (``!(p:bool) a b. (~p \/ a) ==> (p \/ b) ==> (a \/ b)``,
     clause_tactic)

  (* Move exactly the indexed occurrence.  Each recursive step uses a small
     general equality; it never reinterprets a literal's internal syntax. *)
  fun extract 0 [literal] =
        ([], (rule1 SmtReplayRuleObservation.SYM)
          ((rule2 SmtReplayRuleObservation.SPEC) literal right_false))
    | extract 0 (literal :: rest) =
        (rest, (rule1 SmtReplayRuleObservation.REFL) (term (literal :: rest)))
    | extract position (literal :: rest) =
        let
          val (remaining, tail_eq) = extract (position - 1) rest
          val pivot = boolSyntax.lhs (Thm.concl tail_eq)
          val pivot = case remaining of
              [] => pivot
            | _ => #1 (boolSyntax.dest_disj
                (boolSyntax.rhs (Thm.concl tail_eq)))
          val result =
            if List.null remaining then
              (rule2 SmtReplayRuleObservation.D_SPECL) [literal, pivot] swap
            else
              let
                val lifted = Conv.RAND_CONV (fn _ => tail_eq)
                  (term (literal :: rest))
                val moved = (rule2 SmtReplayRuleObservation.D_SPECL)
                  [literal, pivot, term remaining] move
              in (rule2 SmtReplayRuleObservation.TRANS) lifted moved end
        in (literal :: remaining, result) end
    | extract _ [] = raise ERR "extract" "invalid literal occurrence"

  fun merge [] right =
        (rule2 SmtReplayRuleObservation.SPEC) (term right) left_false
    | merge left [] =
        (rule2 SmtReplayRuleObservation.SPEC) (term left) right_false
    | merge [literal] right = (rule1 SmtReplayRuleObservation.REFL)
        (boolSyntax.mk_disj (literal, term right))
    | merge (literal :: rest) right =
        let
          val associated = (rule2 SmtReplayRuleObservation.D_SPECL)
            [literal, term rest, term right] associate
          val tail_eq = merge rest right
          val lifted = Conv.RAND_CONV (fn _ => tail_eq)
            (boolSyntax.rhs (Thm.concl associated))
        in (rule2 SmtReplayRuleObservation.TRANS) associated lifted end

  fun resolve pivot first second =
    let
      val {negative, atom, ...} = occurrence pivot
      val opposite = if negative then atom else boolSyntax.mk_neg atom
    in
      case (find pivot first, find opposite second) of
        (SOME first_index, SOME second_index) =>
          let
            val (left, first_eq) = extract first_index (literals first)
            val (right, second_eq) = extract second_index (literals second)
            val law = (rule2 SmtReplayRuleObservation.D_SPECL)
              [atom, term left, term right]
              (if negative then negative_resolution else positive_resolution)
            val resolved = (rule2 SmtReplayRuleObservation.MP)
              ((rule2 SmtReplayRuleObservation.MP) law
                ((rule2 SmtReplayRuleObservation.EQ_MP)
                  first_eq (theorem first)))
              ((rule2 SmtReplayRuleObservation.EQ_MP)
                second_eq (theorem second))
            val merged = (rule2 SmtReplayRuleObservation.EQ_MP)
              (merge left right) resolved
          in SOME (from_literals (left @ right) merged) end
      | _ => NONE
    end

  (* An absent pivot permits retaining a complete premise, then weakening
     it to the recorded target.  It cannot justify deleting any of that
     premise's literals.  Retain the other premise's hypotheses explicitly. *)
  fun resolve_or_weaken pivot first second =
    case resolve pivot first second of
      SOME result => result
    | NONE =>
        let
          val {negative, atom, ...} = occurrence pivot
          val opposite = if negative then atom else boolSyntax.mk_neg atom
        in
          case resolve opposite first second of
            SOME result => result
          | NONE =>
              if not (contains pivot first) then
                from_literals (literals first)
                  ((rule1 SmtReplayRuleObservation.CONJUNCT1)
                    ((rule2 SmtReplayRuleObservation.CONJ)
                      (theorem first) (theorem second)))
              else from_literals (literals second)
                ((rule1 SmtReplayRuleObservation.CONJUNCT2)
                  ((rule2 SmtReplayRuleObservation.CONJ)
                    (theorem first) (theorem second)))
        end

  (* Reordering, contraction and weakening are checked by mapping each
     explicit source occurrence to an exact target occurrence.  Missing
     occurrences decline before any recursive theorem is built. *)
  fun align target source =
    let
      val target_term = term target
      val destination = from_literals target
        ((rule1 SmtReplayRuleObservation.ASSUME) target_term)
      val source_literals = literals source
      val mapping = SmtReplayClauseOccurrences.alignment_mapping
        List.map same boolSyntax.F find destination source_literals
      fun insert literal position =
        let
          fun introduce 0 [_] thm = thm
            | introduce 0 (_ :: rest) thm =
                (rule2 SmtReplayRuleObservation.DISJ1) thm (term rest)
            | introduce n (head :: rest) thm =
                (rule2 SmtReplayRuleObservation.DISJ2) head
                  (introduce (n - 1) rest thm)
            | introduce _ [] _ = raise ERR "align" "invalid target occurrence"
        in if position < 0 then
             (rule2 SmtReplayRuleObservation.D_CONTR) target_term
               ((rule1 SmtReplayRuleObservation.ASSUME) literal)
           else introduce position target
             ((rule1 SmtReplayRuleObservation.ASSUME) literal) end
      fun derive [] [] thm =
            (rule2 SmtReplayRuleObservation.D_CONTR) target_term thm
        | derive [literal] [SOME position] thm =
            (rule2 SmtReplayRuleObservation.D_PROVE_HYP) thm
              (insert literal position)
        | derive (literal :: rest) (SOME position :: positions) thm =
            (rule3 SmtReplayRuleObservation.DISJ_CASES) thm
              (insert literal position)
              (derive rest positions ((rule1 SmtReplayRuleObservation.ASSUME)
                (term rest)))
        | derive _ _ _ = raise ERR "align" "invalid occurrence mapping"
    in
      if same target_term (Thm.concl (theorem source)) then
        SOME (from_literals target (theorem source))
      else if List.all Option.isSome mapping then
        SOME (from_literals target
          (derive source_literals mapping (theorem source)))
      else NONE
    end
  fun factor source =
    let
      val seen = ref (Redblackmap.mkDict Int.compare)
      fun unique [] kept = List.rev kept
        | unique (literal :: rest) kept =
            let val key = hash 6 literal
                val bucket = Option.getOpt (Redblackmap.peek (!seen, key), [])
            in
              if List.exists (same literal) bucket then
                (observe #index_hits;unique rest kept)
              else (observe #index_misses;
                    seen := Redblackmap.insert (!seen, key, literal :: bucket);
                    unique rest (literal :: kept))
            end
      val target = unique (literals source) []
    in case align target source of SOME result => result
       | NONE => raise ERR "factor" "exact factoring declined" end

  (* Prove in a Boolean schema with one balanced root assumption.  Actual
     atoms are substituted once, after the supplied pivot chain and target
     alignment have been checked.  The final MP checks the instantiated
     root against the balanced conjunction of the actual premise theorems. *)
  fun resolve_chain {pivots, premises, target} =
    let
      val _ = List.length pivots + 1 = List.length premises orelse
        raise ERR "resolve_chain" "pivot/premise arity mismatch"
      val atoms = ref (Redblackmap.mkDict Int.compare)
      val substitutions = ref []
      fun atom tm =
        if same tm boolSyntax.T orelse same tm boolSyntax.F then tm
        else
          let val key = hash 6 tm
              val bucket = Option.getOpt (Redblackmap.peek (!atoms, key), [])
          in case List.find (fn (saved, _) => same saved tm) bucket of
              SOME (_, variable) => (observe #index_hits;variable)
            | NONE => (observe #index_misses;
                let val variable = Term.genvar Type.bool
                in
                  atoms := Redblackmap.insert (!atoms, key,
                    (tm, variable) :: bucket);
                  substitutions := {redex = variable, residue = tm} ::
                    !substitutions;
                  variable
                end)
          end
      fun literal tm = case Lib.total boolSyntax.dest_neg tm of
          SOME body => boolSyntax.mk_neg (atom body)
        | NONE => atom tm
      val sources = List.map (List.map literal o literals) premises
      val signed_pivots = List.map literal pivots
      val destination = Option.map (List.map literal) target
      val root = boolSyntax.lhs (Thm.concl
        (SmtCircuitSat.balanced_equivalences
          (List.map ((rule1 SmtReplayRuleObservation.REFL) o term) sources)))
      fun projections [] _ = []
        | projections [literals] thm = [from_literals literals thm]
        | projections clauses thm =
            let val half = List.length clauses div 2 in
              projections (List.take (clauses, half))
                ((rule1 SmtReplayRuleObservation.CONJUNCT1) thm) @
              projections (List.drop (clauses, half))
                ((rule1 SmtReplayRuleObservation.CONJUNCT2) thm)
            end
      val schema_premises = projections sources
        ((rule1 SmtReplayRuleObservation.ASSUME) root)
      val result = case schema_premises of
          [] => raise ERR "resolve_chain" "empty premise list"
        | first :: rest => List.foldl
            (fn ((next, pivot), accumulated) =>
              resolve_or_weaken pivot accumulated next)
            first (ListPair.zip (rest, signed_pivots))
      val aligned = case destination of
          NONE => SOME result
        | SOME literals => align literals result
      (* A resolved literal may itself be the entire recorded disjunction.
         Its source occurrence remains opaque, but the recorded target can
         supply new outer boundaries when the instantiated HOL endpoints
         agree exactly.  This needs no theory normalization or SAT search. *)
      val checked = case aligned of
          SOME clause => SOME (clause, NONE)
        | NONE => case target of
            NONE => NONE
          | SOME target_literals =>
              if same (Term.subst (!substitutions) (term (literals result)))
                  (term target_literals) then
                SOME (result, SOME target_literals)
              else NONE
    in case checked of
        NONE => NONE
      | SOME (checked, recorded_literals) =>
          let
            val law = (rule2 SmtReplayRuleObservation.DISCH)
              root (theorem checked)
            val _ = List.null (Thm.hyp law) orelse
              raise ERR "resolve_chain" "schema retained extra hypotheses"
            val instantiated = observed_inst (!substitutions) law
            val actual_roots = SmtCircuitSat.balanced_conjunction
              (List.map theorem premises)
            val result = (rule2 SmtReplayRuleObservation.MP)
              instantiated actual_roots
            val literals = case recorded_literals of
                SOME literals => literals
              | NONE => List.map (Term.subst (!substitutions))
                  (literals checked)
          in SOME (from_literals literals result) end
    end

  fun new_normalizer_using {reuse, capacity, conversion} =
    let
      val _ = capacity >= 0 orelse raise ERR "new_normalizer_using"
        "negative normalization cache capacity"
      val saved = ref (Redblackmap.mkDict Int.compare)
      val size = ref 0
      fun literal_bridge literal =
        let
          val key = hash 6 literal
          val bucket = Option.getOpt (Redblackmap.peek (!saved, key), [])
        in
          case List.find (fn (source, _) => same source literal) bucket of
            SOME (_, bridge) => (observe #index_hits;bridge)
          | NONE => (observe #index_misses;
              let
                val bridge = conversion literal
                  handle Conv.UNCHANGED =>
                    (rule1 SmtReplayRuleObservation.REFL) literal
                val (lhs, rhs) = boolSyntax.dest_eq (Thm.concl bridge)
                val _ = same lhs literal andalso
                    Term.type_of rhs = Type.bool andalso
                    List.null (Thm.hyp bridge) orelse
                  raise ERR "new_normalizer_using"
                    "literal normalization has invalid endpoints/hypotheses"
                val _ = Library.check_oracle_tags
                  "SmtClause" "literal normalization" bridge
                val _ = if not reuse orelse capacity = 0 then ()
                  else
                    let
                      val _ = if !size < capacity then () else
                        (saved := Redblackmap.mkDict Int.compare; size := 0)
                      val bucket = Option.getOpt
                        (Redblackmap.peek (!saved, key), [])
                    in
                      saved := Redblackmap.insert (!saved, key,
                        (literal, bridge) :: bucket);
                      size := !size + 1
                    end
              in bridge end)
        end
      val disjunction = Term.rator (Term.rator
        (boolSyntax.mk_disj (boolSyntax.T, boolSyntax.T)))
      fun normalize [] =
            ([], (rule1 SmtReplayRuleObservation.REFL) boolSyntax.F)
        | normalize [literal] =
            let val bridge = literal_bridge literal
            in ([boolSyntax.rhs (Thm.concl bridge)], bridge) end
        | normalize (literal :: rest) =
            let
              val bridge = literal_bridge literal
              val (tail, tail_bridge) = normalize rest
              val whole = (rule1 SmtReplayRuleObservation.MK_COMB)
                ((rule1 SmtReplayRuleObservation.MK_COMB)
                  ((rule1 SmtReplayRuleObservation.REFL) disjunction, bridge),
                  tail_bridge)
            in (boolSyntax.rhs (Thm.concl bridge) :: tail, whole) end
    in normalize end
  fun new_normalizer conversion = new_normalizer_using
    {reuse = true, capacity = bucket_count, conversion = conversion}
  structure W = SmtReplayInvocationWork
  structure Source = SmtReplaySource
  structure Graph = SmtReplayGraph
  val _ = SmtReplayInvocationWork.validate
  datatype owned_witness = OwnedWitness of
    {work:W.portfolio,clause:clause,graph:Graph.graph,scope:Graph.scope,
     sources:Source.sources,limits:W.limits,epoch:int,symbols:int}
  fun retain_with_work work clause =
    let val sources = W.original_sources work
        val graph = Source.owning_graph sources
        val scope = Source.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph scope sources limits
    in OwnedWitness {work = work,clause = clause,graph = graph,scope = scope,
      sources = sources,limits = limits,epoch = Type.type_epoch (),
      symbols = Term.term_epoch ()} end
  fun description_for expected (OwnedWitness
      {work,clause = Clause {thm,occurrences,...},graph,scope,sources,limits,
       epoch,symbols}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "description_for" "different original Work";
      W.validate expected graph scope sources limits;
      if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        then () else raise ERR "description_for" "declaration epoch changed";
      {theorem = thm,occurrences = occurrences})
     handle primary => (W.close expected;raise primary))
end
