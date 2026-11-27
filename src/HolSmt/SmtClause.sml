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
    {literals : Term.term list, thm : Thm.thm,
     index : (int, (Term.term * int) list) Redblackmap.dict}
  fun term [] = boolSyntax.F
    | term [literal] = literal
    | term (literal :: rest) = boolSyntax.mk_disj (literal, term rest)
  fun literals (Clause {literals, ...}) = (observe #clause_accesses;literals)
  fun theorem (Clause {thm, ...}) = (observe #clause_accesses;thm)
  fun occurrence literal =
    case Lib.total boolSyntax.dest_neg literal of
      SOME atom => {literal = literal, negative = true, atom = atom}
    | NONE => {literal = literal, negative = false, atom = literal}
  fun check_endpoint endpoint thm =
    (if same endpoint (Thm.concl thm) then ()
     else raise ERR "from_literals" "clause/theorem endpoint mismatch";
     Library.check_oracle_tags "SmtClause" "clause" thm)
  fun from_literals literals thm =
    let
      val _ = List.all (fn tm => Term.type_of tm = Type.bool) literals orelse
        raise ERR "from_literals" "non-Boolean literal occurrence"
      val _ = check_endpoint (term literals) thm
      (* Prepend from right to left so lookup can stop at the first
         matching source occurrence, including in duplicate-heavy clauses. *)
      fun add (literal, (position, index)) =
        let
          val key = hash 6 literal
          val first = position - 1
        in (first, Redblackmap.insertWith (fn (saved, entry) => entry @ saved)
          (index, key, [(literal, first)])) end
      val (_, index) = List.foldr add
        (List.length literals, Redblackmap.mkDict Int.compare) literals
    in observe #clause_objects;
      Clause {literals = literals, thm = thm, index = index} end
  (* The occurrence list and its Boolean types were checked when indexed.
     Check the replacement theorem against that same typed endpoint. *)
  fun replace_theorem (Clause {literals,thm = previous,index}) thm =
    (check_endpoint (Thm.concl previous) thm;
     observe #clause_objects;
     Clause {literals = literals,thm = thm,index = index})
  fun find literal (Clause {index, ...}) =
    let val key = hash 6 literal in
      let val _ = observe #clause_accesses
          val result = Option.map #2 (List.find (fn (saved, _) =>
            same saved literal)
            (Option.getOpt (Redblackmap.peek (index, key), [])))
          val _ = case result of SOME _ => observe #index_hits
            | NONE => observe #index_misses
      in result end
    end
  fun contains literal clause = Option.isSome (find literal clause)

  val swap = boolTheory.DISJ_COMM
  val move = HolSmtTheory.clause_move
  val associate = HolSmtTheory.clause_associate
  val right_false = cooperTheory.F_or_r
  val left_false = cooperTheory.F_or_l
  val positive_resolution = HolSmtTheory.clause_positive_resolution
  val negative_resolution = HolSmtTheory.clause_negative_resolution

  (* Move exactly the indexed occurrence.  Each recursive step uses a small
     general equality; it never reinterprets a literal's internal syntax. *)
  fun extract 0 [literal] _ =
        ([], (rule1 SmtReplayRuleObservation.SYM)
          ((rule2 SmtReplayRuleObservation.SPEC) literal right_false))
    | extract 0 (_ :: rest) source =
        (rest, (rule1 SmtReplayRuleObservation.REFL) source)
    | extract position (literal :: rest) source =
        let
          val (remaining, tail_eq) =
            extract (position - 1) rest (#2 (boolSyntax.dest_disj source))
          val result =
            if List.null remaining then
              (rule2 SmtReplayRuleObservation.D_SPECL)
                [literal, boolSyntax.lhs (Thm.concl tail_eq)] swap
            else
              let
                val (pivot, suffix) =
                  boolSyntax.dest_disj (boolSyntax.rhs (Thm.concl tail_eq))
                val lifted = Conv.RAND_CONV (fn _ => tail_eq) source
                val moved = (rule2 SmtReplayRuleObservation.D_SPECL)
                  [literal, pivot, suffix] move
              in (rule2 SmtReplayRuleObservation.TRANS) lifted moved end
        in (literal :: remaining, result) end
    | extract _ [] _ = raise ERR "extract" "invalid literal occurrence"

  fun merge left right left_term right_term =
    let
      fun nonempty [_] source = (rule1 SmtReplayRuleObservation.REFL)
            (boolSyntax.mk_disj (source, right_term))
        | nonempty (literal :: rest) source =
            let
              val (_, suffix) = boolSyntax.dest_disj source
              val associated = (rule2 SmtReplayRuleObservation.D_SPECL)
                [literal, suffix, right_term] associate
              val tail_eq = nonempty rest suffix
              val lifted = Conv.RAND_CONV (fn _ => tail_eq)
                (boolSyntax.rhs (Thm.concl associated))
            in (rule2 SmtReplayRuleObservation.TRANS) associated lifted end
        | nonempty [] _ = raise ERR "merge" "expected nonempty clause"
    in case (left, right) of
        ([], _) => (rule2 SmtReplayRuleObservation.SPEC) right_term left_false
      | (_, []) => (rule2 SmtReplayRuleObservation.SPEC) left_term right_false
      | _ => nonempty left left_term
    end

  fun resolve pivot first second =
    let
      val {negative, atom, ...} = occurrence pivot
      val opposite = if negative then atom else boolSyntax.mk_neg atom
    in
      case (find pivot first, find opposite second) of
        (SOME first_index, SOME second_index) =>
          let
            val first_thm = theorem first
            val (left, first_eq) =
              extract first_index (literals first) (Thm.concl first_thm)
            val second_thm = theorem second
            val (right, second_eq) =
              extract second_index (literals second) (Thm.concl second_thm)
            fun residual equality =
              #2 (boolSyntax.dest_disj (boolSyntax.rhs (Thm.concl equality)))
            val left_term = residual first_eq
            val right_term = residual second_eq
            val law = (rule2 SmtReplayRuleObservation.D_SPECL)
              [atom, left_term, right_term]
              (if negative then negative_resolution else positive_resolution)
            val resolved = (rule2 SmtReplayRuleObservation.MP)
              ((rule2 SmtReplayRuleObservation.MP) law
                ((rule2 SmtReplayRuleObservation.EQ_MP)
                  first_eq first_thm))
              ((rule2 SmtReplayRuleObservation.EQ_MP)
                second_eq second_thm)
            val merged = (rule2 SmtReplayRuleObservation.EQ_MP)
              (merge left right left_term right_term) resolved
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
          fun retain projection clause =
            (observe #clause_accesses;
             replace_theorem clause
               ((rule1 projection) ((rule2 SmtReplayRuleObservation.CONJ)
                 (theorem first) (theorem second))))
        in
          case resolve opposite first second of
            SOME result => result
          | NONE =>
              if not (contains pivot first) then
                retain SmtReplayRuleObservation.CONJUNCT1 first
              else retain SmtReplayRuleObservation.CONJUNCT2 second
        end

  (* Reordering, contraction and weakening are checked by mapping each
     explicit source occurrence to an exact target occurrence.  Missing
     occurrences decline before any recursive theorem is built. *)
  fun align target source =
    let
      val target_term = term target
      val source_thm = theorem source
      fun insert literal position =
        let
          fun introduce 0 [_] _ thm = thm
            | introduce 0 (_ :: _) suffix thm =
                (rule2 SmtReplayRuleObservation.DISJ1) thm
                  (#2 (boolSyntax.dest_disj suffix))
            | introduce n (head :: rest) suffix thm =
                (rule2 SmtReplayRuleObservation.DISJ2) head
                  (introduce (n - 1) rest
                    (#2 (boolSyntax.dest_disj suffix)) thm)
            | introduce _ [] _ _ =
                raise ERR "align" "invalid target occurrence"
        in if position < 0 then
             (rule2 SmtReplayRuleObservation.D_CONTR) target_term
               ((rule1 SmtReplayRuleObservation.ASSUME) literal)
           else introduce position target target_term
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
                (#2 (boolSyntax.dest_disj (Thm.concl thm)))))
        | derive _ _ _ = raise ERR "align" "invalid occurrence mapping"
    in
      if same target_term (Thm.concl source_thm) then
        SOME (from_literals target source_thm)
      else
        let
          val destination = from_literals target
            ((rule1 SmtReplayRuleObservation.ASSUME) target_term)
          val source_literals = literals source
          val mapping = SmtReplayClauseOccurrences.alignment_mapping
            List.map same boolSyntax.F find destination source_literals
        in
          if List.all Option.isSome mapping then
            SOME (replace_theorem destination
              (derive source_literals mapping source_thm))
          else NONE
        end
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
      val root =
        SmtCircuitSat.balanced_conjunction_term (List.map term sources)
      fun projections 0 clauses _ result = (clauses, result)
        | projections 1 (literals :: rest) thm result =
            (rest, from_literals literals thm :: result)
        | projections count clauses thm result =
            let
              val half = count div 2
              val (remaining, result) = projections half clauses
                ((rule1 SmtReplayRuleObservation.CONJUNCT1) thm) result
            in projections (count - half) remaining
              ((rule1 SmtReplayRuleObservation.CONJUNCT2) thm) result end
      val (_, reversed) = projections (List.length sources) sources
        ((rule1 SmtReplayRuleObservation.ASSUME) root) []
      val schema_premises = List.rev reversed
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
    {work:W.portfolio,thm:Thm.thm,occurrences:occurrence list,
     graph:Graph.graph,scope:Graph.scope,sources:Source.sources,
     limits:W.limits,epoch:int,symbols:int}
  fun retain_with_work work (Clause {literals,thm,...}) =
    let val sources = W.original_sources work
        val graph = Source.owning_graph sources
        val scope = Source.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph scope sources limits
    in OwnedWitness {work = work,thm = thm,
      occurrences = List.map occurrence literals,graph = graph,scope = scope,
      sources = sources,limits = limits,epoch = Type.type_epoch (),
      symbols = Term.term_epoch ()} end
  fun description_for expected (OwnedWitness
      {work,thm,occurrences,graph,scope,sources,limits,
       epoch,symbols}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "description_for" "different original Work";
      W.validate expected graph scope sources limits;
      if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
        then () else raise ERR "description_for" "declaration epoch changed";
      {theorem = thm,occurrences = occurrences})
     handle primary => (W.close expected;raise primary))
end
