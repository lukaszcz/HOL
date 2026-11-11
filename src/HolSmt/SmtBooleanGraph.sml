(* Proof-local Boolean graph construction shared by checked SAT clients.
   Definitions and substitutions are search data; callers must reconstruct
   and check their instantiated definitions and final theorem endpoints. *)
structure SmtBooleanGraph =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtBooleanGraph"
  local
    type focus_meter =
      {first_insertions:IntInf.int ref,focus_visits:IntInf.int ref,
       cache_hits:IntInf.int ref,cache_misses:IntInf.int ref,
       selected_proof_returns:IntInf.int ref}
    val focus_meter : focus_meter option ref = ref NONE
    fun observe select = case !focus_meter of NONE => ()
      | SOME fields => let val cell = select fields in cell := !cell+1 end
    fun returned proof = (observe #selected_proof_returns;proof)
    fun rule1 operation arg = returned (operation arg)
    fun rule2 operation a b = returned (operation a b)
  in
    type boolean_statistics =
      {first_insertions:IntInf.int,focus_visits:IntInf.int,
       cache_hits:IntInf.int,cache_misses:IntInf.int,
       selected_proof_returns:IntInf.int}
    fun with_boolean_statistics action =
      let val _ = case !focus_meter of NONE => () | SOME _ =>
            raise ERR "with_boolean_statistics" "observation reentry"
          val fields : focus_meter =
            {first_insertions=ref 0,focus_visits=ref 0,cache_hits=ref 0,
             cache_misses=ref 0,selected_proof_returns=ref 0}
          val _ = focus_meter := SOME fields
          val outcome = Exn.capture action ()
          val _ = focus_meter := NONE
          val counts : boolean_statistics =
            {first_insertions= !(#first_insertions fields),
             focus_visits= !(#focus_visits fields),
             cache_hits= !(#cache_hits fields),
             cache_misses= !(#cache_misses fields),
             selected_proof_returns= !(#selected_proof_returns fields)}
      in (Exn.release outcome,counts) end
  val bucket_count = 16381
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
        (* Bound-variable names must not influence an alpha-equality bucket. *)
        else if Term.is_abs tm then 5 else 7
    | hash depth tm =
        if Term.is_comb tm then
          (hash (depth - 1) (Term.rator tm) * 41 +
           hash (depth - 1) (Term.rand tm) * 67 + 11) mod bucket_count
        else if Term.is_abs tm then 5 else hash 0 tm

  fun new {chunk_depth, stops, stop_conversion, leaf, unfold} =
    let
      val memo = ref (Redblackmap.mkDict Int.compare)
      val leaves = ref (Redblackmap.mkDict Int.compare)
      val nodes = ref 0
      val leaf_count = ref 0
      val definitions = ref
        ([] : (Term.term * Term.term * Thm.thm option) list)
      val substitutions = ref
        ([] : {redex : Term.term, residue : Term.term} list)
      fun peek table tm =
        case List.find (fn (saved, _) => same saved tm)
            (Option.getOpt (Redblackmap.peek (!table, hash 4 tm), [])) of
          SOME (_, result) => SOME result
        | NONE => NONE
      fun insert table tm result =
        let val key = hash 4 tm in
          table := Redblackmap.insert (!table, key, (tm, result) ::
            Option.getOpt (Redblackmap.peek (!table, key), []))
        end
      fun variable tm =
        let val result = Term.genvar Type.bool in
          substitutions := {redex = result, residue = tm} :: !substitutions;
          result
        end
      fun opaque tm =
        let
          val canonical = leaf tm
          val _ = same canonical tm orelse
            raise ERR "new" "opaque leaf canonicalization changed its term"
        in case peek leaves canonical of
            SOME result => result
          | NONE =>
              let val result = variable canonical in
                insert leaves canonical result;
                leaf_count := !leaf_count + 1;
                result
              end
        end
      fun bridge source theorem =
        let val (left, right) = boolSyntax.dest_eq (Thm.concl theorem) in
          if same left source andalso Term.type_of right = Type.bool andalso
              List.null (Thm.hyp theorem) then () else
            raise ERR "new" "invalid graph conversion endpoints/hypotheses";
          Library.check_oracle_tags "SmtBooleanGraph" "conversion" theorem;
          right
        end
      fun circuit_depth depth tm =
        (observe #focus_visits;
         case peek memo tm of
          SOME result => (observe #cache_hits;result)
        | NONE =>
            let val _ = observe #cache_misses
              val _ = Term.type_of tm = Type.bool orelse
                raise ERR "new" "non-Boolean circuit node"
              fun internal_with proof skeleton =
                let val result = variable tm in
                  definitions :=
                    (tm, boolSyntax.mk_eq (result, skeleton), proof) ::
                    !definitions;
                  result
                end
              fun internal skeleton =
                case chunk_depth of
                  NONE => internal_with NONE skeleton
                | SOME limit => if depth >= limit then
                    internal_with NONE skeleton else skeleton
              val next_depth = case chunk_depth of NONE => 0
                | SOME limit => if depth >= limit then 0 else depth + 1
              fun child term = circuit_depth next_depth term
              fun converted conversion =
                case conversion tm of
                  NONE => opaque tm
                | SOME theorem =>
                    let val residue = bridge tm theorem in
                      if same tm residue then opaque tm
                      else internal_with (SOME theorem)
                        (circuit_depth 0 residue)
                    end
              val result =
                if List.exists (same tm) stops then converted stop_conversion
                else if same tm boolSyntax.T orelse same tm boolSyntax.F then tm
                else if boolSyntax.is_neg tm then
                  internal (boolSyntax.mk_neg (child (boolSyntax.dest_neg tm)))
                else if boolSyntax.is_conj tm then
                  let val (left, right) = boolSyntax.dest_conj tm in
                    internal (boolSyntax.mk_conj (child left, child right)) end
                else if boolSyntax.is_disj tm then
                  let val (left, right) = boolSyntax.dest_disj tm in
                    internal (boolSyntax.mk_disj (child left, child right)) end
                else if boolSyntax.is_imp tm then
                  let val (left, right) = boolSyntax.dest_imp tm in
                    internal (boolSyntax.mk_imp (child left, child right)) end
                else if boolSyntax.is_eq tm andalso
                    Term.type_of (boolSyntax.lhs tm) = Type.bool then
                  let val (left, right) = boolSyntax.dest_eq tm in
                    internal (boolSyntax.mk_eq (child left, child right)) end
                else if boolSyntax.is_cond tm then
                  let val (condition, yes, no) = boolSyntax.dest_cond tm in
                    internal (boolSyntax.mk_cond
                      (child condition, child yes, child no)) end
                else converted unfold
              val _ = insert memo tm result
              val _ = nodes := !nodes + 1
              val _ = observe #first_insertions
            in result end)
    in
      {circuit = circuit_depth 0,
       definitions = fn () => List.rev (!definitions),
       substitutions = fn () => !substitutions,
       counts = fn () => {nodes = !nodes, leaves = !leaf_count}}
    end

  (* Convert only admitted graph definitions.  The output is a graph root,
     including a gate for an implication; a compound formula must not be
     passed as an opaque DIMACS literal. *)
  fun prove_cnf_using profile {definitions, substitutions, root} =
    let
      val equivalence = profile "cnf" (fn () =>
        SmtCircuitSat.balanced_equivalences (List.map
          (SmtCircuitSat.definition_cnf o #2) definitions))
      val (definition_term, cnf) = boolSyntax.dest_eq (Thm.concl equivalence)
      val law = profile "sat" (fn () =>
        if List.null definitions then HolSatLib.SAT_PROVE_ONLY root
        else
          let val implication = SmtCircuitSat.prove_cnf (cnf, root) in
            (rule2 SmtReplayRuleObservation.DISCH) definition_term ((rule2 SmtReplayRuleObservation.MP) implication
              ((rule2 SmtReplayRuleObservation.EQ_MP) equivalence ((rule1 SmtReplayRuleObservation.ASSUME) definition_term)))
          end)
      val instantiated = profile "instantiate"
        (fn () => (rule2 SmtReplayRuleObservation.INST) substitutions law)
      val result = if List.null definitions then instantiated else
        profile "discharge" (fn () =>
          let
            val antecedent = #1
              (boolSyntax.dest_imp (Thm.concl instantiated))
            val equations = boolSyntax.strip_conj antecedent
            fun prove_definition ((original, _, bridge), equation) =
              let
                val (left, right) = boolSyntax.dest_eq equation
                val proof = case bridge of
                    NONE => (rule2 SmtReplayRuleObservation.ALPHA) left right
                  | SOME theorem => (rule2 SmtReplayRuleObservation.TRANS) ((rule2 SmtReplayRuleObservation.ALPHA) left original)
                      ((rule2 SmtReplayRuleObservation.TRANS) theorem
                        ((rule2 SmtReplayRuleObservation.ALPHA) (boolSyntax.rhs (Thm.concl theorem)) right))
              in proof end
            val proofs = ListPair.mapEq prove_definition
              (definitions, equations)
            val conjunction = SmtCircuitSat.balanced_conjunction proofs
          in (rule2 SmtReplayRuleObservation.MP) instantiated conjunction end)
      val _ = List.null (Thm.hyp result) orelse
        raise ERR "prove_cnf_using" "graph proof retained assumptions"
      val _ = Library.check_oracle_tags "SmtBooleanGraph" "CNF proof" result
    in result end

  (* The owned graph route retains operator structure until the compact
     Boolean schemas have been checked. It uses the same direct CNF/SAT
     procedure as the term adapter above. All SAT operands are node names;
     the only expanded instantiation is the completed block's realization.
     Entry-point DAG/type admission remains the caller's existing contract. *)
  local
    open SmtReplayGraph SmtReplayProof
    structure G = SmtReplayGraph
    structure P = SmtReplayProof
  in
  fun graph_gates graph roots =
    let
      val _ = List.app (fn root =>
        if Type.compare (G.type_of graph root, Type.bool) = EQUAL then ()
        else raise ERR "graph_gates" "non-Boolean graph root") roots

      fun spine node arguments =
        case G.view graph node of
          G.Application (operator, operand) =>
            spine operator (operand :: arguments)
        | G.Constant _ => SOME (node, arguments)
        | _ => NONE

      fun boolean node =
        Type.compare (G.type_of graph node, Type.bool) = EQUAL

      fun gate node =
        case spine node [] of
          NONE => NONE
        | SOME (head, arguments) =>
            let
              val term = G.representative graph head
              fun constant expected = Term.same_const term expected
              val arity = List.length arguments
              val connective =
                (arity = 0 andalso
                 (constant boolSyntax.T orelse constant boolSyntax.F)) orelse
                (arity = 1 andalso constant boolSyntax.negation) orelse
                (arity = 2 andalso
                 (constant boolSyntax.conjunction orelse
                  constant boolSyntax.disjunction orelse
                  constant boolSyntax.implication orelse
                  constant boolSyntax.equality)) orelse
                (arity = 3 andalso constant boolSyntax.conditional)
            in
              if connective andalso List.all boolean arguments then
                SOME arguments
              else NONE
            end

      (* Discovery visits only Boolean operands; theory atoms retain their
         identity even when their representative is a large compound term. *)
      fun discover [] _ result = List.rev result
        | discover (node :: pending) seen result =
            (observe #focus_visits;
             if Redblackset.member (seen, G.node_id node) then
              (observe #cache_hits;discover pending seen result)
            else
              let val _ = observe #cache_misses
                  val seen = Redblackset.add (seen, G.node_id node)
                  val _ = observe #first_insertions
              in
                case gate node of
                  NONE => discover pending seen result
                | SOME operands =>
                    discover (operands @ pending) seen (node :: result)
              end)
    in discover roots (Redblackset.empty Int.compare) [] end

  (* Assemble a checked Boolean step under an existing compact context.
     Premises are named facts, rather than expanded source theorems. This
     permits a whole replay block to share definitions and realize once. *)
  fun assemble_graph_using profile {graph, block, root, premises} =
    let
      val target = P.name block root
      fun premise (node, edge) =
        if Term.aconv (Thm.concl (P.theorem block edge)) (P.name block node)
        then edge else raise ERR "assemble_graph_using"
          "incorrect named Boolean premise endpoint"
      val facts = List.map premise premises
      val gates = graph_gates graph (root :: List.map #1 premises)

      (* Expand a bounded curried Boolean operator using constructor
         projections. Operands remain compact names throughout this proof. *)
      val operator_proofs = ref (Redblackmap.mkDict Int.compare)
      fun operator_proof node =
        case Redblackmap.peek (!operator_proofs, G.node_id node) of
          SOME proof => proof
        | NONE =>
            let
              val proof = P.constructor block node
              val _ = operator_proofs := Redblackmap.insert
                (!operator_proofs, G.node_id node, proof)
            in proof end
      val definitions = List.map operator_proof gates
      val equivalence = profile "cnf" (fn () =>
        SmtCircuitSat.balanced_equivalences (List.map
          (SmtCircuitSat.definition_cnf o Thm.concl o P.theorem block)
          definitions))
      val definition_cnf = boolSyntax.rhs (Thm.concl equivalence)
      val fact_conjunction = boolSyntax.lhs (Thm.concl
        (SmtCircuitSat.balanced_equivalences (List.map
          ((rule1 SmtReplayRuleObservation.REFL) o P.name block o #1) premises)))
      val cnf = if List.null facts then definition_cnf
        else boolSyntax.mk_conj (definition_cnf,fact_conjunction)
      val implication = profile "sat" (fn () =>
        SmtCircuitSat.prove_cnf (cnf, target))
      val definition_count = List.length definitions
    in P.compose block (fn proofs =>
      let
        val definitions = List.take (proofs,definition_count)
        val facts = List.drop (proofs,definition_count)
        val definition_proof = (rule2 SmtReplayRuleObservation.EQ_MP) equivalence
          (SmtCircuitSat.balanced_conjunction definitions)
        val antecedent = if List.null facts then definition_proof
          else (rule2 SmtReplayRuleObservation.CONJ) definition_proof
            (SmtCircuitSat.balanced_conjunction facts)
      in (rule2 SmtReplayRuleObservation.MP) implication antecedent end) (definitions @ facts)
    end

  end
  end
end
