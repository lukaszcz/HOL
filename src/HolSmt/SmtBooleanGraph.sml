(* Proof-local Boolean graph construction shared by checked SAT clients.
   Definitions and substitutions are search data; callers must reconstruct
   and check their instantiated definitions and final theorem endpoints. *)
structure SmtBooleanGraph =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtBooleanGraph"
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
        case peek memo tm of
          SOME result => result
        | NONE =>
            let
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
            in result end
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
            Thm.DISCH definition_term (Thm.MP implication
              (Thm.EQ_MP equivalence (Thm.ASSUME definition_term)))
          end)
      val instantiated = profile "instantiate"
        (fn () => Thm.INST substitutions law)
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
                    NONE => Thm.ALPHA left right
                  | SOME theorem => Thm.TRANS (Thm.ALPHA left original)
                      (Thm.TRANS theorem
                        (Thm.ALPHA (boolSyntax.rhs (Thm.concl theorem)) right))
              in proof end
            val proofs = ListPair.mapEq prove_definition
              (definitions, equations)
            val conjunction = SmtCircuitSat.balanced_conjunction proofs
          in Thm.MP instantiated conjunction end)
      val _ = List.null (Thm.hyp result) orelse
        raise ERR "prove_cnf_using" "graph proof retained assumptions"
      val _ = Library.check_oracle_tags "SmtBooleanGraph" "CNF proof" result
    in result end
end
