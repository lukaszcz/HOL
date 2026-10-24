(* Optional reuse within one fixed replay/conversion context.  Only checked
   closed implication schemas and ordinary SAT declines are retained.
   No timeout, interruption, conversion error or resource refusal is cached. *)
structure SmtReplayAttempt =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtReplayAttempt"
  datatype outcome = Proved of Thm.thm
    | Satisfiable | Counterexample of Thm.thm
  type request =
    {procedure : string, source : Term.term, target : Term.term,
     prove : unit -> Thm.thm}
  type cache =
    {run : request -> Thm.thm,
     statistics : unit -> {hits : int, misses : int, retained : int}}
  fun new {enabled, capacity, hash} =
    let
      val _ = capacity >= 0 orelse raise ERR "new" "negative cache capacity"
      val saved = ref (Redblackmap.mkDict Int.compare)
      val index = SmtSkeletonProve.new_cache_index
        SmtResource.max_bv_replay_term_nodes
      val semantic_order = SmtSkeletonProve.new_semantic_order ()
      val reuse = enabled andalso capacity > 0
      val size = ref 0
      val hits = ref 0
      val misses = ref 0
      fun return outcome = case outcome of
          Proved theorem => theorem
        | Satisfiable => raise HolSatLib.SAT_satisfiable ()
        | Counterexample theorem => raise HolSatLib.SAT_cex theorem
      fun run ({procedure, source, target, prove} : request) =
        let
          (* Hash collisions never establish equality. Typed child IDs decide
             reuse; exhaustion is a miss, not a new admission requirement.
             Disabled reuse must not even invoke an optional hash callback. *)
          val key = if reuse then hash source else 0
          val target_key = if reuse then hash target else 0
          val endpoints = if reuse then
              (case (index source, index target) of
                 (SOME left, SOME right) => SOME (left, right)
               | _ => NONE)
            else NONE
          val bucket = Option.getOpt (Redblackmap.peek (!saved, key), [])
          val candidate = case endpoints of NONE => NONE
            | SOME (left, right) =>
                List.find (fn (label, saved_left, saved_right, right_key, _) =>
                  label = procedure andalso right_key = target_key andalso
                  left = saved_left andalso right = saved_right) bucket
          fun anchor (Proved theorem) =
                let
                  val (left, right) = boolSyntax.dest_imp (Thm.concl theorem)
                in
                  if Portable.pointer_eq (left, source) andalso
                     Portable.pointer_eq (right, target) then Proved theorem
                  else Proved (Thm.EQ_MP
                    (SmtSkeletonProve.bounded_nodewise_equality
                      SmtResource.max_bv_replay_term_nodes
                      (Thm.concl theorem) (boolSyntax.mk_imp (source, target)))
                    theorem)
                end
            | anchor outcome = outcome
          val found = case candidate of NONE => NONE
            | SOME (_, _, _, _, outcome) =>
                (SOME (anchor outcome)
                 handle SmtSkeletonProve.REANCHOR_LIMIT => NONE
                      | Feedback.HOL_ERR detail =>
                          if SmtSkeletonProve.cache_admission_refusal detail
                          then NONE else raise Feedback.HOL_ERR detail)
          fun attempt () =
            (let
               val theorem = prove ()
               (* Fresh-result validation is mandatory, independently of
                  optional index capacity. Exhaustion never grants native
                  whole-term comparison or transport permission. *)
               val expected = boolSyntax.mk_imp (source, target)
               val valid =
                 if (case Lib.total boolSyntax.dest_imp
                       (Thm.concl theorem) of
                       SOME (left, right) =>
                         Portable.pointer_eq (left, source) andalso
                         Portable.pointer_eq (right, target)
                     | NONE => false) then true
                 else case (index (Thm.concl theorem), index expected) of
                     (SOME left, SOME right) => left = right
                   | _ => semantic_order
                       (Thm.concl theorem, expected) = EQUAL
               val _ = List.null (Thm.hyp theorem) andalso valid
                 orelse raise ERR "run" "invalid closed implication schema"
               val _ = Library.check_oracle_tags
                 "SmtReplayAttempt" "implication schema" theorem
               val result = Proved
                 (SmtSkeletonProve.exact_conclusion expected theorem)
             in result end
             handle HolSatLib.SAT_satisfiable _ => Satisfiable
                  | HolSatLib.SAT_cex theorem => Counterexample theorem)
        in case found of
            SOME outcome => (hits := !hits + 1; return outcome)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val outcome = attempt ()
                val _ = case endpoints of NONE => ()
                  | SOME (left, right) =>
                    let
                      val _ = if !size < capacity then () else
                        (saved := Redblackmap.mkDict Int.compare; size := 0)
                      val bucket = Option.getOpt
                        (Redblackmap.peek (!saved, key), [])
                    in
                      saved := Redblackmap.insert (!saved, key,
                        (procedure, left, right, target_key, outcome) ::
                        bucket);
                      size := !size + 1
                    end
              in return outcome end
        end
    in
      {run = run, statistics = fn () =>
        {hits = !hits, misses = !misses, retained = !size}}
    end

  (* A graph cache belongs to one frozen proof block. Both successful and
     negative entries use owned IDs; no realized term is compared on a hit.
     Block ownership and activity are checked even for cached declines. *)
  local
    open SmtReplayGraph SmtReplayProof
    structure G = SmtReplayGraph
    structure P = SmtReplayProof
    datatype graph_outcome = GraphProved of P.edge
      | GraphSatisfiable | GraphCounterexample of Thm.thm
  in
  fun new_graph {block, enabled, capacity} =
    let
      val _ = capacity >= 0 orelse
        raise ERR "new_graph" "negative cache capacity"
      val saved = ref (Redblackmap.mkDict Int.compare)
      val size = ref 0
      val hits = ref 0
      val misses = ref 0
      fun return outcome = case outcome of
          GraphProved edge => edge
        | GraphSatisfiable => raise HolSatLib.SAT_satisfiable ()
        | GraphCounterexample theorem => raise HolSatLib.SAT_cex theorem
      fun run {procedure, source, target, prove} =
        let
          val source_name = P.name block source
          val target_name = P.name block target
          val _ = Term.type_of source_name = Type.bool andalso
              Term.type_of target_name = Type.bool orelse
            raise ERR "new_graph" "non-Boolean implication endpoints"
          val key = G.node_id source
          val target_key = G.node_id target
          val bucket = Option.getOpt (Redblackmap.peek (!saved, key), [])
          val found = if not enabled orelse capacity = 0 then NONE else
            List.find (fn (label, right_key, _) =>
              label = procedure andalso right_key = target_key) bucket
          fun attempt () =
            (let
               val edge = prove ()
               val theorem = P.theorem block edge
               val expected = boolSyntax.mk_imp (source_name, target_name)
               val _ = Term.aconv (Thm.concl theorem) expected orelse
                 raise ERR "new_graph" "invalid compact implication schema"
               (* Edges are abstract checked values. The owner check above
                  rejects foreign blocks without reinterpreting the shared
                  context as a new individual source hypothesis. *)
             in GraphProved edge end
             handle HolSatLib.SAT_satisfiable _ => GraphSatisfiable
                  | HolSatLib.SAT_cex theorem =>
                      (ignore (P.checked block theorem);
                       GraphCounterexample theorem))
        in case found of
            SOME (_, _, outcome) =>
              (hits := !hits + 1; return outcome)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val outcome = attempt ()
                val _ = if not enabled orelse capacity = 0 then () else
                  let
                    val _ = if !size < capacity then () else
                      (saved := Redblackmap.mkDict Int.compare; size := 0)
                    val bucket = Option.getOpt
                      (Redblackmap.peek (!saved, key), [])
                  in
                    saved := Redblackmap.insert (!saved, key,
                      (procedure, target_key, outcome) :: bucket);
                    size := !size + 1
                  end
              in return outcome end
        end
    in
      {run = run, statistics = fn () =>
        {hits = !hits, misses = !misses, retained = !size}}
    end
  end
end
