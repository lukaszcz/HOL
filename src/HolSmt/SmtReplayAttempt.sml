(* Optional reuse of checked closed implication schemas. Exceptional outcomes
   are never proof facts: the original exception escapes without retention. *)
structure SmtReplayAttempt =
struct
  val ERR = Feedback.mk_HOL_ERR "SmtReplayAttempt"
  (* Retirement epochs do not distinguish Context.restore branches. Own all
     optional hints by the actual immutable signature tables instead. Fresh
     inserts may conservatively discard hints as well. *)
  fun signatures () =
    let val context = Context.live () in
      (Context.typesig context, Context.termsig context)
    end
  fun same_signatures ((types, terms), (old_types, old_terms)) =
    Portable.pointer_eq (types, old_types) andalso
    Portable.pointer_eq (terms, old_terms)

  (* Publication admission shared with the existing skeleton caches; this
     is not proof validation or a new mandatory lifetime interface. *)
  val new_live_memo = SmtSkeletonProve.new_live_memo
  val live_check_with_hints = SmtSkeletonProve.live_check_with_hints
  val new_live_check = SmtSkeletonProve.new_cache_live_check

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
      fun new_index () = SmtSkeletonProve.new_cache_index
        SmtResource.max_bv_replay_term_nodes
      val index = ref (new_index ())
      val semantic_order = ref (SmtSkeletonProve.new_semantic_order ())
      val owned_signatures = ref (signatures ())
      val generation = ref (ref ())
      val reuse = enabled andalso capacity > 0
      fun live_hints () = if reuse then SOME (new_live_memo ()) else NONE
      val hints = ref (live_hints ())
      val size = ref 0
      val hits = ref 0
      val misses = ref 0
      fun refresh () =
        let val current = signatures () in
          if same_signatures (current, !owned_signatures) then () else
            (generation := ref ();
             saved := Redblackmap.mkDict Int.compare; size := 0;
             index := new_index ();
             semantic_order := SmtSkeletonProve.new_semantic_order ();
             hints := live_hints ();
             owned_signatures := current)
        end
      fun run ({procedure, source, target, prove} : request) =
        let
          (* Hash collisions never establish equality. Typed child IDs decide
             reuse; exhaustion is a miss, not a new admission requirement.
             Disabled reuse must not even invoke an optional hash callback. *)
          val key = if reuse then hash source else 0
          val target_key = if reuse then hash target else 0
          val _ = refresh ()
          val indexed_signatures = !owned_signatures
          val indexed_generation = !generation
          val endpoints = if reuse then
              (case ((!index) source, (!index) target) of
                 (SOME left, SOME right) => SOME (left, right)
               | _ => NONE)
            else NONE
          val bucket = Option.getOpt (Redblackmap.peek (!saved, key), [])
          (* Entries were published only for live endpoints under this
             exact signature witness; a hit needs no fresh liveness walk. *)
          val candidate = case endpoints of NONE => NONE
            | SOME (left, right) =>
                List.find (fn (label, saved_left, saved_right, right_key, _) =>
                  label = procedure andalso right_key = target_key andalso
                  left = saved_left andalso right = saved_right) bucket
          fun anchor theorem =
            let
              val (left, right) = boolSyntax.dest_imp (Thm.concl theorem)
            in
              if Portable.pointer_eq (left, source) andalso
                 Portable.pointer_eq (right, target) then theorem
              else Thm.EQ_MP
                (SmtSkeletonProve.bounded_nodewise_equality
                  SmtResource.max_bv_replay_term_nodes
                  (Thm.concl theorem) (boolSyntax.mk_imp (source, target)))
                theorem
            end
          val found = case candidate of NONE => NONE
            | SOME (_, _, _, _, theorem) =>
                (SOME (anchor theorem)
                 handle SmtSkeletonProve.REANCHOR_LIMIT => NONE
                      | Feedback.HOL_ERR detail =>
                          if SmtSkeletonProve.cache_admission_refusal detail
                          then NONE else raise Feedback.HOL_ERR detail)
          fun attempt () =
            let
              val theorem = prove ()
              val _ = refresh ()
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
                else case ((!index) (Thm.concl theorem), (!index) expected) of
                    (SOME left, SOME right) => left = right
                  | _ => (!semantic_order)
                      (Thm.concl theorem, expected) = EQUAL
              val _ = List.null (Thm.hyp theorem) andalso valid
                orelse raise ERR "run" "invalid closed implication schema"
              val _ = Library.check_oracle_tags
                "SmtReplayAttempt" "implication schema" theorem
            in SmtSkeletonProve.exact_conclusion expected theorem end
        in case found of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val theorem = attempt ()
                val _ = refresh ()
                (* Liveness is optional publication, never fresh-result
                   validation. IDs captured before a callback cannot be
                   published under different signature tables either. *)
                val _ = case (if indexed_generation = !generation andalso
                    same_signatures (indexed_signatures, !owned_signatures)
                    then endpoints
                    else NONE) of
                    NONE => ()
                  | SOME (left, right) =>
                    (case !hints of NONE => ()
                     | SOME memo =>
                       let
                         val live =
                           live_check_with_hints (!owned_signatures) memo
                       in
                         if not (live source andalso live target) then ()
                         else
                           let
                             val _ = if !size < capacity then () else
                               (saved := Redblackmap.mkDict Int.compare;
                                size := 0)
                             val bucket = Option.getOpt
                               (Redblackmap.peek (!saved, key), [])
                           in
                             saved := Redblackmap.insert (!saved, key,
                               (procedure, left, right, target_key, theorem) ::
                               bucket);
                             size := !size + 1
                           end
                       end)
              in theorem end
        end
    in
      {run = run, statistics = fn () =>
        (refresh (); {hits = !hits, misses = !misses, retained = !size})}
    end

  (* A graph cache belongs to one frozen proof block. Successful entries use
     owned IDs; ownership and activity are checked before every publication. *)
  local
    open SmtReplayGraph SmtReplayProof
    structure G = SmtReplayGraph
    structure P = SmtReplayProof
  in
  fun new_graph {block, enabled, capacity} =
    let
      val _ = capacity >= 0 orelse
        raise ERR "new_graph" "negative cache capacity"
      val saved = ref (Redblackmap.mkDict Int.compare)
      val size = ref 0
      val hits = ref 0
      val misses = ref 0
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
            let
              val edge = prove ()
              val theorem = P.theorem block edge
              val expected = boolSyntax.mk_imp (source_name, target_name)
              val _ = Term.aconv (Thm.concl theorem) expected orelse
                raise ERR "new_graph" "invalid compact implication schema"
              (* Edges are abstract checked values. The owner check above
                 rejects foreign blocks without reinterpreting the shared
                 context as a new individual source hypothesis. *)
            in edge end
        in case found of
            SOME (_, _, edge) => (hits := !hits + 1; edge)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val edge = attempt ()
                val _ = ignore (P.name block source)
                val _ = ignore (P.name block target)
                val _ = if not enabled orelse capacity = 0 then () else
                  let
                    val _ = if !size < capacity then () else
                      (saved := Redblackmap.mkDict Int.compare; size := 0)
                    val bucket = Option.getOpt
                      (Redblackmap.peek (!saved, key), [])
                  in
                    saved := Redblackmap.insert (!saved, key,
                      (procedure, target_key, edge) :: bucket);
                    size := !size + 1
                  end
              in edge end
        end
    in
      {run = run, statistics = fn () =>
        {hits = !hits, misses = !misses, retained = !size}}
    end
  end
end
