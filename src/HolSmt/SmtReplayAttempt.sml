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
  fun same left right = Portable.pointer_eq (left, right) orelse
    Term.aconv left right
  fun new {enabled, capacity, hash} =
    let
      val _ = capacity >= 0 orelse raise ERR "new" "negative cache capacity"
      val saved = ref (Redblackmap.mkDict Int.compare)
      val size = ref 0
      val hits = ref 0
      val misses = ref 0
      fun return outcome = case outcome of
          Proved theorem => theorem
        | Satisfiable => raise HolSatLib.SAT_satisfiable ()
        | Counterexample theorem => raise HolSatLib.SAT_cex theorem
      fun run ({procedure, source, target, prove} : request) =
        let
          (* Keep user-supplied hashes separate to avoid arithmetic overflow.
             Exact typed endpoints and the procedure label decide a hit. *)
          val key = hash source
          val target_key = hash target
          val bucket = Option.getOpt (Redblackmap.peek (!saved, key), [])
          val found = if not enabled orelse capacity = 0 then NONE else
            List.find (fn (label, left, right, right_key, _) =>
              label = procedure andalso right_key = target_key andalso
              same source left andalso same target right) bucket
          fun attempt () =
            (let
               val theorem = prove ()
               val _ = List.null (Thm.hyp theorem) andalso
                   same (Thm.concl theorem) (boolSyntax.mk_imp (source, target))
                 orelse raise ERR "run" "invalid closed implication schema"
               val _ = Library.check_oracle_tags
                 "SmtReplayAttempt" "implication schema" theorem
             in Proved theorem end
             handle HolSatLib.SAT_satisfiable _ => Satisfiable
                  | HolSatLib.SAT_cex theorem => Counterexample theorem)
        in case found of
            SOME (_, _, _, _, outcome) =>
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
                      (procedure, source, target, target_key, outcome) :: bucket);
                    size := !size + 1
                  end
              in return outcome end
        end
    in
      {run = run, statistics = fn () =>
        {hits = !hits, misses = !misses, retained = !size}}
    end
end
