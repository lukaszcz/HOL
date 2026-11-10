(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphQueryAvailability :> SmtLib_GraphQueryAvailability =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  fun compare_key ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of
      EQUAL => Int.compare (ln,rn) | result => result
  fun check (context:Q.outbound_context) {sequence_emission,target} =
    let
      fun guard current = ignore ((#key context) current)
      val _ = guard (#goal context)
      val seen = ref (Redblackset.empty compare_key)
      val constants = ref ([] : (Q.carrier * Term.term) list)
      val visits = ref 0
      fun inventory [] = ()
        | inventory (current :: pending) =
            let val key = (#key context) current in
              if Redblackset.member (!seen,key) then inventory pending
              else
                let
                  val _ = (#step context) ()
                  val next = case (#view context) current of
                      Q.ApplicationView (function,argument) =>
                        [function,argument]
                    | Q.AbstractionView (_,body) => [body]
                    | Q.ConstantView atom =>
                        (constants := (current,atom) :: !constants;[])
                    | Q.VariableView _ => []
                  val _ = guard current val _ = List.app guard next
                  val _ = seen := Redblackset.add (!seen,key)
                  val _ = visits := !visits+1
                in inventory (next @ pending) end
            end
      val _ = inventory (#goal context :: #assumptions context)
      fun occurs expected = List.exists (fn (current,atom) =>
        let val _ = guard current
            (* The native occurrence probe is directional Term.same_const;
               its HOL_ERR catch encloses only these atomic observations. *)
            val answer = Term.same_const atom expected
              handle Feedback.HOL_ERR _ => false
            val _ = guard current
        in answer end) (!constants)
      val _ = SmtLib.outbound_check_operator_availability
        {sequence_emission=sequence_emission} target occurs
      val _ = guard (#goal context)
    in {visits= !visits} end
end
