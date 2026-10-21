structure SmtReplaySimultaneousRealization :>
    SmtReplaySimultaneousRealization =
struct
  structure O = SmtReplayRuleObservation
  fun clean proof =
    let val (oracles,_) = Tag.dest_tag (Thm.tag proof)
    in List.all (fn oracle => oracle="DISK_THM") oracles andalso
      null (Tag.axioms_of (Thm.tag proof)) end
  fun instantiate {guard,error,contexts,proof,substitution} =
    let
      fun close [] = proof
        | close [context] = O.DISCH context proof
        | close (context::rest) =
            let val tail = close rest val _ = guard ()
            in O.DISCH context tail end
      val _ = guard ()
      val law = close contexts
      val _ = if null (Thm.hyp law) andalso clean law then () else
        raise error "compact law is not closed"
      val _ = guard ()
      val result = O.INST substitution law
      val _ = guard ()
    in result end
  fun apply {guard,law,witnesses} =
    let
      fun loop current [] = current
        | loop current (proof::rest) =
            let val _ = guard () val result = O.MP current proof
                val _ = guard ()
            in loop result rest end
    in loop law witnesses end
end
