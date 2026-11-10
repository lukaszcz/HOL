structure SmtReplaySimultaneousRealization :>
    SmtReplaySimultaneousRealization =
struct
  structure O = SmtReplayRuleObservation
  fun clean proof =
    let val (oracles,_) = Tag.dest_tag (Thm.tag proof)
    in List.all (fn oracle => oracle="DISK_THM") oracles andalso
      null (Tag.axioms_of (Thm.tag proof)) end
  fun close {guard,error,contexts,proof} =
    let
      fun discharge [] = proof
        | discharge [context] = O.DISCH context proof
        | discharge (context::rest) =
            let val tail = discharge rest val _ = guard ()
            in O.DISCH context tail end
      val _ = guard ()
      val law = discharge contexts
      val _ = if null (Thm.hyp law) andalso clean law then () else
        raise error "compact law is not closed"
    in law end
  fun instantiate {guard,error,contexts,proof,substitution} =
    let
      val law = close
        {guard=guard,error=error,contexts=contexts,proof=proof}
      val _ = guard ()
      val result = O.INST substitution law
      val _ = guard ()
    in result end
  (* Keep every component CLOSED until after the single INST. Projecting
     the resulting forest before applying witnesses preserves each result's
     own Hyp (including a CLOSED/Original collision). No expanded theorem
     is substituted, retyped, matched or simplified. The forest contains
     only the already admitted compact component laws and Boolean shells. *)
  fun instantiate_batch {guard,error,proofs,substitution} =
    case proofs of [] => (guard ();[])
      | [contexts_and_proof] =>
          let val (contexts,proof)=contexts_and_proof
          in [instantiate {guard=guard,error=error,contexts=contexts,
            proof=proof,substitution=substitution}] end
      | _ =>
        let
          val laws=Vector.fromList (List.map (fn (contexts,proof) =>
            close {guard=guard,error=error,contexts=contexts,proof=proof})
              proofs)
          val tree=SmtReplayNamedContext.make_tree 0 (Vector.length laws)
          val _=guard ()
          val forest=SmtReplayNamedContext.tree_proof laws tree
          val _=guard ()
          val expanded=O.INST substitution forest
          val _=guard ()
          val results=SmtReplayNamedContext.project tree expanded
          val _=guard ()
        in results end
  fun apply {guard,law,witnesses} =
    let
      fun loop current [] = current
        | loop current (proof::rest) =
            let val _ = guard () val result = O.MP current proof
                val _ = guard ()
            in loop result rest end
    in loop law witnesses end
end
