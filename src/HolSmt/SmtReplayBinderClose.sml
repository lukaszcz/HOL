structure SmtReplayBinderClose :> SmtReplayBinderClose =
struct
  datatype kind = Forall | Exists | Lambda
  fun run representative {entries,theorem,target} =
    let
      fun add ((kind,variable),theorem) =
        let val variable = representative variable in
          case kind of Forall => Drule.FORALL_EQ variable theorem
            | Exists => Drule.EXISTS_EQ variable theorem
            | Lambda => Thm.ABS variable theorem end
      val theorem = List.foldr add theorem entries
      val exact = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem)
        (target ())) theorem
    in exact end
end
