(* The ordinary owned O facade; proof/context engine remains in Core. *)
structure SmtReplayOwnedLargeProofAssembly :> SmtReplayOwnedLargeProofAssembly =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure O = SmtReplayOwnedCompactApplication
  structure Core = SmtReplayOwnedLargeProofCore
  val _ = SmtReplayOwnedLargeProofCore.prepare
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedLargeProofAssembly"
  type summary = Core.summary
  datatype plan = Plan of {work : W.portfolio,conversion : O.plan,
                           core : Core.plan}
  datatype result = Result of {plan : plan,core : Core.result}
  fun protected work action = action ()
    handle primary => (W.close work;raise primary)
  fun expected work =
    let val sources = W.original_sources work
    in {graph = S.owning_graph sources,scope = S.owning_scope sources,
        sources = sources,work = work} end
  fun validate work (Plan {work = held,conversion,...}) =
    protected work (fn () =>
      (if Portable.pointer_eq (work,held) then () else
         raise ERR "validate" "different original Work";
       ignore (O.graph_conversion_for (expected work) conversion)))
  fun prepare work {conversion,ordinal,check_type} = protected work (fn () =>
    let val converted = O.graph_conversion_for (expected work) conversion
        val core = Core.prepare work
          {conversion = converted,ordinal = ordinal,check_type = check_type}
        val plan = Plan {work = work,conversion = conversion,core = core}
        val _ = validate work plan
    in plan end)
  fun report (Plan {core,...}) = Core.report core
  fun execute work (plan as Plan {core,...}) = protected work (fn () =>
    let val _ = validate work plan
        val result = Core.execute work core
        val _ = validate work plan
    in Result {plan = plan,core = result} end)
  fun theorem_for work (Result {plan,core}) =
    (validate work plan;Core.theorem_for work core)
  fun conversion_description_for work (Result {plan,core}) =
    let val _ = validate work plan
        val description = Core.conversion_description_for work core
    in {graph = #graph description,scope = #scope description,
        sources = #sources description,source = #source description,
        target = #target description} end
end
