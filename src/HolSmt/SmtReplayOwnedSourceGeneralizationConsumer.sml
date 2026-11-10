structure SmtReplayOwnedSourceGeneralizationConsumer :>
  SmtReplayOwnedSourceGeneralizationConsumer =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure R = SmtReplayRules
  structure Scope = SmtReplayOwnedScopeReceipt
  val _ = SmtReplayProof.source_cut_support_edges_for
  val _ = SmtReplayRules.apply_law
  val _ = SmtReplayOwnedScopeReceipt.description_for
  val ERR = Feedback.mk_HOL_ERR "SmtReplayOwnedSourceGeneralizationConsumer"

  fun execute expected {generalized,check_type} =
    ((let
        (* This opaque-result getter fences expected W before any held
           parent, Scope or proof activation. *)
        val generated = P.source_generalization_data_for expected generalized
        val parent = #source generated
        val data = P.source_realization_data_for expected parent
        val graph = #graph data and scope = #scope data
        val frame = #frame data and target = #target generated
        val cap = #template_limit data
        val proof = #theorem generated
        val hypotheses = Thm.hyp proof
        fun guard () =
          (ignore (P.source_generalization_data_for expected generalized);
           ignore (P.source_realization_data_for expected parent);
           ignore (Scope.description_for expected frame))
        fun raw term = case SmtReplayImport.bounded_raw_size cap term of
            SOME n => n | NONE => raise ERR "execute"
              "actual closed GEN law exceeds original raw cap"
        fun inclusive term =
          case SmtReplayImport.bounded_binder_size cap term of
            SOME n => n | NONE => raise ERR "execute"
              "actual closed GEN law exceeds original binder cap"
        fun supported hypothesis = List.exists (fn (_,node) =>
          Portable.pointer_eq (hypothesis,G.representative graph node))
          (#source_occurrences data)
        val law_data = W.with_step expected (fn () =>
          let
            val _ = guard ()
            val _ = if List.all supported hypotheses then () else
              raise ERR "execute" "GEN Hyp escaped genuine Source supports"
            val conclusion = Thm.concl proof
            (* Each DISCH adds the actual implication shell before its
               public proof operation. No late large insertion under GEN. *)
            fun future count (hypothesis,size) =
              let val operand = count hypothesis
              in if cap<3 orelse size>cap-3-operand then
                raise ERR "execute" "prospective closed GEN law exceeds cap"
                else size+3+operand end
            val raw_law = List.foldl (future raw)
              (raw conclusion) hypotheses
            val inc_law = List.foldl (future inclusive)
              (inclusive conclusion) hypotheses
            val _ = if raw_law<=cap andalso inc_law<=cap then () else
              raise ERR "execute" "prospective closed GEN law exceeds cap"
            val _ = W.spend expected raw_law
            val _ = W.spend expected inc_law
            val types = ref ([] : Type.hol_type list)
            fun ty value =
              (W.spend expected 1;types := value :: !types;
               if Type.is_vartype value then () else
                 List.app ty (#2 (Type.dest_type value)))
            fun term value =
              (W.spend expected 1;ty (Term.type_of value);
               if Term.is_comb value then
                 let val (f,x) = Term.dest_comb value
                 in term f;term x end
               else if Term.is_abs value then
                 let val (v,b) = Term.dest_abs value
                 in term v;term b end else ())
            val _ = List.app term (conclusion::hypotheses)
            (* Every future implication contributes its real constant,
               partial-application and Boolean result annotations. *)
            val _ = List.app (fn _ =>
              (ty (Term.type_of boolSyntax.implication);
               ty (Term.type_of boolSyntax.negation);ty Type.bool)) hypotheses
            val _ = List.app (fn value =>
              (guard ();check_type value;guard ())) (List.rev (!types))
            val _ = guard ()
            val _ = W.spend expected (length hypotheses+1)
            val law = List.foldr (fn (hypothesis,theorem) =>
              SmtReplayRuleObservation.DISCH hypothesis theorem)
              proof hypotheses
            val _ = if null (Thm.hyp law) andalso
                null (Tag.axioms_of (Thm.tag law)) then () else
              raise ERR "execute" "actual GEN law was not closed cleanly"
            val source = G.import graph scope cap (Thm.concl law)
            val _ = guard ()
            (* Preserve this exact import and its admitted opened binder
               construction, rather than guessing auxiliary binder data. *)
            val opened = G.record_opened_view graph scope cap (#node source)
            fun law_guard () =
              (guard ();G.validate_opened_view graph scope (#node source)
                opened;ignore (G.imported_opened_source graph scope
                  (Thm.concl law) (#node opened)))
            val _ = law_guard ()
            val fact = P.record_closed_from_import graph scope
              {node = #node opened,theorem=law,template_limit=cap,
               check_type=fn value =>
                 (law_guard ();check_type value;law_guard ())}
            val _ = law_guard ()
            (* Opened binder nodes carry distinct graph identities. Their
               real checked bridges remain explicit conversion witnesses. *)
            fun bridge original =
              let val view = G.cached_opened_view graph scope original
                  val destination = #node view
              in if original=destination then
                  {source=original,target=destination,conversion=NONE}
                else
                  let val next = G.record_opened_view graph scope cap
                        destination
                      fun bridge_guard () =
                        (law_guard ();
                         G.validate_opened_view graph scope original view;
                         G.validate_opened_view graph scope destination next)
                      val _ = bridge_guard ()
                      val conversion = P.record_conversion graph scope
                        {source=original,source_view=view,target=destination,
                         target_view=next,theorem= #bridge view,
                         template_limit=cap,check_type=fn ty =>
                           (bridge_guard ();check_type ty;bridge_guard ())}
                      val _ = bridge_guard ()
                  in {source=original,target=destination,
                    conversion=SOME conversion} end
              end
            val target_bridge = bridge target
            fun hypothesis_node hypothesis =
              case List.find (fn (_,node) => Portable.pointer_eq
                  (hypothesis,G.representative graph node))
                  (#source_occurrences data) of
                SOME (_,node) => node | NONE => raise ERR "execute"
                  "actual GEN Hyp has no genuine Source occurrence"
            val hypothesis_bridges = List.map
              (bridge o hypothesis_node) hypotheses
            val _ = guard ()
          in {fact=fact,target_bridge=target_bridge,
            hypothesis_bridges=hypothesis_bridges} end)
        val fact = #fact law_data
        val target_bridge = #target_bridge law_data
        val hypothesis_bridges = #hypothesis_bridges law_data
        val conversions = List.mapPartial #conversion
          (target_bridge::hypothesis_bridges)
        val value = P.prepare_retained_source_cut_rule_block expected
          {frame=frame,roots=[],additional_sources=[],closed_facts=[fact],
           conversions=conversions,receipts=[parent],
           targets=[target,#target target_bridge],boolean=true,
           congruence=false}
        val block = P.source_cut_block_for expected value
        val supports = P.source_cut_support_edges_for expected value parent
        val edge = W.with_step expected (fn () =>
          let
            val _ = guard ()
            val _ = P.validate_block_for expected block
            fun primitive recipe edges = P.execute_primitive expected
              (P.prepare_primitive expected block recipe edges)
            fun opened_support (node,edge) =
              case List.find (fn value => #source value=node)
                  hypothesis_bridges of
                NONE => (node,edge)
              | SOME value => case #conversion value of
                  NONE => (node,edge)
                | SOME conversion => (#target value,
                    primitive P.EqualityMP [P.conversion block conversion,
                      edge])
            val actual_supports = List.map opened_support supports
            val generated = R.apply_law graph block
              {law=(P.closed_node fact,P.closed block fact),
               target= #target target_bridge,premises=actual_supports}
            val result = case #conversion target_bridge of NONE => generated
              | SOME conversion => primitive P.EqualityMP
                  [primitive P.Symmetry [P.conversion block conversion],
                   generated]
            val _ = guard ()
          in result end)
        val result = P.realize_source_cut_receipt expected value target edge
        val actual = P.source_realization_data_for expected result
        val theorem = P.source_realization_theorem_for expected result
        val _ = guard ()
        val _ = if #target actual=target andalso
            Portable.pointer_eq (#original_sources actual,
              #original_sources data) andalso
            Portable.pointer_eq (Thm.concl theorem,
              G.representative graph target) andalso
            ListPair.allEq Portable.pointer_eq
              (Thm.hyp theorem,hypotheses) andalso
            null (Tag.axioms_of (Thm.tag theorem)) then () else
          raise ERR "execute" "actual generated Source result changed"
      in result end)
     handle primary => (W.close expected;raise primary))
end
