structure SmtLib_GraphIntegerDivision :> SmtLib_GraphIntegerDivision =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure S = SmtReplaySource
  structure C = SmtReplayCanonGraph
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphIntegerDivision"

  fun conversion work {check_type} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources
      val scope = S.owning_scope sources
      val limits = W.semantic_limits work
      val epoch = Type.type_epoch () val symbols = Term.term_epoch ()
      fun guard () =
        (W.validate work graph scope sources limits;
         if Type.type_epoch () = epoch andalso Term.term_epoch () = symbols
           then () else raise ERR "conversion" "declaration epoch changed")
      fun step () = (guard ();W.spend work 1)
      val ediv = Term.prim_mk_const {Thy = "integer",Name = "ediv"}
      val hole = Term.mk_var ("integer_zero_divisor",intSyntax.int_ty)
      val zero = intSyntax.zero_tm
      fun divide a b = Term.list_mk_comb (ediv,[a,b])
      (* An equality is exposed as a guard, rather than introducing an
         integer conditional whose replay recreates division bounds. This
         closed identity is valid even when HOL's ediv 0 0 is not zero. *)
      val template = boolSyntax.mk_eq
        (boolSyntax.mk_eq (divide zero hole,zero),
         boolSyntax.mk_imp (boolSyntax.mk_eq (hole,zero),
           boolSyntax.mk_eq (divide zero zero,zero)))
      val law = ref NONE
      (* Quote the whole small native proof inventory before invoking the
         existing integer worker. An ineligible optional schema is a miss,
         not a new refusal or a larger template contract. *)
      fun theorem () = case !law of SOME saved => saved
        | NONE =>
          let
            val inventory = template :: List.map Thm.concl
              [integerTheory.EDIV_DEF,integerTheory.INT_DIV_0,
               integerTheory.INT_NEG_EQ0,integerTheory.INT_NEG_0]
            val sizes = List.map (SmtReplayImport.bounded_raw_size
              (#template_limit limits)) inventory
          in if not (List.all Option.isSome sizes) then NONE else
            let
              val _ = List.app (fn size => W.spend work
                (Option.valOf size)) sizes
              fun types term =
                (step ();check_type (Term.type_of term);guard ();
                 if Term.is_comb term then
                   let val (f,x) = Term.dest_comb term
                   in types f;types x end
                 else if Term.is_abs term then
                   let val (v,b) = Term.dest_abs term
                   in types v;types b end
                 else ())
              val _ = List.app types inventory
              val proved = Tactical.TAC_PROOF (([],template),
                Tactical.THEN (Tactic.ASM_CASES_TAC
                    (boolSyntax.mk_eq (hole,zero)),
                  simpLib.ASM_SIMP_TAC boolSimps.bool_ss
                    [integerTheory.EDIV_DEF,integerTheory.INT_DIV_0,
                     integerTheory.INT_NEG_EQ0,integerTheory.INT_NEG_0]))
              val _ = guard ()
              val saved = SOME (hole,proved)
              val _ = law := SOME saved
            in saved end
          end
      fun is_zero node =
        (step ();
         case G.unfolded_nodes graph G.RawNodes 8 node of NONE => false
         | SOME size => if size > 8 then false else
             (W.spend work size;
              Term.aconv (G.representative graph node) zero))
      fun propose node =
        let
          val _ = step ()
          val divisor = case SmtReplayRules.spine graph node of
              SOME (head,[left,right]) =>
                if not (Term.same_const head boolSyntax.equality) orelse
                    not (is_zero right) then NONE
                else (case SmtReplayRules.spine graph left of
                    SOME (head,[a,b]) =>
                      if Term.same_const head ediv andalso is_zero a
                          andalso not (is_zero b) then SOME b else NONE
                  | _ => NONE)
            | _ => NONE
        in case divisor of NONE => NONE
          | SOME b => (case theorem () of NONE => NONE
            | SOME (hole,theorem) =>
              let val _ = step ()
                  val schema = C.checked_graph_schema graph scope
                    {theorem = theorem,holes = [hole],operands = [b],
                     template_limit = #template_limit limits}
              in if C.graph_schema_source schema = node then SOME schema
                 else NONE end)
        end
      (* Reuse the existing memoized DAG traversal/assembler, including
         identity siblings, rather than rebuilding each sibling separately.
         Never revisit generated syntax: ediv 0 0 stays underspecified. *)
      fun convert node =
        let val _ = guard ()
            val result = C.graph_conversion_with_schemas graph scope
              {revisit = false,propose = propose,observe = step} node
        in if C.graph_source result = C.graph_result result then NONE
           else SOME result end
    in convert
    end
end
