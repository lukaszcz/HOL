(* Task43: FP operator custody, generic rule identity and source isolation. *)
structure SmtReplayFpTests =
struct
  open HolKernel Parse boolLib bossLib
  structure H = SmtReplayArithmeticTests
  structure G = SmtReplayGraph
  structure Q = CPC_ProofParser
  structure F = SmtLib_GraphFrontend
  val require = H.require
  val exact = SmtReplayStructuredTests.exact
  val limit = H.limit

  fun classification () =
    let
      fun shared 0 = Type.bool
        | shared n = let val child = shared (n-1)
                     in pairSyntax.mk_prod (child,child) end
      fun check depth =
        let
          val large = shared depth
          val absent = Term.mk_var ("fp_absent",large)
          val present = Term.mk_var ("fp_present",
            pairSyntax.mk_prod (large,``:(4,3)smtfp``))
          val rounding = Term.mk_var ("fp_rounding",
            pairSyntax.mk_prod (large,``:smt_rounding``))
        in require "shared non-FP Type classified as FP"
             (not (SmtFpProve.has_fp_theory_term absent));
           require "shared Type hid its FP suffix"
             (SmtFpProve.has_fp_theory_term present);
           require "shared Type hid its rounding suffix"
             (SmtFpProve.has_fp_theory_term rounding)
        end
      fun independent count =
        let
          val terms = List.tabulate (count,fn i =>
            let val x = Term.mk_var ("fp_independent",
                  Type.mk_vartype ("'fp_independent" ^ Int.toString i))
            in boolSyntax.mk_eq (x,x) end)
        in require "independent non-FP annotations classified as FP"
             (not (SmtFpProve.has_fp_theory_term
               (boolSyntax.list_mk_conj terms))) end
    in List.app check [21,80];List.app independent [256,512,1024] end

  (* Naming retains the previous generic worker's FULL primitive Type
     allowance. Task30's prefix-only producer admission is a separate route;
     its depth21/80 polymorphic positives must not be relabelled negatives. *)
  fun type_route_frontier () =
    let
      fun shared 0 = Type.bool
        | shared n = let val child = shared (n-1)
                     in pairSyntax.mk_prod (child,child) end
      fun gate_message action =
        (action ();raise Fail "oversized generic FP Type was admitted")
        handle Feedback.HOL_ERR error =>
          if SmtResource.is_resource_gate error andalso
             String.isSubstring "word-graph-primitive-type-tree"
               (Feedback.message_of error) then Feedback.message_of error
          else raise Feedback.HOL_ERR error
      fun check depth = H.with_graph (fn graph => fn scope =>
        let
          val dimension = pairSyntax.mk_prod
            (Type.mk_vartype "'fp_prefix",shared depth)
          val ty = Type.mk_thy_type
            {Thy="smtfloat",Tyop="smtfp",Args=[dimension,dimension]}
          val x = Term.mk_var ("fp_suffix",ty)
          val target = H.import graph scope (boolSyntax.mk_eq (x,x))
          val proof:Z3_GraphProofParser.proof =
            {steps=Redblackmap.mkDict Z3_GraphProofParser.compare_id,
             root=Z3_GraphProofParser.Anonymous 0,vars=[],
             z3_version="4.15.3",close=fn () => ()}
          val request:Z3_GraphProofReplay.local_request =
            {rule=valOf (Z3_Proof.lookup_rule "4.15.3" "rewrite"),
             metadata=NONE,target=target,premises=[],arguments=[],law=target}
          fun previous_gate () =
            let val admission = SmtWordGraph.new_type_admission ()
            in List.app (fn node => SmtWordGraph.admit_primitive_type
                 admission (G.type_of graph node))
                 (G.block_reachable graph [target]) end
          val previous = gate_message previous_gate
          val current = gate_message (fn () => ignore
            (Z3_ProofReplay.graph_bounded_local_law graph [] proof request))
        in require "named FP route changed the exact primitive Type gate"
             (previous = current)
        end)
    in List.app check [21,80] end

  fun generic_identities () = List.app H.z3_generic_identity_type
    [(``fp_generic:(4,3)smtfp``,``smtfp_pzero:(4,3)smtfp``),
     (``fp_generic:smt_rounding``,``RNE``)]

  (* Neither pattern matching nor proof transport may hide an operator,
     rounding mode, literal, repeated operand or actual source relationship. *)
  fun operators () = H.with_graph (fn graph => fn scope =>
    let
      val goals =
        [``smtfp_abs (smtfp_abs (x:(4,3)smtfp)) = smtfp_abs x``,
         ``smtfp_neg (smtfp_neg (x:(4,3)smtfp)) = x``,
         ``smtfp_add RNE (smtfp_bits 0w 3w 0w : (4,3)smtfp)
             (smtfp_bits 0w 3w 0w) = smtfp_bits 0w 4w 0w``,
         ``smtfp_unpack_rounding (smtfp_pack_rounding RNE) = RNE``]
      fun check original =
        let
          val calls = ref 0
          fun procedure [named] =
                let
                  val _ = calls := !calls+1
                  val _ = require "FP source variables reached worker"
                    (H.disjoint [original] [named])
                  val (substitution,types) = Term.match_term original named
                  val _ = require "FP operator, field or mode was hidden"
                    (null types andalso List.all
                      (fn {residue,...} => Term.is_var residue) substitution)
                in SmtFpProve.fp_prove named end
            | procedure _ = raise Fail "FP schema arity"
          val result = SmtReplayArithmetic.prove graph scope
            {inputs=[H.import graph scope original],template_limit=limit,
             observe=fn _ => (),procedure=procedure}
          val native = SmtFpProve.fp_prove original
          val _ = require "FP worker was retried or bypassed" (!calls=1)
          val _ = require "FP transport changed full tags"
            (Tag.dest_tag (Thm.tag native) =
             Tag.dest_tag (Thm.tag (#theorem result)))
        in exact original [] (#theorem result) end
      val _ = List.app check goals
      val _ = require "false FP field obligation accepted"
        (H.refuses (fn () => check
          ``smtfp_bits 0w 3w 0w = (smtfp_pzero:(4,3)smtfp)``))
      val _ = require "false FP repeated-operand schema accepted"
        (H.refuses (fn () => check
          ``smtfp_neg (smtfp_neg (x:(4,3)smtfp)) = y``))
    in () end)

  (* A native SELECT source contains beta redexes on purpose. Normalizing
     the generic canonical-fields law must not normalize inside that source,
     for the admitted binder sizes used by this native bridge. Larger
     source fields stay on Task30's checked graph-hole transport route. *)
  fun canonical_sources () =
    let
      val schema = Conv.CONV_RULE (Conv.TOP_DEPTH_CONV Thm.BETA_CONV)
        smtfloatReplayRoundingTheory.smtfp_rep_canonical_fields
      fun check depth =
        let
          val value = ``fp_choice:(4,3)smtfp``
          val redex = ``(\p:bool. p) (smtfp_is_nan ^value)``
          val body = funpow depth (fn term =>
            boolSyntax.mk_conj (term,term)) redex
          val source = boolSyntax.mk_select (value,body)
          val expected = Drule.ISPECL [source] (Drule.GEN_ALL schema)
          val theorem = SmtFpProve.canonical_fields source
          val _ = require "canonical FP source endpoint/Hyp changed"
            (Thm.concl theorem ~~ Thm.concl expected andalso
             null (Thm.hyp theorem))
          val _ = require "canonical FP source acquired different tags"
            (Tag.dest_tag (Thm.tag theorem) =
             Tag.dest_tag (Thm.tag expected))
          val _ = require "canonical fields normalized its SELECT source"
            (SmtResource.contains (fn term =>
              Portable.pointer_eq (term,source)) (Thm.concl theorem))
        in () end
    in List.app check [0,8,12] end

  (* Exercise the real CPC compact consumer, not just a renamed native law.
     Different graph declarations deliberately have identical native terms.
     evaluate must compare its result/argument in the injective namespace. *)
  fun cpc_identities () =
    let
      fun check native different = H.with_graph (fn graph => fn scope =>
        let
          val left = G.variable graph scope G.RigidSource native
          val right = G.variable graph scope G.Generated native
          fun app f x = G.application graph scope (f,x)
          val eq = G.constant graph scope (Term.rator (Term.rator
            (boolSyntax.mk_eq (native,native))))
          fun equality right = app (app eq left) right
          val iff = G.constant graph scope
            (Term.rator (Term.rator ``(p:bool) = q``))
          fun goal right = app (app iff (equality right))
            (G.constant graph scope boolSyntax.T)
          val good = goal left
          val bad = goal right
          val original = G.representative graph good
          val unused = ``fp_unused:bool``
          val sources = SmtReplaySource.new graph scope limit
            {goal=original,assumptions=[unused]}
          val _ = require "FP Source import changed declaration identity"
            (#node (SmtReplaySource.goal_source sources) = good)
          fun loc node:F.term =
            {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
             occurrence=SmtLib_Parser.ConstructionOccurrence
               {value=node,role=SmtLib_Parser.ConstructionAtom,
                token="fp",children=[]}}
          fun rule name = valOf (CPC_Proof.lookup_rule "1.3.4" name)
          val proof:Q.graph_proof =
            {cvc_version="1.3.4",commands=
              [Q.GraphAssume ("@denied",loc
                 (SmtReplaySource.denied_goal_node sources)),
               Q.GraphStep {pop=false,step=
                 {id="@fp",rule=rule "evaluate",premises=[],
                  conclusion=SOME (loc (if different then bad else good)),
                  args=[Q.GraphTerm (loc (equality left))],
                  raw_conclusion=NONE,raw_args=[]}},
               Q.GraphStep {pop=false,step=
                 {id="@done",rule=rule "resolution",
                  premises=["@fp","@denied"],
                  conclusion=SOME (loc (G.constant graph scope boolSyntax.F)),
                  args=[],raw_conclusion=NONE,raw_args=[]}}]}
          fun replay () = CPC_ProofReplay.prove_graph_proof
            {graph=graph,scope=scope,sources=sources,proof=proof}
        in if different then
             require "CPC FP evaluate merged graph declarations"
               (SmtReplayStructuredTests.declines (fn () => SOME (replay ())))
           else exact original [unused] (replay ())
        end)
      fun pair native = (check native false;check native true)
    in List.app pair [``fp_cpc:(4,3)smtfp``,``fp_cpc:smt_rounding``] end

  fun run () =
    let fun test name action =
      (testutils.tprint ("Task43 " ^ name);action ();testutils.OK ())
    in test "shared Type dispatch" classification;
       test "generic Type frontier" type_route_frontier;
       test "Z3 FP/rounding identities" generic_identities;
       test "FP operator schemas" operators;
       test "canonical SELECT isolation" canonical_sources;
       test "CPC FP/rounding identities" cpc_identities
    end
end
