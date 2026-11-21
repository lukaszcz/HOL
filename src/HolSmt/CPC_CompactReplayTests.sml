(* Selected CPC bounded dispatch: actual local-law dependencies must not
   depend on whether the original common Source context fits one block. *)
structure CPC_CompactReplayTests =
struct
  open HolKernel Parse boolLib bossLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  structure Q = CPC_ProofParser
  structure F = SmtLib_GraphFrontend
  structure P = SmtLib_Parser
  structure R = CPC_GraphProofReplay
  val maximum = 512
  val goal = ``SUC (task37_n:num) = SUC task37_n``
  fun require message yes = if yes then () else raise Fail message
  fun clean theorem =
    require "unexpected proof tags"
      (null (Tag.axioms_of (Thm.tag theorem)) andalso
       List.all (fn tag => tag = "DISK_THM")
         (#1 (Tag.dest_tag (Thm.tag theorem))))
  fun exact expected hypotheses theorem =
    (require "wrong endpoint" (Term.aconv (Thm.concl theorem) expected);
     require "wrong actual canonical Hyp" (HOLset.equal
       (Thm.hypset theorem,HOLset.addList (Term.empty_tmset,hypotheses)));
     clean theorem)
  datatype result = Closed | Partial | Duplicate | Wrong | Open
  (* Wide adds unused ORIGINAL slots, not a larger native theorem. All
     cases retain the same call-site native and compact template limits. *)
  fun fixture_with depth repeated_sources wide mode action =
    let
      val assumptions = List.tabulate (if wide then 16 else 2,fn i =>
        Term.mk_var ("task37_unused_" ^ Int.toString i,Type.bool))
      val assumptions = if repeated_sources then
          [hd assumptions,hd assumptions,List.nth (assumptions,1)]
        else assumptions
      val graph = G.new () val scope = G.root_scope graph
      val sources = S.new graph scope maximum
        {goal=goal,assumptions=assumptions}
      val work = W.begin graph scope sources
        {limits={input_limit=maximum,output_limit=maximum,
          template_limit=maximum},work_limit=100000000}
      val calls = ref 0
      val outcome = Exn.capture (fn () =>
        let
          val preprocessing = GP.discover_from_sources graph scope sources
            {import_limit=maximum,revisit=false,check_type=fn _ => (),
             conversion=fn _ => NONE}
          fun located node:F.term =
            {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
             occurrence=SmtLib_Parser.ConstructionOccurrence
               {value=node,role=SmtLib_Parser.ConstructionAtom,
                token="task37",children=[]}}
          val source_nodes = S.assumption_nodes sources
          val target = #node (S.goal_source sources)
          val denied = S.denied_goal_node sources
          val registered = valOf (CPC_Proof.lookup_rule "1.3.4" "trust")
          val resolution = valOf
            (CPC_Proof.lookup_rule "1.3.4" "resolution")
          val ports = case mode of Duplicate => ["@u0","@u0","@u1"]
            | _ => ["@u0","@u1"]
          fun trust id inputs target = Q.GraphStep {pop=false,step=
            {id=id,rule=registered,premises=inputs,
             conclusion=SOME (located target),
             args=[Q.GraphTerm (located target)],
             raw_conclusion=NONE,raw_args=[]}}
          val truth = case mode of Partial => hd source_nodes
            | _ => G.constant graph scope boolSyntax.T
          val scope_rule = valOf (CPC_Proof.lookup_rule "1.3.4" "scope")
          fun nest 0 = ([],[],target,"@law")
            | nest n =
                let val (pushes,pops,body,id) = nest (n-1)
                    val name = "@scope" ^ Int.toString n
                    val closed = SmtReplayRules.implication graph scope
                      [truth] body
                    val pop = Q.GraphStep {pop=true,step=
                      {id=name,rule=scope_rule,premises=[id],
                       conclusion=SOME (located closed),args=[],
                       raw_conclusion=NONE,raw_args=[]}}
                in (Q.GraphAssumePush
                     ("@local" ^ Int.toString n,located truth)::pushes,
                    pops @ [pop],closed,name) end
          val (pushes,pops,_,closed_id) = nest depth
          val proof:Q.graph_proof =
            {cvc_version="1.3.4",commands=
              [Q.GraphAssume ("@u0",located (hd source_nodes)),
               Q.GraphAssume ("@u1",located (List.nth (source_nodes,1))),
               Q.GraphAssume ("@denied",located denied)] @ pushes @
              [trust "@law" ports target] @ pops @
              (if depth=0 then [] else
                 [trust "@apply" (closed_id ::
                   (case mode of Partial => ["@u0"] | _ => [])) target]) @
              [Q.GraphStep {pop=false,step=
                 {id="@done",rule=resolution,
                  premises=[if depth=0 then "@law" else "@apply",
                    "@denied"],
                  conclusion=SOME (located
                    (G.constant graph scope boolSyntax.F)),args=[],
                  raw_conclusion=NONE,raw_args=[]}}]}
          fun worker (request:CPC_Proof.step,inputs) =
            let
              val _ = calls := !calls+1
              val theorem = Thm.REFL ``SUC (task37_n:num)``
              fun retain () = Thm.CONJUNCT1 (Thm.CONJ theorem
                (Thm.ASSUME (#term (hd inputs:CPC_Proof.located_term))))
              fun apply 0 theorem = theorem
                | apply n theorem = apply (n-1)
                    (Thm.MP theorem (case mode of Partial =>
                      Thm.ASSUME (hd assumptions)
                    | _ => boolTheory.TRUTH))
              val theorem = if #id request="@apply" then
                  apply depth (Thm.ASSUME
                    (#term (hd inputs:CPC_Proof.located_term)))
                else case mode of Closed => theorem
                | Partial => retain () | Duplicate => retain ()
                | Wrong => boolTheory.TRUTH
                | Open => Thm.CONJUNCT1 (Thm.CONJ theorem
                    (Thm.ASSUME ``task37_foreign:bool``))
            in (theorem,valOf (#conclusion request)) end
          val checked = Exn.capture (fn () =>
            R.prove_preprocessed_with_work_using work
              {graph=graph,scope=scope,sources=sources,
               preprocessing=preprocessing,proof=proof,
               ordinary_limit=maximum,template_limit=maximum,
               worker=worker,force_worker=NONE}) ()
        in action sources assumptions (!calls) checked end) ()
      val cleanup = Exn.capture (fn () =>
        (W.close work;G.close_scope graph scope)) ()
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end
  fun fixture wide mode = fixture_with 0 false wide mode
  fun positive_with depth repeated wide mode () =
    fixture_with depth repeated wide mode
    (fn sources => fn assumptions => fn calls => fn result =>
      let val theorem = Exn.release result
          val expected = case mode of Closed => []
            | _ => [hd assumptions]
      in S.check_goal sources theorem;exact goal expected theorem;
         require "retained worker law was skipped or rediscovered"
           (calls=(if depth=0 then 1 else 2))
      end)
  fun positive wide mode = positive_with 0 false wide mode
  fun negative mode () = fixture false mode
    (fn _ => fn _ => fn calls => fn result =>
      require "malformed local certificate accepted or retried"
        (calls=1 andalso (case result of
           Exn.Exn (Feedback.HOL_ERR _) => true | _ => false)))
  fun projections invalid () =
    let
      val graph = G.new ()
      val scope = G.root_scope graph
      val assumption = ``projection_p /\ projection_q /\ F``
      val sources = S.new graph scope maximum
        {goal=boolSyntax.T,assumptions=[assumption]}
      val source = hd (S.assumption_nodes sources)
      fun node term = #node (G.import graph scope maximum term)
      val p = node ``projection_p:bool``
      val q = node ``projection_q:bool``
      val falsity = node boolSyntax.F
      val tail = node ``projection_q /\ F``
      fun occurrence role token children node = P.ConstructionOccurrence
        {value=node,role=role,token=token,children=children}
      val atom = occurrence P.ConstructionAtom ""
      val conj = occurrence P.ConstructionApplication "and"
      fun located node occurrence : F.term =
        {node=node,scope=scope,binder_blocks=[],source_syntax=NONE,
         occurrence=occurrence}
      val tail_syntax = conj [atom [] q,atom [] falsity] tail
      val flat = located source
        (conj [atom [] p,atom [] q,atom [] falsity] source)
      val nested = located source (conj [atom [] p,tail_syntax] source)
      val q_term = located q (atom [] q)
      val false_term = located falsity (atom [] falsity)
      val tail_term = located tail tail_syntax
      val rule = valOf (CPC_Proof.lookup_rule "1.3.4" "and_elim")
      fun project id premise index target = Q.GraphStep {pop=false,step=
        {id=id,rule=rule,premises=[premise],conclusion=SOME target,
         args=[Q.GraphIndex index],raw_args=[],raw_conclusion=NONE}}
      val proof : Q.graph_proof = {cvc_version="1.3.4",commands=
        [Q.GraphAssume ("@flat",flat),Q.GraphAssume ("@nested",nested),
         project "@q1" "@flat" 1 q_term,project "@q2" "@flat" 1 q_term] @
        (case invalid of
           SOME index => [project "@done" "@flat" index false_term]
         | NONE =>
             [project "@tail" "@nested" 1 tail_term,
              project "@q3" "@flat" 1 q_term,
              project "@done" "@tail" 1 false_term])}
      exception Fallback
      val result = Exn.capture (fn () =>
        let val contradiction = R.check_contradiction
              {graph=graph,scope=scope,sources=sources,proof=proof,
               ordinary_limit=maximum,template_limit=maximum,
               worker=fn _ => raise Fallback}
        in S.close_contradiction sources contradiction end) ()
      val _ = G.close_scope graph scope
    in case invalid of
         NONE => exact boolSyntax.T [assumption] (Exn.release result)
       | SOME _ => require "out-of-range cached projection accepted"
           (case result of Exn.Exn Fallback => true
              | Exn.Exn (Feedback.HOL_ERR _) => true | _ => false)
    end
  fun test label action =
    (testutils.tprint label;action ();testutils.OK ())
  fun run () =
    (test "CPC fitting law drops all unused original Sources"
       (positive false Closed);
     test "CPC wider law drops all unused original Sources"
       (positive true Closed);
     test "CPC fitting law retains only its checked actual Hyp"
       (positive false Partial);
     test "CPC wider law retains only its checked actual Hyp"
       (positive true Partial);
     test "CPC fitting law discharges duplicate ports once"
       (positive false Duplicate);
     test "CPC wider law discharges duplicate ports once"
       (positive true Duplicate);
     test "CPC distinct equal original ports retain one actual Source"
       (positive_with 0 true false Partial);
     test "CPC scoped-only pruning propagates to the parent"
       (positive_with 1 false false Closed);
     test "CPC nested scopes discharge used locals before original Hyp"
       (positive_with 2 false false Partial);
     test "CPC wrong local-law endpoint rejects" (negative Wrong);
     test "CPC unrelated local-law Hyp rejects" (negative Open);
     test "CPC repeated projections respect each occurrence"
       (projections NONE);
     test "CPC cached projections reject high indices" (projections (SOME 3));
     test "CPC cached projections reject negative indices"
       (projections (SOME (~1))))
end
