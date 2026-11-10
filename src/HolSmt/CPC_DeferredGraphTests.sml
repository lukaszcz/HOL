(* Permanent Task46 selected-graph deferred controls. No solver, unbounded
   search, or production hooks: all native laws below are kernel
   reflexivity/SPEC, followed by the graph's actual contradiction resolution.
   Scope-pop controls reuse CPC_CompactReplayTests' checked fixtures.
   Only the separately exported deadline() sleeps; run() stays fast. *)
structure CPC_DeferredGraphTests =
struct
  open HolKernel Parse boolLib bossLib
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure GP = SmtLib_GraphPreprocess
  structure Q = CPC_ProofParser
  structure F = SmtLib_GraphFrontend
  structure R = CPC_GraphProofReplay
  val maximum = 512
  val allowance = 10000000
  fun require message yes = if yes then () else raise Fail message
  fun test label action =
    (testutils.tprint label;action ();testutils.OK ())
  fun finally action cleanup =
    let val result = Exn.capture action ()
        val closed = Exn.capture cleanup ()
    in case result of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release closed;value) end
  fun exact goal hypotheses theorem =
    (require "wrong deferred endpoint" (Term.aconv (Thm.concl theorem) goal);
     (if HOLset.equal (Thm.hypset theorem,
         HOLset.addList (Term.empty_tmset,hypotheses)) then () else
        let fun terms ts = String.concatWith "; "
              (List.map term_to_string ts)
        in raise Fail ("wrong deferred actual Hyp at " ^
          term_to_string goal ^ ": expected {" ^ terms hypotheses ^
          "}, actual {" ^ terms (Thm.hyp theorem) ^ "}") end);
     require "unclean deferred proof tags"
       (null (Tag.axioms_of (Thm.tag theorem)) andalso
        List.all (fn tag => tag="DISK_THM")
          (#1 (Tag.dest_tag (Thm.tag theorem)))))

  type env = {graph:G.graph,scope:G.scope,sources:S.sources,
    variables:Term.term list,seeds:Term.term list,targets:Term.term list,
    obligations:Term.term list,premise:Term.term}
  fun world_with use_source action =
    let
      val variables = [``task46_n:num``,``task46_b:bool``]
      val seeds = [``SUC 0``,boolSyntax.T]
      val targets = List.map (fn term => boolSyntax.mk_eq (term,term)) seeds
      (* Closed direct obligations keep this test on actual dependency
         closure, not the separate bounded opaque-binder adapter. *)
      val obligations = targets
      val premise = if use_source then
          boolSyntax.mk_conj (hd obligations,boolSyntax.T)
        else ``task46_unused_source:bool``
      val graph = G.new () val scope = G.root_scope graph
      val sources = S.new graph scope maximum
        {goal=hd targets,assumptions=[premise,premise]}
      val e:env = {graph=graph,scope=scope,sources=sources,
        variables=variables,seeds=seeds,targets=targets,
        obligations=obligations,premise=premise}
    in finally (fn () => action e) (fn () => G.close_scope graph scope) end
  fun world action = world_with false action
  (* Source bindings, like Work, are single-attempt objects. Reacquire the
     SAME original term objects on the SAME live graph for a fresh attempt. *)
  fun reacquire (e:env) : env =
    let
      val (assumptions,goal) = S.original_goal (#sources e)
      val sources = S.new (#graph e) (#scope e) maximum
        {goal=goal,assumptions=assumptions}
      val _ = require "retry reused the consumed Source binding"
        (not (Portable.pointer_eq (sources,#sources e)))
    in {graph= #graph e,scope= #scope e,sources=sources,
        variables= #variables e,seeds= #seeds e,targets= #targets e,
        obligations= #obligations e,premise= #premise e} end
  fun located (e:env) node:F.term =
    {node=node,scope= #scope e,binder_blocks=[],source_syntax=NONE,
     occurrence=SmtLib_Parser.ConstructionOccurrence
       {value=node,role=SmtLib_Parser.ConstructionAtom,
        token="task46-deferred",children=[]}}
  fun imported (e:env) term =
    #node (G.import (#graph e) (#scope e) maximum term)
  fun command e id rule premises node = Q.GraphStep {pop=false,step=
    {id=id,rule=valOf (CPC_Proof.lookup_rule "1.3.4" rule),
     premises=premises,conclusion=SOME (located e node),
     args=if rule="trust" then [Q.GraphTerm (located e node)] else [],
     raw_conclusion=NONE,raw_args=[]}}
  datatype shape = Single of bool | Cycle of bool
  fun certificate (e:env) shape : Q.graph_proof =
    let
      val first = imported e (hd (#targets e))
      val second = imported e (List.nth (#targets e,1))
      val h1 = imported e (hd (#obligations e))
      val h2 = imported e (List.nth (#obligations e,1))
      val extras = case shape of Single false => []
        | Single true => [command e "@copy" "trust"
            (List.tabulate (8,fn _ => "@need1")) first]
        | Cycle broken =>
            [command e "@need2" "trust" ["@context"] second,
             command e "@cross1" "trust" ["@need2"] h1,
             command e "@cross2" "trust"
               (if broken then [] else ["@need1"]) h2]
      val last = case shape of Single true => "@copy" | _ => "@need1"
    in {cvc_version="1.3.4",commands=
      (* Record an original port that the native need laws genuinely do
         NOT use. Its removal selects sparse/Source-cut replay. Without
         this, fitting common-context replay deliberately retains unused
         original Sources (including the free-variable denied goal in a
         cycle candidate), so [] is not its promised actual Hyp. *)
      [Q.GraphAssume ("@context",located e
         (hd (S.assumption_nodes (#sources e)))),
       Q.GraphAssume ("@denied",located e
         (S.denied_goal_node (#sources e))),
       command e "@need1" "trust" ["@context"] first] @ extras @
      [command e "@done" "resolution" [last,"@denied"]
        (G.constant (#graph e) (#scope e) boolSyntax.F)]} end
  fun closed (e:env) index = Thm.REFL (List.nth (#seeds e,index))
  fun retain theorem hypothesis = Thm.CONJUNCT1
    (Thm.CONJ theorem (Thm.ASSUME hypothesis))
  fun worker (e:env) shape calls (request,inputs) =
    let
      val request:CPC_Proof.step = request
      val _ = calls := #id request :: !calls
      fun need index = Thm.ASSUME (List.nth (#obligations e,index))
      fun port () = #term (hd inputs:CPC_Proof.located_term)
      val theorem = case #id request of
          "@need1" => need 0
        | "@need2" => need 1
        | "@copy" => Thm.ASSUME (port ())
        | "@cross1" => retain (closed e 0) (port ())
        | "@cross2" => (case shape of Cycle true => closed e 1
            | _ => retain (closed e 1) (port ()))
        | _ => raise Fail "unexpected deferred native worker"
      (* Check each certificate BEFORE replay sees it. In particular, both
         cycle edges have correct endpoints and genuinely retained Hyp. *)
      fun unused_context () = require "wrong unused original need port"
        (length inputs=1 andalso Term.aconv (port ()) (#premise e))
      val _ = case #id request of
          "@need1" => unused_context ()
        | "@need2" => unused_context ()
        | "@cross1" => require "first cycle edge has the wrong dependency"
            (Term.aconv (port ()) (List.nth (#targets e,1)))
        | "@cross2" => (case shape of Cycle true =>
              require "broken edge retained a supplied dependency" (null inputs)
            | _ => require "second cycle edge has the wrong dependency"
                (Term.aconv (port ()) (hd (#targets e))))
        | _ => ()
      val expected_hyp = case #id request of
          "@need1" => [hd (#obligations e)]
        | "@need2" => [List.nth (#obligations e,1)]
        | "@cross2" => (case shape of Cycle true => [] | _ => [port ()])
        | _ => [port ()]
      val target = valOf (#conclusion request)
      val _ = exact (#term target) expected_hyp theorem
    in (theorem,target) end

  (* Each attempt consumes its own Sources and NEW Work/GP invocation.
     Inspect retirement before fixture cleanup. *)
  fun attempt (e:env) shape force inspect =
    let
      val work = W.begin_with_scope_guard (#graph e) (#scope e) (#sources e)
        {limits={input_limit=maximum,output_limit=maximum,
                 template_limit=maximum},work_limit=allowance}
      val calls = ref ([]:string list) val forced = ref 0
      fun body () =
        let
          val input = GP.discover_from_sources (#graph e) (#scope e)
            (#sources e) {import_limit=maximum,revisit=false,
              check_type=fn _ => (),conversion=fn _ => NONE}
          val proof = certificate e shape
          fun checked_force pair =
            (forced := !forced+1;
             require "force entered retired Work"
               (not (#retired (W.audit work)));
             force e pair)
          fun replay () = R.check_contradiction_preprocessed_with_work_using
            work {graph= #graph e,scope= #scope e,sources= #sources e,
              preprocessing=input,proof=proof,ordinary_limit=maximum,
              template_limit=maximum,worker=worker e shape calls,
              force_worker=case shape of Cycle _ => NONE
                | _ => SOME checked_force}
          val outcome = Exn.capture replay ()
        in inspect {work=work,calls=calls,forced=forced,
          outcome=outcome,replay=replay} end
    in finally body (fn () => W.close work) end
  fun expected_calls (Single false) = ["@need1"]
    | expected_calls (Single true) = ["@need1","@copy"]
    | expected_calls (Cycle _) = ["@need1","@need2","@cross1","@cross2"]
  fun successful (e:env) hypotheses contradiction =
    let
      val denied = G.representative (#graph e)
        (S.denied_goal_node (#sources e))
      val original = S.assumption_nodes (#sources e) @
        [S.denied_goal_node (#sources e)]
      val _ = S.check_contradiction (#sources e) contradiction
      val _ = exact boolSyntax.F (denied::hypotheses) contradiction
      val _ = require "noncanonical deferred Source Hyp"
        (List.all (fn term => List.exists (fn node => Portable.pointer_eq
          (term,G.representative (#graph e) node)) original)
          (Thm.hyp contradiction))
      val theorem = S.close_contradiction (#sources e) contradiction
      val goal = hd (#targets e)
      val _ = S.check_goal (#sources e) theorem
    in exact goal hypotheses theorem;
       require "deferred closure replaced the original Goal"
         (Portable.pointer_eq (Thm.concl theorem,goal)) end
  fun force_closed e (request:CPC_Proof.step,inputs) =
    (require "force acquired undocumented premises" (null inputs);
     (closed e 0,valOf (#conclusion request)))
  fun force_source (e:env) (request:CPC_Proof.step,inputs) =
    let val source = hd (S.assumption_nodes (#sources e))
        val theorem = Thm.CONJUNCT1
          (Thm.ASSUME (G.representative (#graph e) source))
    in require "force acquired undocumented premises" (null inputs);
       exact (hd (#obligations e)) [#premise e] theorem;
       (theorem,valOf (#conclusion request)) end
  fun positive wide use_source () = world_with use_source (fn e =>
    let val shape = Single wide
    in attempt e shape (if use_source then force_source else force_closed)
      (fn {work,calls,forced,outcome,...} =>
        (successful e (if use_source then [#premise e] else [])
           (Exn.release outcome);
         require "deferred law skipped, retried or retired successful Work"
           (List.rev (!calls)=expected_calls shape andalso !forced=1 andalso
            not (#retired (W.audit work)) andalso
            #charged (W.audit work)>0 andalso
            #charged (W.audit work)<=allowance))) end)
  fun diagnostic message result = case result of
      Exn.Exn (Feedback.HOL_ERR detail) =>
        Feedback.top_structure_of detail="CPC_GraphProofReplay" andalso
        Feedback.top_function_of detail="obligation" andalso
        Feedback.message_of detail=message
    | _ => false
  fun cycle broken () = world (fn e =>
    let val shape = Cycle broken
    in require "cycle obligations collapsed to one alpha-class"
         (not (Term.aconv (hd (#obligations e))
           (List.nth (#obligations e,1))));
       attempt e shape force_closed
         (fn {work,calls,forced,outcome,...} =>
           (require ("two-obligation cycle missed a valid edge: " ^
              String.concatWith "," (List.rev (!calls)) ^ " result=" ^
              (case outcome of Exn.Res _ => "success"
               | Exn.Exn error => General.exnMessage error))
              (List.rev (!calls)=expected_calls shape andalso !forced=0);
            if broken then
              (successful e [] (Exn.release outcome);
               require "broken cycle retired Work"
                 (not (#retired (W.audit work))))
            else require ("cyclic closure accepted or failed at a malformed law: " ^
              (case outcome of Exn.Res theorem => "success: " ^
                 Library.term_to_string (Thm.concl theorem)
               | Exn.Exn error => General.exnMessage error))
              (diagnostic
                 "no independently checked fact proves deferred obligation"
                 outcome andalso #retired (W.audit work)))) end)
  fun bad_force self () = world (fn e =>
    let
      val foreign = Term.mk_var ("@fp.task46_foreign",Type.bool)
      fun force e (request:CPC_Proof.step,_) =
        let val target = valOf (#conclusion request)
            val theorem = if self then Thm.ASSUME (#term target)
              else retain (closed e 0) foreign
            val _ = exact (#term target)
              [if self then #term target else foreign] theorem
        in (theorem,target) end
    in attempt e (Single false) force
      (fn {work,calls,forced,outcome,...} => require
        ("bad forced Hyp accepted, retried, or rejected at an " ^
         "unrelated endpoint")
        (List.rev (!calls)=["@need1"] andalso !forced=1 andalso
         #retired (W.audit work) andalso diagnostic
           (if self then "forced TRUST deferred or changed target"
            else "deferred proof retains a local or unpermitted hypothesis")
           outcome)) end)

  fun terminal primary same () = world (fn e =>
    let
      val total = ref 0
      val previous = ref (NONE:W.portfolio option)
      fun failed () = attempt (reacquire e) (Single false)
        (fn _ => fn _ => (total := !total+1;raise primary))
        (fn {work,calls,forced,outcome,...} =>
          (require "retry reused the retired Work"
             (case !previous of NONE => true | SOME old =>
               not (Portable.pointer_eq (old,work)) andalso
               #retired (W.audit old));
           require "terminal force was changed, swallowed, cached or retried"
             (List.rev (!calls)=["@need1"] andalso !forced=1 andalso
              #retired (W.audit work) andalso
              (case outcome of Exn.Exn actual => same actual | _ => false));
           G.validate_scope (#graph e) (#scope e);
           previous := SOME work))
      val _ = failed () val _ = failed ()
      val healthy = reacquire e
      val _ = attempt healthy (Single false)
        (fn e => fn pair => (total := !total+1;force_closed e pair))
        (fn {work,calls,forced,outcome,...} =>
          (successful healthy [] (Exn.release outcome);
           require "fresh healthy invocation reused a failed force result"
             (!forced=1 andalso List.rev (!calls)=["@need1"] andalso
              not (#retired (W.audit work)))))
    in require "force callback did not run on every fresh attempt"
         (!total=3) end)
  fun timeout () =
    let val duration = Time.fromMilliseconds 461
    in terminal (Timeout.TIMEOUT duration)
      (fn Timeout.TIMEOUT actual => Portable.pointer_eq (duration,actual)
        | _ => false) () end
  (* Opt-in slow control: unlike timeout(), no exception is injected here.
     The production ten-second entailment timer must interrupt the callback
     before its eleven-second sleep returns. Not part of run(). *)
  fun deadline () = test "CPC real forced entailment deadline" (fn () =>
    world (fn e =>
      let
        val returned = ref false
        fun slow e pair =
          (OS.Process.sleep (Time.fromSeconds 11);
           returned := true;
           force_closed e pair)
        val _ = require "deadline control requires the ten-second policy"
          (Time.toSeconds SmtResource.max_hypothesis_entailment_time=10)
        val _ = attempt e (Single false) slow
          (fn {work,calls,forced,outcome,...} => require
            ("real entailment timer did not interrupt the forced callback: " ^
             (case outcome of Exn.Res _ => "success"
              | Exn.Exn error => General.exnMessage error))
            (List.rev (!calls)=["@need1"] andalso !forced=1 andalso
             not (!returned) andalso #retired (W.audit work) andalso
             (case outcome of Exn.Exn (Timeout.TIMEOUT elapsed) =>
                Time.compare (elapsed,
                  SmtResource.max_hypothesis_entailment_time) <> LESS
              | _ => false)))
        val healthy = reacquire e
      in attempt healthy (Single false) force_closed
        (fn {work,calls,forced,outcome,...} =>
          (successful healthy [] (Exn.release outcome);
           require "real deadline poisoned a fresh invocation"
             (List.rev (!calls)=["@need1"] andalso !forced=1 andalso
              not (#retired (W.audit work))))) end))
  fun interrupt () = terminal Interrupt
    (fn Interrupt => true | _ => false) ()
  fun resource () =
    let
      val primary = case Exn.capture (fn () =>
          SmtResource.check_dag_size_with_limit "Task46" "force" 1 2) () of
          Exn.Exn error => error
        | _ => raise Fail "resource injection did not construct a gate"
      fun same (Feedback.HOL_ERR actual) = (case primary of
            Feedback.HOL_ERR expected =>
              SmtResource.is_resource_gate actual andalso
              Portable.pointer_eq (actual,expected)
          | _ => false)
        | same _ = false
    in terminal primary same () end
  fun stale_cache () = world (fn e => attempt e (Single true) force_closed
    (fn {work,calls,forced,outcome,replay} =>
      let val _ = successful e [] (Exn.release outcome)
          val _ = require "stale-cache control never warmed genuine forcing"
            (List.rev (!calls)=expected_calls (Single true) andalso !forced=1)
          val before_calls = !calls val before_force = !forced
          val _ = W.close work
          val stale = Exn.capture replay ()
      in require "retired Work reused a warmed deferred result"
        (#retired (W.audit work) andalso !calls=before_calls andalso
         !forced=before_force andalso
         (case stale of Exn.Exn (Feedback.HOL_ERR _) => true | _ => false))
      end))
  fun run () =
    (test "CPC deferred entailment bound remains ten seconds" (fn () =>
       (* Fast policy check only; deadline() exercises actual enforcement. *)
       require "changed deferred entailment bound"
         (Time.toSeconds SmtResource.max_hypothesis_entailment_time=10));
     test "CPC genuine closed deferred force" (positive false false);
     test "CPC genuine force retains one duplicate original Source"
       (positive true true);
     test "CPC actual two-obligation dependency cycle rejects" (cycle false);
     test "CPC breaking one cycle edge closes both obligations" (cycle true);
     test "CPC forced self-Hyp rejects at the force gate" (bad_force true);
     test "CPC forced foreign private-Hyp rejects at the Source gate"
       (bad_force false);
     test "CPC forced TIMEOUT identity and fresh invocation retry" timeout;
     test "CPC forced Interrupt and fresh invocation retry" interrupt;
     test "CPC forced SmtResource identity and fresh invocation retry"
       resource;
     test "CPC warmed deferred result cannot revive retired Work" stale_cache;
     test "CPC reused scope-pop control"
       (CPC_CompactReplayTests.positive_with 1 false false
          CPC_CompactReplayTests.Closed);
     test "CPC reused nested scope-pop actual Hyp control"
       (CPC_CompactReplayTests.positive_with 2 false false
          CPC_CompactReplayTests.Partial))
end
