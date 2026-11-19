(* Contract of the two policy provers of SmtLib_GraphCarrierRoot, the
   ordinary one (prepare_closure_admitted_with_policy) and the profiled one
   (prepare_closure_profiled_admitted_with_policy): policy closures, opaque
   predicates, profiles from a wrong or a retired frame, repeated execution
   and the native and Work allowances.

   Every relation is computed inside one run: a complete run measures the
   charged Work; the allowances are then probed at that exact amount and one
   below it, and a refusal must leave a retired owner whose charged prefix
   never exceeds the allowance. The ordinary prover charges everything while
   preparing; the profiled one also charges its native steps while
   executing, so only the profiled one has a native allowance that can fail
   a prepared plan. No charge or allowance is recorded as a constant. *)
structure SmtLib_GraphCarrierRootPolicyTests =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure RP = SmtReplayResourcePolicy
  structure C = SmtLib_GraphCarrierRoot
  structure X = SmtLib_GraphCarrierRootFixture
  (* A qualified use, which Holdep sees through the alias above. *)
  val native = SmtLib_GraphCarrierRootFixture.native
  structure NC = SmtReplayNativeContract

  fun require text yes = if yes then () else testutils.die text
  fun test label action =
    (testutils.tprint label; action (); testutils.OK ())
  fun refuses action = (ignore (action ()); false)
    handle Feedback.HOL_ERR _ => true
  fun charged (e : X.fixture) = #charged (W.audit_policy (#work e))
  fun retired (e : X.fixture) = #retired (W.audit_policy (#work e))

  type endpoints = {source : G.node,target : G.node,theorem : Thm.thm}
  (* [prepare] runs the prover's preparation; the thunk it returns executes
     the prepared plan and reads its endpoints back, and may be run again. *)
  datatype kind = Ordinary | Profiled
  type prover =
    {kind : kind,name : string,
     prepare : X.fixture -> G.policy_opaque_profile list ->
       (Type.hol_type -> unit) -> unit -> endpoints}
  fun request (e : X.fixture) profiles callback =
    {graph= #graph e,scope= #scope e,sources= #sources e,work= #work e,
     ordinal=0,admission= #admission e,law= #law e,
     native_contract= #native e,profiles=profiles,check_type=callback,
     scope_opened=fn _ => ()}
  val ordinary : prover =
    {kind=Ordinary,name="ordinary",
     prepare=fn e => fn profiles => fn callback =>
       let val plan = C.prepare_closure_admitted_with_policy
             (request e profiles callback)
       in fn () => C.endpoints_with_policy_for (X.expected e)
            (C.execute_with_policy plan) end}
  val profiled : prover =
    {kind=Profiled,name="profiled",
     prepare=fn e => fn profiles => fn callback =>
       let val plan = C.prepare_closure_profiled_admitted_with_policy
             (request e profiles callback)
       in fn () => C.endpoints_profiled_with_policy_for (X.expected e)
            (C.execute_profiled_with_policy plan) end}
  val provers = [ordinary,profiled]

  fun limits native_work : NC.limits =
    {semantic_limits= #semantic_limits native,
     import_limit= #import_limit native,type_work_limit=native_work}

  datatype outcome = Refused_in_prepare | Refused_in_execute | Completed
  type observation =
    {outcome : outcome,prepared : IntInf.int,final : IntInf.int,
     retired : bool,callbacks : int}
  (* One complete pipeline over a fresh NUM forall closure. *)
  fun run ({prepare,...} : prover) work_limit native_work : observation =
    let val e = X.setup_limited work_limit ``!n:num. T``
          HolSmtTheory.NUM_FORALL_TO_INT (limits native_work)
        val calls = ref 0
        val held = SOME (prepare e [] (fn _ => calls := !calls + 1))
          handle Feedback.HOL_ERR _ => NONE
        val prepared = charged e
        val outcome = case held of NONE => Refused_in_prepare
          | SOME execute => (ignore (execute ()); Completed)
              handle Feedback.HOL_ERR _ => Refused_in_execute
    in {outcome=outcome,prepared=prepared,final=charged e,
        retired=retired e,callbacks= !calls} end
  fun completes (o_ : observation) = #outcome o_ = Completed
  fun prepares (o_ : observation) = #outcome o_ <> Refused_in_prepare

  (* Least value of a monotone allowance under which [accepts] holds. *)
  fun least accepts hi =
    let fun go lo hi = if lo >= hi then lo else
          let val mid = (lo + hi) div 2
          in if accepts mid then go lo mid else go (mid + 1) hi end
    in go 0 hi end

  fun converted (p : prover) term fixed =
    let val e = X.setup term fixed native val calls = ref 0
        val execute = #prepare p e [] (fn _ => calls := !calls + 1)
        val prepared = charged e
        val d = execute ()
        val (left,right) = boolSyntax.dest_eq (Thm.concl (#theorem d))
    in require (#name p ^ ": carrier lost genuine endpoints or closed proof")
      (#source d = #node e andalso #source d <> #target d andalso !calls > 0
       andalso Portable.pointer_eq
         (left,G.representative (#graph e) (#source d))
       andalso Portable.pointer_eq
         (right,G.representative (#graph e) (#target d))
       andalso null (Thm.hyp (#theorem d)) andalso prepared > 0 andalso
       charged e >= prepared andalso not (retired e));
       (prepared,charged e) end

  fun closures () =
    let val rows =
          [(``!n:num. T``,HolSmtTheory.NUM_FORALL_TO_INT),
           (``?n:num. T``,HolSmtTheory.NUM_EXISTS_TO_INT),
           (``!b:bool->num. T``,HolSmtTheory.BAG_FORALL_TO_INT),
           (``?b:bool->num. T``,HolSmtTheory.BAG_EXISTS_TO_INT)]
    in List.app (fn (term,fixed) =>
         let val (po,to) = converted ordinary term fixed
             val (pp,tp) = converted profiled term fixed
         in require "ordinary prover charged during execution" (po = to);
            require "provers charge different preparation work" (po = pp);
            require "profiled prover charged no native execution steps"
              (tp > pp) end) rows end

  (* The retained opaque predicate of the profiled fixture. *)
  fun opaque body_issued = X.opaque_setup_limited RP.Uncapped body_issued
    native
  fun prepare_with (p : prover) (e : X.fixture) profiles calls =
    #prepare p e profiles (fn _ => calls := !calls + 1)
  fun settled (e : X.fixture) calls count =
    (retired e andalso !calls = 0 andalso Count.thm_count () = count)

  fun opaque_predicate () =
    (List.app (fn body_issued =>
       let val o_ = opaque body_issued val e = #fixture o_
           val calls = ref 0 val count = Count.thm_count ()
           val denied = refuses (fn () =>
             prepare_with ordinary e (#profiles o_) calls)
       in require "ordinary prover accepted an opaque predicate"
            (denied andalso settled e calls count) end) [true,false];
     List.app (fn body_issued =>
       let val o_ = opaque body_issued val e = #fixture o_
           val calls = ref 0
           val execute = prepare_with profiled e (#profiles o_) calls
           val d = execute ()
           val (left,right) = boolSyntax.dest_eq (Thm.concl (#theorem d))
       in require "profiled prover lost opaque source or endpoint proof"
         (#source d = #node e andalso #source d <> #target d andalso
          !calls > 0 andalso Portable.pointer_eq
            (left,G.representative (#graph e) (#source d)) andalso
          Portable.pointer_eq
            (right,G.representative (#graph e) (#target d)) andalso
          null (Thm.hyp (#theorem d)) andalso not (retired e)) end)
       [true,false];
     let val o_ = opaque true val e = #fixture o_
         val calls = ref 0 val count = Count.thm_count ()
         val denied = refuses (fn () => prepare_with profiled e [] calls)
     in require "profiled prover invented a missing opaque profile"
          (denied andalso settled e calls count) end)

  (* A profile is genuine only in the frame that issued it. *)
  fun wrong_frame () =
    let val o_ = opaque true val e = #fixture o_
        val calls = ref 0 val count = Count.thm_count ()
        val denied = refuses (fn () =>
          prepare_with profiled e (#root_profiles o_) calls)
    in require "profiled prover took a root profile for a body-issued node"
         (denied andalso settled e calls count);
       (* The ordinary metric never reads the profiles of a closure
          without opaque nodes; the profiled one revalidates them while
          executing. *)
       let val foreign = X.setup ``!n:num. T``
             HolSmtTheory.NUM_FORALL_TO_INT native
           val calls = ref 0
           val ignored = prepare_with ordinary foreign
             (#profiles (opaque true)) calls
           val d = ignored ()
       in require "ordinary prover refused a profile it does not read"
            (#source d = #node foreign andalso not (retired foreign)) end;
       let val foreign = X.setup ``!n:num. T``
             HolSmtTheory.NUM_FORALL_TO_INT native
           val calls = ref 0
           val denied = refuses (fn () => (prepare_with profiled foreign
             (#profiles (opaque true)) calls) ())
       in require "profiled prover accepted a profile of another graph"
            (denied andalso retired foreign) end
    end

  fun retired_frame () =
    (let val o_ = opaque true val e = #fixture o_
         val calls = ref 0 val count = Count.thm_count ()
         val _ = G.close_scope (#graph e) (#body_frame o_)
         val denied = refuses (fn () =>
           prepare_with profiled e (#profiles o_) calls)
     in require "profiled prover used a profile of a retired frame"
          (denied andalso settled e calls count) end;
     (* A frame retired between preparation and execution. *)
     let val o_ = opaque true val e = #fixture o_
         val calls = ref 0
         val execute = prepare_with profiled e (#profiles o_) calls
         val prepared = charged e
         val _ = G.close_scope (#graph e) (#body_frame o_)
         val count = Count.thm_count ()
         val denied = refuses execute
     in require "profiled execute used a profile retired after preparation"
          (denied andalso retired e andalso Count.thm_count () = count andalso
           charged e >= prepared) end;
     List.app (fn p =>
       let val e = X.setup ``!n:num. T`` HolSmtTheory.NUM_FORALL_TO_INT
             native
           val calls = ref 0
           val execute = prepare_with p e [] calls
           val prepared = charged e
           val _ = G.close_scope (#graph e) (#scope e)
           val count = Count.thm_count ()
           val denied = refuses execute
       in require (#name p ^ " executed in a retired scope")
         (denied andalso retired e andalso Count.thm_count () = count andalso
          charged e >= prepared) end) provers)

  fun repeated_execution () =
    List.app (fn p =>
      let val e = X.setup ``!n:num. T`` HolSmtTheory.NUM_FORALL_TO_INT
            native
          val calls = ref 0
          val execute = prepare_with p e [] calls
          val _ = execute ()
          val done = charged e val count = Count.thm_count ()
          val again = refuses execute
      in require (#name p ^ " reissued a consumed plan")
        (again andalso retired e andalso Count.thm_count () = count andalso
         charged e >= done) end) provers

  (* The Work allowance, at exact and one below, for the whole pipeline and
     for preparation alone. *)
  fun work_allowance (p : prover) =
    let val whole = run p RP.Uncapped (#type_work_limit native)
        val _ = require (#name p ^ ": uncapped run did not complete")
          (completes whole andalso not (#retired whole))
        val total = #final whole val prepared = #prepared whole
        fun at n = run p (RP.AtMost n) (#type_work_limit native)
        val exact = at total val below = at (total - 1)
        val prefix = at prepared val lower = at (prepared - 1)
    in require "exact Work allowance refused or charged differently"
         (completes exact andalso #final exact = total andalso
          #callbacks exact = #callbacks whole);
       require "Work allowance minus one accepted"
         (not (completes below) andalso #retired below andalso
          #final below <= total - 1);
       require "preparation Work allowance exact"
         (prepares prefix andalso #prepared prefix = prepared);
       require "preparation Work allowance minus one accepted"
         (#outcome lower = Refused_in_prepare andalso #retired lower andalso
          #final lower <= prepared - 1 andalso
          #final lower <= #final below);
       (* Everything beyond the prepared charge is paid while executing. *)
       if total = prepared then
         require "exact preparation allowance did not complete"
           (completes prefix)
       else
         require "execution charged nothing beyond the prepared plan"
           (#outcome prefix = Refused_in_execute andalso #retired prefix
            andalso #final prefix >= prepared) end

  (* The native allowance (type_work_limit of the contract). *)
  fun native_allowance (p : prover) =
    let val ceiling = #type_work_limit native
        fun at n = run p RP.Uncapped n
        val whole = at ceiling
        val for_prepare = least (fn n => prepares (at n)) ceiling
        val for_all = least (fn n => completes (at n)) ceiling
    in require "native allowance: uncapped run did not complete"
         (completes whole);
       require "native allowance: preparation exact"
         (prepares (at for_prepare) andalso for_prepare > 0 andalso
          #outcome (at (for_prepare - 1)) = Refused_in_prepare andalso
          #retired (at (for_prepare - 1)));
       require "native allowance: whole pipeline exact"
         (completes (at for_all) andalso for_all >= for_prepare andalso
          not (completes (at (for_all - 1))) andalso
          #retired (at (for_all - 1)));
       require "native allowance changed the charged Work"
         (#final (at for_all) = #final whole andalso
          #callbacks (at for_all) = #callbacks whole);
       case #kind p of
         Ordinary => require "ordinary prover has an execution allowance"
           (for_all = for_prepare)
       | Profiled => require "profiled prover has no execution allowance"
           (for_all > for_prepare andalso
            #outcome (at for_prepare) = Refused_in_execute andalso
            #retired (at for_prepare) andalso
            #final (at (for_all - 1)) < #final whole) end

  fun run_all () =
    (test "policy closures convert in both policy provers" closures;
     test "opaque predicate: ordinary rejects, profiled accepts"
       opaque_predicate;
     test "profile from a wrong frame" wrong_frame;
     test "profile from a retired frame" retired_frame;
     test "repeated execution is refused" repeated_execution;
     List.app (fn p =>
       test (#name p ^ " Work allowance at exact and one below")
         (fn () => work_allowance p)) provers;
     List.app (fn p =>
       test (#name p ^ " native allowance at exact and one below")
         (fn () => native_allowance p)) provers)
  val run = run_all
end
