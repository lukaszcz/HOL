(* Contract of the int prover of SmtLib_GraphCarrierRoot through its three
   entries: [prepare] for an opened view, [prepare_closure] for a canonical
   closure and [prepare_closure_admitted] for a focus admission. It covers
   the four num/bag quantifier carriers, repeated execution, a scope retired
   before execution, the Work allowance at exact and one below, callback
   exceptions, a receipt lent to a foreign owner or in a child scope and
   the refusals of a goal that does not fit (a quantifier that is neither
   forall nor exists, a carrier that is neither num nor a bag, a wrong
   stock law, a negative ordinal and a goal
   over the output limit).

   Every relation is computed inside one run: a complete run measures the
   charged Work, the allowance is then probed at that exact amount and one
   below, and a refusal must leave a retired owner whose charged prefix
   never exceeds the allowance. The only literals are the refusal messages.
   No charge is recorded as a constant. A refusal that must make no theorem
   is checked with the kernel's inference count, which is switched on for the
   run. *)
structure SmtLib_GraphCarrierRootIntTests =
struct
  structure G = SmtReplayGraph
  structure W = SmtReplayInvocationWork
  structure C = SmtLib_GraphCarrierRoot
  structure X = SmtLib_GraphCarrierRootFixture
  (* Holdep does not register the dependency through the alias X above, so
     the fixture is also used qualified. *)
  val cap = SmtLib_GraphCarrierRootFixture.cap
  val require = X.require
  val test = X.test
  val refuses = X.refuses
  fun charged (e : X.int_fixture) = #charged (W.audit (#work e))
  fun retired (e : X.int_fixture) = #retired (W.audit (#work e))

  datatype kind = Opened | Closure | Admitted
  (* [prepare] runs the entry's preparation; the thunk it returns executes
     the prepared plan, and may be run again. [source] is the node the
     conversion must start from. *)
  type entry =
    {kind : kind,name : string,source : X.int_fixture -> G.node,
     prepare : X.int_fixture -> int -> (Type.hol_type -> unit) ->
       (G.scope -> unit) -> unit -> C.conversion}
  fun finish plan = C.execute plan
  (* The endpoints of a conversion, lent to its own owner. *)
  fun endpoints (e : X.int_fixture) conversion =
    (C.validate_for (X.int_expected e) conversion;C.endpoints conversion)
  val opened : entry =
    {kind=Opened,name="opened view",source=fn e => #original e,
     prepare=fn e => fn ordinal => fn check => fn observe =>
       let val plan = C.prepare
             {graph= #graph e,scope= #scope e,sources= #sources e,
              work= #work e,ordinal=ordinal,original= #original e,
              view= #view e,predicate_view= #predicate_view e,law= #law e,
              check_type=check,scope_opened=observe}
       in fn () => finish plan end}
  val closure : entry =
    {kind=Closure,name="closure",source=fn e => #node (#view e),
     prepare=fn e => fn ordinal => fn check => fn observe =>
       let val plan = C.prepare_closure
             {graph= #graph e,scope= #scope e,sources= #sources e,
              work= #work e,ordinal=ordinal,original= #closure e,
              law= #law e,check_type=check,scope_opened=observe}
       in fn () => finish plan end}
  val admitted : entry =
    {kind=Admitted,name="admitted focus",source=fn e => #node (#view e),
     prepare=fn e => fn ordinal => fn check => fn observe =>
       let val plan = C.prepare_closure_admitted
             {graph= #graph e,scope= #scope e,sources= #sources e,
              work= #work e,ordinal=ordinal,admission=X.int_admission e,
              law= #law e,check_type=check,scope_opened=observe}
       in fn () => finish plan end}
  val entries = [opened,closure,admitted]

  (* A Work allowance that no run below exhausts. *)
  val plenty = 2000000
  fun silent _ = ()
  val num_forall = (``!n:num. n = n``,HolSmtTheory.NUM_FORALL_TO_INT)
  val rows =
    [num_forall,
     (``?n:num. T``,HolSmtTheory.NUM_EXISTS_TO_INT),
     (``!b:bool->num. !x:bool. b x = b x``,HolSmtTheory.BAG_FORALL_TO_INT),
     (``?b:bool->num. T``,HolSmtTheory.BAG_EXISTS_TO_INT)]
  fun setup work_limit output (term,fixed) =
    X.int_setup work_limit output term fixed

  datatype outcome = datatype X.outcome
  val completes = X.completes
  (* One complete pipeline over a fresh goal. *)
  fun run ({prepare,...} : entry) work_limit row : int X.observation =
    let val e = setup work_limit cap row
    in X.observe
         {prepare=fn check =>
            let val execute = prepare e 0 check silent
            in fn () => ignore (endpoints e (execute ())) end,
          charged=fn () => charged e,retired=fn () => retired e} end

  (* Conversions: the exact closed endpoints of every carrier. Returns the
     Work charged when the plan was prepared and when it was executed. *)
  fun converted (p : entry) row =
    let val e = setup plenty cap row val calls = ref 0
        val count = Count.thm_count ()
        val execute = #prepare p e 0 (fn _ => calls := !calls + 1) silent
        val prepared = charged e
        val d = endpoints e (execute ())
        val (left,right) = boolSyntax.dest_eq (Thm.concl (#theorem d))
    in require (#name p ^ ": carrier lost genuine endpoints or closed proof")
      (#source d = #source p e andalso #source d <> #target d andalso
       !calls > 0 andalso Count.thm_count () <> count andalso
       Portable.pointer_eq
         (left,G.representative (#graph e) (#source d)) andalso
       Portable.pointer_eq
         (right,G.representative (#graph e) (#target d)) andalso
       null (Thm.hyp (#theorem d)) andalso
       null (Tag.axioms_of (Thm.tag (#theorem d))) andalso prepared > 0 andalso
       charged e >= prepared andalso not (retired e));
       (prepared,charged e) end

  fun conversions () =
    List.app (fn row =>
      let val observed = List.map (fn p => converted p row) entries
          val (po,to) = List.nth (observed,0)
          val (pc,tc) = List.nth (observed,1)
          val (pa,ta) = List.nth (observed,2)
      in (* Preparation pays for the whole proof: executing it only
            consumes the reservation. *)
         require "an entry charged Work while executing"
           (po = to andalso pc = tc andalso pa = ta);
         (* The opened view additionally quotes its ALPHA bridge. *)
         require "opened view charged no more than the closure" (po > pc);
         require "admission cheaper than the closure it describes"
           (pa >= pc) end) rows

  fun repeated_execution () =
    List.app (fn (p : entry) =>
      let val e = setup plenty cap num_forall
          val execute = #prepare p e 0 silent silent
          val _ = execute ()
          val done = charged e val count = Count.thm_count ()
          val again = refuses execute
      in require (#name p ^ " reissued a consumed plan")
        (again andalso retired e andalso Count.thm_count () = count andalso
         charged e >= done) end) entries

  fun retired_scope () =
    List.app (fn (p : entry) =>
      let val e = setup plenty cap num_forall
          val execute = #prepare p e 0 silent silent
          val prepared = charged e
          val _ = G.close_scope (#graph e) (#scope e)
          val count = Count.thm_count ()
          val denied = refuses execute
      in require (#name p ^ " executed in a retired scope")
        (denied andalso retired e andalso Count.thm_count () = count andalso
         charged e >= prepared) end) entries

  (* The Work allowance, at exact and one below. *)
  fun work_allowance (p : entry) row =
    let val whole = run p plenty row
        val _ = require (#name p ^ ": uncapped run did not complete")
          (completes whole andalso not (#retired whole))
        val total = #final whole val prepared = #prepared whole
        fun at n = run p n row
        val exact = at total val below = at (total - 1)
    in (* Preparation pays for the whole proof, so the allowance for the
          preparation is the allowance for the pipeline. *)
       require "int prover charged Work while executing" (total = prepared);
       require "exact Work allowance refused or charged differently"
         (completes exact andalso #final exact = total andalso
          #callbacks exact = #callbacks whole);
       require "Work allowance minus one accepted"
         (#outcome below = Refused_in_prepare andalso #retired below andalso
          #final below <= total - 1) end

  fun allowances () =
    List.app (fn p =>
      List.app (fn row => work_allowance p row) [num_forall,List.nth (rows,3)])
      entries

  (* A refusal from preparation leaves the owner retired, with no callback.
     The inventory of the goal precedes the producer of the law, which makes
     inferences, so a refusal from the inventory also makes no theorem
     ([bare]); the number made by a refusal from the syntax caps, which
     come after the producer, is not asserted. *)
  fun refusal_in_prepare bare (p : entry) ordinal output row message =
    let val e = setup plenty output row
        val calls = ref 0 val count = X.inferences ()
        val reason = (ignore (#prepare p e ordinal
            (fn _ => calls := !calls + 1) silent); NONE)
          handle Feedback.HOL_ERR err => SOME (Feedback.message_of err)
    in require (#name p ^ " did not refuse with: " ^ message)
         (reason = SOME message andalso
          X.settled (if bare then X.nothing else fn _ => true)
            (retired e) calls count) end
  fun refused_goals () =
    List.app (fn (p : entry) =>
      (List.app (fn (term,message) =>
         refusal_in_prepare true p 0 cap (term,HolSmtTheory.NUM_FORALL_TO_INT)
           message)
         [(``!b:bool->int. T``,"carrier is neither num nor arbitrary bag"),
          (``?!n:num. T``,"not forall or exists"),
          (``(P:(num->bool)->bool) (\n:num. T)``,
           "not a constant quantifier")];
       refusal_in_prepare true p 0 cap
         (``!n:num. T``,HolSmtTheory.NUM_EXISTS_TO_INT)
         "not the exact selected original stock law";
       refusal_in_prepare true p 0 cap
         (``!n:num. T``,HolSmtTheory.BAG_FORALL_TO_INT)
         "not the exact selected original stock law";
       refusal_in_prepare true p ~1 cap num_forall "negative ordinal";
       refusal_in_prepare false p 0 1 num_forall
         "prospective carrier syntax exceeds cap"))
      entries

  (* An exception of a type callback or of the scope observer reaches the
     caller unchanged and retires the owner; a callback that retires the
     scope stops the plan at once. *)
  exception Primary of unit ref
  fun callback_exceptions () =
    List.app (fn (p : entry) =>
      (let val e = setup plenty cap num_forall
          val token = ref () val calls = ref 0
          val seen = (ignore (#prepare p e 0
            (fn _ => (calls := !calls + 1; raise Primary token)) silent);
            false)
            handle Primary t => t = token
      in require (#name p ^ " replaced the exception of a type callback")
           (seen andalso !calls = 1 andalso retired e) end;
      let val e = setup plenty cap num_forall
          val calls = ref 0
          val denied = refuses (fn () => #prepare p e 0
            (fn _ => (calls := !calls + 1;
                      G.close_scope (#graph e) (#scope e))) silent)
      in require (#name p ^ " continued after a callback retired its scope")
           (denied andalso !calls = 1 andalso retired e) end;
      let val e = setup plenty cap num_forall
          val calls = ref 0
          val execute = #prepare p e 0 silent
            (fn child => (calls := !calls + 1;
                          G.close_scope (#graph e) child))
          val denied = refuses execute
      in require (#name p ^ " continued after an observer retired a child")
           (denied andalso !calls = 1 andalso retired e) end)) entries

  (* A receipt is lent only to the owner that produced it, in the scope it
     was made in; a foreign owner, or the owner in a child scope, is
     retired by the attempt, the producing one is not. *)
  fun foreign_receipt () =
    List.app (fn (p : entry) =>
      (let val e = setup plenty cap num_forall
          val conversion = #prepare p e 0 silent silent ()
          val other = setup plenty cap num_forall
          val denied = refuses (fn () =>
            C.validate_for (X.int_expected other) conversion)
      in require (#name p ^ " lent a receipt to a foreign owner")
           (denied andalso retired other andalso not (retired e) andalso
            #source (C.endpoints conversion) = #source p e) end;
       let val e = setup plenty cap num_forall
          val conversion = #prepare p e 0 silent silent ()
          val child = G.new_scope (#graph e) (#scope e) []
          val denied = refuses (fn () => C.validate_for
            {graph= #graph e,scope=child,sources= #sources e,
             work= #work e} conversion)
      in require (#name p ^ " lent a receipt to a child scope")
           (denied andalso retired e) end)) entries

  fun run_all () = X.counting (fn () =>
    (test "int carriers convert through the three entries" conversions;
     test "int repeated execution is refused" repeated_execution;
     test "int execution in a retired scope is refused" retired_scope;
     test "int Work allowance at exact and one below" allowances;
     test "int goals that do not fit are refused" refused_goals;
     test "int callback exceptions stop the plan" callback_exceptions;
     test "int receipt is refused to a foreign owner" foreign_receipt))
  val run = run_all
end
