(* Copyright (c) 2026 The HOL4 contributors.
   No top-level jobs: register run with the HolSmt selftest postludes. *)
structure SmtReplayLifecycleTests =
struct
  structure G = SmtReplayGraph
  structure R = ReplayRedblackPrivateWork
  structure RP = SmtReplayResourcePolicy
  structure A = SmtReplayOriginalAcquisition
  structure S = SmtReplaySource
  structure Session = SmtReplayWrapperSession
  structure F = SmtLib_GraphFrontend
  structure Z = Z3_GraphProofParser
  structure Parser = SmtLib_Parser

  exception Primary of unit ref
  exception Cleanup of int
  fun require text yes = if yes then () else raise Fail text
  fun test label action =
    (testutils.tprint label;action ();testutils.OK ())
  fun hol_error action = case Exn.capture action () of
      Exn.Exn (Feedback.HOL_ERR detail) => Feedback.message_of detail
    | Exn.Exn primary => raise primary
    | Exn.Res _ => raise Fail "expected HOL_ERR"
  fun path g scope = G.prepare_scope_path g scope {remaining_work=1000000}
  fun closed g scope saved =
    hol_error (fn () => G.validate_scope_path g scope saved) =
      "scope is closed"
  val cap : IntInf.int = 10000000
  fun paid () =
    let val charged = ref (0:IntInf.int)
        val meter = R.new_scope_meter_with_policy
          {limit=RP.AtMost cap,charged=charged}
        val graph = G.new_with_bootstrap_meter meter
    in (graph,G.root_scope graph,meter,charged) end

  fun exhausted_scope () =
    let
      val (g,root,meter,charged) = paid ()
      val child = G.new_scope g root []
      val sibling = G.new_scope g root []
      val child_path = path g child
      val sibling_path = path g sibling
      val root_path = path g root
      val revision = G.validation_revision_with_scope_path g root root_path
      val before_read = !charged
      val _ = G.validate_scope g child
      val _ = require "ordinary live scope validation lost its original meter"
        (!charged > before_read)
      val _ = R.scope_meter_charge meter (cap - !charged)
      (* Productive reads STILL use the captured meter. *)
      val limited = (G.validate_scope g child;false)
        handle R.Limit => true
      val _ = require "productive scope validation bypassed exhausted meter"
        limited
      val before_close = !charged
      val _ = G.close_scope g child
      val _ = G.close_scope g child
      val _ = require "scope cleanup charged or failed to revoke held path"
        (!charged=before_close andalso closed g child child_path)
      val _ = G.validate_scope_path g sibling sibling_path
      val _ = G.validate_scope_path g root root_path
      val _ = require "scope cleanup failed to invalidate validation witness"
        (G.validation_revision_with_scope_path g root root_path > revision)
      val _ = G.close_scope g root
    in require "ancestor cleanup left sibling path live or charged Work"
      (closed g sibling sibling_path andalso !charged=before_close) end

  fun foreign_scope () =
    let
      val (g,root,_,charged) = paid ()
      val other = G.new () val foreign = G.root_scope other
      val saved = path g root val other_saved = path other foreign
      val before_close = !charged
      val revision = G.validation_revision_with_scope_path g root saved
      val other_revision = G.validation_revision other foreign
      val message = hol_error (fn () => G.close_scope g foreign)
      val _ = G.validate_scope_path g root saved
      val _ = G.validate_scope_path other foreign other_saved
      val _ = require "foreign close touched a meter, witness or another store"
        (message="scope belongs to a different graph" andalso
         !charged=before_close andalso
         G.validation_revision_with_scope_path g root saved=revision andalso
         G.validation_revision other foreign=other_revision)
      val _ = G.close_scope g root
    in G.close_scope other foreign end

  fun retired_epoch () =
    let
      val name = "smt_replay_lifecycle_epoch"
      val _ = Theory.new_constant (name,Type.bool)
      val deleted = ref false
      fun run () =
        let
          val (g,root,_,charged) = paid ()
          val child = G.new_scope g root []
          val saved = path g child
          val _ = Theory.delete_const name
          val _ = deleted := true
          val _ = require "ordinary paid scope lost its semantic epoch guard"
            (hol_error (fn () => G.validate_scope g child) =
             "Type or Term epoch changed")
          val before_close = !charged
          val _ = G.close_scope g child
          val _ = G.close_scope g root
        in require "epoch retirement prevented cleanup or billed stale Work"
          (closed g child saved andalso !charged=before_close) end
    in Portable.finally
      (fn () => if !deleted then () else Theory.delete_const name)
      run () end

  fun retired_session () =
    let
      val (g,root,meter,charged) = paid ()
      val sources = S.new_with_policy g root RP.Uncapped
        {goal=boolSyntax.T,assumptions=[]}
      val session = Session.start sources ([],boolSyntax.T)
      val saved = path g root
      val _ = R.scope_meter_charge meter (cap - !charged)
      val before_close = !charged
      (* close marks the session Retired BEFORE retiring its graph scope.
         A failed first graph cleanup cannot be repaired by a second close. *)
      val _ = Session.close session
      val _ = Session.close session
    in require "retired wrapper stranded its scope on exhausted paid indices"
      (closed g root saved andalso !charged=before_close andalso
       hol_error (fn () => ignore (Session.graph session)) =
         "wrapper session closed") end

  fun retired_acquisition () =
    let
      val semantic = RP.semantic_from_ints
        {input_limit=64,output_limit=64,template_limit=64}
      val request : A.request =
        {construction_limits=RP.graph_from_ints
           {import_limit=64,literal_limit=64,binder_limit=64,
            recipe_limits={template_limit=64,index_limit=64,
                           operand_limit=64,token_limit=64}},
         semantic_limits=semantic,work_limit=RP.AtMost 100000,
         native_limits={semantic_limits=semantic,import_limit=RP.AtMost 64,
                        type_work_limit=RP.AtMost 64}}
      val seed = A.new_metadata request ([],boolSyntax.T)
      val {graph,root} = A.header_metadata seed
      val work = A.claim_work seed
      val saved = path graph root
      (* Exhaust the captured genuine payer, not an unrelated fresh meter.
         This direct G port has no A phase transition; retire A explicitly. *)
      fun exhaust () = (G.validate_scope graph root;exhaust ())
      val _ = exhaust () handle R.Limit => ()
      val _ = A.retire_work work
      val before_close = A.audit work
      val _ = A.close_seed seed
      val _ = A.close_seed seed
      val after_close = A.audit work
    in require "retired acquisition cleanup billed Work or left root live"
      (closed graph root saved andalso #retired after_close andalso
       #publication after_close="Dead" andalso
       #charged before_close= #charged after_close) end

  (* Instrument REAL frontend scopes at the generic parser seam. The parser
     must drain registered close actions even if more than one fails. No
     fake graph store, proof authority or semantic callback is introduced. *)
  fun traced_session opened calls reenter (base:F.session) : F.session =
    let
      fun scoped (F.ScopedSession
          {session,variables,descriptors,parent_scope,scope,close,...}) =
        let
          val id = length (!opened)+1
          fun probe () = ignore ((#parse_from session)
            (fn () => raise Fail "closed frame read tokenizer"))
          val _ = opened := probe:: !opened
          fun finish () =
            (calls := !calls @ [id];close ();(!reenter) ();
             if id=2 orelse id=3 then raise Cleanup id else ())
        in F.ScopedSession
          {session=traced_session opened calls reenter session,
           variables=variables,descriptors=descriptors,
           parent_scope=parent_scope,scope=scope,close=finish,origin=NONE}
        end
    in
      {reader= #reader base,symbol_key= #symbol_key base,
       namespace= #namespace base,sort_dictionary= #sort_dictionary base,
       parse_from= #parse_from base,
       add_literal_parser= #add_literal_parser base,
       add_recipe_parser= #add_recipe_parser base,
       add_constructor_parser= #add_constructor_parser base,
       add_source_parser= #add_source_parser base,
       replace_source_parser= #replace_source_parser base,
       add_symbolic_index= #add_symbolic_index base,
       private_symbol= #private_symbol base,parse_sort= #parse_sort base,
       declare= #declare base,private_variable= #private_variable base,
       define= #define base,define_opaque= #define_opaque base,
       define_variable= #define_variable base,define_list= #define_list base,
       lookup_list= #lookup_list base,declare_sort= #declare_sort base,
       open_binders=fn entries => scoped ((#open_binders base) entries),
       open_bindings=fn entries => scoped ((#open_bindings base) entries),
       open_mixed_bindings=fn entries => fn blocked =>
         scoped ((#open_mixed_bindings base) entries blocked)}
    end

  datatype failure_site = ExplicitClose | ParseFailure | PublishFailure
  fun z3_drain site =
    let
      val g = G.new () val root = G.root_scope g
      val opened = ref ([]:(unit -> unit) list)
      val calls = ref ([]:int list)
      val reenter = ref (fn () => ())
      val primary = ref ()
      val options : F.options =
        {graph=g,scope=root,logic="ALL",sources=[],
         sorts=Redblackmap.mkDict String.compare,binder_lists=[],
         import_limit=8192,literal_limit=8192,binder_limit=8192,
         recipe_limits={template_limit=8192,index_limit=8192,
                        operand_limit=8192,token_limit=8192},
         special=fn _ => fn _ => NONE,
         ascribed=fn _ => fn _ => fn _ => NONE}
      val text = "((proof (let ((a (asserted true))) " ^
        "(let ((b (asserted true))) (let ((c (asserted true))) a)))))"
      val index = ref 0
      fun input () = if !index=String.size text then NONE else
        let val c = String.sub (text,!index)
        in index:= !index+1;SOME c end
      val next = Parser.make_proof_input_tokenizer input
      fun make_terms version tokenizer = traced_session opened calls reenter
        (F.create_session options (Z.policy_description version) tokenizer)
      fun complete _ = case site of ParseFailure => raise Primary primary
        | _ => ()
      fun publish {reader:F.reader,proof:Z.proof,requested_version,close} =
        case site of PublishFailure => raise Primary primary | _ => proof
      val result = Exn.capture (fn () => Z.create_using_session
        (Z.graph_observations g) publish "4.8.12" (fn () => next)
        complete make_terms) ()
      fun check_primary outcome = require "cleanup replaced parse Primary"
        (case outcome of Exn.Exn (Primary actual) => actual=primary
         | Exn.Exn error => raise error | _ => false)
      fun run () =
        let
          val _ = case (site,result) of
              (ExplicitClose,Exn.Res proof) =>
                let
                  val _ = reenter := #close proof
                  val outcome = Exn.capture (#close proof) ()
                  val _ = require "explicit close lost its first failure"
                    (case outcome of Exn.Exn (Cleanup 3) => true
                     | Exn.Exn error => raise error | _ => false)
                  val _ = (#close proof) ()
                in () end
            | (ExplicitClose,Exn.Exn error) => raise error
            | _ => check_primary result
          val _ = require "Z3 close skipped, repeated or reordered closures"
            (!calls=[3,2,1] andalso length (!opened)=3)
          (* Let values retain their construction scope. It is the lexical
             frame, not the retained proof scope, that must be revoked. *)
          val _ = List.app (fn probe =>
            require "Z3 close stranded a real frontend lexical frame"
              (hol_error probe="lexical frame is closed")) (!opened)
        in G.validate_scope g root end
    in Portable.finally (fn () => G.close_scope g root) run () end

  fun run () =
    (test "Exhausted paid scope cleanup retains ordinary metering"
       exhausted_scope;
     test "Foreign cleanup changes no scope store or witness" foreign_scope;
     test "Retired epoch still permits exact scope cleanup" retired_epoch;
     test "Retired wrapper closes its exhausted original scope" retired_session;
     test "Retired acquisition closes its exhausted original scope"
       retired_acquisition;
     test "Z3 explicit close drains all failures once, including reentrancy"
       (fn () => z3_drain ExplicitClose);
     test "Z3 parse Primary survives multi-closure cleanup failures"
       (fn () => z3_drain ParseFailure);
     test "Z3 publication Primary survives multi-closure cleanup failures"
       (fn () => z3_drain PublishFailure))
end
