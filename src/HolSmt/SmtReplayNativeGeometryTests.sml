(* Direct import-geometry regressions. No top-level execution; suite owner
   registers run in one existing Unittest group. *)
structure SmtReplayNativeGeometryTests =
struct
  structure G = SmtReplayGraph
  structure PV = SmtLib_GraphParserValue
  structure RP = SmtReplayResourcePolicy
  exception Primary of unit ref
  fun require text yes = if yes then () else raise Fail text
  fun rejected action =
    (action ();false) handle Feedback.HOL_ERR _ => true
  fun test label action =
    (testutils.tprint label;action ();testutils.OK ())

  fun routing_hint () =
    let
      val x = Term.mk_var (String.implode (List.tabulate (257,
        fn n => Char.chr (97 + n mod 26))),Type.bool)
      val y = Term.mk_var ("routing_y",Type.bool)
      val leaf = Term.mk_abs (x,boolSyntax.mk_conj (x,y))
      fun grow 0 term = term
        | grow n term = grow (n-1) (boolSyntax.mk_conj (term,term))
      val terms = [x,y,boolSyntax.T,boolSyntax.conjunction,leaf,
        Term.mk_comb (leaf,x),grow 12 x,
        boolSyntax.mk_conj (grow 5 x,grow 7 y)]
      fun check term depth modulus =
        require "unmetered route differs from paid routing programme"
          (SmtReplayImport.pointer_bucket depth modulus term =
           SmtReplayImport.pointer_bucket_observed (fn _ => ())
             depth modulus term)
      fun failure action =
        (ignore (action ());raise Fail "nonpositive modulus accepted")
        handle Feedback.HOL_ERR detail =>
          (Feedback.top_structure_of detail,Feedback.top_function_of detail,
           Feedback.message_of detail)
      val _ = List.app (fn term => List.app (fn depth =>
        List.app (check term depth) [1,17,4093,8191])
        [~1,0,1,2,4,8]) terms
    in List.app (fn modulus =>
      require "routing modulus diagnostic changed"
        (failure (fn () => SmtReplayImport.pointer_bucket 4 modulus x) =
         failure (fn () => SmtReplayImport.pointer_bucket_observed
           (fn _ => ()) 4 modulus x))) [0,~1] end

  structure W = SmtReplayInvocationWork

  fun semantic_pair_buckets () =
    let
      val order = SmtSkeletonProve.new_semantic_order ()
      fun pair n =
        let
          val a = Term.mk_var ("pair_bucket_a_" ^ Int.toString n,Type.bool)
          val b = Term.mk_var ("pair_bucket_z_" ^ Int.toString n,Type.bool)
        in if n mod 2=0 then (a,b) else (b,a) end
      (* More distinct pairs than buckets force collisions. Requery them
         after growth, including reverse keys, against the native order. *)
      val pairs = List.tabulate (6144,pair)
      fun check pair = require "semantic pair memo changed native order"
        (order pair = Term.compare pair)
      val _ = List.app check pairs
      val _ = List.app check (List.rev pairs)
      val _ = List.app (fn (left,right) => check (right,left)) pairs
      fun shared_type 0 = Type.bool
        | shared_type n =
            let val child = shared_type (n-1)
            in Type.mk_type ("fun",[child,child]) end
      val left = Term.mk_var ("pair_bucket_shared",shared_type 38)
      val right = Term.mk_var ("pair_bucket_shared",shared_type 38)
      (* Native Type comparison would unfold these independent annotations.
         This is metadata equality, without a native theorem admission. *)
      val _ = Timeout.apply (Time.fromSeconds 2) (fn () =>
        require "pair memo lost DAG-aware independent Type equality"
          (order (left,right)=EQUAL andalso order (right,left)=EQUAL)) ()
      val x = Term.mk_var ("pair_bucket_bound_x",Type.bool)
      val y = Term.mk_var ("pair_bucket_bound_y",Type.bool)
    in check (Term.mk_abs (x,boolSyntax.mk_conj (x,boolSyntax.T)),
              Term.mk_abs (y,boolSyntax.mk_conj (y,boolSyntax.T))) end

  fun canonical_difference () =
    let
      fun checked goal =
        let
          val theorem = SmtReplayCanon.z3_rewrite_canon_conv goal
          val (left,right) = Term.dest_eq (Thm.concl theorem)
          val _ = require "canonical conversion changed its source"
            (Term.aconv left goal)
          val _ = require "canonical conversion acquired hypotheses"
            (null (Thm.hyp theorem))
          val _ = Library.check_oracle_tags "Task59"
            "canonical-difference" theorem
        in right end
      val word = Parse.Term [QUOTE
        "((geometry_canon_x:word8) + geometry_canon_y) = \
        \ (geometry_canon_y + geometry_canon_x)"]
      val primary = boolSyntax.rhs (Thm.concl
        (SmtReplayCanon.z3_primary_rewrite_canon_conv word))
      val _ = require "irrelevant difference passes changed word normal form"
        (Term.aconv (checked word) primary)
      val positive =
        ["((x:int) > y) = (y < x)",
         "((x:real) >= y) = (y <= x)",
         "((x:int) + y) = (y + x)",
         "((x:real) + y) = (y + x)",
         "(if ~g then (x:word8) else y) = (if g then y else x)",
         "(\\x:int. x + y) = (\\x:int. y + x)"]
    in List.app (fn text =>
      require "required difference normalization was skipped"
        (SmtReplayCanon.equality_operands_alpha_equal
          (checked (Parse.Term [QUOTE text])))) positive end
  fun with_work g r action =
    let
      val sources = SmtReplaySource.new_with_policy g r RP.Uncapped
        {goal=boolSyntax.T,assumptions=[]}
      val work = W.begin_with_policy g r sources
        {limits={input_limit=RP.Uncapped,output_limit=RP.Uncapped,
                 template_limit=RP.Uncapped},work_limit=RP.AtMost 1000000}
      val outcome = Exn.capture (fn () => W.with_step work
        (fn () => action work)) ()
      val cleanup = Exn.capture W.close work
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end

  fun publish_on g r work profiles =
    let
      val prior = #charged (W.audit_policy work)
      val saved = G.publish_policy_native_raw_geometry_observed g r
        {profiles=profiles,remaining_work=W.remaining_policy work,
         observe=W.spend_policy work}
    in require "optional geometry was not paid on genuine Work"
      (saved andalso #charged (W.audit_policy work)>prior) end
  fun publish g r profiles = with_work g r (fn work =>
    publish_on g r work profiles)

  fun fixture_source action =
    let
      val g = G.new ()
      val r = G.root_scope g
      val x = Term.mk_var ("geometry_x",Type.bool)
      val z = Term.mk_var ("geometry_z",Type.bool)
      val opaque = Term.mk_abs (x,x)
      val original = boolSyntax.mk_eq (opaque,opaque)
      (* A real relevant sibling makes discovery collect the unchanged
         opaque equality operands, not an injected profile/cache row. *)
      val beta = Term.mk_comb
        (Term.mk_abs (z,boolSyntax.mk_neg z),boolSyntax.T)
      val seed = boolSyntax.mk_conj (beta,original)
      val source = G.import_with_policy g r RP.Uncapped seed
      val outcome = Exn.capture
        (fn () => action (g,r,original,#node source)) ()
      val cleanup = Exn.capture (G.close_scope g) r
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end

  fun fixture warm action = fixture_source (fn (g,r,original,node) =>
    let
      val _ = if warm then with_work g r (fn work =>
          let val found = G.discover_partial_with_policy g r
                {original=node,maximum=RP.Uncapped,
                 scan_limit=RP.Uncapped,step=fn () => W.spend_policy work 1}
          in publish_on g r work
            (G.partial_profiles_with_policy g r found) end)
        else ()
    in action (g,r,original) end)

  fun probe g r original observe =
    G.imported_native_raw_geometry_observed g r
      {original=original,maximum=RP.Uncapped,observe=observe}
  fun context g r = PV.create
    {graph=g,scope=r,validate=fn () => (),spend=fn _ => (),
     retire=fn () => ()}
  fun with_context g r action =
    let val c = context g r
        val outcome = Exn.capture action c
        val cleanup = Exn.capture PV.close c
    in case outcome of Exn.Exn primary => raise primary
      | Exn.Res value => (Exn.release cleanup;value) end

  fun cold_binder_bound () =
    let
      val x = Term.mk_var ("geometry_cold_x",Type.bool)
      val p = Term.mk_var ("geometry_cold_p",Type.bool)
      val schema = Thm.REFL (Term.mk_abs (x,p))
      fun shared 0 = boolSyntax.T
        | shared n = let val child = shared (n-1)
                     in boolSyntax.mk_conj (child,child) end
      (* INST inserts the DAG into a tiny binder without traversing the
         residue. Eager dest_abs would expand 2^31 body incidences. *)
      val theorem = Thm.INST [{redex=p,residue=shared 30}] schema
      val abstraction = boolSyntax.lhs (Thm.concl theorem)
      val result = Timeout.apply (Time.fromSeconds 2)
        (SmtReplayImport.raw_size_with_policy (RP.AtMost 2)) abstraction
    in require "cold binder rejection eagerly expanded its body"
      (result=NONE) end

  fun admitted_geometry () = fixture false (fn (g,r,original) =>
    let
      val opaque = boolSyntax.lhs original
      val source = G.import_with_policy g r RP.Uncapped opaque
      val _ = ignore (G.record_opened_view_with_policy g r
        (RP.AtMost 2) (#node source))
      val prior = Count.thm_count ()
      val _ = require "completed binder admission lost exact native count"
        (probe g r original (fn _ => ())=SOME 7 andalso
         Count.thm_count ()=prior)
      val clone = Term.mk_abs
        (Term.mk_var ("geometry_cold_clone",Type.bool),boolSyntax.T)
      val _ = ignore (G.import_with_policy g r RP.Uncapped clone)
    in require "admission count escaped its exact native input"
      (probe g r clone (fn _ => ())=NONE) end)

  fun exact () =
    let
      val _ = fixture false (fn (g,r,original) =>
        require "cold opaque import borrowed geometry"
          (probe g r original (fn _ => ()) = NONE))
      val _ = fixture true (fn (g,r,original) =>
        let
          val expected = SmtReplayImport.raw_size_with_policy
            RP.Uncapped original
          val spent = ref (0:IntInf.int)
          fun observe amount = spent := !spent+amount
          val prior = Count.thm_count ()
          val (actual,stats) = G.with_node_statistics g r
            (fn () => probe g r original observe)
          val _ = require "warm exact unfolded raw count changed"
            (expected=SOME 7 andalso actual=expected andalso !spent>7)
          val _ = require "warm geometry accessed graph nodes/proofs"
            (#node_accesses stats=0 andalso #node_creations stats=0 andalso
             Count.thm_count ()=prior)
          val first = !spent
          fun scopes 0 parent = ()
            | scopes n parent = scopes (n-1) (G.new_scope g parent [])
          val _ = scopes 128 r
          val _ = spent := 0
          val _ = require "scope-map growth changed native geometry"
            (probe g r original observe=expected andalso !spent=first)
          val huge = IntInf.pow (2,80)
          val _ = require "large policy ceiling truncated raw geometry"
            (G.imported_native_raw_geometry_observed g r
              {original=original,maximum=RP.AtMost huge,
               observe=fn _ => ()}=expected)
          val y = Term.mk_var ("geometry_alpha",Type.bool)
          val clone = Term.mk_abs (y,y)
          val clone = boolSyntax.mk_eq (clone,clone)
          val _ = ignore (G.import_with_policy g r RP.Uncapped clone)
        in require "alpha clone borrowed another original's native count"
          (Term.aconv original clone andalso
           probe g r clone (fn _ => ())=NONE) end)
    in () end

  (* These are the ORIGINAL collector scan counts: no optional geometry
     suffix is part of either admission boundary or observer trace. *)
  fun scan_boundaries () =
    List.app (fn selected =>
      let
        val (expected,old_scans) = if selected then (191,205) else (188,202)
        val expected = IntInf.fromInt expected
        val old_scans = IntInf.fromInt old_scans
        fun collect g r node limit step =
          if selected then
            let
              val heads = G.record_discovery_heads g r
                {heads=[],maximum=32,step=fn () => ()}
              val found = G.discover_selected_partial_with_policy g r
                {original=node,heads=heads,maximum=RP.Uncapped,
                 scan_limit=limit,step=step}
            in #profiles (G.selected_partial_data_with_policy g r heads
                 found) end
          else let
            val found = G.discover_partial_with_policy g r
              {original=node,maximum=RP.Uncapped,
               scan_limit=limit,step=step}
            val _ = require "original discovery scan total changed"
              (#scans (G.partial_discovery_policy_data g r found)=old_scans)
          in G.partial_profiles_with_policy g r found end
        val _ = fixture_source (fn (g,r,_,node) =>
          let val calls = ref (0:IntInf.int)
              val profiles = collect g r node RP.Uncapped
                (fn () => calls := !calls+1)
              val _ = require "scan fixture captured no opaque profiles"
                (not (null profiles))
          in require "uncapped original observer count changed"
            (!calls=expected) end)
        val _ = fixture_source (fn (g,r,original,node) =>
          let
            val calls = ref (0:IntInf.int)
            val profiles = collect g r node (RP.AtMost old_scans)
              (fn () => calls := !calls+1)
            val _ = require "exact old scan cap changed observer count"
              (!calls=expected)
            val _ = require "discovery implicitly published optional data"
              (probe g r original (fn _ => ())=NONE)
            val _ = publish g r profiles
            val _ = require "explicit publication did not warm geometry"
              (probe g r original (fn _ => ())=SOME 7)
            val _ = calls := 0
            val _ = collect g r node (RP.AtMost old_scans)
              (fn () => calls := !calls+1)
          in require "warm discovery added an optional observer suffix"
            (!calls=expected) end)
        val _ = fixture_source (fn (g,r,_,node) =>
          let val calls = ref (0:IntInf.int)
          in require "old insufficient scan cap changed callback boundary"
            (rejected (fn () => ignore (collect g r node
              (RP.AtMost (old_scans-1)) (fn () => calls := !calls+1)))
             andalso !calls=expected-1) end)
        val _ = fixture_source (fn (g,r,_,node) =>
          let val calls = ref (0:IntInf.int)
              val token = ref ()
              val outcome = Exn.capture (fn () => collect g r node
                (RP.AtMost old_scans) (fn () =>
                  (calls := !calls+1;if !calls=expected then
                     raise Primary token else ()))) ()
          in require "last original discovery observer Primary replaced"
            (!calls=expected andalso case outcome of
              Exn.Exn (Primary actual) => actual=token | _ => false) end)
      in () end) [false,true]

  fun optional_publication () = fixture_source (fn (g,r,original,node) =>
    let
      val found = G.discover_partial_with_policy g r
        {original=node,maximum=RP.Uncapped,
         scan_limit=RP.Uncapped,step=fn () => ()}
      val profiles = G.partial_profiles_with_policy g r found
      val _ = with_work g r (fn work =>
        let val prior = #charged (W.audit_policy work)
            val saved = G.publish_policy_native_raw_geometry_observed g r
              {profiles=profiles,remaining_work=RP.AtMost 0,
               observe=W.spend_policy work}
        in require "unfunded optional publication paid/published"
          (not saved andalso #charged (W.audit_policy work)=prior) end)
      val _ = with_work g r (fn work =>
        let val saved = G.publish_policy_native_raw_geometry_observed g r
              {profiles=profiles @ profiles,remaining_work=RP.AtMost 600,
               observe=W.spend_policy work}
        in require "incomplete optional batch was published or retired Work"
          (not saved andalso not (#retired (W.audit_policy work)) andalso
           probe g r original (fn _ => ())=NONE) end)
      val _ = with_work g r (fn work =>
        let val token = ref ()
            val outcome = Exn.capture (fn () =>
              G.publish_policy_native_raw_geometry_observed g r
                {profiles=profiles,remaining_work=W.remaining_policy work,
                 observe=fn amount =>
                   (W.spend_policy work amount;raise Primary token)}) ()
        in require "optional publication swallowed caller Primary"
          ((case outcome of Exn.Exn (Primary actual) => actual=token
             | _ => false) andalso
           probe g r original (fn _ => ())=NONE) end)
    in publish g r profiles end)

  fun parser_import () =
    List.app (fn warm => fixture warm (fn (g,r,original) =>
      let
        val _ = with_context g r (fn c =>
          let val prior = Count.thm_count ()
              val value = PV.import c r (RP.AtMost 7) original
              val _ = require "import did not retain graph value"
                (case PV.view c value of PV.RetainedGraph => true | _ => false)
          in require "warm parser import opened native opaque syntax"
            (not warm orelse Count.thm_count ()=prior) end)
        val _ = with_context g r (fn c =>
          require "raw cap bypassed by exposed import DAG or warm geometry"
            (rejected (fn () =>
              ignore (PV.import c r (RP.AtMost 6) original))))
      in () end)) [false,true]

  (* Genuine finite Work, not the no-op syntax callbacks used by the
     geometry-only tests. A cold atomic import originally costs exactly4.
     Extra cache lookup debits may not retire that accepted invocation. *)
  fun finite_import () =
    let
      fun check budget original maximum expected_charge expected =
        let
          val g = G.new () val r = G.root_scope g
          val sources = SmtReplaySource.new g r 100
            {goal=boolSyntax.T,assumptions=[]}
          val limits = {input_limit=100,output_limit=100,template_limit=100}
          val work = W.begin g r sources
            {limits=limits,work_limit=budget}
          val c = PV.create
            {graph=g,scope=r,
             validate=fn () => W.validate work g r sources limits,
             spend=fn amount => W.spend work (IntInf.toInt amount),
             retire=fn () => W.close work}
          val outcome = Exn.capture (fn () => W.with_step work (fn () =>
            PV.import c r maximum original)) ()
          val {charged,retired} = W.audit work
          val _ = require "finite import changed original payment/retirement"
            (charged=expected_charge andalso retired=not expected andalso
             (case outcome of Exn.Res _ => expected
                | Exn.Exn (Feedback.HOL_ERR _) => not expected | _ => false))
          val _ = require "finite failure did not close parser context"
            (PV.failure_requires_propagation c=not expected)
          val _ = PV.close c val _ = W.close work
        in G.close_scope g r end
      val x = Term.mk_var ("geometry_finite_cold",Type.bool)
      val _ = List.app (fn original =>
        (check 4 original (RP.AtMost 1) 4 true;
         check 100000 original (RP.AtMost 1) 4 true;
         check 3 original (RP.AtMost 1) 3 false;
         check 4 original (RP.AtMost 0) 1 false)) [x,boolSyntax.T]
      val _ = check 4 (Term.mk_abs (x,x)) (RP.AtMost 2) 4 true
      val _ = fixture true (fn (g,r,original) =>
        let
          val sources = SmtReplaySource.new g r 100
            {goal=boolSyntax.T,assumptions=[]}
          val limits = {input_limit=100,output_limit=100,template_limit=100}
          (* raw7, initial1, RetainedGraph row1; no free variables. *)
          val work = W.begin g r sources {limits=limits,work_limit=9}
          val c = PV.create
            {graph=g,scope=r,
             validate=fn () => W.validate work g r sources limits,
             spend=fn amount => W.spend work (IntInf.toInt amount),
             retire=fn () => W.close work}
          val _ = W.with_step work (fn () =>
            ignore (PV.import c r (RP.AtMost 7) original))
          val _ = require "warm finite import spent optional geometry Work"
            (#charged (W.audit work)=9 andalso
             not (#retired (W.audit work)))
          val _ = PV.close c
        in W.close work end)
    in () end

  fun funded_factory_import () =
    List.app (fn budget =>
      let
        val g = G.new () val r = G.root_scope g
        val sources = SmtReplaySource.new g r 100
          {goal=boolSyntax.T,assumptions=[]}
        val limits = {input_limit=100,output_limit=100,template_limit=100}
        val work = W.begin g r sources {limits=limits,work_limit=budget}
        val factory = W.create_value_factory_with_policy work
          {graph=g,scope=r,validate_metadata=fn () => (),
           import_limit=RP.AtMost 1,literal_limit=RP.AtMost 1,
           binder_limit=RP.AtMost 1}
        val c = #context (W.value_factory_data_for work factory)
        val _ = W.with_step work (fn () =>
          ignore (PV.import c r (RP.AtMost 1)
            (Term.mk_var ("geometry_factory_cold",Type.bool))))
        val {charged,retired} = W.audit work
        val _ = require "factory raw import changed original Work payment"
          (not retired andalso charged=4)
        val _ = W.close_value_factory factory val _ = W.close work
      in G.close_scope g r end) [4,1000,100000]

  fun uncapped_import () =
    List.app (fn failure =>
      let
        val g = G.new () val r = G.root_scope g
        val sources = SmtReplaySource.new g r 100
          {goal=boolSyntax.T,assumptions=[]}
        val limits = RP.semantic_from_ints
          {input_limit=100,output_limit=100,template_limit=100}
        val work = W.begin_with_policy g r sources
          {limits=limits,work_limit=RP.Uncapped}
        val token = ref ()
        val calls = ref 0
        val c = PV.create
          {graph=g,scope=r,
           validate=fn () => W.validate_policy work g r sources limits,
           spend=fn amount =>
             (W.spend_policy work amount;calls := !calls+1;
              if !calls<>3 then () else
                if failure=1 then raise Primary token
                else if failure=2 then G.close_scope g r else ()),
           retire=fn () => W.close work}
        val outcome = Exn.capture (fn () => W.with_step work (fn () =>
          PV.import c r (RP.AtMost 1)
            (Term.mk_var ("geometry_uncapped_cold",Type.bool)))) ()
        val {charged,retired} = W.audit_policy work
        val _ = require "raw import skipped real payment or Primary"
          (if failure<>0 then charged=2 andalso retired andalso
             PV.failure_requires_propagation c andalso
             (case outcome of
                Exn.Exn (Primary actual) => failure=1 andalso actual=token
              | Exn.Exn (Feedback.HOL_ERR _) => failure=2 | _ => false)
           else charged=4 andalso not retired andalso !calls>=4 andalso
             (case outcome of Exn.Res _ => true | _ => false))
        val _ = PV.close c val _ = W.close work
      in G.close_scope g r end) [0,1,2]

  fun bounded_prelookup () =
    let
      val g = G.new () val r = G.root_scope g
      val name = CharVector.tabulate (1000000,fn _ => #"x")
      val f = Term.mk_var (name,Type.mk_type ("fun",[Type.bool,Type.bool]))
      val input = Term.mk_comb (f,boolSyntax.T)
      val _ = with_context g r (fn c =>
        let val prior = Count.thm_count ()
            val result = Timeout.apply (Time.fromSeconds 2)
              (fn () => rejected (fn () =>
                ignore (PV.import c r (RP.AtMost 1) input))) ()
        in require "routing preceded bounded raw rejection without a bound"
          (result andalso Count.thm_count ()=prior) end)
      (* All abstractions route to the same bucket. Put the measured input
         behind more rows than the pre-admission lookup may examine. *)
      val x = Term.mk_var ("geometry_bucket",Type.bool)
      val original = Term.mk_abs (x,x)
      val source = G.import_with_policy g r (RP.AtMost 2) original
      val _ = ignore (G.record_opened_view_with_policy g r
        (RP.AtMost 2) (#node source))
      val _ = List.app (fn i =>
        let val v = Term.mk_var ("geometry_bucket_" ^ Int.toString i,Type.bool)
        in ignore (G.import_with_policy g r (RP.AtMost 2)
          (Term.mk_abs (v,v))) end) (List.tabulate (80,Lib.I))
      val sources = SmtReplaySource.new g r 100
        {goal=boolSyntax.T,assumptions=[]}
      val limits = {input_limit=100,output_limit=100,template_limit=100}
      val work = W.begin g r sources {limits=limits,work_limit=4}
      val c = PV.create
        {graph=g,scope=r,
         validate=fn () => W.validate work g r sources limits,
         spend=fn amount => W.spend work (IntInf.toInt amount),
         retire=fn () => W.close work}
      val _ = W.with_step work (fn () =>
        ignore (PV.import c r (RP.AtMost 2) original))
      val _ = require "deferred bucket lookup changed original payment"
        (#charged (W.audit work)=4 andalso not (#retired (W.audit work)))
      val _ = PV.close c val _ = W.close work
    in G.close_scope g r end

  (* A callback can prepend memo rows after prelookup. A deferred cursor
     must then be discarded; a completed miss must find the callback's
     newly imported Source rather than rebuild it. *)
  fun mutated_prelookup () =
    List.app (fn deferred =>
      let
        val g = G.new () val r = G.root_scope g
        fun abstraction name =
          let val x = Term.mk_var (name,Type.bool)
          in Term.mk_abs (x,x) end
        val original = abstraction "geometry_mutated_target"
        val _ = if deferred then
          (ignore (G.import_with_policy g r (RP.AtMost 2) original);
           List.app (fn i => ignore (G.import_with_policy g r (RP.AtMost 2)
             (abstraction ("geometry_mutated_" ^ Int.toString i))))
             (List.tabulate (80,Lib.I))) else ()
        val paid = ref (0:IntInf.int)
        val snapshot = ref (Count.thm_count ())
        val result = G.import_sized_with_policy g r (RP.AtMost 2)
          {original=original,admit=fn amount =>
             (paid := !paid+amount;
              ignore (G.import_with_policy g r (RP.AtMost 2)
                (if deferred then abstraction "geometry_mutated_new"
                 else original));
              snapshot := Count.thm_count ())}
        val _ = require "callback memo mutation rebuilt or lost exact Source"
          (!paid=2 andalso Count.thm_count ()= !snapshot andalso
           Portable.pointer_eq (#original result,original))
      in G.close_scope g r end) [false,true]

  fun owners () = fixture true (fn (g,r,original) =>
    let
      val other = G.new ()
      val foreign = G.root_scope other
      val calls = ref 0
      fun observe _ = calls := !calls+1
      val _ = require "foreign header reached observer/payload"
        (rejected (fn () => ignore (probe g foreign original observe)) andalso
         !calls=0)
      val _ = require "different graph borrowed native capture"
        (probe other foreign original observe=NONE)
      val _ = G.close_scope other foreign
      val sibling = G.new_scope g r []
      val _ = ignore (G.import_with_policy g sibling RP.Uncapped original)
      val _ = require "non-root caller borrowed root native capture"
        (probe g sibling original observe=NONE)
      val _ = G.close_scope g sibling
      val _ = require "retired non-root did not take payload-free fallback"
        (probe g sibling original observe=NONE)
      val _ = G.close_scope g r
      val prior = !calls
    in require "retired root reached observer or remained live"
      (rejected (fn () => ignore (probe g r original observe)) andalso
       !calls=prior) end)

  fun callbacks () =
    let
      val _ = fixture true (fn (g,r,original) =>
        let val token = ref ()
            val result = Exn.capture (fn () =>
              probe g r original (fn _ =>
                (G.close_scope g r;raise Primary token))) ()
        in require "observer Primary replaced by retirement error"
          (case result of Exn.Exn (Primary actual) => actual=token
             | _ => false) end)
      (* Exercise both initial header debit and the final return note. *)
      val _ = List.app (fn last => fixture true (fn (g,r,original) =>
        let
          val calls = ref 0
          val _ = ignore (probe g r original (fn _ => calls := !calls+1))
          val target = if last then !calls else 1
          val calls = ref 0
          fun retire _ =
            (calls := !calls+1;
             if !calls=target then G.close_scope g r else ())
        in require "observer return leaked a retired-root count"
          (rejected (fn () => ignore (probe g r original retire)) andalso
           !calls=target) end)) [false,true]
      val _ = List.app (fn last => fixture true (fn (g,r,original) =>
        let
          val name = "geometry_observer_epoch"
          val calls = ref 0
          val _ = ignore (probe g r original (fn _ => calls := !calls+1))
          val target = if last then !calls else 1
          val calls = ref 0
          val _ = require "private Type canary already exists"
            (not (List.exists (fn declaration =>
              #Thy declaration=Theory.current_theory ()) (Type.decls name)))
          val _ = Theory.new_type (name,0)
          val live = ref true
          val epoch = Type.type_epoch ()
          fun mutate _ =
            (calls := !calls+1;
             if !calls=target then
               (Theory.delete_type name;live := false) else ())
          val outcome = Exn.capture (fn () =>
            require "observer epoch change leaked native geometry"
              (rejected (fn () => ignore (probe g r original mutate)) andalso
               not (!live) andalso Type.type_epoch ()<>epoch andalso
               !calls=target)) ()
          val cleanup = Exn.capture (fn () =>
            if !live then Theory.delete_type name else ()) ()
        in Exn.release outcome;Exn.release cleanup end)) [false,true]
      val _ = fixture true (fn (g,r,original) =>
        let
          val name = "geometry_observer_term_epoch"
          val _ = require "private Term canary already exists"
            (not (List.exists (fn term => #Thy (Term.dest_thy_const term)=
              Theory.current_theory ()) (Term.decls name)))
          val _ = Theory.new_constant (name,Type.bool)
          val live = ref true
          val epoch = Term.term_epoch ()
          fun mutate _ = (Theory.delete_const name;live := false)
          val outcome = Exn.capture (fn () =>
            require "observer Term epoch change leaked native geometry"
              (rejected (fn () => ignore (probe g r original mutate))
               andalso not (!live) andalso Term.term_epoch ()<>epoch)) ()
          val cleanup = Exn.capture (fn () =>
            if !live then Theory.delete_const name else ()) ()
        in Exn.release outcome;Exn.release cleanup end)
    in () end

  fun run () =
    let
      val _=Count.counting_thms true
      val outcome=Exn.capture (fn () =>
        (test "native geometry: unmetered/paid routing agreement"
           routing_hint;
         test "native geometry: semantic pair collisions and shared Types"
           semantic_pair_buckets;
         test "native geometry: canonical difference presence/absence"
           canonical_difference;
         test "native geometry: bounded cold binder rejection"
           cold_binder_bound;
         test "native geometry: completed admission count reuse"
           admitted_geometry;
         test "native geometry: original scan caps and callback counts"
           scan_boundaries;
         test "native geometry: optional publication funding/Primary"
           optional_publication;
         test "native geometry: genuine cold/warm/alpha/exact count" exact;
         test "native geometry: parser import raw cap and warm native silence"
           parser_import;
         test "native geometry: genuine finite Work4 cold import/failure"
           finite_import;
         test "native geometry: production tight/funded exact payment"
           funded_factory_import;
         test "native geometry: genuine payment/Primary/root retirement"
           uncapped_import;
         test "native geometry: bounded routing/collision fallback"
           bounded_prelookup;
         test "native geometry: callback-mutated miss/deferred bucket"
           mutated_prelookup;
         test "native geometry: foreign, sibling and retired root" owners;
         test "native geometry: observer Primary/return/epoch freshness"
           callbacks)) ()
      val _=Count.counting_thms false
    in Exn.release outcome end
end
