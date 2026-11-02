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

  structure W = SmtReplayInvocationWork
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
        (test "native geometry: bounded cold binder rejection"
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
         test "native geometry: foreign, sibling and retired root" owners;
         test "native geometry: observer Primary/return/epoch freshness"
           callbacks)) ()
      val _=Count.counting_thms false
    in Exn.release outcome end
end
