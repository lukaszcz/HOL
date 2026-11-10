structure SmtLib_CarrierLaws :> SmtLib_CarrierLaws =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  val ERR = Feedback.mk_HOL_ERR "SmtLib_CarrierLaws"
  datatype kind = NumForall | NumExists | BagForall | BagExists
  type count = {raw : IntInf.int,binder : IntInf.int,
                ann : IntInf.int,ty : IntInf.int}
  datatype syntax = Atom of Term.term
    | Application of Term.term * syntax * syntax
    | Abstraction of Term.term * Term.term * syntax
  type row = {kind : kind,original : Thm.thm,source : G.source,
              opened : G.source,fact : P.closed_fact}
  datatype portfolio = Portfolio of
    {work : W.portfolio,graph : G.graph,root : G.scope,sources : S.sources,
     limits : W.limits,epoch : int,rows : row list,
     held : G.closure_child list}
  fun ordinal NumForall = 0
    | ordinal NumExists = 1 | ordinal BagForall = 2 | ordinal BagExists = 3
  fun fixed NumForall = HolSmtTheory.NUM_FORALL_TO_INT
    | fixed NumExists = HolSmtTheory.NUM_EXISTS_TO_INT
    | fixed BagForall = HolSmtTheory.BAG_FORALL_TO_INT
    | fixed BagExists = HolSmtTheory.BAG_EXISTS_TO_INT

  fun prepare_inside work {needed,check_type} =
    let
      val _ = W.spend work 0
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = W.semantic_limits work val epoch = Type.type_epoch ()
      val held = ref ([] : G.closure_child list)
      fun guard () =
        (W.validate work graph root sources limits;
         if Type.type_epoch () = epoch then () else
           raise ERR "prepare_inside" "original Type epoch changed";
         List.app (fn child =>
           ignore (G.closure_child_node graph root child)) (!held))
      fun tick () = (guard ();W.spend work 1)
      fun call operation =
        (guard ();let val value = operation () val _ = guard () in value end)
      val ceiling = IntInf.fromInt (W.work_limit work)
      fun plus a b = IntInf.min (ceiling+1,a+b)
      val cap = IntInf.fromInt (#template_limit limits)
      fun bounded label n = if n <= cap then () else
        raise ERR "prepare_inside" (label ^ " exceeds original template cap")
      (* The enum admits exactly four declarations, not arbitrary theorem
         DATA. Each supplied spine/comparison is billed before inspection. *)
      fun unique pending seen =
        (tick ();case pending of [] => [] | kind::rest =>
          let fun duplicate [] = false
                | duplicate (old::more) =
                    (tick ();kind = old orelse duplicate more)
              val _ = if duplicate seen then
                raise ERR "prepare_inside" "duplicate requested stock law"
                else ()
              val _ = tick () val suffix = unique rest (kind::seen)
              val _ = tick ()
          in kind::suffix end)
      val kinds = unique needed []
      val _ = tick () val types = ref ([] : Type.hol_type list)
      fun skeleton term =
        let val _ = tick ()
        in if call (fn () => Term.is_comb term) then
            let val (f,x) = call (fn () => Term.dest_comb term)
                val left = skeleton f val right = skeleton x
                val _ = tick () val _ = tick ()
            in Application (term,left,right) end
           else if call (fn () => Term.is_abs term) then
            let val (v,b) = call (fn () => Term.dest_abs term)
                val body = skeleton b val _ = tick () val _ = tick ()
            in Abstraction (term,v,body) end
           else if call (fn () => Term.is_var term orelse Term.is_const term)
             then (tick ();Atom term)
           else raise ERR "prepare_inside" "unknown fixed law syntax"
        end
      fun size (Atom _) = (tick ();(1 : IntInf.int,1 : IntInf.int))
        | size (Application (_,a,b)) =
            let val (ar,ab) = size a val (br,bb) = size b val _ = tick ()
            in (plus 1 (plus ar br),plus 1 (plus ab bb)) end
        | size (Abstraction (_,_,b)) =
            let val (r,i) = size b val _ = tick ()
            in (plus 1 r,plus 2 i) end
      fun type_weight ty =
        let fun walk pending n =
              (tick ();case pending of [] => n | spine::more =>
                (tick ();case spine of [] => walk more n
                 | current::rest =>
                   let val n = plus n 1 val _ = bounded "law Type tree" n
                       val _ = tick ()
                   in if call (fn () => Type.is_vartype current) then
                        (tick ();walk (rest::more) n)
                      else let val args = call
                          (fn () => #2 (Type.dest_type current))
                        val _ = tick () val _ = tick ()
                      in walk (args::rest::more) n end end))
            val _ = tick () val _ = tick ()
        in walk [[ty]] 0 end
      fun annotate term =
        let val _ = tick () val ty = call (fn () => Term.type_of term)
            val weight = type_weight ty
            val _ = tick () val _ = tick () val _ = types := ty :: !types
        in weight end
      fun profile (Atom term) =
            let val t = annotate term val _ = tick ()
            in {raw = 1,binder = 1,ann = t,ty = t} : count end
        | profile (Application (term,a,b)) =
            let val x = profile a val y = profile b val t = annotate term
                val _ = tick ()
            in {raw = plus 1 (plus (#raw x) (#raw y)),
                binder = plus 1 (plus (#binder x) (#binder y)),
                ann = plus t (plus (#ann x) (#ann y)),ty = t} : count end
        | profile (Abstraction (term,variable,b)) =
            let val body = profile b val v = annotate variable
                val t = annotate term val _ = tick ()
            in {raw = plus 1 (#raw body),binder = plus 2 (#binder body),
                ann = plus t (plus v (#ann body)),ty = t} : count end
      fun plan kind =
        let val _ = tick () val theorem = fixed kind
            val term = call (fn () => Thm.concl theorem)
            (* Fixed stock input only. term_size is theorem-free; its
               primitive full traversal is an explicit unclosed cost. *)
            val measured = call (fn () => Term.term_size term)
            val _ = bounded "stock law raw" (IntInf.fromInt measured)
            val syntax = skeleton term val (r,b) = size syntax
            val _ = bounded "stock law raw" r
            val _ = bounded "stock law binder-inclusive" b
            val _ = if r = IntInf.fromInt measured then () else
              raise ERR "prepare_inside" "public law shape metric differs"
            val counts = profile syntax
            (* Import/opened/whole-anchor records preserve the complete law
               alpha shape. These are nominal full equation and EQ_MP
               inventories, not proof-operation-count or private G costs. *)
            val eq_raw = plus 3 (plus r r)
            val eq_binder = plus 3 (plus b b)
            val eq_ann = plus 9 (plus (#ann counts) (#ann counts))
            val _ = if eq_raw <= IntInf.fromInt (#output_limit limits)
                andalso eq_binder <= IntInf.fromInt (#output_limit limits)
              then () else raise ERR "prepare_inside"
                "whole law bridge exceeds original output cap"
            val equation = plus eq_raw (plus eq_binder eq_ann)
            val amount = plus r (plus b (plus (#ann counts)
              (plus equation (plus equation equation))))
            val _ = tick () val _ = tick ()
        in (kind,theorem,term,amount) end
      fun plans pending =
        (tick ();case pending of [] => [] | k::rest =>
          let val row = plan k val suffix = plans rest val _ = tick ()
          in row::suffix end)
      val plans = plans kinds
      fun total [] result = result
        | total ((_,_,_,amount)::rest) result =
            (tick ();total rest (plus result amount))
      val amount = total plans 0
      val _ = if amount <= IntInf.fromInt
          (W.work_limit work - #charged (W.audit work)) then () else
        raise ERR "prepare_inside" "needed laws exhaust original Work"
      (* This lazy owner invokes prepare for one needed kind at a time.
         Fixed LawInstance ordinals 0..3 never overlap selected C/L
         LocalCarrier/ClosedRecord names. A second owner cannot reissue one
         and renew its allowance; global Work remains the original object. *)
      val _ = case kinds of [] => () | [kind] =>
        let val token = W.reserve work
              {role = W.LawInstance,ordinal = ordinal kind,
               amount = IntInf.toInt amount}
        in W.consume work token (IntInf.toInt amount) end
        | _ => raise ERR "prepare_inside" "private lazy preparation shape"
      (* Equality is Boolean: exact newly built schema types are admitted
         from known fixed Boolean constructors after the nominal debit. *)
      val _ = tick ()
      val bool_arrow = call (fn () => Type.mk_type ("fun",[Type.bool,Type.bool]))
      val _ = tick ()
      val eq_type = call (fn () => Type.mk_type ("fun",[Type.bool,bool_arrow]))
      fun policy ty = (guard ();check_type ty;guard ())
      val _ = List.app policy (eq_type::bool_arrow:: !types)
      fun build [] = []
        | build ((kind,theorem,term,_)::rest) =
          let val _ = tick ()
              val prepared = call (fn () => G.plan_import graph root
                (#template_limit limits) term)
              val source = call (fn () => G.execute_import prepared)
              val opened = call (fn () => G.record_opened_view graph root
                (#template_limit limits) (#node source))
              val _ = call (fn () => G.validate_opened_view graph root
                (#node source) opened)
              (* Retain every genuine canonical path before P's callbacks.
                 Descendants carry root as fixed getter caller and their
                 actual body-frame links inside the opaque G handle. *)
              fun retain child =
                let val _ = tick ()
                    val node = call (fn () =>
                      G.closure_child_node graph root child)
                    val _ = tick () val _ = held := child :: !held
                in case call (fn () => G.view graph node) of
                    G.Application _ =>
                      let val (a,b) = call (fn () =>
                            G.closure_application_children graph root child)
                      in retain a;retain b end
                  | G.AdmittedBinder _ =>
                      let val closure = call (fn () =>
                            G.closure_child_binder graph root child)
                      in retain (call (fn () =>
                        G.binder_closure_body graph root closure)) end
                  | G.OpaqueRetained => raise ERR "prepare_inside"
                      "stock law discovery did not complete closure metadata"
                  | _ => () end
              val _ = retain (call (fn () =>
                G.closure_root graph root (#node opened)))
              val fact = call (fn () => P.record_closed_from_import graph root
                {node = #node opened,theorem = theorem,
                 template_limit = #template_limit limits,check_type = policy})
              val _ = if Portable.pointer_eq (P.closed_original fact,theorem)
                then () else raise ERR "prepare_inside" "original law changed"
              val _ = tick ()
              val row = {kind = kind,original = theorem,source = source,
                         opened = opened,fact = fact}
              val suffix = build rest val _ = tick ()
          in row::suffix end
      val rows = build plans val _ = guard ()
    in Portfolio {work = work,graph = graph,root = root,sources = sources,
       limits = limits,epoch = epoch,rows = rows,held = !held} end
    handle primary => (W.close work;raise primary)

  fun find_for expected scope kind
      (Portfolio {work,graph,root,sources,limits,epoch,rows,held}) =
    let
      val _ = if Portable.pointer_eq (expected,work) then () else
        raise ERR "find_for" "foreign expected Work"
      val _ = W.validate expected graph root sources limits
      val _ = if G.scope_visible graph scope root andalso
          Type.type_epoch () = epoch then () else
        raise ERR "find_for" "scope or Type epoch changed"
      val _ = List.app (fn child =>
        ignore (G.closure_child_node graph root child)) held
      fun find [] = NONE
        | find ((row : row)::rest) = if #kind row = kind then
            let val _ = G.validate_opened_view graph root
                  (#node (#source row)) (#opened row)
                val _ = P.validate_closed_fact graph scope
                  (#template_limit limits) (#fact row)
                val _ = if Portable.pointer_eq
                    (P.closed_original (#fact row),fixed kind) then () else
                  raise ERR "find_for" "stock theorem identity changed"
            in SOME (#fact row) end
          else find rest
    in find rows end
    handle primary => (W.close expected;raise primary)

  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,root : G.scope,sources : S.sources,
     limits : W.limits,epoch : int,check_type : Type.hol_type -> unit,
     cache : (kind * portfolio) list ref}
  fun validate (Owner {work,graph,root,sources,limits,epoch,cache,...}) =
    ((W.validate work graph root sources limits;
      if Type.type_epoch () = epoch then () else
        raise ERR "validate" "original owner epoch changed";
      List.app (fn (kind,portfolio) =>
        ignore (find_for work root kind portfolio)) (!cache))
     handle primary => (W.close work;raise primary))
  fun begin work {check_type} =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_limits work
        val _ = W.validate work graph root sources limits
    in Owner {work = work,graph = graph,root = root,sources = sources,
       limits = limits,epoch = Type.type_epoch (),check_type = check_type,
       cache = ref []} end
    handle primary => (W.close work;raise primary)
  fun get (owner as Owner {work,root,check_type,cache,...})
      {natural,universal} =
    let
      val _ = validate owner
      val kind = case (natural,universal) of
          (true,true) => NumForall | (true,false) => NumExists
        | (false,true) => BagForall | (false,false) => BagExists
      fun previous [] = NONE
        | previous ((old,value)::rest) =
            if kind = old then SOME value else previous rest
      val prepared = case previous (!cache) of SOME value => value
        | NONE =>
          let val value = W.with_step work (fn () =>
                prepare_inside work {needed = [kind],check_type = check_type})
              val _ = validate owner
              val _ = cache := (kind,value) :: !cache
          in value end
      val result = case find_for work root kind prepared of
          SOME fact => fact
        | NONE => raise ERR "get" "missing privately prepared stock law"
      val _ = validate owner
    in result end
    handle primary => (W.close work;raise primary)
  structure RP = SmtReplayResourcePolicy
  datatype policy_portfolio = PolicyPortfolio of
    {work : W.portfolio,graph : G.graph,root : G.scope,sources : S.sources,
     limits : RP.semantic_policy,epoch : int,rows : row list,
     held : G.closure_child list}
  fun laws_prepare_policy work {needed,check_type} =
    let
      val _ = W.spend_policy work 0
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = W.semantic_policy work val epoch = Type.type_epoch ()
      val held = ref ([] : G.closure_child list)
      fun guard () =
        (W.validate_policy work graph root sources limits;
         if Type.type_epoch () = epoch then () else
           raise ERR "laws_prepare_policy" "original Type epoch changed";
         List.app (fn child =>
           ignore (G.closure_child_node graph root child)) (!held))
      fun tick () = (guard ();W.spend_policy work 1)
      fun call operation =
        (guard ();let val value = operation () val _ = guard () in value end)
      fun plus a b = RP.add_up_to (W.work_policy work) (a,b)
      val cap = #template_limit limits
      fun bounded label n = if RP.allows cap n then () else
        raise ERR "laws_prepare_policy" (label ^
          " exceeds original template cap")
      (* The enum admits exactly four declarations, not arbitrary theorem
         DATA. Each supplied spine/comparison is billed before inspection. *)
      fun unique pending seen =
        (tick ();case pending of [] => [] | kind::rest =>
          let fun duplicate [] = false
                | duplicate (old::more) =
                    (tick ();kind = old orelse duplicate more)
              val _ = if duplicate seen then
                raise ERR "laws_prepare_policy" "duplicate requested stock law"
                else ()
              val _ = tick () val suffix = unique rest (kind::seen)
              val _ = tick ()
          in kind::suffix end)
      val kinds = unique needed []
      val _ = tick () val types = ref ([] : Type.hol_type list)
      fun skeleton term =
        let val _ = tick ()
        in if call (fn () => Term.is_comb term) then
            let val (f,x) = call (fn () => Term.dest_comb term)
                val left = skeleton f val right = skeleton x
                val _ = tick () val _ = tick ()
            in Application (term,left,right) end
           else if call (fn () => Term.is_abs term) then
            let val (v,b) = call (fn () => Term.dest_abs term)
                val body = skeleton b val _ = tick () val _ = tick ()
            in Abstraction (term,v,body) end
           else if call (fn () => Term.is_var term orelse Term.is_const term)
             then (tick ();Atom term)
           else raise ERR "laws_prepare_policy" "unknown fixed law syntax"
        end
      fun size (Atom _) = (tick ();(1 : IntInf.int,1 : IntInf.int))
        | size (Application (_,a,b)) =
            let val (ar,ab) = size a val (br,bb) = size b val _ = tick ()
            in (plus 1 (plus ar br),plus 1 (plus ab bb)) end
        | size (Abstraction (_,_,b)) =
            let val (r,i) = size b val _ = tick ()
            in (plus 1 r,plus 2 i) end
      fun type_weight ty =
        let fun walk pending n =
              (tick ();case pending of [] => n | spine::more =>
                (tick ();case spine of [] => walk more n
                 | current::rest =>
                   let val n = plus n 1 val _ = bounded "law Type tree" n
                       val _ = tick ()
                   in if call (fn () => Type.is_vartype current) then
                        (tick ();walk (rest::more) n)
                      else let val args = call
                          (fn () => #2 (Type.dest_type current))
                        val _ = tick () val _ = tick ()
                      in walk (args::rest::more) n end end))
            val _ = tick () val _ = tick ()
        in walk [[ty]] 0 end
      fun annotate term =
        let val _ = tick () val ty = call (fn () => Term.type_of term)
            val weight = type_weight ty
            val _ = tick () val _ = tick () val _ = types := ty :: !types
        in weight end
      fun profile (Atom term) =
            let val t = annotate term val _ = tick ()
            in {raw = 1,binder = 1,ann = t,ty = t} : count end
        | profile (Application (term,a,b)) =
            let val x = profile a val y = profile b val t = annotate term
                val _ = tick ()
            in {raw = plus 1 (plus (#raw x) (#raw y)),
                binder = plus 1 (plus (#binder x) (#binder y)),
                ann = plus t (plus (#ann x) (#ann y)),ty = t} : count end
        | profile (Abstraction (term,variable,b)) =
            let val body = profile b val v = annotate variable
                val t = annotate term val _ = tick ()
            in {raw = plus 1 (#raw body),binder = plus 2 (#binder body),
                ann = plus t (plus v (#ann body)),ty = t} : count end
      fun plan kind =
        let val _ = tick () val theorem = fixed kind
            val term = call (fn () => Thm.concl theorem)
            (* Fixed stock input only. term_size is theorem-free; its
               primitive full traversal is an explicit unclosed cost. *)
            val measured = call (fn () => Term.term_size term)
            val _ = bounded "stock law raw" (IntInf.fromInt measured)
            val syntax = skeleton term val (r,b) = size syntax
            val _ = bounded "stock law raw" r
            val _ = bounded "stock law binder-inclusive" b
            val _ = if r = IntInf.fromInt measured then () else
              raise ERR "laws_prepare_policy" "public law shape metric differs"
            val counts = profile syntax
            (* Import/opened/whole-anchor records preserve the complete law
               alpha shape. These are nominal full equation and EQ_MP
               inventories, not proof-operation-count or private G costs. *)
            val eq_raw = plus 3 (plus r r)
            val eq_binder = plus 3 (plus b b)
            val eq_ann = plus 9 (plus (#ann counts) (#ann counts))
            val _ = if RP.allows (#output_limit limits) eq_raw
                andalso RP.allows (#output_limit limits) eq_binder
              then () else raise ERR "laws_prepare_policy"
                "whole law bridge exceeds original output cap"
            val equation = plus eq_raw (plus eq_binder eq_ann)
            val amount = plus r (plus b (plus (#ann counts)
              (plus equation (plus equation equation))))
            val _ = tick () val _ = tick ()
        in (kind,theorem,term,amount) end
      fun plans pending =
        (tick ();case pending of [] => [] | k::rest =>
          let val row = plan k val suffix = plans rest val _ = tick ()
          in row::suffix end)
      val plans = plans kinds
      fun total [] result = result
        | total ((_,_,_,amount)::rest) result =
            (tick ();total rest (plus result amount))
      val amount = total plans 0
      val _ = if RP.allows (W.remaining_policy work) amount then () else
        raise ERR "laws_prepare_policy" "needed laws exhaust original Work"
      (* This lazy policy_owner invokes prepare for one needed kind at a time.
         Fixed LawInstance ordinals 0..3 never overlap selected C/L
         LocalCarrier/ClosedRecord names. A second policy_owner cannot reissue
           one
         and renew its allowance; global Work remains the original object. *)
      val _ = case kinds of [] => () | [kind] =>
        let val token = W.reserve_policy work
              {role = W.LawInstance,ordinal = ordinal kind,
               amount = amount}
        in W.consume_policy work token (amount) end
        | _ => raise ERR "laws_prepare_policy" "private lazy preparation shape"
      (* Equality is Boolean: exact newly built schema types are admitted
         from known fixed Boolean constructors after the nominal debit. *)
      val _ = tick ()
      val bool_arrow = call (fn () => Type.mk_type
        ("fun",[Type.bool,Type.bool]))
      val _ = tick ()
      val eq_type = call (fn () => Type.mk_type ("fun",[Type.bool,bool_arrow]))
      fun policy ty = (guard ();check_type ty;guard ())
      val _ = List.app policy (eq_type::bool_arrow:: !types)
      fun build [] = []
        | build ((kind,theorem,term,_)::rest) =
          let val _ = tick ()
              val prepared = call (fn () => G.plan_import_with_policy graph
                root
                (#template_limit limits) term)
              val source = call (fn () => G.execute_import_with_policy
                prepared)
              val opened = call (fn () => G.record_opened_view_with_policy
                graph root
                (#template_limit limits) (#node source))
              val _ = call (fn () => G.validate_opened_view graph root
                (#node source) opened)
              (* Retain every genuine canonical path before P's callbacks.
                 Descendants carry root as fixed getter caller and their
                 actual body-frame links inside the opaque G handle. *)
              fun retain child =
                let val _ = tick ()
                    val node = call (fn () =>
                      G.closure_child_node graph root child)
                    val _ = tick () val _ = held := child :: !held
                in case call (fn () => G.view graph node) of
                    G.Application _ =>
                      let val (a,b) = call (fn () =>
                            G.closure_application_children graph root child)
                      in retain a;retain b end
                  | G.AdmittedBinder _ =>
                      let val closure = call (fn () =>
                            G.closure_child_binder graph root child)
                      in retain (call (fn () =>
                        G.binder_closure_body graph root closure)) end
                  | G.OpaqueRetained => raise ERR "laws_prepare_policy"
                      "stock law discovery did not complete closure metadata"
                  | _ => () end
              val _ = retain (call (fn () =>
                G.closure_root graph root (#node opened)))
              val fact = call (fn () =>
                P.record_closed_from_import_with_policy graph root
                {node = #node opened,theorem = theorem,
                 template_limit = #template_limit limits,check_type = policy})
              val _ = if Portable.pointer_eq (P.closed_original fact,theorem)
                then () else raise ERR "laws_prepare_policy"
                  "original law changed"
              val _ = tick ()
              val row = {kind = kind,original = theorem,source = source,
                         opened = opened,fact = fact}
              val suffix = build rest val _ = tick ()
          in row::suffix end
      val rows = build plans val _ = guard ()
    in PolicyPortfolio {work = work,graph = graph,root = root,sources =
      sources,
       limits = limits,epoch = epoch,rows = rows,held = !held} end
    handle primary => (W.close work;raise primary)

  fun laws_find_policy expected scope kind
      (PolicyPortfolio {work,graph,root,sources,limits,epoch,rows,held}) =
    let
      val _ = if Portable.pointer_eq (expected,work) then () else
        raise ERR "laws_find_policy" "foreign expected Work"
      val _ = W.validate_policy expected graph root sources limits
      val _ = if G.scope_visible graph scope root andalso
          Type.type_epoch () = epoch then () else
        raise ERR "laws_find_policy" "scope or Type epoch changed"
      val _ = List.app (fn child =>
        ignore (G.closure_child_node graph root child)) held
      fun find [] = NONE
        | find ((row : row)::rest) = if #kind row = kind then
            let val _ = G.validate_opened_view graph root
                  (#node (#source row)) (#opened row)
                val _ = P.validate_closed_fact_with_policy graph scope
                  (#template_limit limits) (#fact row)
                val _ = if Portable.pointer_eq
                    (P.closed_original (#fact row),fixed kind) then () else
                  raise ERR "laws_find_policy" "stock theorem identity changed"
            in SOME (#fact row) end
          else find rest
    in find rows end
    handle primary => (W.close expected;raise primary)

  datatype policy_owner = PolicyOwner of
    {work : W.portfolio,graph : G.graph,root : G.scope,sources : S.sources,
     limits : RP.semantic_policy,epoch : int,check_type : Type.hol_type ->
       unit,
     cache : (kind * policy_portfolio) list ref}
  fun validate_with_policy (PolicyOwner
    {work,graph,root,sources,limits,epoch,cache,...}) =
    ((W.validate_policy work graph root sources limits;
      if Type.type_epoch () = epoch then () else
        raise ERR "validate_with_policy" "original policy_owner epoch changed";
      List.app (fn (kind,policy_portfolio) =>
        ignore (laws_find_policy work root kind policy_portfolio)) (!cache))
     handle primary => (W.close work;raise primary))
  fun begin_with_policy work {check_type} =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val root = S.owning_scope sources
        val limits = W.semantic_policy work
        val _ = W.validate_policy work graph root sources limits
    in PolicyOwner {work = work,graph = graph,root = root,sources = sources,
       limits = limits,epoch = Type.type_epoch (),check_type = check_type,
       cache = ref []} end
    handle primary => (W.close work;raise primary)
  fun get_with_policy (policy_owner as PolicyOwner
    {work,root,check_type,cache,...})
      {natural,universal} =
    let
      val _ = validate_with_policy policy_owner
      val kind = case (natural,universal) of
          (true,true) => NumForall | (true,false) => NumExists
        | (false,true) => BagForall | (false,false) => BagExists
      fun previous [] = NONE
        | previous ((old,value)::rest) =
            if kind = old then SOME value else previous rest
      val prepared = case previous (!cache) of SOME value => value
        | NONE =>
          let val value = W.with_step work (fn () =>
                laws_prepare_policy work {needed = [kind],check_type =
                  check_type})
              val _ = validate_with_policy policy_owner
              val _ = cache := (kind,value) :: !cache
          in value end
      val result = case laws_find_policy work root kind prepared of
          SOME fact => fact
        | NONE => raise ERR "get_with_policy"
          "missing privately prepared stock law"
      val _ = validate_with_policy policy_owner
    in result end
    handle primary => (W.close work;raise primary)
  fun validate_with_policy_for expected
      (held as PolicyOwner {work,...}) =
    ((if Portable.pointer_eq (expected,work) then () else
        raise ERR "validate_with_policy_for" "foreign expected Work";
      validate_with_policy held)
     handle primary => (W.close expected;raise primary))
  fun get_with_policy_for expected held flags =
    (validate_with_policy_for expected held;get_with_policy held flags)


  fun nl_min RP.Uncapped b=b
    | nl_min a RP.Uncapped=a
    | nl_min (RP.AtMost a)(RP.AtMost b)=RP.AtMost(IntInf.min(a,b))
  fun nl_prepare work contract {needed,check_type} =
    let
      val native=SmtReplayNativeContract.for_work work contract
      val native_limits= #semantic_limits native
      val native_work=IntInf.fromInt(#type_work_limit native)
      val _ = W.spend_policy work 0
      val sources = W.original_sources work
      val graph = S.owning_graph sources val root = S.owning_scope sources
      val limits = W.semantic_policy work val epoch = Type.type_epoch ()
      val held = ref ([] : G.closure_child list)
      fun guard () =
        (SmtReplayNativeContract.validate_for work contract;
         W.validate_policy work graph root sources limits;
         if Type.type_epoch () = epoch then () else
           raise ERR "laws_prepare_policy" "original Type epoch changed";
         List.app (fn child =>
           ignore (G.closure_child_node graph root child)) (!held))
      fun tick () = (guard ();W.spend_policy work 1)
      fun call operation =
        (guard ();let val value = operation () val _ = guard () in value end)
      fun plus a b = RP.add_up_to (W.work_policy work) (a,b)
      val cap=nl_min (#template_limit limits)
        (RP.AtMost(IntInf.fromInt(#template_limit native_limits)))
      fun bounded label n = if RP.allows cap n then () else
        raise ERR "laws_prepare_policy" (label ^
          " exceeds original template cap")
      (* The enum admits exactly four declarations, not arbitrary theorem
         DATA. Each supplied spine/comparison is billed before inspection. *)
      fun unique pending seen =
        (tick ();case pending of [] => [] | kind::rest =>
          let fun duplicate [] = false
                | duplicate (old::more) =
                    (tick ();kind = old orelse duplicate more)
              val _ = if duplicate seen then
                raise ERR "laws_prepare_policy" "duplicate requested stock law"
                else ()
              val _ = tick () val suffix = unique rest (kind::seen)
              val _ = tick ()
          in kind::suffix end)
      val kinds = unique needed []
      val _ = tick () val types = ref ([] : Type.hol_type list)
      fun skeleton term =
        let val _ = tick ()
        in if call (fn () => Term.is_comb term) then
            let val (f,x) = call (fn () => Term.dest_comb term)
                val left = skeleton f val right = skeleton x
                val _ = tick () val _ = tick ()
            in Application (term,left,right) end
           else if call (fn () => Term.is_abs term) then
            let val (v,b) = call (fn () => Term.dest_abs term)
                val body = skeleton b val _ = tick () val _ = tick ()
            in Abstraction (term,v,body) end
           else if call (fn () => Term.is_var term orelse Term.is_const term)
             then (tick ();Atom term)
           else raise ERR "laws_prepare_policy" "unknown fixed law syntax"
        end
      fun size (Atom _) = (tick ();(1 : IntInf.int,1 : IntInf.int))
        | size (Application (_,a,b)) =
            let val (ar,ab) = size a val (br,bb) = size b val _ = tick ()
            in (plus 1 (plus ar br),plus 1 (plus ab bb)) end
        | size (Abstraction (_,_,b)) =
            let val (r,i) = size b val _ = tick ()
            in (plus 1 r,plus 2 i) end
      fun type_weight ty =
        let fun walk pending n =
              (tick ();case pending of [] => n | spine::more =>
                (tick ();case spine of [] => walk more n
                 | current::rest =>
                   let val n = plus n 1 val _ = bounded "law Type tree" n
                       val _ = tick ()
                   in if call (fn () => Type.is_vartype current) then
                        (tick ();walk (rest::more) n)
                      else let val args = call
                          (fn () => #2 (Type.dest_type current))
                        val _ = tick () val _ = tick ()
                      in walk (args::rest::more) n end end))
            val _ = tick () val _ = tick ()
        in walk [[ty]] 0 end
      fun annotate term =
        let val _ = tick () val ty = call (fn () => Term.type_of term)
            val weight = type_weight ty
            val _ = tick () val _ = tick () val _ = types := ty :: !types
        in weight end
      fun profile (Atom term) =
            let val t = annotate term val _ = tick ()
            in {raw = 1,binder = 1,ann = t,ty = t} : count end
        | profile (Application (term,a,b)) =
            let val x = profile a val y = profile b val t = annotate term
                val _ = tick ()
            in {raw = plus 1 (plus (#raw x) (#raw y)),
                binder = plus 1 (plus (#binder x) (#binder y)),
                ann = plus t (plus (#ann x) (#ann y)),ty = t} : count end
        | profile (Abstraction (term,variable,b)) =
            let val body = profile b val v = annotate variable
                val t = annotate term val _ = tick ()
            in {raw = plus 1 (#raw body),binder = plus 2 (#binder body),
                ann = plus t (plus v (#ann body)),ty = t} : count end
      fun plan kind =
        let val _ = tick () val theorem = fixed kind
            val term = call (fn () => Thm.concl theorem)
            (* Fixed stock input only. term_size is theorem-free; its
               primitive full traversal is an explicit unclosed cost. *)
            val measured = call (fn () => Term.term_size term)
            val _ = bounded "stock law raw" (IntInf.fromInt measured)
            val syntax = skeleton term val (r,b) = size syntax
            val _ = bounded "stock law raw" r
            val _ = bounded "stock law binder-inclusive" b
            val _ = if r = IntInf.fromInt measured then () else
              raise ERR "laws_prepare_policy" "public law shape metric differs"
            val counts = profile syntax
            (* Import/opened/whole-anchor records preserve the complete law
               alpha shape. These are nominal full equation and EQ_MP
               inventories, not proof-operation-count or private G costs. *)
            val eq_raw = plus 3 (plus r r)
            val eq_binder = plus 3 (plus b b)
            val eq_ann = plus 9 (plus (#ann counts) (#ann counts))
            val _ = if RP.allows (#output_limit limits) eq_raw
                andalso RP.allows (#output_limit limits) eq_binder
              then () else raise ERR "laws_prepare_policy"
                "whole law bridge exceeds original output cap"
            val _=if eq_raw<=IntInf.fromInt(#output_limit native_limits)
                andalso eq_binder<=IntInf.fromInt
                  (#output_limit native_limits)then ()else
              raise ERR "native_law"
                "native stock law output exceeds original cap"
            (* Complete annotation vector, plus P's unique graph vector;
               whole-import anchoring adds no composite atom Type roots.
               The two fixed Boolean arrows have Type weights 5 and 3. *)
            val callback_forest=2 * #ann counts+8
            val _=if callback_forest<=native_work then ()else
              raise ERR "native_law"
                "native stock law callback forest exceeds Type work"
            val equation = plus eq_raw (plus eq_binder eq_ann)
            val amount = plus r (plus b (plus (#ann counts)
              (plus equation (plus equation equation))))
            val _ = tick () val _ = tick ()
        in (kind,theorem,term,amount) end
      fun plans pending =
        (tick ();case pending of [] => [] | k::rest =>
          let val row = plan k val suffix = plans rest val _ = tick ()
          in row::suffix end)
      val plans = plans kinds
      fun total [] result = result
        | total ((_,_,_,amount)::rest) result =
            (tick ();total rest (plus result amount))
      val amount = total plans 0
      val _=if amount<=native_work then ()else
        raise ERR "native_law"
          "native stock law portfolio exceeds caller Type work"
      val _ = if RP.allows (W.remaining_policy work) amount then () else
        raise ERR "laws_prepare_policy" "needed laws exhaust original Work"
      (* This lazy policy_owner invokes prepare for one needed kind at a time.
         Fixed LawInstance ordinals 0..3 never overlap selected C/L
         LocalCarrier/ClosedRecord names. A second policy_owner cannot reissue
           one
         and renew its allowance; global Work remains the original object. *)
      val _ = case kinds of [] => () | [kind] =>
        let val token = W.reserve_policy work
              {role = W.LawInstance,ordinal = ordinal kind,
               amount = amount}
        in W.consume_policy work token (amount) end
        | _ => raise ERR "laws_prepare_policy" "private lazy preparation shape"
      fun import_plan(kind,theorem,term,amount)=
        let val prepared=call(fn()=>G.plan_import_with_policy graph root
              (nl_min (#template_limit limits)
                (RP.AtMost(IntInf.fromInt(#import_limit native))))term)
        in (kind,theorem,term,amount,prepared)end
      val prepared_plans=List.map import_plan plans
      (* Equality is Boolean: exact newly built schema types are admitted
         from known fixed Boolean constructors after the nominal debit. *)
      val _ = tick ()
      val bool_arrow = call (fn () => Type.mk_type
        ("fun",[Type.bool,Type.bool]))
      val _ = tick ()
      val eq_type = call (fn () => Type.mk_type ("fun",[Type.bool,bool_arrow]))
      fun policy ty = (guard ();check_type ty;guard ())
      val _ = List.app policy (eq_type::bool_arrow:: !types)
      fun build [] = []
        | build ((kind,theorem,term,_,prepared)::rest) =
          let val _ = tick ()
              val source = call (fn () => G.execute_import_with_policy
                prepared)
              val opened = call (fn () => G.record_opened_view_with_policy
                graph root
                cap (#node source))
              val _ = call (fn () => G.validate_opened_view graph root
                (#node source) opened)
              (* Retain every genuine canonical path before P's callbacks.
                 Descendants carry root as fixed getter caller and their
                 actual body-frame links inside the opaque G handle. *)
              fun retain child =
                let val _ = tick ()
                    val node = call (fn () =>
                      G.closure_child_node graph root child)
                    val _ = tick () val _ = held := child :: !held
                in case call (fn () => G.view graph node) of
                    G.Application _ =>
                      let val (a,b) = call (fn () =>
                            G.closure_application_children graph root child)
                      in retain a;retain b end
                  | G.AdmittedBinder _ =>
                      let val closure = call (fn () =>
                            G.closure_child_binder graph root child)
                      in retain (call (fn () =>
                        G.binder_closure_body graph root closure)) end
                  | G.OpaqueRetained => raise ERR "laws_prepare_policy"
                      "stock law discovery did not complete closure metadata"
                  | _ => () end
              val _ = retain (call (fn () =>
                G.closure_root graph root (#node opened)))
              val fact = call (fn () =>
                P.record_closed_from_import_with_policy graph root
                {node = #node opened,theorem = theorem,
                 template_limit = #template_limit limits,check_type = policy})
              val _ = if Portable.pointer_eq (P.closed_original fact,theorem)
                then () else raise ERR "laws_prepare_policy"
                  "original law changed"
              val _ = tick ()
              val row = {kind = kind,original = theorem,source = source,
                         opened = opened,fact = fact}
              val suffix = build rest val _ = tick ()
          in row::suffix end
      val rows = build prepared_plans val _ = guard ()
    in PolicyPortfolio {work = work,graph = graph,root = root,sources =
      sources,
       limits = limits,epoch = epoch,rows = rows,held = !held} end
    handle primary => (W.close work;raise primary)

  (* The legacy owner is private and can only be populated by nl_prepare.
     Its single per-kind cache therefore retains actual native preflight. *)
  datatype native_policy_owner=NativePolicyOwner of
    {work:W.portfolio,contract:SmtReplayNativeContract.contract,
     legacy:policy_owner}
  fun validate_native_with_policy_for expected
      (saved as NativePolicyOwner{work,...})=
    ((if Portable.pointer_eq(expected,work)then ()else
        raise ERR "native_law" "different original native-law Work";
      let val NativePolicyOwner{contract,legacy,...}=saved
      in SmtReplayNativeContract.validate_for expected contract;
         validate_with_policy_for expected legacy end)
     handle primary=>(W.close expected;raise primary))
  fun native_contract_with_policy_for expected saved=
    (validate_native_with_policy_for expected saved;
     let val NativePolicyOwner{contract,...}=saved in contract end)
  fun begin_native_with_policy work {native_contract,check_type}=
    ((SmtReplayNativeContract.validate_for work native_contract;
      let fun policy ty=
            (SmtReplayNativeContract.validate_for work native_contract;
             check_type ty;
             SmtReplayNativeContract.validate_for work native_contract)
          val legacy=begin_with_policy work {check_type=policy}
      in NativePolicyOwner
        {work=work,contract=native_contract,legacy=legacy}end)
     handle primary=>(W.close work;raise primary))
  fun get_native_with_policy_for expected saved {natural,universal}=
    ((validate_native_with_policy_for expected saved;
      let val NativePolicyOwner{contract,legacy=PolicyOwner
            {root,cache,check_type,...},...}=saved
          val kind=case(natural,universal)of
              (true,true)=>NumForall|(true,false)=>NumExists
            | (false,true)=>BagForall|(false,false)=>BagExists
          val previous=List.find(fn(old,_)=>old=kind)(!cache)
          val prepared=case previous of SOME(_,value)=>value|NONE=>
            let val value=W.with_step expected(fn()=>nl_prepare
                  expected contract {needed=[kind],check_type=check_type})
                val _=validate_native_with_policy_for expected saved
                val _=cache:=(kind,value):: !cache
            in value end
          val fact=case laws_find_policy expected root kind prepared of
              SOME fact=>fact|NONE=>raise ERR "native_law"
                "missing privately prepared native stock law"
          val _=validate_native_with_policy_for expected saved
      in fact end)
     handle primary=>(W.close expected;raise primary))
end
