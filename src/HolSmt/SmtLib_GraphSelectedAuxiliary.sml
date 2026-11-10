(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphSelectedAuxiliary :>
    SmtLib_GraphSelectedAuxiliary =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure I = SmtReplayImport
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphSelectedAuxiliary"
  datatype phase = New | Prepared | Executed | Retired
  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     symbols : int,phase : phase ref,check_type : Type.hol_type -> unit,
     head : Term.term,ordinal : int,original : Thm.thm}
  datatype plan = Plan of {owner : owner,originals : Thm.thm list}
  type expected =
    {graph : G.graph,scope : G.scope,sources : S.sources,work : W.portfolio}
  datatype receipt = Receipt of
    {owner : owner,imported : G.source,opened : G.source,
     law : P.closed_fact,canonical : Thm.thm}
  fun retire (Owner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected owner action = action () handle primary =>
    (retire owner;raise primary)
  fun active (owner as Owner {work,graph,scope,sources,symbols,phase,...}) =
    protected owner (fn () =>
      (if !phase = Retired then raise ERR "active" "catalogue retired" else ();
       W.validate work graph scope sources (W.semantic_limits work);
       if Term.term_epoch () = symbols then () else
         raise ERR "active" "constant retirement epoch changed"))
  fun begin work {selection,ordinal,check_type} = W.with_step work (fn () =>
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val limits = W.semantic_limits work
        val symbols = Term.term_epoch ()
        fun live () =
          (W.validate work graph scope sources limits;
           if Term.term_epoch () = symbols then () else
             raise ERR "begin" "constant retirement during selection")
        fun charge n = (live ();W.spend work n;live ())
        val _ = charge 1
        val data = SmtLib_GraphNumericStock.selection_data selection
        val _ = live ()
        val head = #head data
        val _ = if ordinal >= 0 andalso Term.is_const head then () else
          raise ERR "begin" "head/ordinal is not a stock selection"
        (* SAME retained opaque selection, not a second dynamic GEN_ALL/SYM
           call. Its original selection cost is not a past Work grant. *)
        val selected = #laws data
        val _ = live ()
        fun choose [] _ = raise ERR "begin" "absent stock law ordinal"
          | choose (law :: rest) i =
              (charge 1;if i = 0 then law else choose rest (i-1))
        val original = choose selected ordinal
    in Owner {work = work,graph = graph,scope = scope,sources = sources,
      symbols = symbols,phase = ref New,check_type = check_type,
      head = head,ordinal = ordinal,original = original} end)
  fun guarded owner action = protected owner (fn () =>
    (active owner;let val value = action () in active owner;value end))
  fun checked_policy (owner as Owner {check_type,...}) ty =
    guarded owner (fn () => check_type ty)
  fun spend (owner as Owner {work,...}) amount =
    (active owner;W.spend work amount;active owner)
  fun debit (owner as Owner {work,...}) amount =
    if amount >= 0 andalso amount <= IntInf.fromInt (W.work_limit work)
    then spend owner (IntInf.toInt amount)
    else (retire owner;raise ERR "debit" "fixed portfolio exceeds Work")

  fun prepare (owner as Owner {work,phase,original,...}) =
    protected owner (fn () => W.with_step work (fn () =>
    let
      val _ = active owner
      val _ = if !phase = New then phase := Prepared else
        raise ERR "prepare" "fixed catalogue attempt already consumed"
      val originals = [original]
      val cap = IntInf.fromInt (#template_limit (W.semantic_limits work))
      val types = ref ([] : Type.hol_type list)
      fun type_profile root =
        let
          fun walk [] count = count
            | walk (ty :: rest) count =
              (spend owner 1;
               if Type.is_vartype ty then
                 (spend owner (String.size (Type.dest_vartype ty));
                  walk rest (count+1))
               else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                        val _ = spend owner
                          (String.size Thy + String.size Tyop)
                        val _ = List.app (fn _ => spend owner 1) Args
                    in walk (Args @ rest) (count+1) end)
        in walk [root] (0 : IntInf.int) end
      (* Exact repeated annotation multiplicities, including the binder
         variable slot. count_body names confer no matching/FV authority. *)
      fun syntax root =
        let
          fun walk [] raw inclusive annotation = (raw,inclusive,annotation)
            | walk (current :: rest) raw inclusive annotation =
              (spend owner 1;
               let val ty = Term.type_of current
                   val weight = type_profile ty
                   val _ = types := ty :: !types
               in if Term.is_comb current then
                    let val (f,x) = Term.dest_comb current
                    in walk (f :: x :: rest) (raw+1) (inclusive+1)
                         (annotation+weight) end
                  else if Term.is_abs current then
                    let val (domain,_) = Type.dom_rng ty
                        val binder_weight = type_profile domain
                        val _ = types := domain :: !types
                        val body = guarded owner
                          (fn () => I.count_body current)
                    in walk (body :: rest) (raw+1) (inclusive+2)
                         (annotation+weight+binder_weight) end
                  else walk rest (raw+1) (inclusive+1) (annotation+weight)
               end)
        in walk [root] (0 : IntInf.int) 0 0 end
      fun clean th =
        let val (oracles,_) = Tag.dest_tag (Thm.tag th)
            fun tags [] = true
              | tags (name :: rest) =
                  (spend owner 1;name = "DISK_THM" andalso tags rest)
        in null (Thm.hyp th) andalso null (Tag.axioms_of (Thm.tag th))
          andalso tags oracles end
      fun inspect [] quote = quote
        | inspect (th :: rest) quote =
          let
            val _ = spend owner 1
            val _ = if clean th then () else
              raise ERR "prepare" "fixed normalization rule is not closed"
            val (raw,inclusive,ann) = syntax (Thm.concl th)
            val _ = if raw <= cap andalso inclusive <= cap then () else
              raise ERR "prepare" "fixed rule exceeds recording template"
            (* Two import/opened equality operands, P and retained receipt
               TRANS/EQ_MP results. Nominal constructor/annotation footprint only;
               private G/P/kernel/symbol work remains explicitly unquoted. *)
            val footprint = 4*(2*inclusive+3) + 2*inclusive + 10*ann+36
          in inspect rest (quote+footprint) end
      val quote = inspect originals (0 : IntInf.int)
      val _ = debit owner quote
      (* Complete original rules and future bridge metadata precede the first
         external policy and any graph import/opening/closed recording. *)
      val _ = List.app (checked_policy owner) (List.rev (!types))
    in Plan {owner = owner,originals = originals} end))

  fun execute (Plan {owner = owner as Owner
      {work,graph,scope,phase,...},originals}) =
    protected owner (fn () => W.with_step work (fn () =>
    let
      val _ = active owner
      val _ = if !phase = Prepared then phase := Executed else
        raise ERR "execute" "fixed catalogue plan already consumed"
      val cap = #template_limit (W.semantic_limits work)
      val (original,imported,opened,law,canonical) = case originals of
          [th] =>
            let val imported = guarded owner (fn () =>
                  G.import graph scope cap (Thm.concl th))
                val opened = guarded owner (fn () =>
                  G.record_opened_view graph scope cap (#node imported))
                val _ = G.validate_opened_view graph scope
                  (#node imported) opened
                val law = guarded owner (fn () =>
                  P.record_closed_from_import graph scope
                    {node = #node opened,theorem = th,template_limit = cap,
                     check_type = checked_policy owner})
                val bridge = guarded owner (fn () =>
                  Thm.TRANS (#bridge imported) (#bridge opened))
                val canonical = guarded owner (fn () => Thm.EQ_MP bridge th)
                val _ = if null (Thm.hyp canonical) andalso
                    Portable.pointer_eq (Thm.concl canonical,
                      G.representative graph (#node opened)) then () else
                  raise ERR "execute" "canonical original law changed"
            in (th,imported,opened,law,canonical) end
        | _ => raise ERR "execute" "selected law count changed"
    in Receipt {owner = owner,imported = imported,opened = opened,
      law = law,canonical = canonical} end))

  fun validate_for {graph,scope,sources,work = expected}
      (Receipt {owner = owner as Owner
        {work,graph = held_graph,scope = held_scope,sources = held_sources,
         original,...},imported,opened,law,canonical}) =
    ((if Portable.pointer_eq (expected,work) andalso
          Portable.pointer_eq (graph,held_graph) andalso scope = held_scope
          andalso Portable.pointer_eq (sources,held_sources) then () else
        raise ERR "validate_for" "foreign selected auxiliary owner";
      active owner;
      P.validate_closed_fact graph scope
        (#template_limit (W.semantic_limits expected)) law;
      G.validate_opened_view graph scope (#node imported) opened;
      if Portable.pointer_eq (P.closed_original law,original) andalso
          P.closed_node law = #node opened andalso
          Portable.pointer_eq (#original imported,Thm.concl original) andalso
          Portable.pointer_eq (Thm.concl canonical,
            G.representative graph (#node opened)) andalso
          null (Thm.hyp canonical) then () else
        raise ERR "validate_for" "selected law/bridge endpoint changed")
     handle primary => (W.close expected;raise primary))
  fun describe_for expected (held as Receipt
      {owner = Owner {head,ordinal,original,...},
       imported,opened,law,canonical}) =
    (validate_for expected held;
     {head = head,ordinal = ordinal,original = original,
      imported = imported,opened = opened,law = law,
      canonical_theorem = canonical})
  structure RP = SmtReplayResourcePolicy
  structure NC = SmtReplayNativeContract
  datatype policy_owner = PolicyOwner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     symbols : int,phase : phase ref,check_type : Type.hol_type -> unit,
     head : Term.term,ordinal : int,original :
       Thm.thm,native_contract:NC.contract,
     limits:RP.semantic_policy}
  datatype policy_plan = PolicyPlan of
    {policy_owner:policy_owner,originals:Thm.thm list,
     import_plan:G.policy_import_plan}
  datatype policy_receipt = PolicyReceipt of
    {policy_owner : policy_owner,imported : G.source,opened : G.source,
     law : P.closed_fact,canonical : Thm.thm}
  fun sa_retire (PolicyOwner {work,phase,...}) = (phase := Retired;W.close
    work)
  fun sa_protected policy_owner action = action () handle primary =>
    (sa_retire policy_owner;raise primary)
  fun sa_active (policy_owner as PolicyOwner
    {work,graph,scope,sources,symbols,phase,native_contract,limits,...}) =
    sa_protected policy_owner (fn () =>
      (if !phase = Retired then raise ERR "sa_active" "catalogue retired" else
        ();
       W.validate_policy work graph scope sources limits;
       NC.validate_for work native_contract;
       if Term.term_epoch () = symbols then () else
         raise ERR "sa_active" "constant retirement epoch changed"))
  fun begin_with_policy work
      {selection,ordinal,check_type,native_contract} = W.with_step work (fn ()
        =>
    let val _ = NC.validate_for work native_contract
        val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val limits = W.semantic_policy work
        val symbols = Term.term_epoch ()
        fun live () =
          (W.validate_policy work graph scope sources limits;
           if Term.term_epoch () = symbols then () else
             raise ERR "begin_with_policy"
               "constant retirement during selection")
        fun charge n = (live ();W.spend_policy work (IntInf.fromInt n);live ())
        val _ = charge 1
        val data = SmtLib_GraphNumericStock.selection_data selection
        val _ = live ()
        val head = #head data
        val _ = if ordinal >= 0 andalso Term.is_const head then () else
          raise ERR "begin_with_policy" "head/ordinal is not a stock selection"
        (* SAME retained opaque selection, not a second dynamic GEN_ALL/SYM
           call. Its original selection cost is not a past Work grant. *)
        val selected = #laws data
        val _ = live ()
        fun choose [] _ = raise ERR "begin_with_policy"
          "absent stock law ordinal"
          | choose (law :: rest) i =
              (charge 1;if i = 0 then law else choose rest (i-1))
        val original = choose selected ordinal
    in PolicyOwner {work = work,graph = graph,scope = scope,sources = sources,
      symbols = symbols,phase = ref New,check_type = check_type,
      head = head,ordinal = ordinal,original = original,
      native_contract=native_contract,limits=limits} end)
  fun sa_guarded policy_owner action = sa_protected policy_owner (fn () =>
    (sa_active policy_owner;let val value = action () in sa_active
      policy_owner;value end))
  fun sa_checked_policy (policy_owner as PolicyOwner {check_type,...}) ty =
    sa_guarded policy_owner (fn () => check_type ty)
  fun sa_spend (policy_owner as PolicyOwner {work,...}) amount =
    (sa_active policy_owner;W.spend_policy work (IntInf.fromInt
      amount);sa_active policy_owner)
  fun sa_debit (policy_owner as PolicyOwner {work,native_contract,...}) amount
    =
    let val native=NC.for_work work native_contract
    in if amount >= 0 andalso
        amount <= IntInf.fromInt (#type_work_limit native) andalso
        RP.allows (W.remaining_policy work) amount then
      (sa_active policy_owner;W.spend_policy work amount;sa_active
        policy_owner)
    else (sa_retire policy_owner;
      raise ERR "sa_debit" "fixed portfolio exceeds native or Work bound") end

  fun prepare_with_policy (policy_owner as PolicyOwner
    {work,graph,scope,phase,original,native_contract,...}) =
    sa_protected policy_owner (fn () => W.with_step work (fn () =>
    let
      val _ = sa_active policy_owner
      val _ = if !phase = New then phase := Prepared else
        raise ERR "prepare_with_policy"
          "fixed catalogue attempt already consumed"
      val originals = [original]
      val cap = #template_limit (W.semantic_policy work)
      val native=NC.for_work work native_contract
      val native_cap=IntInf.fromInt
        (#template_limit (#semantic_limits native))
      val native_types=IntInf.fromInt (#type_work_limit native)
      val annotation_used=ref (0:IntInf.int)
      val types = ref ([] : Type.hol_type list)
      fun type_profile root =
        let
          fun walk [] count = count
            | walk (ty :: rest) count =
              (sa_spend policy_owner 1;
               annotation_used := !annotation_used+1;
               if !annotation_used<=native_types then () else
                 raise ERR "prepare_with_policy" "native Type bound exceeded";
               if Type.is_vartype ty then
                 (sa_spend policy_owner (String.size (Type.dest_vartype ty));
                  walk rest (count+1))
               else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                        val _ = sa_spend policy_owner
                          (String.size Thy + String.size Tyop)
                        val _ = List.app (fn _ => sa_spend policy_owner 1) Args
                    in walk (Args @ rest) (count+1) end)
        in walk [root] (0 : IntInf.int) end
      (* Exact repeated annotation multiplicities, including the binder
         variable slot. count_body names confer no matching/FV authority. *)
      fun syntax root =
        let
          fun walk [] raw inclusive annotation = (raw,inclusive,annotation)
            | walk (current :: rest) raw inclusive annotation =
              (sa_spend policy_owner 1;
               let val ty = Term.type_of current
                   val weight = type_profile ty
                   val _ = types := ty :: !types
               in if Term.is_comb current then
                    let val (f,x) = Term.dest_comb current
                    in walk (f :: x :: rest) (raw+1) (inclusive+1)
                         (annotation+weight) end
                  else if Term.is_abs current then
                    let val (domain,_) = Type.dom_rng ty
                        val binder_weight = type_profile domain
                        val _ = types := domain :: !types
                        val body = sa_guarded policy_owner
                          (fn () => I.count_body current)
                    in walk (body :: rest) (raw+1) (inclusive+2)
                         (annotation+weight+binder_weight) end
                  else walk rest (raw+1) (inclusive+1) (annotation+weight)
               end)
        in walk [root] (0 : IntInf.int) 0 0 end
      fun clean th =
        let val (oracles,_) = Tag.dest_tag (Thm.tag th)
            fun tags [] = true
              | tags (name :: rest) =
                  (sa_spend policy_owner 1;name = "DISK_THM" andalso tags rest)
        in null (Thm.hyp th) andalso null (Tag.axioms_of (Thm.tag th))
          andalso tags oracles end
      fun inspect [] quote = quote
        | inspect (th :: rest) quote =
          let
            val _ = sa_spend policy_owner 1
            val _ = if clean th then () else
              raise ERR "prepare_with_policy"
                "fixed normalization rule is not closed"
            val (raw,inclusive,ann) = syntax (Thm.concl th)
            val _ = if RP.allows cap raw andalso RP.allows cap inclusive
              andalso
                raw<=native_cap andalso inclusive<=native_cap then () else
              raise ERR "prepare_with_policy"
                "fixed rule exceeds recording template"
            (* Two import/opened equality operands, P and retained
              policy_receipt
               TRANS/EQ_MP results. Nominal constructor/annotation footprint
                 only;
               private G/P/kernel/symbol work remains explicitly unquoted. *)
            val footprint = 4*(2*inclusive+3) + 2*inclusive + 10*ann+36
          in inspect rest (quote+footprint) end
      val quote = inspect originals (0 : IntInf.int)
      val _ = sa_debit policy_owner quote
      (* Plan the actual exposed import misses under the captured finite
         import contract before any external callback or bridge constructor.
         Execution retains the real plan and repeats its actual checks. *)
      val _ = sa_spend policy_owner 1
      val import_plan=sa_guarded policy_owner (fn()=>
        G.plan_import_with_policy graph scope
          (RP.AtMost (IntInf.fromInt (#import_limit native)))
          (Thm.concl original))
      (* Complete original rules and future bridge metadata precede the first
         external policy and any graph import/opening/closed recording. *)
      val _ = List.app (sa_checked_policy policy_owner) (List.rev (!types))
    in PolicyPlan {policy_owner=policy_owner,originals=originals,
      import_plan=import_plan} end))

  fun execute_with_policy (PolicyPlan {policy_owner = policy_owner as
    PolicyOwner
      {work,graph,scope,phase,native_contract,...},originals,import_plan}) =
    sa_protected policy_owner (fn () => W.with_step work (fn () =>
    let
      val _ = sa_active policy_owner
      val _ = if !phase = Prepared then phase := Executed else
        raise ERR "execute_with_policy"
          "fixed catalogue policy_plan already consumed"
      val cap = #template_limit (W.semantic_policy work)
      val native=NC.for_work work native_contract
      val native_cap=RP.AtMost (IntInf.fromInt
        (#template_limit (#semantic_limits native)))
      val (original,imported,opened,law,canonical) = case originals of
          [th] =>
            let val imported = sa_guarded policy_owner (fn () =>
                  G.execute_import_with_policy import_plan)
                val opened = sa_guarded policy_owner (fn () =>
                  G.record_opened_view_with_policy graph scope native_cap
                    (#node imported))
                val _ = G.validate_opened_view graph scope
                  (#node imported) opened
                val law = sa_guarded policy_owner (fn () =>
                  P.record_closed_from_import_with_policy graph scope
                    {node = #node opened,theorem = th,template_limit = cap,
                     check_type = sa_checked_policy policy_owner})
                val bridge = sa_guarded policy_owner (fn () =>
                  Thm.TRANS (#bridge imported) (#bridge opened))
                val canonical = sa_guarded policy_owner (fn () => Thm.EQ_MP
                  bridge th)
                val _ = if null (Thm.hyp canonical) andalso
                    Portable.pointer_eq (Thm.concl canonical,
                      G.representative graph (#node opened)) then () else
                  raise ERR "execute_with_policy"
                    "canonical original law changed"
            in (th,imported,opened,law,canonical) end
        | _ => raise ERR "execute_with_policy" "selected law count changed"
    in PolicyReceipt {policy_owner = policy_owner,imported = imported,opened =
      opened,
      law = law,canonical = canonical} end))

  fun validate_with_policy_for {graph,scope,sources,work = expected}
      (PolicyReceipt {policy_owner = policy_owner as PolicyOwner
        {work,graph = held_graph,scope = held_scope,sources = held_sources,
         original,...},imported,opened,law,canonical}) =
    ((if Portable.pointer_eq (expected,work) andalso
          Portable.pointer_eq (graph,held_graph) andalso scope = held_scope
          andalso Portable.pointer_eq (sources,held_sources) then () else
        raise ERR "validate_with_policy_for"
          "foreign selected auxiliary policy_owner";
      sa_active policy_owner;
      P.validate_closed_fact_with_policy graph scope
        (#template_limit (W.semantic_policy expected)) law;
      G.validate_opened_view graph scope (#node imported) opened;
      if Portable.pointer_eq (P.closed_original law,original) andalso
          P.closed_node law = #node opened andalso
          Portable.pointer_eq (#original imported,Thm.concl original) andalso
          Portable.pointer_eq (Thm.concl canonical,
            G.representative graph (#node opened)) andalso
          null (Thm.hyp canonical) then () else
        raise ERR "validate_with_policy_for"
          "selected law/bridge endpoint changed")
     handle primary => (W.close expected;raise primary))
  fun describe_with_policy_for expected (held as PolicyReceipt
      {policy_owner = PolicyOwner {head,ordinal,original,...},
       imported,opened,law,canonical}) =
    (validate_with_policy_for expected held;
     {head = head,ordinal = ordinal,original = original,
      imported = imported,opened = opened,law = law,
      canonical_theorem = canonical})

  (* Only the actual completed producer owns this token. Compare the full
     expected header BEFORE activating any held frame or proof backing. *)
  fun native_contract_with_policy_for
      (expected as {graph,scope,sources,work=expected_work}:expected)
      (held as PolicyReceipt {policy_owner=PolicyOwner
        {work,graph=held_graph,scope=held_scope,sources=held_sources,
         native_contract,...},...}) =
    ((if Portable.pointer_eq(expected_work,work) andalso
          Portable.pointer_eq(graph,held_graph) andalso scope=held_scope
          andalso Portable.pointer_eq(sources,held_sources) then () else
        raise ERR "native_contract_with_policy_for"
          "foreign selected auxiliary policy_owner";
      validate_with_policy_for expected held;native_contract)
     handle primary=>(W.close expected_work;raise primary))

end
