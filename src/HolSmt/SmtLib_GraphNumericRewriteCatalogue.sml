(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphNumericRewriteCatalogue :>
    SmtLib_GraphNumericRewriteCatalogue =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure P = SmtReplayProof
  structure I = SmtReplayImport
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNumericRewriteCatalogue"
  datatype phase = New | Prepared | Executed | Retired
  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     symbols : int,phase : phase ref,check_type : Type.hol_type -> unit}
  datatype plan = Plan of {owner : owner,originals : Thm.thm list}
  datatype catalogue = Catalogue of
    {owner : owner,originals : Thm.thm list,rules : P.closed_fact list}
  fun retire (Owner {work,phase,...}) = (phase := Retired;W.close work)
  fun protected owner action = action () handle primary =>
    (retire owner;raise primary)
  fun active (owner as Owner {work,graph,scope,sources,symbols,phase,...}) =
    protected owner (fn () =>
      (if !phase = Retired then raise ERR "active" "catalogue retired" else ();
       W.validate work graph scope sources (W.semantic_limits work);
       if Term.term_epoch () = symbols then () else
         raise ERR "active" "constant retirement epoch changed"))
  fun begin work {check_type} =
    let val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val _ = W.validate work graph scope sources (W.semantic_limits work)
    in Owner {work = work,graph = graph,scope = scope,sources = sources,
      symbols = Term.term_epoch (),phase = ref New,check_type = check_type} end
    handle primary => (W.close work;raise primary)
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

  fun prepare (owner as Owner {work,phase,...}) =
    protected owner (fn () => W.with_step work (fn () =>
    let
      val _ = active owner
      val _ = if !phase = New then phase := Prepared else
        raise ERR "prepare" "fixed catalogue attempt already consumed"
      val originals = SmtLib_GraphNumericStock.rewrites
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
            (* Two import/opened equality operands, their TRANS result and
               EQ_MP result. Nominal constructor/annotation footprint only;
               private G/P/kernel/symbol work remains explicitly unquoted. *)
            val footprint = 3*(2*inclusive+3) + inclusive + 6*ann+27+ann
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
      fun record th =
        let
          val imported = guarded owner (fn () =>
            G.import graph scope cap (Thm.concl th))
          val opened = guarded owner (fn () =>
            G.record_opened_view graph scope cap (#node imported))
          val _ = G.validate_opened_view graph scope (#node imported) opened
          val rule = guarded owner (fn () =>
            P.record_closed_from_import graph scope
              {node = #node opened,theorem = th,template_limit = cap,
               check_type = checked_policy owner})
        in rule end
      val rules = List.map record originals
    in Catalogue {owner = owner,originals = originals,rules = rules} end))

  fun validate_for expected
      (Catalogue {owner = owner as Owner {work,...},rules,...}) =
    ((ignore (W.original_sources expected);
      if Portable.pointer_eq (expected,work) then active owner else
        raise ERR "validate_for" "foreign Work catalogue";
      let val Owner {graph,scope,...} = owner
          val cap = #template_limit (W.semantic_limits expected)
      in List.app (P.validate_closed_fact graph scope cap) rules end)
     handle primary => (W.close expected;raise primary))
  fun originals (Catalogue {owner,originals,...}) =
    (active owner;originals)
  fun checked_rules (Catalogue {owner,rules,...}) = (active owner;rules)
  structure RP = SmtReplayResourcePolicy
  structure NC = SmtReplayNativeContract
  datatype policy_owner = PolicyOwner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     symbols : int,phase : phase ref,check_type : Type.hol_type -> unit,
     native_contract:NC.contract,limits:RP.semantic_policy}
  datatype policy_plan = PolicyPlan of {policy_owner :
    policy_owner,originals_with_policy : Thm.thm list,
     imports:G.policy_import_plan list}
  datatype policy_catalogue = PolicyCatalogue of
    {policy_owner : policy_owner,originals_with_policy : Thm.thm list,rules :
      P.closed_fact list}
  fun nr_retire (PolicyOwner {work,phase,...}) = (phase := Retired;W.close
    work)
  fun nr_protected policy_owner action = action () handle primary =>
    (nr_retire policy_owner;raise primary)
  fun nr_active (policy_owner as PolicyOwner
    {work,graph,scope,sources,symbols,phase,native_contract,limits,...}) =
    nr_protected policy_owner (fn () =>
      (if !phase = Retired then raise ERR "nr_active"
        "policy_catalogue retired" else ();
       W.validate_policy work graph scope sources limits;
       NC.validate_for work native_contract;
       if Term.term_epoch () = symbols then () else
         raise ERR "nr_active" "constant retirement epoch changed"))
  fun begin_with_policy work {check_type,native_contract} =
    let val _ = NC.validate_for work native_contract
        val sources = W.original_sources work
        val graph = S.owning_graph sources val scope = S.owning_scope sources
        val _ = W.validate_policy work graph scope sources (W.semantic_policy
          work)
    in PolicyOwner {work = work,graph = graph,scope = scope,sources = sources,
      symbols = Term.term_epoch (),phase = ref New,check_type = check_type,
      native_contract=native_contract,limits=W.semantic_policy work} end
    handle primary => (W.close work;raise primary)
  fun nr_guarded policy_owner action = nr_protected policy_owner (fn () =>
    (nr_active policy_owner;let val value = action () in nr_active
      policy_owner;value end))
  fun nr_checked_policy (policy_owner as PolicyOwner {check_type,...}) ty =
    nr_guarded policy_owner (fn () => check_type ty)
  fun nr_spend (policy_owner as PolicyOwner {work,...}) amount =
    (nr_active policy_owner;W.spend_policy work (IntInf.fromInt
      amount);nr_active policy_owner)
  fun nr_debit (policy_owner as PolicyOwner
      {work,native_contract,...}) amount =
    let val native=NC.for_work work native_contract
    in if amount>=0 andalso
        amount<=IntInf.fromInt (#type_work_limit native) andalso
        RP.allows (W.remaining_policy work) amount then
      (nr_active policy_owner;W.spend_policy work amount;
       nr_active policy_owner)
    else (nr_retire policy_owner;raise ERR "debit"
      "fixed portfolio exceeds native or Work allowance") end

  fun prepare_with_policy (policy_owner as PolicyOwner
    {work,graph,scope,phase,native_contract,...}) =
    nr_protected policy_owner (fn () => W.with_step work (fn () =>
    let
      val _ = nr_active policy_owner
      val _ = if !phase = New then phase := Prepared else
        raise ERR "prepare_with_policy"
          "fixed policy_catalogue attempt already consumed"
      val originals_with_policy = SmtLib_GraphNumericStock.rewrites
      val cap = #template_limit (W.semantic_policy work)
      val native=NC.for_work work native_contract
      val native_cap=IntInf.fromInt
        (#template_limit (#semantic_limits native))
      val annotation_used=ref (0:IntInf.int)
      val types = ref ([] : Type.hol_type list)
      fun type_profile root =
        let
          fun walk [] count = count
            | walk (ty :: rest) count =
              (nr_spend policy_owner 1;
               annotation_used := !annotation_used+1;
               if !annotation_used<=IntInf.fromInt (#type_work_limit native)
               then () else raise ERR "prepare_with_policy"
                 "native annotation ceiling exceeded";
               if Type.is_vartype ty then
                 (nr_spend policy_owner (String.size (Type.dest_vartype ty));
                  walk rest (count+1))
               else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                        val _ = nr_spend policy_owner
                          (String.size Thy + String.size Tyop)
                        val _ = List.app (fn _ => nr_spend policy_owner 1) Args
                    in walk (Args @ rest) (count+1) end)
        in walk [root] (0 : IntInf.int) end
      (* Exact repeated annotation multiplicities, including the binder
         variable slot. count_body names confer no matching/FV authority. *)
      fun syntax root =
        let
          fun walk [] raw inclusive annotation = (raw,inclusive,annotation)
            | walk (current :: rest) raw inclusive annotation =
              (nr_spend policy_owner 1;
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
                        val body = nr_guarded policy_owner
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
                  (nr_spend policy_owner 1;name = "DISK_THM" andalso tags rest)
        in null (Thm.hyp th) andalso null (Tag.axioms_of (Thm.tag th))
          andalso tags oracles end
      fun inspect [] quote = quote
        | inspect (th :: rest) quote =
          let
            val _ = nr_spend policy_owner 1
            val _ = if clean th then () else
              raise ERR "prepare_with_policy"
                "fixed normalization rule is not closed"
            val (raw,inclusive,ann) = syntax (Thm.concl th)
            val _ = if RP.allows cap raw andalso RP.allows cap inclusive
              andalso
                raw<=native_cap andalso inclusive<=native_cap then () else
              raise ERR "prepare_with_policy"
                "fixed rule exceeds recording template"
            (* Two import/opened equality operands, their TRANS result and
               EQ_MP result. Nominal constructor/annotation footprint only;
               private G/P/kernel/symbol work remains explicitly unquoted. *)
            val footprint = 3*(2*inclusive+3) + inclusive + 6*ann+27+ann
          in inspect rest (quote+footprint) end
      val quote = inspect originals_with_policy (0 : IntInf.int)
      val _ = nr_debit policy_owner quote
      val imports=List.map (fn th=>nr_guarded policy_owner (fn()=>
        G.plan_import_with_policy graph scope
          (RP.AtMost (IntInf.fromInt (#import_limit native)))
          (Thm.concl th))) originals_with_policy
      (* Complete original rules and future bridge metadata precede the first
         external policy and any graph import/opening/closed recording. *)
      val _ = List.app (nr_checked_policy policy_owner) (List.rev (!types))
    in PolicyPlan {policy_owner=policy_owner,
      originals_with_policy=originals_with_policy,imports=imports} end))

  fun execute_with_policy (PolicyPlan {policy_owner = policy_owner as
    PolicyOwner
      {work,graph,scope,phase,native_contract,...},
       originals_with_policy,imports}) =
    nr_protected policy_owner (fn () => W.with_step work (fn () =>
    let
      val _ = nr_active policy_owner
      val _ = if !phase = Prepared then phase := Executed else
        raise ERR "execute_with_policy"
          "fixed policy_catalogue policy_plan already consumed"
      val cap = #template_limit (W.semantic_policy work)
      val native=NC.for_work work native_contract
      val native_cap=RP.AtMost (IntInf.fromInt
        (#template_limit (#semantic_limits native)))
      fun record (th,import_plan) =
        let
          val imported = nr_guarded policy_owner (fn () =>
            G.execute_import_with_policy import_plan)
          val opened = nr_guarded policy_owner (fn () =>
            G.record_opened_view_with_policy graph scope native_cap
              (#node imported))
          val _ = G.validate_opened_view graph scope (#node imported) opened
          val rule = nr_guarded policy_owner (fn () =>
            P.record_closed_from_import_with_policy graph scope
              {node = #node opened,theorem = th,template_limit = cap,
               check_type = nr_checked_policy policy_owner})
        in rule end
      fun records [] [] = []
        | records (th::rest) (p::more) =
            record (th,p)::records rest more
        | records _ _ = raise ERR "execute_with_policy"
            "retained import incidence changed"
      val rules = records originals_with_policy imports
    in PolicyCatalogue {policy_owner = policy_owner,originals_with_policy =
      originals_with_policy,rules = rules} end))

  fun validate_with_policy_for expected
      (PolicyCatalogue {policy_owner = policy_owner as PolicyOwner
        {work,...},rules,...}) =
    ((ignore (W.original_sources expected);
      if Portable.pointer_eq (expected,work) then nr_active policy_owner else
        raise ERR "validate_with_policy_for" "foreign Work policy_catalogue";
      let val PolicyOwner {graph,scope,...} = policy_owner
          val cap = #template_limit (W.semantic_policy expected)
      in List.app (P.validate_closed_fact_with_policy graph scope cap) rules
        end)
     handle primary => (W.close expected;raise primary))
  fun originals_with_policy (PolicyCatalogue
    {policy_owner,originals_with_policy,...}) =
    (nr_active policy_owner;originals_with_policy)
  fun checked_rules_with_policy (PolicyCatalogue {policy_owner,rules,...}) =
    (nr_active policy_owner;rules)
  fun native_contract_for expected
      (held as PolicyCatalogue {policy_owner=PolicyOwner
        {native_contract,...},...}) =
    (validate_with_policy_for expected held;native_contract)

end
