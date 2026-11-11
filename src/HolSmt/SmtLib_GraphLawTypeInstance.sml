(* Proposed explicit type-instance producer. No legacy selector change. *)
structure SmtLib_GraphLawTypeInstance :> SmtLib_GraphLawTypeInstance =
struct
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure I = SmtReplayImport
  structure W = SmtReplayInvocationWork
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphLawTypeInstance"
  datatype producer = Producer of
    {graph : G.graph,scope : G.scope,original : P.closed_fact,
     limit : int,used : int ref,bytes : int ref,epoch : int,
     annotations : Type.hol_type list,variables : Type.hol_type vector,
     raw : int,binder : int,check_type : Type.hol_type -> unit,
     work : W.portfolio option}
  datatype plan = Plan of
    {producer : producer,theta : (Type.hol_type,Type.hol_type) Lib.subst,
     expected : (Type.hol_type,unit) Redblackmap.dict,
     typed_annotations : Type.hol_type list,executed : bool ref}
    | IdentityPlan of
      {producer : producer,term_epoch : int,executed : bool ref}
  datatype instance = Instance of
    {producer : producer,typed : P.closed_fact,
     theta : (Type.hol_type,Type.hol_type) Lib.subst,
     identity_epoch : int option}
  fun active (Producer {graph,scope,epoch,limit,work,...}) =
    ((case work of NONE => () | SOME budget =>
        W.validate_template budget graph scope limit);
     G.validate_scope graph scope;
     if Type.type_epoch () = epoch then () else
       raise ERR "active" "type declaration epoch changed")
  fun original_theorem (p as Producer {original,...}) =
    (active p;P.closed_original original)
  fun type_variables (p as Producer {variables,...}) =
    (active p;Vector.foldr op:: [] variables)
  fun charged (p as Producer {used,...}) = (active p;!used)
  fun spend (p as Producer {limit,used,work,...}) count =
    (active p;
     if count < 0 orelse count > limit - !used then
       raise ERR "admit" "original cumulative type-instance cap exhausted"
     else ((case work of NONE => () | SOME budget => W.spend budget count);
           used := !used + count))
  fun run (Producer {work,...}) action =
    case work of NONE => action () | SOME budget => W.with_step budget action
  fun policy (p as Producer {check_type,...}) ty =
    (active p;check_type ty;active p)

  (* Types are visited BEFORE type_subst/compare/type_vars/matching. The
     declaration ID is retained by the actual Type object, not its text.
     Symbol byte totals are reported, not an invented admission allowance. *)
  fun type_walk spend bytes collect root =
    let
      (* A stack of borrowed spines avoids copying an unadmitted Args
         list. Each child is charged BEFORE its own type inspection. *)
      fun walk [] = ()
        | walk ([] :: rest) = walk rest
        | walk ((ty :: pending) :: rest) =
            (spend 1;
             if Type.is_vartype ty then
               (bytes := !bytes + String.size (Type.dest_vartype ty);
                collect ty;walk (pending :: rest))
             else let
               val {Thy,Tyop,Args} = Type.dest_thy_typeid ty
               val _ = bytes := !bytes + String.size Thy
               (* Tyop is the original kernel declaration identity. *)
               val _ = ignore Tyop
             in walk (Args :: pending :: rest) end)
    in walk [[root]] end

  fun begin_internal work graph scope {original,template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val epoch = Type.type_epoch ()
      val _ = P.validate_closed_fact graph scope template_limit original
      val node = P.closed_node original
      val _ = List.app (fn kind =>
        case G.unfolded_nodes graph kind template_limit node of
          SOME n => if n <= template_limit then () else
            raise ERR "begin_original" "original graph metric exceeds cap"
        | NONE => raise ERR "begin_original" "unknown original graph metric")
        [G.RawNodes,G.BinderInclusiveNodes]
      val theorem = P.closed_original original
      val term = Thm.concl theorem
      (* Measure ACTUAL original input, not the canonical graph spelling.
         The existing counter has its own small binder/count-body envelope;
         it is not a theorem-free whole early-admission claim. *)
      val raw = case I.bounded_raw_size template_limit term of SOME n => n
        | NONE => raise ERR "begin_original" "actual original raw size"
      val binder = case I.bounded_binder_size template_limit term of
          SOME n => n
        | NONE => raise ERR "begin_original" "actual original binder size"
      val used = ref 0
      val bytes = ref 0
      fun charge n =
        if n < 0 orelse n > template_limit - !used then
          raise ERR "begin_original" "original annotation/name cap exhausted"
        else ((case work of NONE => () | SOME budget => W.spend budget n);
              used := !used + n)
      fun guard () =
        (G.validate_scope graph scope;
         if Type.type_epoch () = epoch then () else
           raise ERR "begin_original" "type epoch changed")
      val annotations = ref ([] : Type.hol_type list)
      val variables = ref ([] : Type.hol_type list)
      fun variable ty =
        let fun exists [] = false
              | exists (v :: rest) =
                  (charge 1; (* Each admitted atomic variable comparison. *)
                   Type.compare (v,ty) = EQUAL orelse exists rest)
        in if exists (!variables) then () else variables := ty :: !variables
        end
      fun annotation ty =
        (type_walk charge bytes variable ty;
         annotations := ty :: !annotations)
      (* Experimental inst1 can rename only when a matching new variable
         key has a DIFFERENT original type. ONE actual original type per
         spelling excludes that branch, including repeated same-type
         binder names in fixed BAG laws. Different-type collisions remain
         an explicitly unsupported pre-kernel refusal. *)
      val spellings = ref ([] : (string * Type.hol_type) list)
      fun spelling (name,ty) =
        let fun find [] = NONE
              | find ((held,old) :: rest) =
                  (charge 1; (* Text work has no symbol-byte grant. *)
                   if held = name then SOME old else find rest)
        in case find (!spellings) of
          NONE => spellings := (name,ty) :: !spellings
        | SOME held =>
            (type_walk charge bytes (fn _ => ()) held;
             type_walk charge bytes (fn _ => ()) ty;
             if Type.compare (held,ty) = EQUAL then () else
               raise ERR "begin_original" "ambiguous actual variable spelling")
        end
      fun walk current =
        let val _ = guard () val _ = charge 1
            val _ = annotation (Term.type_of current)
        in
          if Term.is_comb current then
            let val (f,x) = Term.dest_comb current in
              walk f;walk x end
          else if Term.is_abs current then
            let val (v,body) = Term.dest_abs current
                val (name,ty) = Term.dest_var v
                val _ = annotation ty
                val _ = bytes := !bytes + String.size name
                val _ = spelling (name,ty)
            in walk body end
          else if Term.is_var current then
            let val value as (name,_) = Term.dest_var current
                val _ = bytes := !bytes + String.size name
            in spelling value end
          else ()
        end
      val _ = walk term
      val _ = guard ()
    in Producer {graph = graph,scope = scope,original = original,
      limit = template_limit,used = used,bytes = bytes,epoch = epoch,
      annotations = List.rev (!annotations),
      variables = Vector.fromList (List.rev (!variables)),
      raw = raw,binder = binder,check_type = check_type,work = work} end

  (* Existing APIs retain their old per-producer cap and no-op hook. *)
  fun begin_original graph scope args = begin_internal NONE graph scope args
  fun begin_original_with_work graph scope
      {original,template_limit,check_type,work} =
    W.with_step work (fn () =>
      (W.validate_template work graph scope template_limit;
       begin_internal (SOME work) graph scope
         {original = original,template_limit = template_limit,
          check_type = check_type}))

  fun prepare_internal (p as Producer
      {graph,scope,limit,variables,annotations,bytes,raw,binder,...})
      {bindings} =
    let
      val _ = active p
      val seen = ref ([] : int list)
      fun seen_index _ [] = false
        | seen_index index (old :: rest) =
            (spend p 1;old = index orelse seen_index index rest)
      fun reserve_product factors =
        let val Producer {used,...} = p
            val remaining = limit - !used
            fun product [] value = value
              | product (factor :: rest) value =
                  if factor = 0 then 0
                  else if factor < 0 orelse value > remaining div factor
                  then raise ERR "prepare" "comparison work exceeds cap"
                  else product rest (value * factor)
        in spend p (product factors 1) end
      fun rows [] = []
        | rows ((index,residue) :: rest) =
            let
              val _ = spend p 1 (* BEFORE ordinal/table lookup *)
              val _ = if index >= 0 andalso index < Vector.length variables
                  andalso not (seen_index index (!seen))
                then () else raise ERR "prepare" "invalid/duplicate domain"
              val _ = type_walk (spend p) bytes (fn _ => ()) residue
              val _ = seen := index :: !seen
              val redex = Vector.sub (variables,index)
            in {redex = redex,residue = residue} :: rows rest end
      val theta = rows bindings
      (* Repeated annotations count separately. A returned residue is walked
         literally, never recursively substituted: self ranges/swaps are
         valid finite simultaneous instances, not unification cycles. *)
      fun lookup _ [] = NONE
        | lookup ty ({redex,residue} :: rest) =
            (* One forecast search plus TWO reserved kernel searches:
               Type.type_subst over annotations and actual INST_TYPE.
               Domain variables are admitted atomic types; text-byte work
               remains an explicit prerequisite outside this node counter. *)
            (spend p 3;
             if Type.compare (redex,ty) = EQUAL then SOME residue
             else lookup ty rest)
      fun output ty =
        let val _ = spend p 5
        in if Type.is_vartype ty then
          (case lookup ty theta of
             NONE =>
               (bytes := !bytes + String.size (Type.dest_vartype ty);1)
           | SOME residue =>
               let val count = ref 0
                   fun charge n = (spend p (5*n);count := !count+n)
                   val _ = type_walk charge bytes (fn _ => ()) residue
               in !count end)
        else let val {Thy,Args,...} = Type.dest_thy_typeid ty
                 val _ = bytes := !bytes + String.size Thy
                 fun children [] size = size
                   | children (child :: rest) size =
                       children rest (size + output child)
             in children Args 1 end
        end
      val sizes = List.map output annotations
      val max_size = List.foldl Int.max 0 sizes
      (* Reserve typed graph and P-recording incidences BEFORE proof work.
         Type instantiation preserves syntax shape under this no-rename
         envelope; binder variable slots are included independently. *)
      val _ = spend p raw
      val _ = spend p binder
      val _ = spend p 1
      val output_types = List.map (Type.type_subst theta) annotations
      (* Table construction occurs before proof and charges EVERY actual
         comparison plus both already admitted type trees. No trusted
         equality or uncharged full-list membership is used afterward. *)
      fun compare (left,right) =
        (spend p 1;
         type_walk (spend p) bytes (fn _ => ()) left;
         type_walk (spend p) bytes (fn _ => ()) right;
         Type.compare (left,right))
      val charged_table = List.foldl (fn (ty,table) =>
        (spend p 1;Redblackmap.insert (table,ty,())))
        (Redblackmap.mkDict compare) output_types
      val items = Redblackmap.numItems charged_table
      fun ceil_log n =
        if n <= 1 then 0 else 1 + ceil_log (n div 2 + n mod 2)
      (* Okasaki red-black height <= 2*ceil(log2(items+1)); this slightly
         larger bound avoids overflowing items+1 at the original Int cap.
         Peek performs ONE key comparison per visited node. *)
      val height = if items = 0 then 0 else 2 * (ceil_log items + 1)
      val _ = reserve_product [binder,height]
      val _ = reserve_product [binder,height,max_size]
      val _ = reserve_product [binder,height,max_size]
      (* Copy a known bounded ordered portfolio into a table whose ordinary
         comparator consumes the already retained lookup reservation. *)
      val _ = reserve_product [items,3]
      val expected = Redblackmap.fromOrderedList Type.compare
        (Redblackmap.listItems charged_table)
      val _ = List.app (policy p) (annotations @ output_types)
      val _ = active p
    in Plan {producer = p,theta = theta,expected = expected,
             typed_annotations = output_types,executed = ref false} end

  fun prepare p args = run p (fn () => prepare_internal p args)

  (* Empty-variable identity has no substitution, new type table,
     INST_TYPE, import or P recording. The original repeated portfolio is
     still paid BEFORE any policy call; no cumulative counter is reset. *)
  fun identity_active (p as Producer
      {graph,scope,original,limit,work,...}) epoch =
    (active p;
     if Term.term_epoch () = epoch then () else
       raise ERR "identity" "term declaration epoch changed";
     P.validate_closed_fact graph scope limit original;
     active p)
    handle primary =>
      ((case work of NONE => () | SOME budget => W.close budget);
       raise primary)

  fun prepare_identity_internal (p as Producer
      {original,variables,annotations,bytes,check_type,...}) =
    let
      val _ = active p
      val _ = if Vector.length variables = 0 then () else
        raise ERR "prepare_identity" "original law has type variables"
      val epoch = Term.term_epoch ()
      fun guard () = identity_active p epoch
      (* Borrow the original list. Pay each retained policy-list incidence
         and actual type node BEFORE inspecting it or invoking policies. *)
      fun quote [] = ()
        | quote (ty :: rest) =
            (guard ();spend p 1;
             type_walk (spend p) bytes (fn _ => ()) ty;
             guard ();quote rest)
      val _ = quote annotations
      val _ = spend p 2 (* Plan and retained identity-result records. *)
      val _ = if Term.uptodate_term (Thm.concl (P.closed_original original))
        then () else raise ERR "prepare_identity" "retired original law"
      val _ = guard ()
      fun checked ty = (guard ();check_type ty;guard ())
      val _ = List.app checked annotations
      val _ = guard ()
    in IdentityPlan {producer = p,term_epoch = epoch,
                     executed = ref false} end

  fun prepare_identity p = run p (fn () => prepare_identity_internal p)

  fun planned_syntax (Plan {producer = p as Producer {raw,binder,...},
      typed_annotations,...}) =
    (active p;{raw = raw,binder = binder,
      typed_annotations = typed_annotations})
    | planned_syntax (IdentityPlan {producer = p as Producer
        {raw,binder,annotations,...},term_epoch,...}) =
        (identity_active p term_epoch;
         {raw = raw,binder = binder,typed_annotations = annotations})

  fun execute_internal (Plan {producer = p as Producer
      {graph,scope,original,limit,...},theta,expected,executed,...}) =
    let
      val _ = active p
      val _ = if !executed then raise ERR "execute" "instance plan consumed"
        else executed := true
      val theorem = Thm.INST_TYPE theta (P.closed_original original)
      val _ = active p
      (* Retain the whole genuine source bridge, including distinct raw
         occurrences of an alpha-shared binder. Do not discard child bridges.
           *)
      val imported = G.import graph scope limit (Thm.concl theorem)
      val _ = active p
      val opened = G.record_opened_view graph scope limit (#node imported)
      val _ = active p
      val _ = G.validate_opened_view graph scope (#node imported) opened
      val node = #node opened
      val _ = List.app (fn kind =>
        case G.unfolded_nodes graph kind limit node of
          SOME n => if n <= limit then () else
            raise ERR "execute" "typed result metric exceeds original cap"
        | NONE => raise ERR "execute" "typed result remains opaque")
        [G.RawNodes,G.BinderInclusiveNodes]
      fun admitted ty =
        (active p;
         case Redblackmap.peek (expected,ty) of SOME () => ()
         | NONE => raise ERR "execute" "unplanned typed annotation")
      val typed = P.record_closed_from_import graph scope
        {node = node,theorem = theorem,template_limit = limit,
         check_type = admitted}
      val _ = active p
    in Instance {producer = p,typed = typed,theta = theta,
                 identity_epoch = NONE} end

  fun execute (plan as Plan {producer,...}) =
    run producer (fn () => execute_internal plan)
    | execute (IdentityPlan {producer = p as Producer {original,...},
                            term_epoch,executed}) =
        run p (fn () =>
          let val _ = identity_active p term_epoch
              val _ = if !executed then
                raise ERR "execute" "instance plan consumed"
                else executed := true
              val result = Instance {producer = p,typed = original,
                theta = [],identity_epoch = SOME term_epoch}
              val _ = identity_active p term_epoch
          in result end)

  fun instance_active (Instance {producer,identity_epoch,...}) =
    case identity_epoch of NONE => active producer
      | SOME epoch => identity_active producer epoch

  fun selected_original (value as Instance
      {producer = Producer {original,...},...}) =
    (instance_active value;P.closed_original original)
  fun typed_theorem (value as Instance {typed,...}) =
    (instance_active value;P.closed_original typed)
  fun typed_plan (value as Instance {typed,...}) =
    (instance_active value;typed)
  fun substitution (value as Instance {theta,...}) =
    (instance_active value;theta)
  fun validate_instance graph scope limit
      (value as Instance {producer = p as Producer
        {graph = owner,scope = frame,limit = held,...},typed,...}) =
    (instance_active value;
     if Portable.pointer_eq (graph,owner) andalso scope = frame andalso
         limit = held then () else
       raise ERR "validate_instance" "different graph/scope/original cap";
     P.validate_closed_fact graph scope limit typed)
  fun validate_instance_with_work graph scope cap budget
      (instance as Instance {producer = Producer {work,...},...}) =
    ((W.validate_template budget graph scope cap;
      (case work of SOME held =>
         if Portable.pointer_eq (held,budget) then ()
         else raise ERR "validate_instance_with_work" "different work owner"
       | NONE => raise ERR "validate_instance_with_work" "unhooked instance");
      validate_instance graph scope cap instance;
      W.validate_template budget graph scope cap)
     handle primary => (W.close budget;raise primary))
  fun specialize_internal (value as Instance {producer = p as Producer
      {graph,scope,limit,...},typed,...}) {operands} =
    let
      fun admit [] = ()
        | admit (node :: rest) =
            let val _ = instance_active value val _ = spend p 1
                val _ = List.app (fn kind =>
                  case G.unfolded_nodes graph kind limit node of
                    SOME n => if n <= limit then spend p n else
                      raise ERR "specialize" "operand exceeds original cap"
                  | NONE => raise ERR "specialize" "unknown operand metric")
                  [G.RawNodes,G.BinderInclusiveNodes]
                val ty = G.type_of graph node
                val Producer {bytes,...} = p
                val _ = type_walk (spend p) bytes (fn _ => ()) ty
            in admit rest end
      val _ = admit operands
      val _ = instance_active value
      val answer = P.specialize_closed typed
        {operands = operands,check_type = fn ty =>
          (instance_active value;policy p ty;instance_active value)}
      val _ = instance_active value
    in answer end
  fun specialize (instance as Instance {producer,...}) args =
    run producer (fn () => specialize_internal instance args)
  structure RP=SmtReplayResourcePolicy
  structure NC=SmtReplayNativeContract
  datatype policy_producer = PolicyProducer of
    {graph : G.graph,scope : G.scope,original : P.closed_fact,
     limit : int,used : int ref,bytes : int ref,epoch : int,
     annotations : Type.hol_type list,variables : Type.hol_type vector,
     raw : int,binder : int,check_type : Type.hol_type -> unit,
     work : W.portfolio option,native_contract:NC.contract,
     model_limit:int,policy_limit:RP.limit}
  datatype policy_plan = PolicyPlan of
    {policy_producer : policy_producer,theta : (Type.hol_type,Type.hol_type)
      Lib.subst,
     expected : (Type.hol_type,unit) Redblackmap.dict,
     typed_annotations : Type.hol_type list,executed : bool ref}
    | PolicyIdentityPlan of
      {policy_producer : policy_producer,term_epoch : int,executed : bool ref}
  datatype policy_instance = PolicyInstance of
    {policy_producer : policy_producer,typed : P.closed_fact,
     theta : (Type.hol_type,Type.hol_type) Lib.subst,
     identity_epoch : int option}
  fun active (PolicyProducer
    {graph,scope,epoch,limit,work,native_contract,policy_limit,...}) =
    ((case work of NONE => () | SOME budget =>
        (NC.validate_for budget native_contract;
         W.validate_template_policy budget graph scope policy_limit));
     G.validate_scope graph scope;
     if Type.type_epoch () = epoch then () else
       raise ERR "active" "type declaration epoch changed")
  fun type_variables_with_policy (p as PolicyProducer {variables,...}) =
    (active p;Vector.foldr op:: [] variables)
  fun charged_with_policy (p as PolicyProducer {used,...}) = (active p;!used)
  fun spend (p as PolicyProducer {limit,used,work,model_limit,...}) count =
    (active p;
     if count < 0 orelse count > model_limit - !used then
       raise ERR "admit"
         "original cumulative type-policy_instance cap exhausted"
     else ((case work of NONE => () | SOME budget => W.spend_policy budget
       (IntInf.fromInt count));
           used := !used + count))
  fun run (PolicyProducer {work,...}) action =
    case work of NONE => action () | SOME budget => W.with_step budget action
  fun policy (p as PolicyProducer {check_type,...}) ty =
    (active p;check_type ty;active p)

  (* Types are visited BEFORE type_subst/compare/type_vars/matching. The
     declaration ID is retained by the actual Type object, not its text.
     Symbol byte totals are reported, not an invented admission allowance. *)
  fun type_walk spend bytes collect root =
    let
      (* A stack of borrowed spines avoids copying an unadmitted Args
         list. Each child is charged_with_policy BEFORE its own type
           inspection. *)
      fun walk [] = ()
        | walk ([] :: rest) = walk rest
        | walk ((ty :: pending) :: rest) =
            (spend 1;
             if Type.is_vartype ty then
               (bytes := !bytes + String.size (Type.dest_vartype ty);
                collect ty;walk (pending :: rest))
             else let
               val {Thy,Tyop,Args} = Type.dest_thy_typeid ty
               val _ = bytes := !bytes + String.size Thy
               (* Tyop is the original kernel declaration identity. *)
               val _ = ignore Tyop
             in walk (Args :: pending :: rest) end)
    in walk [[root]] end

  fun begin_internal work native_contract graph scope
      {original,template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val native=case work of SOME budget=>NC.for_work budget native_contract
        | NONE=>raise ERR "begin_policy" "unhooked policy producer"
      val policy_limit=case work of SOME budget=>
          #template_limit (W.semantic_policy budget)
        | NONE=>raise ERR "begin_policy" "unhooked policy producer"
      val model_limit=Int.min (template_limit,#type_work_limit native)
      val epoch = Type.type_epoch ()
      val _ = P.validate_closed_fact_with_policy graph scope policy_limit
        original
      val node = P.closed_node original
      val _ = List.app (fn kind =>
        case G.unfolded_nodes graph kind template_limit node of
          SOME n => if n <= template_limit then () else
            raise ERR "begin_original" "original graph metric exceeds cap"
        | NONE => raise ERR "begin_original" "unknown original graph metric")
        [G.RawNodes,G.BinderInclusiveNodes]
      val theorem = P.closed_original original
      val term = Thm.concl theorem
      (* Measure ACTUAL original input, not the canonical graph spelling.
         The existing counter has its own small binder/count-body envelope;
         it is not a theorem-free whole early-admission claim. *)
      val raw = case I.bounded_raw_size template_limit term of SOME n => n
        | NONE => raise ERR "begin_original" "actual original raw size"
      val binder = case I.bounded_binder_size template_limit term of
          SOME n => n
        | NONE => raise ERR "begin_original" "actual original binder size"
      val used = ref 0
      val bytes = ref 0
      fun charge n =
        if n < 0 orelse n > model_limit - !used then
          raise ERR "begin_original" "original annotation/name cap exhausted"
        else ((case work of NONE => () | SOME budget => W.spend_policy budget
          (IntInf.fromInt n));
              used := !used + n)
      fun guard () =
        ((case work of SOME budget=>NC.validate_for budget native_contract
          | NONE=>raise ERR "guard" "unhooked policy producer");
         G.validate_scope graph scope;
         if Type.type_epoch () = epoch then () else
           raise ERR "begin_original" "type epoch changed")
      val annotations = ref ([] : Type.hol_type list)
      val variables = ref ([] : Type.hol_type list)
      fun variable ty =
        let fun exists [] = false
              | exists (v :: rest) =
                  (charge 1; (* Each admitted atomic variable comparison. *)
                   Type.compare (v,ty) = EQUAL orelse exists rest)
        in if exists (!variables) then () else variables := ty :: !variables
        end
      fun annotation ty =
        (type_walk charge bytes variable ty;
         annotations := ty :: !annotations)
      (* Experimental inst1 can rename only when a matching new variable
         key has a DIFFERENT original type. ONE actual original type per
         spelling excludes that branch, including repeated same-type
         binder names in fixed BAG laws. Different-type collisions remain
         an explicitly unsupported pre-kernel refusal. *)
      val spellings = ref ([] : (string * Type.hol_type) list)
      fun spelling (name,ty) =
        let fun find [] = NONE
              | find ((held,old) :: rest) =
                  (charge 1; (* Text work has no symbol-byte grant. *)
                   if held = name then SOME old else find rest)
        in case find (!spellings) of
          NONE => spellings := (name,ty) :: !spellings
        | SOME held =>
            (type_walk charge bytes (fn _ => ()) held;
             type_walk charge bytes (fn _ => ()) ty;
             if Type.compare (held,ty) = EQUAL then () else
               raise ERR "begin_original" "ambiguous actual variable spelling")
        end
      fun walk current =
        let val _ = guard () val _ = charge 1
            val _ = annotation (Term.type_of current)
        in
          if Term.is_comb current then
            let val (f,x) = Term.dest_comb current in
              walk f;walk x end
          else if Term.is_abs current then
            let val (v,body) = Term.dest_abs current
                val (name,ty) = Term.dest_var v
                val _ = annotation ty
                val _ = bytes := !bytes + String.size name
                val _ = spelling (name,ty)
            in walk body end
          else if Term.is_var current then
            let val value as (name,_) = Term.dest_var current
                val _ = bytes := !bytes + String.size name
            in spelling value end
          else ()
        end
      val _ = walk term
      val _ = guard ()
    in PolicyProducer {graph = graph,scope = scope,original = original,
      limit = template_limit,used = used,bytes = bytes,epoch = epoch,
      annotations = List.rev (!annotations),
      variables = Vector.fromList (List.rev (!variables)),
      raw = raw,binder = binder,check_type = check_type,work = work,
      native_contract=native_contract,model_limit=model_limit,
      policy_limit=policy_limit} end

  (* Actual finite native contract, never an int metadata projection. *)
  fun begin_original_with_policy graph scope
      {original,check_type,work,native_contract} =
    ((NC.validate_for work native_contract;
      W.with_step work (fn()=>
        let val native=NC.for_work work native_contract
            val cap= #template_limit (#semantic_limits native)
            val _=W.validate_template_policy work graph scope
              (#template_limit (W.semantic_policy work))
        in begin_internal (SOME work) native_contract graph scope
          {original=original,template_limit=cap,check_type=check_type} end))
     handle primary=>(W.close work;raise primary))

  fun prepare_internal (p as PolicyProducer
    {graph,scope,limit,model_limit,variables,annotations,bytes,raw,binder,...})
      {bindings} =
    let
      val _ = active p
      val seen = ref ([] : int list)
      fun seen_index _ [] = false
        | seen_index index (old :: rest) =
            (spend p 1;old = index orelse seen_index index rest)
      fun reserve_product factors =
        let val PolicyProducer {used,...} = p
            val remaining = model_limit - !used
            fun product [] value = value
              | product (factor :: rest) value =
                  if factor = 0 then 0
                  else if factor < 0 orelse value > remaining div factor
                  then raise ERR "prepare_with_policy"
                    "comparison work exceeds cap"
                  else product rest (value * factor)
        in spend p (product factors 1) end
      fun rows [] = []
        | rows ((index,residue) :: rest) =
            let
              val _ = spend p 1 (* BEFORE ordinal/table lookup *)
              val _ = if index >= 0 andalso index < Vector.length variables
                  andalso not (seen_index index (!seen))
                then () else raise ERR "prepare_with_policy"
                  "invalid/duplicate domain"
              val _ = type_walk (spend p) bytes (fn _ => ()) residue
              val _ = seen := index :: !seen
              val redex = Vector.sub (variables,index)
            in {redex = redex,residue = residue} :: rows rest end
      val theta = rows bindings
      (* Repeated annotations count separately. A returned residue is walked
         literally, never recursively substituted: self ranges/swaps are
         valid finite simultaneous instances, not unification cycles. *)
      fun lookup _ [] = NONE
        | lookup ty ({redex,residue} :: rest) =
            (* One forecast search plus TWO reserved kernel searches:
               Type.type_subst over annotations and actual INST_TYPE.
               Domain variables are admitted atomic types; text-byte work
               remains an explicit prerequisite outside this node counter. *)
            (spend p 3;
             if Type.compare (redex,ty) = EQUAL then SOME residue
             else lookup ty rest)
      fun output ty =
        let val _ = spend p 5
        in if Type.is_vartype ty then
          (case lookup ty theta of
             NONE =>
               (bytes := !bytes + String.size (Type.dest_vartype ty);1)
           | SOME residue =>
               let val count = ref 0
                   fun charge n = (spend p (5*n);count := !count+n)
                   val _ = type_walk charge bytes (fn _ => ()) residue
               in !count end)
        else let val {Thy,Args,...} = Type.dest_thy_typeid ty
                 val _ = bytes := !bytes + String.size Thy
                 fun children [] size = size
                   | children (child :: rest) size =
                       children rest (size + output child)
             in children Args 1 end
        end
      val sizes = List.map output annotations
      val max_size = List.foldl Int.max 0 sizes
      (* Reserve typed graph and P-recording incidences BEFORE proof work.
         Type instantiation preserves syntax shape under this no-rename
         envelope; binder variable slots are included independently. *)
      val _ = spend p raw
      val _ = spend p binder
      val _ = spend p 1
      val output_types = List.map (Type.type_subst theta) annotations
      (* Table construction occurs before proof and charges EVERY actual
         comparison plus both already admitted type trees. No trusted
         equality or uncharged full-list membership is used afterward. *)
      fun compare (left,right) =
        (spend p 1;
         type_walk (spend p) bytes (fn _ => ()) left;
         type_walk (spend p) bytes (fn _ => ()) right;
         Type.compare (left,right))
      val charged_table = List.foldl (fn (ty,table) =>
        (spend p 1;Redblackmap.insert (table,ty,())))
        (Redblackmap.mkDict compare) output_types
      val items = Redblackmap.numItems charged_table
      fun ceil_log n =
        if n <= 1 then 0 else 1 + ceil_log (n div 2 + n mod 2)
      (* Okasaki red-black height <= 2*ceil(log2(items+1)); this slightly
         larger bound avoids overflowing items+1 at the original Int cap.
         Peek performs ONE key comparison per visited node. *)
      val height = if items = 0 then 0 else 2 * (ceil_log items + 1)
      val _ = reserve_product [binder,height]
      val _ = reserve_product [binder,height,max_size]
      val _ = reserve_product [binder,height,max_size]
      (* Copy a known bounded ordered portfolio into a table whose ordinary
         comparator consumes the already retained lookup reservation. *)
      val _ = reserve_product [items,3]
      val expected = Redblackmap.fromOrderedList Type.compare
        (Redblackmap.listItems charged_table)
      val _ = List.app (policy p) (annotations @ output_types)
      val _ = active p
    in PolicyPlan {policy_producer = p,theta = theta,expected = expected,
             typed_annotations = output_types,executed = ref false} end

  fun prepare_with_policy p args = run p (fn () => prepare_internal p args)

  (* Empty-variable identity has no substitution_with_policy, new type table,
     INST_TYPE, import or P recording. The original repeated portfolio is
     still paid BEFORE any policy call; no cumulative counter is reset. *)
  fun identity_active (p as PolicyProducer
      {graph,scope,original,limit,work,policy_limit,...}) epoch =
    (active p;
     if Term.term_epoch () = epoch then () else
       raise ERR "identity" "term declaration epoch changed";
     P.validate_closed_fact_with_policy graph scope policy_limit original;
     active p)
    handle primary =>
      ((case work of NONE => () | SOME budget => W.close budget);
       raise primary)

  fun prepare_identity_internal (p as PolicyProducer
      {original,variables,annotations,bytes,check_type,...}) =
    let
      val _ = active p
      val _ = if Vector.length variables = 0 then () else
        raise ERR "prepare_identity_with_policy"
          "original law has type variables"
      val epoch = Term.term_epoch ()
      fun guard () = identity_active p epoch
      (* Borrow the original list. Pay each retained policy-list incidence
         and actual type node BEFORE inspecting it or invoking policies. *)
      fun quote [] = ()
        | quote (ty :: rest) =
            (guard ();spend p 1;
             type_walk (spend p) bytes (fn _ => ()) ty;
             guard ();quote rest)
      val _ = quote annotations
      val _ = spend p 2 (* PolicyPlan and retained identity-result records. *)
      val _ = if Term.uptodate_term (Thm.concl (P.closed_original original))
        then () else raise ERR "prepare_identity_with_policy"
          "retired original law"
      val _ = guard ()
      fun checked ty = (guard ();check_type ty;guard ())
      val _ = List.app checked annotations
      val _ = guard ()
    in PolicyIdentityPlan {policy_producer = p,term_epoch = epoch,
                     executed = ref false} end

  fun prepare_identity_with_policy p = run p (fn () =>
    prepare_identity_internal p)

  fun planned_syntax_with_policy (PolicyPlan {policy_producer = p as
    PolicyProducer {raw,binder,...},
      typed_annotations,...}) =
    (active p;{raw = raw,binder = binder,
      typed_annotations = typed_annotations})
    | planned_syntax_with_policy (PolicyIdentityPlan {policy_producer = p as
      PolicyProducer
        {raw,binder,annotations,...},term_epoch,...}) =
        (identity_active p term_epoch;
         {raw = raw,binder = binder,typed_annotations = annotations})

  fun execute_internal (PolicyPlan {policy_producer = p as PolicyProducer
      {graph,scope,original,limit,policy_limit,native_contract,work,...},
       theta,expected,executed,...}) =
    let
      val _ = active p
      val _ = if !executed then raise ERR "execute_with_policy"
        "policy_instance policy_plan consumed"
        else executed := true
      val theorem = Thm.INST_TYPE theta (P.closed_original original)
      val _ = active p
      (* Retain the whole genuine source bridge, including distinct raw
         occurrences of an alpha-shared binder. Do not discard child bridges.
           *)
      val imported = G.import_with_policy graph scope
        (RP.AtMost (IntInf.fromInt (#import_limit
          (case work of SOME budget=>NC.for_work budget native_contract
           | NONE=>raise ERR "execute_policy" "unhooked policy instance"))))
        (Thm.concl theorem)
      val _ = active p
      val opened = G.record_opened_view_with_policy graph scope
        (RP.AtMost (IntInf.fromInt limit)) (#node imported)
      val _ = active p
      val _ = G.validate_opened_view graph scope (#node imported) opened
      val node = #node opened
      val _ = List.app (fn kind =>
        case G.unfolded_nodes graph kind limit node of
          SOME n => if n <= limit then () else
            raise ERR "execute_with_policy"
              "typed result metric exceeds original cap"
        | NONE => raise ERR "execute_with_policy"
          "typed result remains opaque")
        [G.RawNodes,G.BinderInclusiveNodes]
      fun admitted ty =
        (active p;
         case Redblackmap.peek (expected,ty) of SOME () => ()
         | NONE => raise ERR "execute_with_policy"
           "unplanned typed annotation")
      val typed = P.record_closed_from_import_with_policy graph scope
        {node = node,theorem = theorem,template_limit = policy_limit,
         check_type = admitted}
      val _ = active p
    in PolicyInstance {policy_producer = p,typed = typed,theta = theta,
                 identity_epoch = NONE} end

  fun execute_with_policy (policy_plan as PolicyPlan {policy_producer,...}) =
    run policy_producer (fn () => execute_internal policy_plan)
    | execute_with_policy (PolicyIdentityPlan {policy_producer = p as
      PolicyProducer {original,...},
                            term_epoch,executed}) =
        run p (fn () =>
          let val _ = identity_active p term_epoch
              val _ = if !executed then
                raise ERR "execute_with_policy"
                  "policy_instance policy_plan consumed"
                else executed := true
              val result = PolicyInstance {policy_producer = p,typed =
                original,
                theta = [],identity_epoch = SOME term_epoch}
              val _ = identity_active p term_epoch
          in result end)

  fun instance_active (PolicyInstance {policy_producer,identity_epoch,...}) =
    case identity_epoch of NONE => active policy_producer
      | SOME epoch => identity_active policy_producer epoch

  fun typed_theorem_with_policy (value as PolicyInstance {typed,...}) =
    (instance_active value;P.closed_original typed)
  fun typed_plan_with_policy (value as PolicyInstance {typed,...}) =
    (instance_active value;typed)
  fun substitution_with_policy (value as PolicyInstance {theta,...}) =
    (instance_active value;theta)
  fun validate_instance_with_policy_for {graph,scope,work=expected}
      (held as PolicyInstance {policy_producer=PolicyProducer {work,...},...})
        =
    ((case work of SOME actual=>
         if Portable.pointer_eq (expected,actual) then () else
           raise ERR "validate_policy_instance" "different original Work"
       | NONE=>raise ERR "validate_policy_instance" "unhooked policy instance";
      let val PolicyInstance {policy_producer=p as PolicyProducer
            {graph=owner,scope=frame,policy_limit,...},typed,...}=held
      in if Portable.pointer_eq (graph,owner) andalso scope=frame then ()
          else raise ERR "validate_policy_instance" "different graph/frame";
        instance_active held;
        P.validate_closed_fact_with_policy graph scope policy_limit typed;
        active p end)
     handle primary=>(W.close expected;raise primary))

end
