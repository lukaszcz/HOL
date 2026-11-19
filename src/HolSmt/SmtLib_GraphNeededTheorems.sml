(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphNeededTheorems :> SmtLib_GraphNeededTheorems =
struct
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure W = SmtReplayInvocationWork
  structure I = SmtReplayImport
  structure P = SmtReplayProof
  structure F = SmtLib_GraphSourcePortfolio
  structure GP = SmtLib_GraphPreprocess
  structure D = SmtReplayOwnedTransport
  structure X = SmtLib_GraphSelectedAuxiliary
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphNeededTheorems"
  type request = {head : Term.term,ordinal : int,original : Thm.thm}
  (* Receipts shared by the int and policy collectors. The owner type 'o
     and the owner's own receipt part 'x (what only that owner exposes:
     the int owner's root stock heads, nothing for the policy owner) are
     what differ. *)
  datatype 'o norm = Normalized of
    {owner : 'o,original : Thm.thm,
     kept : (Thm.thm * P.closed_fact) option,guard : unit -> unit,
     proof_revision : IntInf.int option ref}
  datatype ('o,'x) pend = Pending of
    {owner : 'o,originals : Thm.thm list,own : 'x,
     requests : request list,
     selections : {selection : SmtLib_GraphNumericStock.selection,
                   ordinal : int} list,
     resumed : bool ref,
     continuation : 'o norm list -> ('o,'x) outcome}
  and ('o,'x) outcome = Done of GP.validation | Need of ('o,'x) pend

  (* ---- Collector pieces shared by both owners. A kit is the owner's
     retirement check and its raw Work charge, as for normalize_with;
     spend (check, charge, check) and its one-unit form spend1 are
     derived from it once. The walkers, select_with (Source/auxiliary
     selection), finish_with and fixed_point are shared. Left to each
     owner are the operations they are instantiated with: the atom
     walk, the Type walk, the stock selector, the fixed-law
     disposition, the next-roots step, the finish preparation and the
     owner's receipt part, plus the collect preamble and the result
     lift. ---- *)
  type kit = {active : unit -> unit,charge : IntInf.int -> unit}
  fun spend ({active,charge} : kit) n = (active ();charge n;active ())
  fun spend1 k () = spend k 1
  fun guarded_by ({active,...} : kit) action =
    (active ();let val value = action () in active ();value end)
  fun terms_of (k : kit) th = (spend1 k ();Thm.concl th :: Thm.hyp th)
  fun compare_terms (k : kit) (a,b) =
    (spend1 k ();guarded_by k (fn () => Term.compare (a,b)))
  fun compare_thms k (a,b) =
    List.collate (compare_terms k) (terms_of k a,terms_of k b)
  fun empty_terms k () = HOLset.empty (compare_terms k)
  fun empty_thms k () = HOLset.empty (compare_thms k)

  fun select_with (k : kit) {selections,type_walk,select} head =
    let
      val _ = type_walk (Term.type_of head)
      fun find [] = NONE
        | find ((old,selection)::rest) =
            (spend1 k ();if compare_terms k (head,old)=EQUAL then
               SOME selection else find rest)
      (* Exact typed atomic head, private to THIS original N owner.
         The first genuine selector materializes its laws ONCE. Later
         batches request that SAME retained selection/theorem object;
         Stage's original-law pointer key is not relaxed. *)
      val selection = case find (!selections) of SOME held => held
        | NONE =>
            let val _ = spend1 k ()
                val fresh = guarded_by k (fn () => select head)
                val _ = spend1 k ()
                val _ = selections := (head,fresh) :: !selections
            in fresh end
      val data = guarded_by k (fn () =>
        SmtLib_GraphNumericStock.selection_data selection)
      val _ = if compare_terms k (head,#head data)=EQUAL then () else
        raise ERR "selected" "retained typed stock head changed"
    in selection end

  (* [prepare] attaches the checked laws to the portfolio and validates
     the result; it is the only owner-specific step. *)
  fun finish_with (k : kit) prepare accumulated proofs =
    let
      val laws = HOLset.listItems accumulated
      val _ = List.app (fn _ => spend1 k ()) laws
      fun find th = case List.find
          (fn (original,_) => compare_thms k (th,original) = EQUAL) proofs of
          SOME (_,proof) => proof
        | NONE => raise ERR "finish"
            "normalized law lost its checked proof"
      val checked = List.map find laws
    in Done (prepare checked) end

  (* What the normalization loop does with one wanted original law that no
     request is needed for. *)
  datatype unchanged = Blocked | Dropped | Kept of P.closed_fact

  (* The fixed-point loop over wanted laws. [atoms] finds the stock heads
     of the roots, [selected] selects a head, [unchanged] disposes of a
     law that needs no request, [roots_of_added] gives the next roots from
     the newly added normalized laws and the proofs so far, [finish] ends
     the loop, and [own] makes the owner's own part of a request receipt
     from the stock heads (only when a request is issued). Returns the
     loop, to be started on the initial roots. *)
  fun fixed_point (k : kit) owner
      {atoms,selected,unchanged,roots_of_added,finish,own} =
    let
      val spend1 = spend1 k
      fun guarded action = guarded_by k action
      val empty_thms = empty_thms k
      fun loop [] accumulated proofs = finish accumulated proofs
        | loop roots accumulated proofs =
          let
            val heads = atoms roots
            val occurrences = ref ([] : (request *
              SmtLib_GraphNumericStock.selection) list)
            fun add (head,wanted) =
              let val selection = selected head
                  val laws = #laws (guarded (fn () =>
                    SmtLib_GraphNumericStock.selection_data selection))
                  fun retain [] _ = ()
                    | retain (original :: rest) ordinal =
                        (spend1 ();occurrences :=
                           ({head = head,ordinal = ordinal,
                             original = original},
                            selection) :: !occurrences;
                         retain rest (ordinal+1))
                  val _ = retain laws 0
              in HOLset.addList (wanted,laws) end
            val wanted = HOLset.foldl add (empty_thms ()) heads
            (* Legacy normalizes ALL wanted originals first. Difference is
               taken against the NORMALIZED set only after that whole fold. *)
            val todo = HOLset.listItems wanted
            fun normalize [] next records blocked =
                  if null blocked then
                    let val added = HOLset.difference (next,accumulated)
                        val roots = roots_of_added added records
                    in loop roots (HOLset.union (accumulated,added))
                         records end
                  else
                    let
                      val originals = List.rev blocked
                      val ordered = List.rev (!occurrences)
                      fun origin th = case List.find
                          (fn (({original,...} : request),_) =>
                            (spend1 ();Portable.pointer_eq (th,original)))
                          ordered of
                          SOME pair => pair
                        | NONE => raise ERR "request"
                            "exact selected stock origin missing"
                      val origins = List.map origin originals
                      val requests = List.map #1 origins
                      val selections = List.map
                        (fn (({ordinal,...} : request),selection) =>
                          {ordinal = ordinal,selection = selection}) origins
                      fun continuation completed =
                        let
                          fun find original = case List.find
                              (fn Normalized
                                  {owner = held,original = th,...} =>
                                Portable.pointer_eq (held,owner) andalso
                                Portable.pointer_eq (original,th)) completed of
                              SOME value => value
                            | NONE => raise ERR "resume"
                                "missing exact requested normalization"
                          fun insert [] next records =
                                normalize [] next records []
                            | insert (original :: rest) next records =
                                let val Normalized {kept,guard,...} =
                                      find original
                                    val _ = spend1 ()
                                    val _ = guarded guard
                                in case kept of NONE =>
                                      insert rest next records
                                  | SOME (th,proof) => insert rest
                                      (HOLset.add (next,th))
                                      ((th,proof) :: records) end
                        in insert originals next records end
                    in Need (Pending {owner = owner,originals = originals,
                      requests = requests,selections = selections,
                      own = own heads,resumed = ref false,
                      continuation = continuation}) end
              | normalize (th :: rest) next records blocked =
                  (spend1 ();case unchanged th of
                     Blocked => normalize rest next records (th :: blocked)
                   | Dropped => normalize rest next records blocked
                   | Kept proof => normalize rest (HOLset.add (next,th))
                       ((th,proof) :: records) blocked)
          in normalize todo (empty_thms ()) proofs [] end
    in loop end

  (* The normalization of one selected law. [mk] receives the guarded
     Work operations and returns the operations that differ: the int and
     policy transport/proof calls, the target's size measure, the
     footprint bound and its message. *)
  type norm_ops =
    {describe_conversion : unit -> {source : G.node,target : G.node},
     describe_law : unit -> {original : Thm.thm,endpoint : G.node,
       canonical : Thm.thm,law : P.closed_fact},
     prelude : G.node -> unit -> unit,
     bounded : IntInf.int -> IntInf.int,open_abs : Term.term -> Term.term,
     amount_limit : unit -> IntInf.int,footprint_message : string,
     guard : unit -> unit,
     record_conversion : (Type.hol_type -> unit) -> unit,
     endpoints_theorem : unit -> Thm.thm,
     record : {node : G.node,theorem : Thm.thm,
       check_type : Type.hol_type -> unit} -> P.closed_fact}
  fun normalize_with {name,graph,work,active,charge,backing,check_type,
                      originals,resumed}
      (mk : {live : unit -> unit,spend : IntInf.int -> unit} -> norm_ops) =
    let
      fun live () = (active ();backing ())
      val lk = {active = live,charge = charge}
      fun guarded action = guarded_by lk action
      val spend = spend lk
      fun policy ty = (live ();check_type ty;live ())
      val ops = mk {live = live,spend = spend}
      val (original,target,canonical) = W.with_step work (fn () =>
        let
          val _ = live ()
          val _ = if !resumed then raise ERR name
            "pending already consumed" else ()
          (* Expected fields checked before either foreign receipt
             activates. *)
          val description = #describe_conversion ops ()
          val data = #describe_law ops ()
          val original = #original data
          val _ = if List.exists (fn th =>
              (spend 1;Portable.pointer_eq (th,original))) originals then ()
            else raise ERR name "unrequested selected original"
          val _ = if #source description = #endpoint data then () else
            raise ERR name "different selected-law endpoint"
          val target = #target description
          val held = #prelude ops target
          fun tywalk [] count = count
            | tywalk (ty :: rest) count =
                (spend 1;
                 if Type.is_vartype ty then
                   (spend (IntInf.fromInt
                      (String.size (Type.dest_vartype ty)));
                    tywalk rest (#bounded ops (count+1)))
                 else let val {Thy,Tyop,Args} = Type.dest_thy_type ty
                          val _ = spend (IntInf.fromInt
                            (String.size Thy+String.size Tyop))
                          val _ = List.app (fn _ => spend 1) Args
                      in tywalk (Args @ rest) (#bounded ops (count+1)) end)
          fun walk [] raw inclusive annotations = (raw,inclusive,annotations)
            | walk (current :: rest) raw inclusive annotations =
                (spend 1;
                 let val ty = Term.type_of current
                     val weight = tywalk [ty] (0 : IntInf.int)
                     val next = #bounded ops (annotations+weight)
                 in if Term.is_comb current then
                      let val (f,x) = Term.dest_comb current
                      in walk (f :: x :: rest) (raw+1) (inclusive+1) next end
                    else if Term.is_abs current then
                      let val (domain,_) = Type.dom_rng ty
                          val binder_weight = tywalk [domain] 0
                          val body = guarded (fn () => #open_abs ops current)
                      in walk (body :: rest) (raw+1) (inclusive+2)
                           (#bounded ops (next+binder_weight)) end
                    else walk rest (raw+1) (inclusive+1) next end)
          val (raw,inclusive,ann) = walk [G.representative graph target]
            (0 : IntInf.int) 0 0
          (* New EQ_MP, identity P REFL/EQ_MP and outcome comparison syntax.
             Source/target equality recording is separately debited by D. *)
          val amount = 5*(raw+inclusive+ann)+15
          val _ = if amount <= #amount_limit ops () then spend amount
            else raise ERR name (#footprint_message ops)
          val _ = held ()
        in (original,target,#canonical data) end)
      val _ = #record_conversion ops policy
      val value = W.with_step work (fn () =>
        let
          val _ = #guard ops ()
          val theorem = guarded (fn () =>
            Thm.EQ_MP (#endpoints_theorem ops ()) canonical)
          val _ = if null (Thm.hyp theorem) andalso
              Portable.pointer_eq (Thm.concl theorem,
                G.representative graph target) then () else
            raise ERR name "normalized canonical theorem changed"
          val proof = guarded (fn () => #record ops
            {node = target,theorem = theorem,check_type = policy})
          val term = Thm.concl theorem
          (* Exact legacy successful-conversion/dest_eq outcome. Non-equality
             keeps ORIGINAL, even if a remaining forall body was converted.
             Other exceptions are never swallowed as semantic fallback. *)
          val kept = if boolSyntax.is_eq term then
              let val (a,b) = boolSyntax.dest_eq term
              in if guarded (fn () => Term.aconv a b) then NONE
                 else SOME (theorem,proof) end
            else let val data = #describe_law ops ()
                 in SOME (original,#law data) end
          val _ = #guard ops ()
        in {original = original,kept = kept} end)
    in value end
    handle primary => (W.close work;raise primary)

  datatype owner = Owner of
    {work : W.portfolio,graph : G.graph,scope : G.scope,sources : S.sources,
     portfolio : F.validation,check_type : Type.hol_type -> unit,
     symbols : int,types : int,used : bool ref,
     selections : (Term.term * SmtLib_GraphNumericStock.selection) list ref,
     retained : (unit -> unit) list ref,
     validated : (IntInf.int * (unit -> unit) list) option ref}
  type pending = (owner,Term.term list) pend
  type normalized = owner norm
  datatype result = Complete of GP.validation
    | NeedsNormalization of pending
  fun lift (Done value) = Complete value
    | lift (Need pending) = NeedsNormalization pending

  fun active (Owner {work,graph,scope,sources,symbols,types,retained,
                    validated,...}) =
    ((let
        val _ = W.validate work graph scope sources (W.semantic_limits work)
        val _ = if Term.term_epoch () = symbols andalso
            Type.type_epoch () = types then () else
          raise ERR "active" "constant retirement epoch changed"
        val revision=G.validation_revision graph scope val rows= !retained
        val hit=case !validated of SOME (old,held) =>
            old=revision andalso Portable.pointer_eq (held,rows)
          | NONE => false
      in if hit then () else
        (List.app (fn guard => guard ()) rows;
         W.validate work graph scope sources (W.semantic_limits work);
         if Term.term_epoch ()=symbols andalso
             Type.type_epoch ()=types andalso
             G.validation_revision graph scope=revision andalso
             Portable.pointer_eq (rows,!retained) then
           validated := SOME (revision,rows) else
         raise ERR "active" "validation state changed during backing pass")
      end)
     handle primary => (W.close work;raise primary))
  fun revalidate (owner as Owner {validated,...}) =
    (validated := NONE;active owner)
  fun begin work {portfolio,check_type} =
    let
      val sources = W.original_sources work
      val graph = S.owning_graph sources
      val scope = S.owning_scope sources
      val _ = W.validate work graph scope sources (W.semantic_limits work)
      val _ = F.validate_for graph scope sources portfolio
      val _ = if Portable.pointer_eq
          (sources,F.original_sources portfolio) andalso
          F.template_limit portfolio = #template_limit (W.semantic_limits work)
        then () else raise ERR "begin" "different Source or template owner"
    in Owner {work = work,graph = graph,scope = scope,sources = sources,
      portfolio = portfolio,check_type = check_type,
      symbols = Term.term_epoch (),types = Type.type_epoch (),
      used = ref false,selections = ref [],retained = ref [],
      validated = ref NONE} end
    handle primary => (W.close work;raise primary)

  fun pending_originals (Pending {owner,originals,...}) =
    (active owner;originals)
  fun begin_preprocessed work {preprocessed,check_type} =
    (ignore (W.original_sources work);
     case GP.portfolio_validation preprocessed of
       SOME portfolio => begin work
         {portfolio = portfolio,check_type = check_type}
     | NONE => raise ERR "begin_preprocessed"
         "legacy GP has no original dependency portfolio")
    handle primary => (W.close work;raise primary)
  fun pending_heads (Pending {owner,own,...}) = (active owner;own)
  fun pending_requests (Pending {owner,requests,...}) =
    (active owner;requests)
  fun pending_selections (Pending {owner,selections,...}) =
    (active owner;selections)

  fun collect (owner as Owner
      {work,graph,scope,portfolio,check_type,used,selections,...}) =
    lift (W.with_step work (fn () =>
    let
      val _ = active owner
      val _ = if !used then raise ERR "collect" "collector already consumed"
        else used := true
      val k = {active = fn () => active owner,
               charge = fn n => W.spend work (IntInf.toInt n)}
      val spend = spend k
      fun guarded action = guarded_by k action
      fun policy ty =
        (active owner;check_type ty;active owner)
      val terms = terms_of k
      val empty_terms = empty_terms k
      val empty_thms = empty_thms k

      (* Count-body markers replace bound variables only. Constants, types,
         applications and beta recognition cannot depend on marker names.
         Public count_body's internal kernel/destructor envelope is a stated
         remaining private-cost prerequisite, not priced by one spend. *)
      fun atoms roots =
        let
          (* Exact physical sharing only. No table is allocated for a leaf-only
             query. The first compound uses a fraction of remaining SAME Work;
             its actual slots are charged before allocation. No cache crosses
             a policy or fixed-point pass, and every bucket hit checks pointer
             identity. A routing hint can never certify a missing stock
             head. *)
          val _ = spend 1
          val seen = ref
            (NONE : (Term.term list Array.array) option)
          fun table () = case !seen of SOME cells => cells
            | NONE =>
                let val remaining = W.work_limit work - #charged (W.audit work)
                    val slots = Int.max (1,Int.min (4093,remaining div 16))
                    val _ = spend (IntInf.fromInt slots)
                    val cells = Array.array (slots,[] : Term.term list)
                    val _ = seen := SOME cells
                in cells end
          fun first current =
            let val cells = table ()
                val _ = spend 1
                val bucket = I.pointer_bucket 4 (Array.length cells) current
                fun member [] = false
                  | member (held :: rest) =
                      (spend 1;Portable.pointer_eq (held,current) orelse
                       member rest)
            in if member (Array.sub (cells,bucket)) then false else
              (spend 1;Array.update (cells,bucket,
                 current :: Array.sub (cells,bucket));true) end
          fun walk [] found = found
            | walk (current :: rest) found =
              (spend 1;
               if Term.is_comb current then
                 if not (first current) then walk rest found else
                   let val (f,x) = Term.dest_comb current
                   in walk (f :: x :: rest) found end
               else if Term.is_abs current then
                 if not (first current) then walk rest found else
                   walk (guarded (fn () => I.count_body current) :: rest) found
               else if Term.is_const current then
                 walk rest (HOLset.add (found,current))
               else walk rest found)
        in walk roots (empty_terms ()) end

      (* The selector does no conversion. Full type metadata is visited
         before its declaration/type dispatch. Semantic input/output limits
         are not used as a universal unfolded source cutoff. *)
      fun type_walk ty =
        let fun walk [] = ()
              | walk (current :: rest) =
                  (spend 1;
                   if Type.is_vartype current then walk rest else
                     let val (_,args) = Type.dest_type current
                         val _ = List.app (fn _ => spend 1) args
                     in walk (args @ rest) end)
        in walk [ty] end
      val selected = select_with k {selections = selections,
        type_walk = type_walk,select = SmtLib_GraphNumericStock.select}

      (* A fixed nonnumeric stock recipe, not a supplied normalizer. Every
         NUM transfer rewrite has a num/int/real-typed match position. This
         exact stock Boolean law has only bool/function-of-bool annotations,
         no eligible carrier and no beta redex, so its NUM_TO_INT result is
         unchanged. Both the successful non-equation fallback and an equality
         result retain the original law; no remaining-forall generalization
         is made. Other laws remain explicit normalization requests. *)
      fun bool_type ty =
        (type_walk ty;
         if Type.compare (ty,Type.bool) = EQUAL then true
         else if Type.is_vartype ty then false
         else case Type.dest_type ty of
           ("fun",[a,b]) => bool_type a andalso bool_type b
         | _ => false)
      fun unchanged_marker th =
        if not (Portable.pointer_eq (th,markerTheory.Abbrev_def)) then NONE
        else
          let
            val raw = ref 0 val inclusive = ref 0
            val types = ref ([] : Type.hol_type list)
            fun inspect current =
              (spend 1;raw := !raw+1;inclusive := !inclusive+1;
               let val ty = Term.type_of current
                   val _ = if bool_type ty then () else
                     raise ERR "marker" "fixed Boolean law annotation changed"
                   val _ = types := ty :: !types
               in if Term.is_comb current then
                    let val (f,x) = Term.dest_comb current
                        val _ = if Term.is_abs f then
                          raise ERR "marker" "fixed Boolean law acquired beta"
                          else ()
                    in inspect f;inspect x end
                  else if Term.is_abs current then
                    (inclusive := !inclusive+1;
                     inspect (guarded (fn () => I.count_body current)))
                  else () end)
            val _ = inspect (Thm.concl th)
            val cap = #template_limit (W.semantic_limits work)
            val _ = if !raw <= cap andalso !inclusive <= cap andalso
                2 * IntInf.fromInt (!raw) + 3 <= IntInf.fromInt cap andalso
                2 * IntInf.fromInt (!inclusive) + 3 <= IntInf.fromInt cap
              then () else raise ERR "marker" "closed bridge exceeds template"
            val _ = if null (Thm.hyp th) then () else
              raise ERR "marker" "stock auxiliary has hypotheses"
            (* Quote equality raw/binder incidences before import/opening.
               This does not account private G/P maps or kernel traversals. *)
            val _ = spend (IntInf.fromInt (2 * !inclusive + 3))
            val _ = List.app policy (!types)
            val imported = guarded (fn () =>
              G.import graph scope cap (Thm.concl th))
            val opened = guarded (fn () =>
              G.record_opened_view graph scope cap (#node imported))
            val _ = G.validate_opened_view graph scope (#node imported) opened
            val plan = guarded (fn () =>
              P.record_closed_from_import graph scope
              {node = #node opened,theorem = th,template_limit = cap,
               check_type = policy})
          in SOME plan end

      (* Reflexive fixed-law results are dropped; the others are kept. *)
      fun unchanged th = case unchanged_marker th of NONE => Blocked
        | SOME proof =>
            let val term = Thm.concl th
                val reflexive = if boolSyntax.is_eq term then
                  let val (a,b) = boolSyntax.dest_eq term
                  in guarded (fn () => Term.aconv a b) end else false
            in if reflexive then Dropped else Kept proof end
      fun roots_of_added added _ =
        HOLset.listItems (HOLset.foldl
          (fn (th,ts) => HOLset.addList (ts,terms th)) (empty_terms ()) added)
      val loop = fixed_point k owner
        {atoms = atoms,selected = selected,unchanged = unchanged,
         roots_of_added = roots_of_added,own = HOLset.listItems,
         finish = finish_with k (fn checked => GP.from_portfolio
           (F.prepend_recorded graph scope portfolio checked))}
      val (assumptions,goal) = F.processed_goal portfolio
    in loop (goal :: assumptions) (empty_thms ()) [] end))

  fun validate_reuse (Pending
      {owner=owner as Owner {work,graph,scope,...},originals,resumed,...})
      (Normalized {owner=held,original,kept,guard,...}) =
    ((if Portable.pointer_eq (owner,held) then () else
        raise ERR "validate_reuse" "foreign normalization owner";
      revalidate owner;
      if !resumed then raise ERR "validate_reuse" "pending consumed" else ();
      if List.exists (fn th => Portable.pointer_eq (th,original)) originals
        then () else raise ERR "validate_reuse" "unrequested original";
      guard ();
      case kept of NONE => () | SOME (_,proof) =>
        P.validate_closed_fact graph scope
          (#template_limit (W.semantic_limits work)) proof;
      active owner)
     handle primary => (W.close work;raise primary))

  fun validate_reuse_cached (Pending
      {owner=owner as Owner {work,graph,scope,...},originals,resumed,...})
      (Normalized {owner=held,original,kept,guard,proof_revision}) =
    ((if Portable.pointer_eq (owner,held) then () else
        raise ERR "validate_reuse_cached" "foreign normalization owner";
      active owner;
      if !resumed then raise ERR "validate_reuse_cached" "pending consumed"
        else ();
      if List.exists (fn th=>Portable.pointer_eq (th,original)) originals
        then () else raise ERR "validate_reuse_cached" "unrequested original";
      (* guard itself retains exact Aux/D lookup and authentic graph revision.
         Its private owner phases cannot change without retiring SAME W;
         declaration, registry, naming-plan and Scope changes are witnessed. *)
      guard ();
      let val revision=G.validation_revision graph scope
      in if !proof_revision=SOME revision then () else
        (case kept of NONE=>() | SOME (_,proof)=>
           P.validate_closed_fact graph scope
             (#template_limit (W.semantic_limits work)) proof;
         active owner;
         if G.validation_revision graph scope=revision then
           proof_revision:=SOME revision else
           raise ERR "validate_reuse_cached"
             "validation state changed during proof backing pass")
      end;
      active owner)
     handle primary=>(W.close work;raise primary))

  fun reuse (Pending
      {owner=owner as Owner {work,graph,scope,...},originals,resumed,...})
      {completed=completed as Normalized
         {owner=held,original,kept,guard,...},selection,ordinal} =
    ((W.with_step work (fn () =>
      let
        (* Do not activate a foreign receipt, even when its retired frame
           would fail first. Only this expected invocation can be retired. *)
        val _ = if Portable.pointer_eq (owner,held) then () else
          raise ERR "reuse" "foreign completed normalization owner"
        val _ = active owner
        val _ = if !resumed then raise ERR "reuse" "pending consumed" else ()
        fun spend n = (active owner;W.spend work n;active owner)
        val data=SmtLib_GraphNumericStock.selection_data selection
        fun selected [] _ = raise ERR "reuse" "selected law ordinal absent"
          | selected (th::rest) n =
              (spend 1;if n=0 then th else selected rest (n-1))
        val _ = if ordinal>=0 then () else
          raise ERR "reuse" "negative selected law ordinal"
        val _ = if Portable.pointer_eq
            (selected (#laws data) ordinal,original) andalso
            List.exists (fn th =>
              (spend 1;Portable.pointer_eq (th,original))) originals then ()
          else raise ERR "reuse" "different exact requested original law"
        val _ = guard ()
        val _ = case kept of NONE => () | SOME (_,proof) =>
          P.validate_closed_fact graph scope
            (#template_limit (W.semantic_limits work)) proof
        val _ = active owner
      in completed end))
     handle primary => (W.close work;raise primary))

  (* Completion accepts only opaque locally checked normalized receipts.
     It does not accept a caller converter, theorem or replacement Source. *)
  fun resume (Pending {owner = owner as Owner {work,retained,...},resumed,
                        continuation,originals,...}) completed =
    lift (W.with_step work (fn () =>
      let val _ = active owner
          val _ = if !resumed then raise ERR "resume" "pending consumed"
            else resumed := true
          val _ = if length completed = length originals then () else
            raise ERR "resume" "different completion count"
          val _ = List.app (fn Normalized {owner = held,...} =>
            if Portable.pointer_eq (held,owner) then () else
              raise ERR "resume" "foreign normalization owner") completed
          (* Pure backing guards, never recursive calls to this N owner.
             Retain them across every later policy/fixedpoint/finish step. *)
          val guards = List.map (fn Normalized {guard,...} => guard) completed
          val _ = List.app (fn guard => guard ()) guards
          val _ = retained := guards @ !retained
      in continuation completed end))

  (* The conversion is genuine SAME Work semantic evidence, not an exact
     NUM/SIMP policy certificate or a credit for its previous construction.
     The future numeric producer must build it from the required whole pass. *)
  fun normalize_result (Pending
      {owner = owner as Owner {work,graph,scope,sources,check_type,...},
       originals,resumed,...}) {law,conversion,ordinal} =
    let
      val expected =
        {graph = graph,scope = scope,sources = sources,work = work}
      val backing_validated = ref (NONE : IntInf.int option)
      fun backing () =
        let val revision=G.validation_revision graph scope
        in if !backing_validated=SOME revision then () else
          (X.validate_for expected law;
           ignore (D.conversion_description_for expected conversion);
           if G.validation_revision graph scope=revision then
             backing_validated := SOME revision else
             raise ERR "normalize_result" "backing changed during validation")
        end
      val {original,kept} = normalize_with
        {name = "normalize_result",graph = graph,work = work,
         active = fn () => active owner,
         charge = fn n => W.spend work (IntInf.toInt n),backing = backing,
         check_type = check_type,originals = originals,resumed = resumed}
        (fn {live,spend} =>
          let
            val limits = W.semantic_limits work
            fun prelude target =
              (List.app (fn (cap,label) => List.app (fn metric =>
                (spend 1;case G.unfolded_nodes graph metric cap target of
                    SOME n => if n <= cap then () else
                      raise ERR "normalize_result" label
                  | NONE => raise ERR "normalize_result"
                      "target needs genuine syntax admission"))
                [G.RawNodes,G.BinderInclusiveNodes])
                [(#output_limit limits,
                  "normalized output exceeds original cap"),
                 (#template_limit limits,
                  "normalized law exceeds recording cap")];
               fn () => ())
          in
            {describe_conversion = fn () =>
               let val d = D.conversion_description_for expected conversion
               in {source = #source d,target = #target d} end,
             describe_law = fn () =>
               let val d = X.describe_for expected law
               in {original = #original d,endpoint = #node (#opened d),
                   canonical = #canonical_theorem d,law = #law d} end,
             prelude = prelude,bounded = fn count => count,
             open_abs = I.count_body,
             amount_limit = fn () => IntInf.fromInt (W.work_limit work),
             footprint_message =
               "normalized proof footprint exceeds original Work",
             guard = fn () =>
               (live ();X.validate_for expected law;
                ignore (D.conversion_description_for expected conversion)),
             record_conversion = fn check_type => ignore
               (D.closed_fact conversion
                {ordinal = ordinal,check_type = check_type}),
             endpoints_theorem = fn () => #theorem (D.endpoints conversion),
             record = fn {node,theorem,check_type} =>
               P.record_closed graph scope
               {node = node,theorem = theorem,
                template_limit = #template_limit limits,
                check_type = check_type}}
          end)
    in Normalized {owner = owner,original = original,kept = kept,
                   guard = backing,proof_revision = ref NONE} end
  structure PolicyNeeded=
  struct
    structure NC=SmtReplayNativeContract
    structure RP=SmtReplayResourcePolicy
  datatype owner = Owner of
    {work : W.portfolio,native:NC.contract,
     profiles:G.policy_opaque_profile list,graph : G.graph,
     scope : G.scope,sources : S.sources,
     portfolio : F.validation,check_type : Type.hol_type -> unit,
     symbols : int,types : int,used : bool ref,
     selections : (Term.term * SmtLib_GraphNumericStock.selection) list ref,
     retained : (unit -> unit) list ref,
     validated : (IntInf.int * (unit -> unit) list) option ref}
  type pending = (owner,unit) pend
  type normalized = owner norm
  datatype result = PolicyComplete of GP.validation
    | PolicyNeedsNormalization of pending
  fun lift (Done value) = PolicyComplete value
    | lift (Need pending) = PolicyNeedsNormalization pending

  fun active (Owner {work,native,graph,scope,sources,symbols,types,retained,
                    validated,...}) =
    ((let
        val _ = W.validate_policy work graph scope sources
          (W.semantic_policy work)
        val _ = NC.validate_for work native
        val _ = if Term.term_epoch () = symbols andalso
            Type.type_epoch () = types then () else
          raise ERR "active" "constant retirement epoch changed"
        val revision=G.validation_revision graph scope val rows= !retained
        val hit=case !validated of SOME (old,held) =>
            old=revision andalso Portable.pointer_eq (held,rows)
          | NONE => false
      in if hit then () else
        (List.app (fn guard => guard ()) rows;
         W.validate_policy work graph scope sources
          (W.semantic_policy work);
         if Term.term_epoch ()=symbols andalso
             Type.type_epoch ()=types andalso
             G.validation_revision graph scope=revision andalso
             Portable.pointer_eq (rows,!retained) then
           validated := SOME (revision,rows) else
         raise ERR "active" "validation state changed during backing pass")
      end)
     handle primary => (W.close work;raise primary))
  fun begin work {portfolio,check_type,native_contract,profiles} =
    let
      val _=NC.validate_for work native_contract
      val sources=W.original_sources work
      val graph=S.owning_graph sources val scope=S.owning_scope sources
      val _=F.validate_with_policy work portfolio
      val _=if Portable.pointer_eq(sources,F.original_sources portfolio)
          then ()else raise ERR "begin_with_policy" "different Source"
      val _=List.app(G.validate_policy_opaque_profile graph)profiles
    in Owner{work=work,native=native_contract,profiles=profiles,graph=graph,
      scope=scope,sources=sources,portfolio=portfolio,check_type=check_type,
      symbols=Term.term_epoch(),types=Type.type_epoch(),used=ref false,
      selections=ref[],retained=ref[],validated=ref NONE}end
    handle primary=>(W.close work;raise primary)

  fun pending_originals (Pending {owner,originals,...}) =
    (active owner;originals)
  fun begin_preprocessed work
      {preprocessed,check_type,native_contract,profiles}=
    ((GP.validate_with_policy work preprocessed;
      case GP.portfolio_validation_with_work work preprocessed of
        SOME portfolio=>begin work {portfolio=portfolio,check_type=check_type,
          native_contract=native_contract,profiles=profiles}
      | NONE=>raise ERR "begin_preprocessed_with_policy"
          "legacy GP has no original dependency portfolio")
     handle primary=>(W.close work;raise primary))
  fun pending_requests (Pending {owner,requests,...}) =
    (active owner;requests)
  fun pending_selections (Pending {owner,selections,...}) =
    (active owner;selections)

  fun collect (owner as Owner
      {work,native,profiles,graph,scope,portfolio,used,selections,
       retained,validated,...}) =
    lift (W.with_step work (fn () =>
    let
      val _ = active owner
      val _ = if !used then raise ERR "collect" "collector already consumed"
        else used := true
      val k = {active = fn () => active owner,
               charge = fn n => W.spend_policy work n}
      val spend = spend k
      fun guarded action = guarded_by k action
      val empty_terms = empty_terms k
      val empty_thms = empty_thms k
      val compare_thms = compare_thms k

      (* Only genuine graph/closure ports are traversed. An opaque leaf
         needs the retained profile from the same actual node; its heads
         were captured by the original guarded profile walk, not re-opened. *)
      fun atoms roots =
        let val seen=ref(Redblackmap.mkDict
              (Lib.pair_compare (Int.compare,Int.compare)))
            fun retain guard=(guard();retained:=guard:: !retained;
              validated:=NONE)
            fun opaque frame node found =
              let fun find []=raise ERR "atoms_with_policy"
                        "opaque Source lacks authentic retained heads"
                    | find(profile::rest)=
                      (spend 1;case G.opaque_profile_for_node_with_policy
                          graph frame node profile of NONE=>find rest
                        | SOME _=>profile)
                  val profile=find profiles
                  fun backing()=ignore(G.opaque_profile_heads_with_policy
                    graph frame profile)
                  val _=retain backing
                  val data=G.opaque_profile_heads_with_policy
                    graph frame profile
                  val _=if #node data=node then ()else
                    raise ERR "atoms_with_policy" "different actual leaf"
              in List.foldl(fn(head,acc)=>(spend 1;HOLset.add(acc,head)))
                found (#heads data)end
            fun walk [] found=found
              | walk((frame,node)::rest)found=
                let val _=spend 1
                    val _=ignore(G.closure_root graph frame node)
                    val key=(G.scope_id frame,G.node_id node)
                in case Redblackmap.peek(!seen,key)of SOME _=>walk rest found
                  | NONE=>
                    let val _=seen:=Redblackmap.insert(!seen,key,())
                    in case guarded(fn()=>G.view graph node)of
                        G.Application(left,right)=>
                          walk((frame,left)::(frame,right)::rest)found
                      | G.AdmittedBinder _=>
                          let val closure=G.binder_closure graph frame node
                              fun backing()=ignore
                                (G.binder_closure_data graph frame closure)
                              val data=G.binder_closure_data
                                graph frame closure
                              val _=retain backing
                          in walk((#body_frame data,#body data)::rest)found end
                      | G.OpaqueRetained=>walk rest(opaque frame node found)
                      | G.Constant _=>walk rest(HOLset.add(found,
                          guarded(fn()=>G.representative graph node)))
                      | _=>walk rest found
                    end
                end
        in walk roots(empty_terms())end

      (* This declaration-only walk has no callbacks or repeated-occurrence
         admission meaning. Visit each actual immutable Type object once in
         this owned fixed point; physical hits still pay real lookup work.
         Retirement is checked by active BEFORE every lookup or reuse. *)
      val inspected_types=ref([]:Type.hol_type list)
      fun inspected current []=(spend 1;false)
        | inspected current(held::rest)=
            (spend 1;Portable.pointer_eq(current,held)orelse
             inspected current rest)
      fun type_walk ty =
        let fun walk []=spend 1
              | walk(current::rest)=
                  (spend 1;
                   if inspected current(!inspected_types)then walk rest else
                     (spend 1;inspected_types:=current:: !inspected_types;
                      if Type.is_vartype current then walk rest else
                        let val(_,args)=Type.dest_type current
                            val _=List.app(fn _=>spend 1)args
                        in walk(args@rest)end))
        in walk[ty]end
      val selected = select_with k {selections = selections,
        type_walk = type_walk,
        select = fn head => SmtLib_GraphNumericStock.select_with_policy
          work native head}

      (* Every selected law is normalized by the genuine numeric pass.
         In particular the fixed Boolean marker is an actual request, not
         a caller-supplied no-op certificate or a skipped auxiliary. *)
      fun roots_of_added added records =
        let val next_terms = HOLset.foldl
              (fn (th,ts) => HOLset.add(ts,th)) (empty_thms ()) added
        in List.map(fn th=>
             let val proof=case List.find(fn(original,_)=>
                   compare_thms(th,original)=EQUAL)records of
                   SOME(_,proof)=>proof | NONE=>
                     raise ERR "loop" "normalized fact lost"
             in (scope,P.closed_node proof)end)
               (HOLset.listItems next_terms) end
      val loop = fixed_point k owner
        {atoms = atoms,selected = selected,unchanged = fn _ => Blocked,
         roots_of_added = roots_of_added,own = fn _ => (),
         finish = finish_with k (fn checked => GP.from_portfolio_with_policy
           work (F.prepend_recorded_with_policy work portfolio checked))}
      val {assumptions,goal}=F.processed_nodes_with_policy_for work portfolio
    in loop(List.map(fn node=>(scope,node))(goal::assumptions))
      (empty_thms())[] end))

  fun validate_reuse_cached (Pending
      {owner=owner as Owner {work,graph,scope,...},originals,resumed,...})
      (Normalized {owner=held,original,kept,guard,proof_revision}) =
    ((if Portable.pointer_eq (owner,held) then () else
        raise ERR "validate_reuse_cached" "foreign normalization owner";
      active owner;
      if !resumed then raise ERR "validate_reuse_cached" "pending consumed"
        else ();
      if List.exists (fn th=>Portable.pointer_eq (th,original)) originals
        then () else raise ERR "validate_reuse_cached" "unrequested original";
      (* guard itself retains exact Aux/D lookup and authentic graph revision.
         Its private owner phases cannot change without retiring SAME W;
         declaration, registry, naming-plan and Scope changes are witnessed. *)
      guard ();
      let val revision=G.validation_revision graph scope
      in if !proof_revision=SOME revision then () else
        (case kept of NONE=>() | SOME (_,proof)=>
           P.validate_closed_fact_with_policy graph scope
             (#template_limit (W.semantic_policy work)) proof;
         active owner;
         if G.validation_revision graph scope=revision then
           proof_revision:=SOME revision else
           raise ERR "validate_reuse_cached"
             "validation state changed during proof backing pass")
      end;
      active owner)
     handle primary=>(W.close work;raise primary))

  fun reuse (Pending
      {owner=owner as Owner {work,graph,scope,...},originals,resumed,...})
      {completed=completed as Normalized
         {owner=held,original,kept,guard,...},selection,ordinal} =
    ((W.with_step work (fn () =>
      let
        (* Do not activate a foreign receipt, even when its retired frame
           would fail first. Only this expected invocation can be retired. *)
        val _ = if Portable.pointer_eq (owner,held) then () else
          raise ERR "reuse" "foreign completed normalization owner"
        val _ = active owner
        val _ = if !resumed then raise ERR "reuse" "pending consumed" else ()
        fun spend n = (active owner;W.spend_policy work n;active owner)
        val data=SmtLib_GraphNumericStock.selection_data selection
        fun selected [] _ = raise ERR "reuse" "selected law ordinal absent"
          | selected (th::rest) n =
              (spend 1;if n=0 then th else selected rest (n-1))
        val _ = if ordinal>=0 then () else
          raise ERR "reuse" "negative selected law ordinal"
        val _ = if Portable.pointer_eq
            (selected (#laws data) ordinal,original) andalso
            List.exists (fn th =>
              (spend 1;Portable.pointer_eq (th,original))) originals then ()
          else raise ERR "reuse" "different exact requested original law"
        val _ = guard ()
        val _ = case kept of NONE => () | SOME (_,proof) =>
          P.validate_closed_fact_with_policy graph scope
            (#template_limit (W.semantic_policy work)) proof
        val _ = active owner
      in completed end))
     handle primary => (W.close work;raise primary))

  (* Completion accepts only opaque locally checked normalized receipts.
     It does not accept a caller converter, theorem or replacement Source. *)
  fun resume (Pending {owner = owner as Owner {work,retained,...},resumed,
                        continuation,originals,...}) completed =
    lift (W.with_step work (fn () =>
      let val _ = active owner
          val _ = if !resumed then raise ERR "resume" "pending consumed"
            else resumed := true
          val _ = if length completed = length originals then () else
            raise ERR "resume" "different completion count"
          val _ = List.app (fn Normalized {owner = held,...} =>
            if Portable.pointer_eq (held,owner) then () else
              raise ERR "resume" "foreign normalization owner") completed
          (* Pure backing guards, never recursive calls to this N owner.
             Retain them across every later policy/fixedpoint/finish step. *)
          val guards = List.map (fn Normalized {guard,...} => guard) completed
          val _ = List.app (fn guard => guard ()) guards
          val _ = retained := guards @ !retained
      in continuation completed end))

  (* A selected receipt and its actual owned conversion are mandatory. The
     outcome programme remains the legacy one: reflexive equation drops;
     nonreflexive equation keeps the normalized theorem; non-equation keeps
     ORIGINAL. No other exception is converted to semantic fallback. *)
  fun normalize_result (Pending
      {owner=owner as Owner{work,native,profiles,graph,scope,sources,
         check_type,...},originals,resumed,...}) {law,conversion,ordinal}=
    let
      val expected_request=
        {graph=graph,scope=scope,sources=sources,work=work}
      fun backing()=
        let val selected=X.native_contract_with_policy_for expected_request law
            val converted=D.native_contract_conversion_with_policy_for
              expected_request conversion
            val _=if Portable.pointer_eq(selected,native)andalso
                Portable.pointer_eq(converted,native)then ()else
              raise ERR "normalize_result_with_policy"
                "different actual normalization native contract"
            val _=X.validate_with_policy_for expected_request law
        in ignore(D.conversion_description_with_policy_for
          expected_request conversion)end
      val {original,kept}=normalize_with
        {name="normalize_result_with_policy",graph=graph,work=work,
         active=fn()=>active owner,charge=fn n=>W.spend_policy work n,
         backing=backing,check_type=check_type,originals=originals,
         resumed=resumed}
        (fn{live,...}=>
          let
            val native_data=NC.for_work work native
            val native_limits= #semantic_limits native_data
            val metadata=W.semantic_policy work
            fun prelude target=
              let val metric=G.prepare_scoped_profiled_metric graph scope
                    {node=target,profiles=profiles}
                  fun held()=ignore(G.profiled_metric_data graph scope metric)
                  val measured=G.profiled_metric_data graph scope metric
                  val _=List.app(fn cap=>
                    if #raw measured<=IntInf.fromInt cap andalso
                       #inc measured<=IntInf.fromInt cap then ()else
                    raise ERR "normalize_result_with_policy"
                      ("normalized auxiliary exceeds actual native "^
                       "output/template"))
                    [#output_limit native_limits,#template_limit native_limits]
              in held end
            (* The real selected auxiliary is fully realized here. Preserve
               the old repeated annotation walk and its local quote; this is
               not a bound imposed on the unrelated original Source DAG. *)
            val ceiling=IntInf.fromInt(#type_work_limit native_data)
            fun bounded count=if count<=ceiling then count else
              raise ERR "normalize_result_with_policy"
                "normalized auxiliary Type programme exceeds native contract"
          in
            {describe_conversion=fn()=>
               let val d=D.conversion_description_with_policy_for
                     expected_request conversion
               in {source= #source d,target= #target d}end,
             describe_law=fn()=>
               let val d=X.describe_with_policy_for expected_request law
               in {original= #original d,endpoint= #node(#opened d),
                   canonical= #canonical_theorem d,law= #law d}end,
             prelude=prelude,bounded=bounded,
             open_abs=fn current=> #2(Term.dest_abs current),
             amount_limit=fn()=>ceiling,
             footprint_message=
               "normalized proof footprint exceeds actual native Work",
             guard=live,
             record_conversion=fn check_type=>ignore
               (D.closed_fact_with_policy_for expected_request conversion
                {ordinal=ordinal,check_type=check_type}),
             endpoints_theorem=fn()=> #theorem(D.endpoints_with_policy
               conversion),
             record=fn{node,theorem,check_type}=>
               P.record_closed_with_policy_profiles graph scope
               {node=node,theorem=theorem,
                template_limit= #template_limit metadata,
                check_type=check_type,profiles=profiles}}
          end)
    in Normalized{owner=owner,original=original,kept=kept,
      guard=backing,proof_revision=ref NONE}end
  end
  type policy_owner=PolicyNeeded.owner
  type policy_pending=PolicyNeeded.pending
  type policy_normalized=PolicyNeeded.normalized
  type policy_request=request
  datatype policy_result=datatype PolicyNeeded.result
  val begin_with_policy=PolicyNeeded.begin
  val begin_preprocessed_with_policy=PolicyNeeded.begin_preprocessed
  val collect_with_policy=PolicyNeeded.collect
  val normalize_result_with_policy=PolicyNeeded.normalize_result
  val validate_reuse_cached_with_policy=PolicyNeeded.validate_reuse_cached
  val reuse_with_policy=PolicyNeeded.reuse
  val resume_with_policy=PolicyNeeded.resume
  val pending_originals_with_policy=PolicyNeeded.pending_originals
  val pending_requests_with_policy=PolicyNeeded.pending_requests
  val pending_selections_with_policy=PolicyNeeded.pending_selections
end
