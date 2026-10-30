(* Copyright (c) 2026 The HOL4 contributors. *)
structure Z3_DefinitionClosureTests =
struct
  open HolKernel Parse testutils
  structure G = SmtReplayGraph
  structure E = SmtReplayDefinitionEnvironment
  structure D = SmtReplayGroundDefinitions
  structure R = Z3_GraphProofReplay
  structure S = SmtReplaySource
  structure Z = Z3_GraphProofParser
  structure Q = SmtLib_GraphProof
  val limit = 10000
  fun require message yes = if yes then () else raise Fail message
  fun refuses action = (action ();false) handle Feedback.HOL_ERR _ => true
  fun clean theorem =
    let val (tags,_) = Tag.dest_tag (Thm.tag theorem)
    in null (Tag.axioms_of (Thm.tag theorem)) andalso
       List.all (fn tag => tag = "DISK_THM") tags end
  fun imported graph scope term = #node (G.import graph scope limit term)
  fun equation graph scope left right =
    let val head = G.constant graph scope (Term.rator (Term.rator
          (boolSyntax.mk_eq (G.representative graph left,
                            G.representative graph right))))
    in G.application graph scope
      (G.application graph scope (head,left),right) end
  fun flexible graph scope term = G.fresh_flexible_variable graph scope term
  fun ground () =
    let
      val graph = G.new () val scope = G.root_scope graph
      val terms = [``((\x:num. x) 2) = 2``,``(2:num) DIV 1 = 2``,
        ``(1w:word8)+1w=2w``,``(\x:num. x)=(\x:num. x)``,
        ``(q:num)=q``,``(1:num)=2``]
      val nodes = List.map (imported graph scope) terms
      val sources = nodes @ [hd nodes]
      val plan = D.prepare_complete_recorded graph
        {scope=scope,allocated=[],sources=sources,needed=sources,
         definitions=nodes,limit=limit}
      val proofs = D.execute plan {check_type=fn _ => ()}
      val _ = require "complete ground category/order/duplicates differ"
        (List.map #1 proofs = List.take (nodes,5) @ [hd nodes] andalso
         Portable.pointer_eq (#2 (hd proofs),#2 (List.last proofs)))
      val _ = List.app (fn (node,theorem) =>
        require "ground discharge lost exact original Source/Hyp/tags"
          (Portable.pointer_eq (Thm.concl theorem,
             G.representative graph node) andalso
           null (Thm.hyp theorem) andalso clean theorem)) proofs
      val calls = ref 0
      val _ = require "complete ground admission followed type callback"
        (refuses (fn () => ignore (D.execute
          (D.prepare_complete_recorded graph
            {scope=scope,allocated=[],sources=sources,needed=sources,
             definitions=nodes,limit=1})
          {check_type=fn _ => calls := !calls+1})) andalso !calls=0)
      val empty = D.execute (D.prepare_complete_recorded graph
        {scope=scope,allocated=[],sources=sources,needed=sources,
         definitions=[],limit=limit}) {check_type=fn _ => calls := !calls+1}
    in require "assertion truth inferred definition authority"
      (null empty andalso !calls=0) end

  fun definitions graph scope packed reverse =
    let
      val x = flexible graph scope ``closure_x:num``
      val y = flexible graph scope ``closure_y:num``
      fun stored left right = if reverse then equation graph scope right left
        else equation graph scope left right
      val f = flexible graph scope ``closure_function:num->num``
      val lexical = G.new_scope graph scope
        [(G.representative graph y,y)]
      val body = Term.mk_abs (``n:num``,G.representative graph y)
      val binder = #node (G.rehome graph scope
        (#node (G.admit_binder graph lexical limit body)))
      val ground_beta = imported graph scope ``((\n:num. n) 2)=2``
      val ground_beta = #node
        (G.record_opened_view graph scope limit ground_beta)
      val base = [stored x x,stored y (imported graph scope ``0:num``),
        stored f binder,imported graph scope ``(2:num) DIV 1 = 2``,
        ground_beta]
      val base = base @ [hd base]
    in if not packed then ([x,y,f],base) else
      let
        val word = flexible graph scope ``closure_word:word4``
        val bits = List.tabulate (4,fn i => flexible graph scope
          (Term.mk_var ("closure_bit" ^ Int.toString i,Type.bool)))
        val index = fcpSyntax.mk_int_numeric_type 4
        val empty = G.constant graph scope (listSyntax.mk_nil Type.bool)
        val cons = G.constant graph scope (Term.rator (Term.rator
          (listSyntax.mk_cons (boolSyntax.T,listSyntax.mk_nil Type.bool))))
        val list = List.foldr (fn (bit,tail) => G.application graph scope
          (G.application graph scope (cons,bit),tail)) empty bits
        val v2w = G.constant graph scope (Term.rator
          (bitstringSyntax.mk_v2w (listSyntax.mk_nil Type.bool,index)))
        val vector = G.application graph scope (v2w,list)
        fun bit i =
          let val number = numSyntax.term_of_int (3-i)
              val head = G.constant graph scope (Term.rator (Term.rator
                (wordsSyntax.mk_word_bit (number,``0w:word4``))))
          in G.application graph scope (G.application graph scope
            (head,imported graph scope number),word) end
        val anchor = imported graph scope ``closure_anchor:word4``
        val family = [stored word anchor,stored word vector] @
          List.tabulate (4,fn i => stored (List.nth (bits,i)) (bit i))
      in (x::y::f::word::bits,base @ family @ [List.nth (family,1)]) end
    end

  (* All recorded equations are retained in the actual compact Hyp of the
     successful rule. They are not merely discovery/dependency metadata. *)
  fun combined packed reverse assumption goal =
    let
      val graph = G.new () val scope = G.root_scope graph
      val sources = S.new graph scope limit
        {goal=goal,assumptions=[assumption,assumption,
          ``(closure_unused_word:'a word)=closure_unused_word``]}
      val options = Z3_CompactReplayTests.options graph scope [("p",goal)]
      val stream = TextIO.openString
        "((proof (unit-resolution (nnf-pos (asserted p) p) \
        \(asserted (not p)) false)))"
      val packet = Z.create_packet options "4.15.3" stream
      val parsed = Q.proof packet
      val (allocated,definitions) = definitions graph scope packed reverse
      val proof : Z.proof = {steps= #steps parsed,root= #root parsed,
        vars=allocated,z3_version= #z3_version parsed,close= #close parsed}
      val replay = imported graph scope goal
      val originals = List.map #node (S.reconciliation_sources sources)
      val views = List.map (fn node =>
        (node,G.record_opened_view graph scope limit node))
        (originals @ [replay])
      val calls = ref 0
      fun producer (request:R.local_request) =
        let
          val _ = calls := !calls+1
          val target = G.representative graph (#target request)
          val theorem = Thm.DISCH target (Thm.ASSUME target)
          val theorem = List.foldl (fn (node,theorem) =>
            Drule.ADD_ASSUM (G.representative graph node) theorem)
            theorem definitions
          val theorem = List.foldr (fn (node,theorem) =>
            Thm.DISCH (G.representative graph node) theorem)
            theorem definitions
          val law = SmtReplayRules.implication graph scope
            (definitions @ #premises request) (#target request)
          val theorem = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem)
            (G.representative graph law)) theorem
        in SOME {definitions=definitions,theorem=theorem} end
      fun run () = R.check_proof_with_definition_closure_using graph scope
        {sources=sources,proof=proof,template_limit=limit,
         local_law=fn _ => NONE,recorded_law=producer,nnf=fn _ => NONE,
         views=views,admission={raw_limit=limit,binder_limit=limit,
           step_limit=limit,check_type=fn _ => ()}}
      val result = Exn.capture run ()
      val _ = Q.close packet val _ = TextIO.closeIn stream
      val theorem = Exn.release result
      val _ = S.check_goal sources theorem
    in require "combined closure changed original Goal/Hyp/tags or discovery"
      (Portable.pointer_eq (Thm.concl theorem,goal)
       andalso HOLset.equal (Thm.hypset theorem,
         HOLset.addList (Term.empty_tmset,[assumption])) andalso
       clean theorem andalso !calls=1) end

  fun legacy_controls () =
    let
      val x = ``closure_legacy_x:num`` val y = ``closure_legacy_y:num``
      val ground = ``((\x:num. x) 2)=2``
      val unused = boolSyntax.mk_eq (x,numSyntax.mk_plus (x,``1:num``))
      fun remove definitions variables theorem =
        Z3_ProofReplay.remove_definitions
          (HOLset.addList (Term.empty_tmset,definitions),
           HOLset.addList (Term.empty_tmset,variables),theorem)
      fun theorem definitions = List.foldl (fn (term,proof) =>
        Drule.ADD_ASSUM term proof) boolTheory.TRUTH definitions
      val defs = [boolSyntax.mk_eq (x,x),boolSyntax.mk_eq (y,``0:num``),ground]
      val result = remove (unused::defs) [x,y] (theorem defs)
      val _ = require "unused self dependency blocked actual definitions"
        (null (Thm.hyp result) andalso clean result)
      val f = ``closure_legacy_f:num->num``
      val binders = [boolSyntax.mk_eq (f,``\n:num. (closure_legacy_x:num)``),
        boolSyntax.mk_eq (x,``0:num``),
        boolSyntax.mk_eq (f,``\n:num. (closure_legacy_y:num)``),
        boolSyntax.mk_eq (y,``0:num``)]
      val bounded = remove binders [f,x,y] (theorem binders)
      val _ = require "bounded affected binder definitions lost compatibility"
        (null (Thm.hyp bounded) andalso clean bounded)
      fun grow 0 term = term
        | grow n term = let val child = grow (n-1) term
            in boolSyntax.mk_conj (child,child) end
      val large = Term.mk_abs (``n:num``,grow 21 ``closure_public:bool``)
      val retained = boolSyntax.mk_eq (large,large)
      val unrelated = remove [boolSyntax.mk_eq (x,``0:num``)] [x]
        (Drule.ADD_ASSUM retained (theorem [boolSyntax.mk_eq (x,``0:num``)]))
      val _ = require "unrelated retained binder gained an opening quota"
        ((case Thm.hyp unrelated of [term] =>
            Term.aconv term retained | _ => false)
         andalso clean unrelated)
      val bad = [boolSyntax.mk_eq (x,numSyntax.mk_plus (y,``1:num``)),
        boolSyntax.mk_eq (y,numSyntax.mk_plus (x,``1:num``))]
      val _ = require "genuine unresolved cycle gained an assignment"
        (refuses (fn () => ignore (remove bad [x,y] (theorem bad))))
    in require "direct self dependency gained an assignment"
      (refuses (fn () => ignore (remove [unused] [x] (theorem [unused])))) end

  fun run () =
    (tprint "Complete ground definitions retain checked legacy families";
     ground ();OK ();
     tprint "Reflexive, acyclic and ground actual Hyp compose with beta";
     combined false false ``(\x:bool. x) closure_p`` ``closure_p:bool``;
     OK ();
     tprint "Anchored packed SCC composes with beta and ground actual Hyp";
     combined true false ``(\x:bool. x) closure_p`` ``closure_p:bool``;
     OK ();
     tprint "Reversed packed SCC composes with exact eta Source spelling";
     combined true true
       ``(\x:num. closure_f x) = (closure_g:num->num)``
       ``(closure_f:num->num) = closure_g``;
     OK ();
     tprint "Combined closure refuses semantic Source rescue";
     require "semantic hypothesis was silently proved at finalization"
       (refuses (fn () => combined true false
         ``closure_p \/ closure_p`` ``closure_p:bool``));
     OK ();
     tprint "Legacy one-shot definition closure preserves unused/cycle policy";
     legacy_controls ();OK ())
end
