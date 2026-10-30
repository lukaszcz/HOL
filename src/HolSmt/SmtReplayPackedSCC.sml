(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayPackedSCC :> SmtReplayPackedSCC =
struct
  structure G = SmtReplayGraph
  structure E = SmtReplayDefinitionEnvironment
  structure U = SmtReplayUnify
  structure R = SmtReplayResolve
  datatype outcome = Resolved of
    {resolution : R.resolution,images : (int * Thm.thm) list,
     assignments : E.definition list}
    | RequiresWitness of E.selection
    | UnificationRefused of U.failure
    | ResolutionRefused of R.failure
  val ERR = Feedback.mk_HOL_ERR "SmtReplayPackedSCC"
  (* GENLIST_CONV applies its callback inside the base equation too.
     Reduce generated element applications; preserve that equation. *)
  fun packed_element dimension term =
    if Term.is_comb term andalso Term.is_abs (Term.rator term) then
      Conv.THENC (Thm.BETA_CONV,
        simpLib.SIMP_CONV
          (simpLib.++ (boolSimps.bool_ss,numSimps.ARITH_ss))
          [dimension,wordsTheory.word_bit]) term
    else raise Conv.UNCHANGED
  fun empty () = Redblackmap.mkDict Int.compare
  fun set () = Redblackset.empty Int.compare
  fun get table id = Option.getOpt (Redblackmap.peek (table,id),[])
  fun has ids node = Redblackset.member (ids,G.node_id node)
  fun require yes message = if yes then () else raise ERR "resolve" message
  fun check_instantiation_template limit theorem =
    let
      val conclusion = Thm.concl theorem
      val (tags,_) = Tag.dest_tag (Thm.tag theorem)
      val _ = require (limit > 0 andalso List.null (Thm.hyp theorem) andalso
        List.all (fn tag => tag = "DISK_THM") tags andalso
        List.null (Tag.axioms_of (Thm.tag theorem)))
        "packed insertion template is not closed and clean"
      (* Count without opening a binder or performing a theorem operation.
         The public negative boundary stops immediately on an abstraction. *)
      fun walk [] count = ()
        | walk (term :: rest) count =
            if count >= limit then raise ERR "resolve"
              "packed insertion template exceeds original raw limit"
            else if Term.is_abs term then raise ERR "resolve"
              "actual word insertion below a residual binder is forbidden"
            else if Term.is_comb term then
              let val (operator,operand) = Term.dest_comb term
              in walk (operator :: operand :: rest) (count+1) end
            else if Term.is_const term andalso
              (Term.same_const term listSyntax.genlist_tm orelse
               Term.same_const term bitstringSyntax.w2v_tm) then
              raise ERR "resolve"
                "actual word insertion before finite word-list expansion"
            else walk rest (count+1)
    in walk [conclusion] 0 end
  (* Match the checked definition environment's bounded binder composition
     in both packed workers, including alpha canonicalization. *)
  fun unify_bounded graph scope allocated limit equations =
    U.unify_with_binders graph
      (fn (left,right) => Option.map SmtReplayUnifyBinder.assignments
        (SmtReplayUnifyBinder.discover_raw graph scope
          {left=left,right=right,flexible=allocated,limit=limit}))
      {scope=scope,binders=[],flexible=allocated,equations=equations}
  fun prepare_bounded graph scope limit input =
    R.prepare_using graph scope
      (fn {node,resolve} =>
        let
          val (normalized,_) = SmtReplayUnifyBinder.normalize_raw graph scope
            {node=node,resolve=resolve,limit=limit}
        in SOME (#node (G.admit_binder graph scope limit
          (G.representative graph normalized))) end) input
  fun packed_operands (row : E.definition,anchor : E.definition,bit_rows) =
    List.map (fn row : E.definition => #stored row) (row :: anchor :: bit_rows)
  (* Fresh pairs may be generated obligations rather than original rows.
     Only matching original bit definitions enter original operand admission. *)
  fun original_bit_rows by_name pairs =
    List.concat (List.map (fn (bit,residue) => List.filter
      (fn row : E.definition => #residue row = residue)
      (get by_name (G.node_id bit))) pairs)
  datatype task = Enter of int | Leave of int
  (* The exact iterative SCC metadata algorithm used by the parent E. *)
  fun visit [] adjacency seen order = (seen,order)
    | visit (Leave id :: rest) adjacency seen order =
        visit rest adjacency seen (id :: order)
    | visit (Enter id :: rest) adjacency seen order =
        if Redblackset.member (seen,id) then visit rest adjacency seen order
        else visit (List.map Enter (get adjacency id) @ Leave id :: rest)
          adjacency (Redblackset.add (seen,id)) order
  fun components names adjacency =
    let
      val (_,order) = List.foldl
        (fn (id,(seen,order)) => visit [Enter id] adjacency seen order)
        (set (),[]) names
      val reversed = Redblackmap.foldl
        (fn (id,children,table) => List.foldl
          (fn (child,table) => Redblackmap.insert
            (table,child,id :: get table child)) table children)
        (empty ()) adjacency
      fun collect (id,(seen,table)) =
        if Redblackset.member (seen,id) then (seen,table)
        else let
          val (seen,part) = visit [Enter id] reversed seen []
          val part_set = Redblackset.addList (set (),part)
          val table = List.foldl
            (fn (member,table) => Redblackmap.insert (table,member,part_set))
            table part
        in (seen,table) end
    in #2 (List.foldl collect (set (),empty ()) order) end
  fun resolve graph {scope,allocated,sources,needed,roots,preserved,laws,
      admission = {metric,limit,check_type}} =
    let
      val _ = require (limit > 0) "nonpositive packed witness limit"
      fun size node = case G.unfolded_nodes graph metric limit node of
          SOME count => if count <= limit then count else raise ERR
            "resolve" "packed witness exceeds original graph limit"
        | NONE => raise ERR "resolve" "unknown packed witness size"
      val env = E.prepare graph {scope = scope,allocated = allocated,
        sources = sources,needed = needed,roots = roots @ preserved}
      val rows = E.definitions env
      val original = Redblackset.addList (set (),List.map G.node_id sources)
      val permitted = List.foldl (fn ((node,proof),ids) =>
        let val (tags,_) = Tag.dest_tag (Thm.tag proof)
        in require (has original node andalso List.null (Thm.hyp proof)
             andalso List.all (fn tag => tag = "DISK_THM") tags andalso
             List.null (Tag.axioms_of (Thm.tag proof)) andalso
             Portable.pointer_eq (Thm.concl proof,
               G.representative graph node)) "original closed law differs";
           Redblackset.add (ids,G.node_id node) end) (set ()) laws
      val rows = List.filter (fn row : E.definition =>
        not (has permitted (#stored row))) rows
      val by_name = List.foldl (fn (row : E.definition,table) =>
        let val id = G.node_id (#variable row) in
          Redblackmap.insert (table,id,row :: get table id) end)
        (empty ()) rows
      val by_name = Redblackmap.map (fn (_,rs) => List.rev rs) by_name
      val names = List.map #1 (Redblackmap.listItems by_name)
      val defined = Redblackset.addList (set (),names)
      val cache = ref (empty ())
      fun dependencies node = case Redblackmap.peek (!cache,G.node_id node) of
          SOME ids => ids
        | NONE => let
            val free = case G.free_variable_nodes graph node of SOME ns => ns
              | NONE => raise ERR "resolve" "unknown packed dependencies"
            val ids = Redblackset.addList (set (),List.map G.node_id free)
            val _ = cache := Redblackmap.insert (!cache,G.node_id node,ids)
          in ids end
      val adjacency = Redblackmap.map (fn (_,rs) =>
        Redblackset.listItems (List.foldl (fn (row : E.definition,ids) =>
          Redblackset.union (ids,Redblackset.intersection
            (defined,dependencies (#residue row)))) (set ()) rs)) by_name
      val parts = components names adjacency
      fun constant node expected = case G.view graph node of G.Constant _ =>
          Term.same_const (G.representative graph node) expected | _ => false
      fun vector node = case G.view graph node of G.Application (head,list) =>
          if constant head bitstringSyntax.v2w_tm then SOME (head,list)
          else NONE | _ => NONE
      fun bits node = if constant node listSyntax.nil_tm then SOME ([],node)
        else case G.view graph node of G.Application (inner,tail) =>
          (case G.view graph inner of G.Application (head,bit) =>
             if constant head listSyntax.cons_tm then
               Option.map (fn (rest,tail_node) => (bit :: rest,tail_node))
                 (bits tail)
             else NONE | _ => NONE)
        | _ => NONE
      fun bit_equation word index (row : E.definition) =
        case G.view graph (#residue row) of G.Application (inner,operand) =>
          (case G.view graph inner of G.Application (head,number) =>
             if constant head wordsSyntax.word_bit_tm andalso operand = word
             then (numSyntax.int_of_term
               (G.representative graph number) = index
               handle Feedback.HOL_ERR _ => false | Overflow => false)
             else false | _ => false)
        | _ => false
      fun candidate (id,rs : E.definition list) =
        let
          val word = #variable (hd rs)
          val part = Redblackmap.find (parts,id)
          val distinct = Redblackset.addList (set (),
            List.map (G.node_id o #stored) rs)
          fun self (row : E.definition) = has (dependencies (#residue row)) word
          fun outside (row : E.definition) = Redblackset.isEmpty
            (Redblackset.intersection (part,dependencies (#residue row)))
          val anchor = List.find outside rs
          fun family (row : E.definition) = case vector (#residue row) of
              NONE => NONE
            | SOME (_,list) => case bits list of NONE => NONE
              | SOME (bs,_) => let
                  val width = length bs
                  val word_type = G.type_of graph word
                  val vector_type = G.type_of graph (#residue row)
                  val allocated_ids = Redblackset.addList
                    (set (),List.map G.node_id allocated)
                  val unique = Redblackset.addList
                    (set (),List.map G.node_id bs)
                  val numeric = wordsSyntax.is_word_type word_type andalso
                    fcpSyntax.is_numeric_type
                      (wordsSyntax.dest_word_type word_type)
                  val dimensions = numeric andalso width > 0 andalso
                    Type.compare (word_type,vector_type) = EQUAL andalso
                    fcpSyntax.dest_int_numeric_type
                      (wordsSyntax.dest_word_type word_type) = width
                  val valid_bits = List.all (fn bit =>
                    has allocated_ids bit andalso
                    (case G.view graph bit of
                       G.Variable (G.SolverFlexible,_) => true | _ => false)
                    andalso Type.compare
                      (G.type_of graph bit,Type.bool) = EQUAL)
                    bs andalso Redblackset.numItems unique = width
                  val independent = case anchor of NONE => false
                    | SOME a => Redblackset.isEmpty
                        (Redblackset.intersection
                          (unique,dependencies (#residue a)))
                  val definitions = List.map (fn (i,bit) => List.find
                    (bit_equation word (width-i-1))
                    (get by_name (G.node_id bit)))
                    (ListPair.zip (List.tabulate (width,Lib.I),bs))
                in if dimensions andalso valid_bits andalso independent
                     andalso List.all Option.isSome definitions then
                    SOME (row,Option.valOf anchor,
                      List.map Option.valOf definitions,width)
                   else NONE end
        in if Redblackset.numItems part <= 1 orelse
             Redblackset.numItems distinct <= 1 orelse List.exists self rs
             orelse not (Option.isSome anchor) then []
           else List.mapPartial family rs end
      val discovered = List.concat (List.map candidate
        (Redblackmap.listItems by_name))
      val (_,families) = List.foldl
        (fn (family as (row : E.definition,_,_,_),(seen,kept)) =>
          if has seen (#stored row) then (seen,kept)
          else (Redblackset.add (seen,G.node_id (#stored row)),family :: kept))
        (set (),[]) discovered
      val families = List.rev families
      (* Only selected packed equations, anchors and bit definitions are
         witness operands. Unrelated needed acyclic rows keep their own
         admission contract. Admit before type callbacks or word proof. *)
      val operands = List.concat (List.map
        (fn (row,anchor,bit_rows,_) =>
          packed_operands (row,anchor,bit_rows)) families)
      val _ = List.app (fn node => ignore (size node)) operands
      val packed_ids = Redblackset.addList (set (),List.map
        (fn (row : E.definition,_,_,_) => G.node_id (#stored row)) families)
      val ordinary = List.filter (fn row : E.definition =>
        not (has packed_ids (#stored row))) rows
      val selected = Redblackset.addList (set (),List.map
        (G.node_id o #stored) rows)
      val stable = List.filter (fn node => not (has selected node)
        andalso not (has permitted node)) needed
      (* These inputs are ONLY the fixed public laws and local-variable
         finite templates below, never the actual canonical anchor. Both
         public kernels' term_size traverse syntax without theorem callbacks.
         This fixed-template full traversal is not a general bounded reader. *)
      fun raw term = require (Term.term_size term <= limit)
        "packed fixed-law input exceeds original raw limit"
      (* Fixed public laws and the exact local identity schema are additional
         raw theorem inputs, under the same limit. They do not gain a fresh
         budget. Graph operand admission above still uses the chosen metric. *)
      fun schema (row : E.definition,_,bit_rows,width) =
        let
          val word = G.representative graph (#variable row)
          val index = wordsSyntax.dest_word_type (Term.type_of word)
          val vector = bitstringSyntax.mk_v2w
            (listSyntax.mk_list (List.map
              (G.representative graph o #residue) bit_rows,Type.bool),index)
        in raw (boolSyntax.mk_eq (word,vector));
           raw (bitstringSyntax.mk_w2v word);
           raw (boolSyntax.mk_eq (fcpSyntax.mk_dimindex index,
             numSyntax.term_of_int width));
           raw (boolSyntax.mk_eq (bitstringSyntax.mk_v2w
             (bitstringSyntax.mk_w2v word,index),word)) end
      val _ = if null families then () else
        (raw (Thm.concl bitstringTheory.v2w_w2v);
         raw (Thm.concl bitstringTheory.w2v_def);
         raw (Thm.concl wordsTheory.word_bit);
         List.app schema families;
         List.app (check_type o G.type_of graph)
           (G.reachable graph operands))
      fun run () = case unify_bounded graph scope allocated limit
          (List.map (fn row : E.definition =>
            (#variable row,#residue row)) ordinary) of
          U.NoMatch failure => UnificationRefused failure
        | U.Unified unification =>
            (U.validate_result graph scope unification;
             case prepare_bounded graph scope limit {flexible = allocated,
               assignments = U.assignments unification,
               roots = roots @ sources @ U.roots unification,
               preserved = preserved @ stable} of
               R.Refused failure => ResolutionRefused failure
             | R.Resolved resolution => let
                 val resolution = R.record_assignment_sources resolution
                   (List.map #stored ordinary)
                 (* Every current equation is admitted before the first
                    type callback or fixed word-identity witness operation. *)
                 val currents = List.map
                   (fn (row : E.definition,_,_,_) =>
                     R.node resolution (#stored row)) families
                 val _ = List.app (fn node => ignore (size node)) currents
                 val _ = List.app (check_type o G.type_of graph)
                   (G.reachable graph currents)
                 fun identity (row : E.definition,anchor,bit_rows,width) =
                   let
                     val current = R.node resolution (#stored row)
                     val word = R.node resolution (#variable row)
                     val original_word = G.representative graph (#variable row)
                     val index_type = wordsSyntax.dest_word_type
                       (G.type_of graph (#variable row))
                     val dimension = fcpLib.DIMINDEX (Arbnum.fromInt width)
                     val unpacked = bitstringSyntax.mk_w2v original_word
                     val _ = require (Term.is_var original_word)
                       "packed template operand is not a compact variable"
                     val _ = raw unpacked
                     val opening = Conv.REWR_CONV bitstringTheory.w2v_def
                       unpacked
                     val _ = raw (Thm.concl opening)
                     val length = Conv.RAND_CONV (Conv.REWR_CONV dimension)
                       (Lib.snd (boolSyntax.dest_eq (Thm.concl opening)))
                     val _ = raw (Thm.concl length)
                     val expanded = listLib.GENLIST_CONV
                       (packed_element dimension)
                       (Lib.snd (boolSyntax.dest_eq (Thm.concl length)))
                     val _ = raw (Thm.concl expanded)
                     val unpacked = Thm.TRANS opening
                       (Thm.TRANS length expanded)
                     val identity = Drule.ISPEC original_word
                       bitstringTheory.v2w_w2v
                     val head = Term.rator (Lib.fst
                       (boolSyntax.dest_eq (Thm.concl identity)))
                     val packed = Thm.AP_TERM head unpacked
                     val law = Thm.SYM (Thm.TRANS (Thm.SYM packed) identity)
                     val _ = raw (Thm.concl law)
                     (* All type specialization, GENLIST beta/LET expansion
                        and word_bit rewriting above use only the original
                        small flexible variable. Insert the actual resolved
                        anchor only after this explicit no-binder boundary. *)
                     val _ = check_instantiation_template limit law
                     val law = Thm.INST
                       [{redex = original_word,
                         residue = G.representative graph word}] law
                     val law = if #name_on_left row then law else Thm.SYM law
                     val law = Thm.EQ_MP (Thm.ALPHA (Thm.concl law)
                       (G.representative graph current)) law
                     val (tags,_) = Tag.dest_tag (Thm.tag law)
                     val _ = require (List.null (Thm.hyp law) andalso
                       List.all (fn tag => tag = "DISK_THM") tags andalso
                       List.null (Tag.axioms_of (Thm.tag law)))
                       "packed identity is not closed and clean"
                   in (#stored row,law) end
                 val witnesses = List.map identity families
                 val table = List.foldl (fn ((node,law),table) =>
                   Redblackmap.insert (table,G.node_id node,law))
                   (empty ()) witnesses
                 val images = List.mapPartial (fn (index,node) =>
                   Option.map (fn law => (index,law))
                     (Redblackmap.peek (table,G.node_id node)))
                   (ListPair.zip (List.tabulate (length sources,Lib.I),sources))
               in Resolved {resolution = resolution,images = images,
                    assignments = ordinary} end)
    in if null families then RequiresWitness (E.selection env) else run () end

  (* Separate opt-in: conservative resolve above is exact. *)
  fun resolve_using fresh graph
      {scope,allocated,sources,needed,roots,preserved,laws,
      admission = {metric,limit,check_type}} =
    let
      val _ = require (limit > 0) "nonpositive packed witness limit"
      fun size node = case G.unfolded_nodes graph metric limit node of
          SOME count => if count <= limit then count else raise ERR
            "resolve" "packed witness exceeds original graph limit"
        | NONE => raise ERR "resolve" "unknown packed witness size"
      val env = E.prepare graph {scope = scope,allocated = allocated,
        sources = sources,needed = needed,roots = roots @ preserved}
      val rows = E.definitions env
      val original = Redblackset.addList (set (),List.map G.node_id sources)
      val permitted = List.foldl (fn ((node,proof),ids) =>
        let val (tags,_) = Tag.dest_tag (Thm.tag proof)
        in require (has original node andalso List.null (Thm.hyp proof)
             andalso List.all (fn tag => tag = "DISK_THM") tags andalso
             List.null (Tag.axioms_of (Thm.tag proof)) andalso
             Portable.pointer_eq (Thm.concl proof,
               G.representative graph node)) "original closed law differs";
           Redblackset.add (ids,G.node_id node) end) (set ()) laws
      val rows = List.filter (fn row : E.definition =>
        not (has permitted (#stored row))) rows
      val by_name = List.foldl (fn (row : E.definition,table) =>
        let val id = G.node_id (#variable row) in
          Redblackmap.insert (table,id,row :: get table id) end)
        (empty ()) rows
      val by_name = Redblackmap.map (fn (_,rs) => List.rev rs) by_name
      val names = List.map #1 (Redblackmap.listItems by_name)
      val defined = Redblackset.addList (set (),names)
      val cache = ref (empty ())
      fun dependencies node = case Redblackmap.peek (!cache,G.node_id node) of
          SOME ids => ids
        | NONE => let
            val free = case G.free_variable_nodes graph node of SOME ns => ns
              | NONE => raise ERR "resolve" "unknown packed dependencies"
            val ids = Redblackset.addList (set (),List.map G.node_id free)
            val _ = cache := Redblackmap.insert (!cache,G.node_id node,ids)
          in ids end
      val adjacency = Redblackmap.map (fn (_,rs) =>
        Redblackset.listItems (List.foldl (fn (row : E.definition,ids) =>
          Redblackset.union (ids,Redblackset.intersection
            (defined,dependencies (#residue row)))) (set ()) rs)) by_name
      val parts = components names adjacency
      fun constant node expected = case G.view graph node of G.Constant _ =>
          Term.same_const (G.representative graph node) expected | _ => false
      fun vector node = case G.view graph node of G.Application (head,list) =>
          if constant head bitstringSyntax.v2w_tm then SOME (head,list)
          else NONE | _ => NONE
      fun bits node = if constant node listSyntax.nil_tm then SOME ([],node)
        else case G.view graph node of G.Application (inner,tail) =>
          (case G.view graph inner of G.Application (head,bit) =>
             if constant head listSyntax.cons_tm then
               Option.map (fn (rest,tail_node) => (bit :: rest,tail_node))
                 (bits tail)
             else NONE | _ => NONE)
        | _ => NONE
      fun bit_equation word index (row : E.definition) =
        case G.view graph (#residue row) of G.Application (inner,operand) =>
          (case G.view graph inner of G.Application (head,number) =>
             if constant head wordsSyntax.word_bit_tm andalso operand = word
             then (numSyntax.int_of_term
               (G.representative graph number) = index
               handle Feedback.HOL_ERR _ => false | Overflow => false)
             else false | _ => false)
        | _ => false
      (* A fresh equation is an abstract assignment obligation, never an
         original Source row or an assignment-source authority grant. All
         operands here are original small variables. Actual anchor insertion
         is delayed until the closed implication template is binder-free. *)
      (* Numeric literals have no binder or variable. Construct their finite
         graph structurally; G.import would produce a theorem before the
         generated obligation admission below. This path makes no theorem. *)
      fun numeral_node number =
        let
          val remaining = ref limit
          fun visit term =
            (require (!remaining > 0) "fresh numeral exceeds graph limit";
             remaining := !remaining-1;
             if Term.is_comb term then
               let val (operator,operand) = Term.dest_comb term
               in G.application graph scope (visit operator,visit operand) end
             else if Term.is_const term then G.constant graph scope term
             else raise ERR "resolve" "fresh numeral is not a constant tree")
        in visit number end
      fun new_bit word index =
        let
          val term = G.representative graph word
          val number = numSyntax.term_of_int index
          val bit_term = wordsSyntax.mk_word_bit (number,term)
          val head = G.constant graph scope (Term.rator (Term.rator bit_term))
          val number_node = numeral_node number
        in G.application graph scope
          (G.application graph scope (head,number_node),word) end
      fun equation left right =
        let
          val term = boolSyntax.mk_eq (G.representative graph left,
            G.representative graph right)
          val head = G.constant graph scope (Term.rator (Term.rator term))
        in G.application graph scope
          (G.application graph scope (head,left),right) end
      fun candidate (id,rs : E.definition list) =
        let
          val word = #variable (hd rs)
          val part = Redblackmap.find (parts,id)
          val distinct = Redblackset.addList (set (),
            List.map (G.node_id o #stored) rs)
          fun self (row : E.definition) = has (dependencies (#residue row)) word
          fun outside (row : E.definition) = Redblackset.isEmpty
            (Redblackset.intersection (part,dependencies (#residue row)))
          val anchor = List.find outside rs
          fun family (row : E.definition) = case vector (#residue row) of
              NONE => NONE
            | SOME (_,list) => case bits list of NONE => NONE
              | SOME (bs,_) => let
                  val width = length bs
                  val word_type = G.type_of graph word
                  val vector_type = G.type_of graph (#residue row)
                  val allocated_ids = Redblackset.addList
                    (set (),List.map G.node_id allocated)
                  val unique = Redblackset.addList
                    (set (),List.map G.node_id bs)
                  val numeric = wordsSyntax.is_word_type word_type andalso
                    fcpSyntax.is_numeric_type
                      (wordsSyntax.dest_word_type word_type)
                  val dimensions = numeric andalso width > 0 andalso
                    Type.compare (word_type,vector_type) = EQUAL andalso
                    fcpSyntax.dest_int_numeric_type
                      (wordsSyntax.dest_word_type word_type) = width
                  val valid_bits = List.all (fn bit =>
                    has allocated_ids bit andalso
                    (case G.view graph bit of
                       G.Variable (G.SolverFlexible,_) => true | _ => false)
                    andalso Type.compare
                      (G.type_of graph bit,Type.bool) = EQUAL)
                    bs andalso Redblackset.numItems unique = width
                  fun independent_anchor (a : E.definition) =
                    outside a andalso #stored a <> #stored row andalso
                    Redblackset.isEmpty (Redblackset.intersection
                      (unique,dependencies (#residue a)))
                  val anchor = case List.find (fn a =>
                      independent_anchor a andalso
                      not (Option.isSome (vector (#residue a)))) rs of
                      SOME a => SOME a
                    | NONE => List.find independent_anchor rs
                  val independent = Option.isSome anchor
                  val definitions = List.map (fn (i,bit) => List.find
                    (bit_equation word (width-i-1))
                    (get by_name (G.node_id bit)))
                    (ListPair.zip (List.tabulate (width,Lib.I),bs))
                in if dimensions andalso valid_bits andalso independent
                     andalso List.all Option.isSome definitions then
                    SOME (row,Option.valOf anchor,List.map
                      (fn definition => let val r = Option.valOf definition
                        in (#variable r,#residue r) end) definitions,width)
                   else if fresh andalso dimensions andalso valid_bits
                     andalso independent then
                    SOME (row,Option.valOf anchor,ListPair.map
                      (fn (i,bit) => (bit,new_bit word (width-i-1)))
                      (List.tabulate (width,Lib.I),bs),width)
                   else NONE end
        in if (not fresh andalso Redblackset.numItems part <= 1) orelse
             Redblackset.numItems distinct <= 1 orelse List.exists self rs
             orelse not (Option.isSome anchor) then []
           else List.mapPartial family rs end
      val discovered = List.concat (List.map candidate
        (Redblackmap.listItems by_name))
      val (_,families) = List.foldl
        (fn (family as (row : E.definition,_,_,_),(seen,kept)) =>
          if has seen (#stored row) then (seen,kept)
          else (Redblackset.add (seen,G.node_id (#stored row)),family :: kept))
        (set (),[]) discovered
      val anchors = Redblackset.addList (set (),List.map
        (fn (_,anchor : E.definition,_,_) => G.node_id (#stored anchor))
        families)
      (* Never delete the sole original anchor as another packed family.
         Anchor equations retain original assignment-source authority only. *)
      val families = List.filter
        (fn (row : E.definition,_,_,_) => not (has anchors (#stored row)))
        (List.rev families)
      (* Match the conservative worker's selected original operand boundary.
         Fresh obligations have their separate same-limit admission below. *)
      val operands = List.concat (List.map
        (fn (row,anchor,pairs,_) => packed_operands
          (row,anchor,original_bit_rows by_name pairs)) families)
      val _ = List.app (fn node => ignore (size node)) operands
      val packed_ids = Redblackset.addList (set (),List.map
        (fn (row : E.definition,_,_,_) => G.node_id (#stored row)) families)
      val obligation_pairs = if not fresh then [] else
        List.concat (List.map (fn (_,_,pairs,_) => pairs) families)
      val obligation_nodes = List.map (fn (left,right) => equation left right)
        obligation_pairs
      (* Prospective same-limit graph admission includes every generated
         equation BEFORE any type callback, ASSUME or proof-template work. *)
      val _ = List.app (fn node => ignore (size node)) obligation_nodes
      val ordinary = List.filter (fn row : E.definition =>
        not (has packed_ids (#stored row))) rows
      val selected = Redblackset.addList (set (),List.map
        (G.node_id o #stored) rows)
      val stable = List.filter (fn node => not (has selected node)
        andalso not (has permitted node)) needed
      (* These inputs are ONLY the fixed public laws and local-variable
         finite templates below, never the actual canonical anchor. Both
         public kernels' term_size traverse syntax without theorem callbacks.
         This fixed-template full traversal is not a general bounded reader. *)
      fun raw term = require (Term.term_size term <= limit)
        "packed fixed-law input exceeds original raw limit"
      (* Fixed public laws and the exact local identity schema are additional
         raw theorem inputs, under the same limit. They do not gain a fresh
         budget. Graph operand admission above still uses the chosen metric. *)
      fun schema (row : E.definition,_,bit_rows,width) =
        let
          val word = G.representative graph (#variable row)
          val index = wordsSyntax.dest_word_type (Term.type_of word)
          val vector = bitstringSyntax.mk_v2w
            (listSyntax.mk_list (List.map
              (G.representative graph o #2) bit_rows,Type.bool),index)
          val equations = List.map (fn (bit,residue) => boolSyntax.mk_eq
            (G.representative graph bit,G.representative graph residue))
            bit_rows
          val bit_vector = bitstringSyntax.mk_v2w
            (listSyntax.mk_list (List.map
              (G.representative graph o #1) bit_rows,Type.bool),index)
        in if not fresh then () else
             (List.app raw equations;
              raw (boolSyntax.list_mk_imp
                (equations,boolSyntax.mk_eq (word,bit_vector))));
           raw (boolSyntax.mk_eq (word,vector));
           raw (bitstringSyntax.mk_w2v word);
           raw (boolSyntax.mk_eq (fcpSyntax.mk_dimindex index,
             numSyntax.term_of_int width));
           raw (boolSyntax.mk_eq (bitstringSyntax.mk_v2w
             (bitstringSyntax.mk_w2v word,index),word)) end
      val _ = if null families then () else
        (raw (Thm.concl bitstringTheory.v2w_w2v);
         raw (Thm.concl bitstringTheory.w2v_def);
         raw (Thm.concl wordsTheory.word_bit);
         List.app schema families;
         List.app (check_type o G.type_of graph)
           (G.reachable graph operands))
      fun run () = case unify_bounded graph scope allocated limit
          (List.map (fn row : E.definition =>
            (#variable row,#residue row)) ordinary @ obligation_pairs) of
          U.NoMatch failure => UnificationRefused failure
        | U.Unified unification =>
            (U.validate_result graph scope unification;
             case prepare_bounded graph scope limit {flexible = allocated,
               assignments = U.assignments unification,
               roots = roots @ sources @ obligation_nodes @
                 U.roots unification,
               preserved = preserved @ stable} of
               R.Refused failure => ResolutionRefused failure
             | R.Resolved resolution => let
                 val resolution = R.record_assignment_sources resolution
                   (List.map #stored ordinary)
                 (* Every current equation is admitted before the first
                    type callback or fixed word-identity witness operation. *)
                 val currents = List.map
                   (fn (row : E.definition,_,_,_) =>
                     R.node resolution (#stored row)) families
                 val current_obligations = List.map
                   (R.node resolution) obligation_nodes
                 val _ = List.app (fn node => ignore (size node))
                   (currents @ current_obligations)
                 val _ = List.app (check_type o G.type_of graph)
                   (G.reachable graph (currents @ current_obligations))
                 fun identity (row : E.definition,anchor,bit_rows,width) =
                   let
                     val current = R.node resolution (#stored row)
                     val word = R.node resolution (#variable row)
                     val original_word = G.representative graph (#variable row)
                     val index_type = wordsSyntax.dest_word_type
                       (G.type_of graph (#variable row))
                     val dimension = fcpLib.DIMINDEX (Arbnum.fromInt width)
                     val unpacked = bitstringSyntax.mk_w2v original_word
                     val _ = require (Term.is_var original_word)
                       "packed template operand is not a compact variable"
                     val _ = raw unpacked
                     val opening = Conv.REWR_CONV bitstringTheory.w2v_def
                       unpacked
                     val _ = raw (Thm.concl opening)
                     val length = Conv.RAND_CONV (Conv.REWR_CONV dimension)
                       (Lib.snd (boolSyntax.dest_eq (Thm.concl opening)))
                     val _ = raw (Thm.concl length)
                     val expanded = listLib.GENLIST_CONV
                       (packed_element dimension)
                       (Lib.snd (boolSyntax.dest_eq (Thm.concl length)))
                     val _ = raw (Thm.concl expanded)
                     val unpacked = Thm.TRANS opening
                       (Thm.TRANS length expanded)
                     val identity = Drule.ISPEC original_word
                       bitstringTheory.v2w_w2v
                     val head = Term.rator (Lib.fst
                       (boolSyntax.dest_eq (Thm.concl identity)))
                     val packed = Thm.AP_TERM head unpacked
                     val law = Thm.SYM (Thm.TRANS (Thm.SYM packed) identity)
                     (* Genuine abstract obligations are kernel assumptions
                        only inside this small-variable local proof. DISCH
                        closes all of them before actual operands are inserted.
                        Never append them to P.sources or original laws. *)
                     val equations = List.map (fn (bit,residue) =>
                       boolSyntax.mk_eq (G.representative graph bit,
                         G.representative graph residue)) bit_rows
                     val law = if not fresh then law else let
                       val bit_proofs = List.map Thm.ASSUME equations
                       val nil_term = listSyntax.mk_nil Type.bool
                       val cons = Term.rator (Term.rator
                         (listSyntax.mk_cons (boolSyntax.T,nil_term)))
                       val list_proof = List.foldr
                         (fn (proof,tail) => Thm.MK_COMB
                           (Thm.MK_COMB (Thm.REFL cons,proof),tail))
                         (Thm.REFL nil_term) bit_proofs
                       val vector_head = Term.rator
                         (bitstringSyntax.mk_v2w (nil_term,index_type))
                       val vector_proof = Thm.MK_COMB
                         (Thm.REFL vector_head,list_proof)
                       val conditional = Thm.TRANS law
                         (Thm.SYM vector_proof)
                       val closed = List.foldr
                         (fn (assumption,proof) => Thm.DISCH assumption proof)
                         conditional equations
                     in closed end
                     val _ = raw (Thm.concl law)
                     (* All type specialization, GENLIST beta/LET expansion
                        and word_bit rewriting above use only the original
                        small flexible variable. Insert the actual resolved
                        anchor only after this explicit no-binder boundary. *)
                     val _ = check_instantiation_template limit law
                     val substitutions =
                       {redex = original_word,
                        residue = G.representative graph word} ::
                       (if not fresh then [] else List.map
                         (fn (bit,_) => {redex = G.representative graph bit,
                           residue = G.representative graph
                             (R.node resolution bit)}) bit_rows)
                     val law = Thm.INST substitutions law
                     fun discharge ((bit,residue),proof) =
                       let
                         val left = R.node resolution bit
                         val right = R.node resolution residue
                         val target = R.node resolution (equation bit residue)
                         val _ = require (left = right)
                           "fresh bit obligation is not pointer-reflexive"
                         val reflexive = Thm.REFL
                           (G.representative graph left)
                         val exact = Thm.EQ_MP (Thm.ALPHA
                           (Thm.concl reflexive)
                           (G.representative graph target)) reflexive
                       in Thm.MP proof exact end
                     val law = if not fresh then law else
                       List.foldl discharge law bit_rows
                     val law = if #name_on_left row then law else Thm.SYM law
                     val law = Thm.EQ_MP (Thm.ALPHA (Thm.concl law)
                       (G.representative graph current)) law
                     val (tags,_) = Tag.dest_tag (Thm.tag law)
                     val _ = require (List.null (Thm.hyp law) andalso
                       List.all (fn tag => tag = "DISK_THM") tags andalso
                       List.null (Tag.axioms_of (Thm.tag law)))
                       "packed identity is not closed and clean"
                   in (#stored row,law) end
                 val witnesses = List.map identity families
                 val table = List.foldl (fn ((node,law),table) =>
                   Redblackmap.insert (table,G.node_id node,law))
                   (empty ()) witnesses
                 val images = List.mapPartial (fn (index,node) =>
                   Option.map (fn law => (index,law))
                     (Redblackmap.peek (table,G.node_id node)))
                   (ListPair.zip (List.tabulate (length sources,Lib.I),sources))
               in Resolved {resolution = resolution,images = images,
                    assignments = ordinary} end)
    in if null families then RequiresWitness (E.selection env) else run () end
  fun resolve_with_fresh_bits graph inputs =
    resolve_using true graph inputs
end
