(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtReplayGroundDefinitions :> SmtReplayGroundDefinitions =
struct
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "SmtReplayGroundDefinitions"
  exception Declined
  type step = {node : G.node, children : G.node list,
               input : Term.term, result : Term.term, reduce : bool}
  type obligation = {root : G.node, steps : step list}
  datatype plan = Plan of
    {graph : G.graph, scope : G.scope, allocated : G.node list,
     sources : G.node list,
     needed : G.node list, definitions : G.node list,
     obligations : obligation list,limit : int}
  datatype task = Enter of G.node | Leave of G.node
  fun empty () = Redblackmap.mkDict Int.compare
  fun boolean value = if value then boolSyntax.T else boolSyntax.F
  fun bool_value term =
    if Term.is_const term andalso Term.same_const term boolSyntax.T
      then SOME true
    else if Term.is_const term andalso Term.same_const term boolSyntax.F
      then SOME false
    else NONE
  fun natural term = if numSyntax.is_numeral term then
      SOME (numSyntax.dest_numeral term) else NONE
  fun integer term = if intSyntax.is_int_literal term then
      SOME (intSyntax.int_of_term term) else NONE
  fun same_constant term theory name = Term.is_const term andalso
    let val id = Term.dest_thy_const term in
      #Thy id = theory andalso #Name id = name end
  (* Prospective output syntax only. The public computation remains the
     semantic authority; this metadata never becomes a theorem or adapter. *)
  fun lower term =
    let
      val (head,args) = boolSyntax.strip_comb term
      fun unary_bool operation = case args of [arg] =>
          Option.map (boolean o operation) (bool_value arg) | _ => NONE
      fun binary_bool operation = case args of [left,right] =>
          (case (bool_value left,bool_value right) of
             (SOME a,SOME b) => SOME (boolean (operation (a,b)))
           | _ => NONE) | _ => NONE
      fun binary_num operation = case args of [left,right] =>
          (case (natural left,natural right) of
             (SOME a,SOME b) => SOME (numSyntax.mk_numeral (operation (a,b)))
           | _ => NONE) | _ => NONE
      fun unary_int operation = case args of [arg] =>
          Option.map (intSyntax.term_of_int o operation) (integer arg)
        | _ => NONE
      fun binary_int operation = case args of [left,right] =>
          (case (integer left,integer right) of
             (SOME a,SOME b) => SOME (intSyntax.term_of_int (operation (a,b)))
           | _ => NONE) | _ => NONE
      fun compare_int operation = case args of [left,right] =>
          (case (integer left,integer right) of
             (SOME a,SOME b) => SOME (boolean (operation (a,b)))
           | _ => NONE) | _ => NONE
      fun compare_num operation = case args of [left,right] =>
          (case (natural left,natural right) of
             (SOME a,SOME b) => SOME (boolean (operation (a,b)))
           | _ => NONE) | _ => NONE
    in
      if same_constant head "bool" "~" then unary_bool not
      else if same_constant head "bool" "/\\" then
        binary_bool (fn (a,b) => a andalso b)
      else if same_constant head "bool" "\\/" then
        binary_bool (fn (a,b) => a orelse b)
      else if same_constant head "min" "==>" then
        binary_bool (fn (a,b) => not a orelse b)
      else if same_constant head "min" "=" then
        (case args of [left,right] =>
           if Portable.pointer_eq (left,right) then SOME boolSyntax.T
           else (case (natural left,natural right) of
               (SOME a,SOME b) => SOME (boolean (Arbnum.compare (a,b) = EQUAL))
             | _ => (case (integer left,integer right) of
                 (SOME a,SOME b) => SOME
                   (boolean (Arbint.compare (a,b) = EQUAL))
               | _ => (case (bool_value left,bool_value right) of
                   (SOME a,SOME b) => SOME (boolean (a = b)) | _ => NONE)))
         | _ => NONE)
      else if same_constant head "bool" "COND" then
        (case args of [condition,left,right] =>
           if (Option.isSome (natural left) andalso
               Option.isSome (natural right)) orelse
              (Option.isSome (integer left) andalso
               Option.isSome (integer right)) orelse
              (Option.isSome (bool_value left) andalso
               Option.isSome (bool_value right)) then
             Option.map (fn yes => if yes then left else right)
               (bool_value condition) else NONE | _ => NONE)
      else if same_constant head "arithmetic" "+" then binary_num Arbnum.+
      else if same_constant head "arithmetic" "*" then binary_num Arbnum.*
      else if same_constant head "arithmetic" "-" then
        binary_num (fn (a,b) => if Arbnum.< (a,b) then Arbnum.zero
          else Arbnum.- (a,b))
      else if same_constant head "num" "SUC" then
        (case args of [arg] => Option.map
          (numSyntax.mk_numeral o Arbnum.plus1) (natural arg) | _ => NONE)
      else if same_constant head "prim_rec" "<" then compare_num Arbnum.<
      else if same_constant head "arithmetic" "<=" then compare_num Arbnum.<=
      else if same_constant head "arithmetic" ">" then compare_num Arbnum.>
      else if same_constant head "arithmetic" ">=" then compare_num Arbnum.>=
      else if same_constant head "integer" "int_of_num" then
        (case args of [arg] => Option.map
          (intSyntax.term_of_int o Arbint.fromNat) (natural arg) | _ => NONE)
      else if same_constant head "integer" "int_neg" then unary_int Arbint.~
      else if same_constant head "integer" "ABS" then unary_int Arbint.abs
      else if same_constant head "integer" "int_add" then binary_int Arbint.+
      else if same_constant head "integer" "int_sub" then binary_int Arbint.-
      else if same_constant head "integer" "int_mul" then binary_int Arbint.*
      else if same_constant head "integer" "int_min" then binary_int Arbint.min
      else if same_constant head "integer" "int_max" then binary_int Arbint.max
      else if same_constant head "integer" "int_lt" then compare_int Arbint.<
      else if same_constant head "integer" "int_le" then compare_int Arbint.<=
      else if same_constant head "integer" "int_gt" then compare_int Arbint.>
      else if same_constant head "integer" "int_ge" then compare_int Arbint.>=
      else NONE
    end

  (* Exact CHR literals are restricted to the proved 0..255 range.
     CHR outside that range is not modular arithmetic and is never guessed. *)
  fun character term =
    if Term.is_comb term then let
      val (head,arg) = Term.dest_comb term
    in if same_constant head "string" "CHR" then
        (case natural arg of SOME value =>
           if Arbnum.< (value,Arbnum.fromInt 256) then SOME value else NONE
         | NONE => NONE)
      else NONE end else NONE
  fun lower_character term = case lower term of SOME result => SOME result
    | NONE => let
        val (head,args) = boolSyntax.strip_comb term
        fun compare operation = case args of [left,right] =>
            (case (character left,character right) of
               (SOME a,SOME b) => SOME (boolean (operation (a,b)))
             | _ => NONE) | _ => NONE
      in
        if same_constant head "string" "ORD" then
          (case args of [arg] => Option.map numSyntax.mk_numeral
            (character arg) | _ => NONE)
        else if same_constant head "min" "=" then
          compare (fn (a,b) => Arbnum.compare (a,b) = EQUAL)
        else if same_constant head "string" "char_lt" then compare Arbnum.<
        else if same_constant head "string" "char_le" then compare Arbnum.<=
        else if same_constant head "string" "char_gt" then compare Arbnum.>
        else if same_constant head "string" "char_ge" then compare Arbnum.>=
        else if same_constant head "bool" "COND" then
          (case args of [condition,left,right] =>
             if Option.isSome (character left) andalso
                Option.isSome (character right) then
               Option.map (fn yes => if yes then left else right)
                 (bool_value condition) else NONE | _ => NONE)
        else NONE
      end

  fun visible graph scope node =
    (ignore (G.type_of graph node);
     if G.scope_visible graph scope (G.node_scope graph node) then () else
       raise ERR "prepare" "foreign or retired Source")
  fun active (Plan {graph,scope,allocated,sources,needed,definitions,...}) =
    (G.validate_scope graph scope;
     List.app (visible graph scope) (allocated @ sources @ needed @ definitions))
  fun prepare_portfolio graph
      {scope,allocated,sources,needed,definitions,recorded,characters,limit} =
    let
      val _ = G.validate_scope graph scope
      val _ = if limit > 0 then () else
        raise ERR "prepare" "nonpositive ground operand limit"
      val _ = List.app (visible graph scope)
        (allocated @ sources @ needed @ definitions)
      val _ = List.app (fn node => if
        Type.compare (G.type_of graph node,Type.bool) = EQUAL then () else
          raise ERR "prepare" "Source is not Boolean") sources
      val ids = Redblackset.addList (Redblackset.empty Int.compare,
        List.map G.node_id sources)
      val _ = List.app (fn node => if
        Redblackset.member (ids,G.node_id node) then () else
          raise ERR "prepare" "needed node is not an original Source") needed
      val _ = List.app (fn node => if
        Redblackset.member (ids,G.node_id node) then () else
          raise ERR "prepare" "definition is not an original Source")
        definitions
      val definition_ids = Redblackset.addList
        (Redblackset.empty Int.compare,List.map G.node_id definitions)
      val solver = Redblackset.addList (Redblackset.empty Int.compare,
        List.map G.node_id allocated)
      val _ = List.app (fn node => case G.view graph node of
          G.Variable (G.SolverFlexible,_) => ()
        | _ => raise ERR "prepare" "allocation is not SolverFlexible")
        allocated
      fun allocated_endpoint node =
        Redblackset.member (solver,G.node_id node)
      fun oriented node = case G.view graph node of
          G.Application (inner,right) =>
            (case G.view graph inner of G.Application (head,left) =>
               same_constant (G.representative graph head) "min" "=" andalso
               (allocated_endpoint left orelse allocated_endpoint right)
             | _ => false)
        | _ => false
      fun literal node =
        Option.isSome (natural (G.representative graph node)) orelse
        Option.isSome (integer (G.representative graph node))
      fun obligation root =
        let
          (* New opt-in family: cached original metrics precede ALL numeric
             and character syntax callbacks in this nodewise obligation. *)
          val _ = if characters then List.app (fn metric =>
            case G.unfolded_nodes graph metric limit root of
              SOME size => if size <= limit then () else
                raise ERR "prepare" "original ground Source exceeds limit"
            | NONE => raise Declined)
              [G.RawNodes,G.BinderInclusiveNodes] else ()
          val table = ref (empty ())
          val order = ref ([] : step list)
          fun saved node = Redblackmap.find (!table,G.node_id node)
          fun insert (step : step) =
            (table := Redblackmap.insert (!table,G.node_id (#node step),step);
             order := step :: !order)
          fun visit [] = ()
            | visit (Enter node :: rest) =
                if Option.isSome (Redblackmap.peek (!table,G.node_id node))
                  then visit rest
                else if literal node then
                  (insert {node = node,children = [],
                    input = G.representative graph node,
                    result = G.representative graph node,reduce = false};
                   visit rest)
                else (case G.view graph node of
                    G.Application (left,right) =>
                      visit (Enter left :: Enter right :: Leave node :: rest)
                  | G.Constant _ =>
                      (insert {node = node,children = [],
                        input = G.representative graph node,
                        result = G.representative graph node,reduce = false};
                       visit rest)
                  | G.Variable _ =>
                      (insert {node = node,children = [],
                        input = G.representative graph node,
                        result = G.representative graph node,reduce = false};
                       visit rest)
                  | _ => raise Declined)
            | visit (Leave node :: rest) =
                if Option.isSome (Redblackmap.peek (!table,G.node_id node))
                  then visit rest
                else (case G.view graph node of
                    G.Application (left,right) => let
                      val input = Term.mk_comb
                        (#result (saved left),#result (saved right))
                      val lowered = if characters then lower_character input
                        else lower input
                      val result = case lowered of NONE => input
                        | SOME value => value
                    in insert {node = node,children = [left,right],
                      input = input,result = result,
                      reduce = Option.isSome lowered};visit rest end
                  | _ => raise ERR "prepare" "unexpected nodewise stage")
          val _ = visit [Enter root]
        in if bool_value (#result (saved root)) = SOME true then
            SOME {root = root,steps = List.rev (!order)} else NONE end
        handle Declined => NONE
      (* Non-oriented includes nonclosed identities, as in legacy EVAL.
         Never discharge merely because metadata calls something ground. *)
      val candidates = List.filter (fn node => not (oriented node) andalso
        (not recorded orelse
         Redblackset.member (definition_ids,G.node_id node))) needed
      val obligations = List.mapPartial obligation candidates
      (* Every successful step is built from literal, constant, variable and
         application nodes. Literal predicates expose only injection/negation
         and numeral constructors, never abstractions. The explicit walk
         enforces that induction even if a later lowering recipe changes.
         Raw and binder-inclusive counts coincide on this binder-free slice;
         no public Beta/REFL call is hidden in admission. *)
      fun admit_term term =
        let fun walk ([],_) = ()
              | walk (current :: rest,count) =
                  if count >= limit then
                    raise ERR "prepare" "ground operator operand exceeds limit"
                  else if Term.is_comb current then
                    let val (left,right) = Term.dest_comb current in
                      walk (left :: right :: rest,count+1) end
                  else if Term.is_const current orelse Term.is_var current then
                    walk (rest,count+1)
                  else raise ERR "prepare"
                    "ground operator operand needs recorded binder metadata"
        in walk ([term],0) end
      fun admit ({root,steps} : obligation) =
        (List.app (fn metric =>
          case G.unfolded_nodes graph metric limit root of
            SOME size => if size <= limit then () else
              raise ERR "prepare" "original ground Source exceeds limit"
          | NONE => raise ERR "prepare" "unknown original ground Source size")
           [G.RawNodes,G.BinderInclusiveNodes];
         List.app (fn ({input,result,...} : step) =>
           (admit_term input;admit_term result)) steps)
      val _ = List.app admit obligations
    in Plan {graph = graph,scope = scope,allocated = allocated,
      sources = sources,needed = needed,definitions = definitions,
      obligations = obligations,limit = limit} end

  (* Compatibility route retains its historical broad Source portfolio.
     It is not an exact legacy definition-category producer. *)
  fun prepare graph {scope,allocated,sources,needed,limit} =
    prepare_portfolio graph {scope = scope,allocated = allocated,
      sources = sources,needed = needed,definitions = [],recorded = false,
      characters = false,limit = limit}
  (* The caller must supply retained original definition occurrences; Source
     membership alone checks identity, not parser provenance. No new parser
     or old Z3 entry route is silently given that authority. *)
  fun prepare_recorded graph {scope,allocated,sources,needed,definitions,limit} =
    prepare_portfolio graph {scope = scope,allocated = allocated,
      sources = sources,needed = needed,definitions = definitions,
      recorded = true,characters = false,limit = limit}

  (* Separate opt-in route. It retains the same original definition-only
     needed portfolio and does not install a new parser/category authority. *)
  fun prepare_recorded_characters graph
      {scope,allocated,sources,needed,definitions,limit} =
    prepare_portfolio graph {scope = scope,allocated = allocated,
      sources = sources,needed = needed,definitions = definitions,
      recorded = true,characters = true,limit = limit}

  fun clean proof =
    let val (tags,_) = Tag.dest_tag (Thm.tag proof) in
      List.null (Thm.hyp proof) andalso
      List.null (Tag.axioms_of (Thm.tag proof)) andalso
      List.all (fn tag => tag = "DISK_THM") tags end
  fun execute (plan as Plan {graph,obligations,limit,...}) {check_type} =
    let
      val _ = active plan
      val _ = List.app (fn ({steps,...} : obligation) =>
        List.app (fn ({input,result,...} : step) =>
          (check_type (Term.type_of input);check_type (Term.type_of result)))
          steps) obligations
      val _ = active plan
      (* Kernel constructors allocate fresh outer application/equality cells.
         Admit actual returned endpoints BEFORE syntax matching or ALPHA.
         No abstraction is opened and no semantic conversion is attempted. *)
      fun admit_endpoint term =
        let fun walk [] count = ()
              | walk (term :: rest) count =
                  if count >= limit then raise Declined
                  else if Term.is_abs term then raise Declined
                  else if Term.is_comb term then
                    let val (operator,operand) = Term.dest_comb term in
                      walk (operator :: operand :: rest) (count+1) end
                  else if Term.is_var term orelse Term.is_const term then
                    walk rest (count+1)
                  else raise Declined
        in walk [term] 0 end
      fun syntax_pair left right =
        let
          fun walk [] count = ()
            | walk ((left,right) :: rest) count =
                if count >= limit then raise Declined
                else if Portable.pointer_eq (left,right) then
                  walk rest (count+1)
                else if Term.is_comb left andalso Term.is_comb right then
                  let val (lf,lx) = Term.dest_comb left
                      val (rf,rx) = Term.dest_comb right
                  in walk ((lf,rf) :: (lx,rx) :: rest) (count+1) end
                else if Term.is_var left andalso Term.is_var right then
                  let val (ln,lt) = Term.dest_var left
                      val (rn,rt) = Term.dest_var right
                  in if ln = rn andalso Type.compare (lt,rt) = EQUAL then
                       walk rest (count+1) else raise Declined end
                else if Term.is_const left andalso Term.is_const right then
                  if Term.same_const left right andalso Type.compare
                      (Term.type_of left,Term.type_of right) = EQUAL then
                    walk rest (count+1) else raise Declined
                else raise Declined
        in walk [(left,right)] 0 end
      fun align expected_left expected_right theorem =
        let
          val (left,right) = boolSyntax.dest_eq (Thm.concl theorem)
          val _ = List.app admit_endpoint
            [left,right,expected_left,expected_right]
          val _ = syntax_pair left expected_left
          val _ = syntax_pair right expected_right
          val equality = boolSyntax.mk_eq (expected_left,expected_right)
          (* The equality wrapper is a fixed three-node skeleton over four
             already admitted endpoints, not a new operand-size cutoff. *)
        in Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem) equality) theorem end
      fun run ({root,steps} : obligation) =
        let
          val proofs = ref (empty ())
          fun proof node = Redblackmap.find (!proofs,G.node_id node)
          fun step ({node,children,input,result,reduce} : step) =
            let
              val congruence = case children of [] =>
                    Thm.REFL (G.representative graph node)
                | [left,right] => Thm.MK_COMB (proof left,proof right)
                | _ => raise ERR "execute" "incorrect child schema"
              (* Only the actual recorded constructor may justify this
                 bridge. Existing child proofs already retain exact original
                 and predicted endpoint objects. Graph IDs are not rewrites. *)
              val _ = case (children,G.view graph node) of
                  ([],G.Constant _) => () | ([],G.Variable _) => ()
                | ([],G.Application _) =>
                    if Option.isSome (natural (G.representative graph node))
                      orelse Option.isSome
                        (integer (G.representative graph node)) then ()
                    else raise Declined
                | ([],_) => raise Declined
                | ([left,right],G.Application (f,x)) =>
                    if left = f andalso right = x then () else raise Declined
                | _ => raise Declined
              val congruence = align (G.representative graph node)
                input congruence
              val checked = if not reduce then congruence else let
                  (* An open/compound identity is proved directly. It never
                     enters EVAL as a disguised expanded ground operand. *)
                  val evaluated = if boolSyntax.is_eq input then
                      let val (left,right) = boolSyntax.dest_eq input in
                        if Portable.pointer_eq (left,right) then
                          Drule.EQT_INTRO (Thm.REFL left)
                        else bossLib.EVAL input end
                    else bossLib.EVAL input
                  val _ = if clean evaluated then () else raise Declined
                  val evaluated = align input result evaluated
                in Thm.TRANS congruence evaluated end
              val checked = align (G.representative graph node) result checked
            in proofs := Redblackmap.insert
              (!proofs,G.node_id node,checked) end
          val _ = List.app step steps
          val theorem = Drule.EQT_ELIM (proof root)
          val _ = if clean theorem andalso Portable.pointer_eq
              (Thm.concl theorem,G.representative graph root) then () else
            raise ERR "execute" "closed original Source differs"
        in SOME (root,theorem) end
        handle Declined => NONE
             | Feedback.HOL_ERR error =>
                 if SmtResource.is_resource_gate error then
                   raise Feedback.HOL_ERR error else NONE
      val result = List.mapPartial run obligations
      val _ = active plan
    in result end
end
