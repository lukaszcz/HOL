structure SmtLib_GraphGuardedBagPolicy
  :> SmtLib_GraphGuardedBagPolicy =
struct
  open SmtReplayGraph SmtLib_GraphNativeOrderedValidation bagSyntax
    SmtLib_GraphGuardedCarrierCancel SmtLib_GraphGuardedBagCarrier
    SmtLib_GraphWordEntanglement
  structure G = SmtReplayGraph
  structure V = SmtLib_GraphNativeOrderedValidation
  structure W = SmtLib_GraphWordEntanglement
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphGuardedBagPolicy"
  datatype numeric_choice = Skip | TransferAll | TransferExceptBags
    | Unresolved
  exception TypeBudget
  datatype type_work = VisitType of Type.hol_type
    | FinishType of Type.hol_type * Type.hol_type list
  (* Use physical type identity while admitting the complete type grammar.
     Cache saturated unfolded counts so a shared type cannot expand here or
     in the later bounded ordinary type predicates. *)
  fun admit_types limit roots =
    let
      val memo = ref ([] : (Type.hol_type * int) list)
      val visited = ref 0
      fun lookup ty = Option.map #2 (List.find (fn (old,_) =>
        Portable.pointer_eq (old,ty)) (!memo))
      fun save ty count = if count > limit then raise TypeBudget else
        memo := (ty,count) :: !memo
      fun sum [] count = count
        | sum (ty :: rest) count =
            let val size = valOf (lookup ty)
            in if size > limit-count then raise TypeBudget
              else sum rest (count+size) end
      fun loop [] = ()
        | loop (VisitType ty :: rest) =
            if Option.isSome (lookup ty) then loop rest else
              let val _ = if !visited >= limit then raise TypeBudget else
                    visited := !visited+1
              in if Type.is_vartype ty then (save ty 1;loop rest) else
                let val {Args,...} = Type.dest_thy_type ty
                in loop (List.map VisitType Args @
                  FinishType (ty,Args) :: rest) end end
        | loop (FinishType (ty,args) :: rest) =
            (save ty (sum args 1);loop rest)
    in loop (List.map VisitType roots) end
  type options =
    {graph : G.graph,scope : G.scope,preserve_native_bags : bool,
     dag_limit : int,type_limit : int}
  datatype inventory = Inventory of
    {graph : G.graph,scope : G.scope,validation : V.validation,
     choice : numeric_choice,free : G.node list,excluded : G.node list,
     bags : G.node list,evidence : (G.node * G.node) list,gaps : string list,
     words : W.inventory}
  fun active (Inventory {graph,scope,words,...}) =
    (G.validate_scope graph scope;ignore (W.complete words))
  fun choice (value as Inventory {choice,...}) = (active value;choice)
  fun free_numeric_ids (value as Inventory {free,...}) = (active value;free)
  fun excluded_bag_ids (value as Inventory {excluded,...}) =
    (active value;excluded)
  fun bags (value as Inventory {bags,...}) = (active value;bags)
  fun finite_evidence (value as Inventory {evidence,...}) =
    (active value;evidence)
  fun gaps (value as Inventory {gaps,...}) = (active value;gaps)
  fun finite_assembler (value as Inventory {validation,evidence,...})
      block node =
    (active value;
     if List.exists (fn (_,assumption) => assumption = node) evidence then
       V.assembler validation block node else NONE)
  fun guarded_cancel
      (value as Inventory {graph,scope,validation,choice,...})
      (options : SmtLib_GraphGuardedCarrierCancel.options) input =
    let
      val _ = active value
      val _ = G.validate_scope (#graph options) (#scope options)
      val _ = if G.root_scope graph = G.root_scope (#graph options) andalso
          scope = #scope options then () else
        raise ERR "guarded_cancel" "foreign policy graph or scope"
      val current = G.reachable graph (V.processed_denied_goal validation ::
        V.processed_assumptions validation)
      val _ = if List.exists (fn node => node = #body input) current then ()
        else raise ERR "guarded_cancel" "body is not a current checked root"
    in case choice of TransferAll =>
        SmtLib_GraphGuardedCarrierCancel.discover options input
      | TransferExceptBags =>
          SmtLib_GraphGuardedCarrierCancel.discover options input
      | _ => NONE end
  fun carrier_pass (value as Inventory {graph,scope,choice,...})
      (options : SmtLib_GraphGuardedBagCarrier.options) =
    let val _ = active value
        val _ = if G.root_scope graph = G.root_scope (#graph options) then ()
          else raise ERR "carrier_pass" "foreign carrier graph"
        val pass : SmtLib_GraphNativeOrderedConversion.pass =
          {name = "bounded-bag-carrier",propose = fn _ => fn _ => NONE,
           local_witness = fn active => fn node =>
             if G.scope_visible graph active scope then
               SmtLib_GraphGuardedBagCarrier.local_witness
                 options active node
             else raise ERR "carrier_pass" "carrier frame escaped policy"}
    in case choice of TransferAll => SOME pass
      | TransferExceptBags => SOME pass | _ => NONE end
  fun remaining () =
    ["Free numeric SPEC/GEN and guarded post-transfer cleanup",
     "Parsed bag literals and collection fields of arbitrary datatypes",
     "Pointwise bag nonnegative guards and native guarded cancellation",
     "Complete natural/word/type policy beyond the admitted graph subset"]

  fun inspect
      ({graph,scope,preserve_native_bags,dag_limit,type_limit} : options)
      validation =
    let
      val _ = G.validate_scope graph scope
      val _ = if dag_limit > 0 andalso type_limit > 0 then () else
        raise ERR "inspect" "nonpositive DAG contract"
      val assumptions = V.processed_assumptions validation
      val denied = V.processed_denied_goal validation
      val goal = case G.view graph denied of G.Application (_,goal) => goal
        | _ => raise ERR "inspect" "changed checked denied-goal shape"
      val roots = goal :: assumptions
      val _ = List.app (fn node =>
        (ignore (G.type_of graph node);
         if G.scope_visible graph scope (G.node_scope graph node) then () else
           raise ERR "inspect" "current sequent escapes active owner")) roots
      val nodes = G.reachable graph roots
      val _ = if List.length nodes <= dag_limit then () else
        raise ERR "inspect" "complete current sequent exceeds DAG contract"
      val problems = ref ([] : string list)
      fun gap text = if List.exists (fn old => old = text) (!problems) then ()
        else problems := text :: !problems
      val _ = List.app (fn node => case G.view graph node of
          G.OpaqueRetained => gap "Unknown complete sequent dependencies"
        | _ => ()) nodes
      val _ = admit_types type_limit (List.map (G.type_of graph) nodes)
      fun same_type left right = Type.compare (left,right) = EQUAL
      fun bag_type ty = case Lib.total Type.dom_rng ty of
          SOME (_,range) => same_type range numSyntax.num | NONE => false
      fun type_num ty = same_type ty numSyntax.num orelse
        (case Lib.total Type.dom_rng ty of SOME (left,right) =>
           type_num left orelse type_num right | NONE => false)
      fun word_type ty = case Lib.total wordsSyntax.dest_word_type ty of
          SOME _ => true | NONE => false
      fun contains_collection ty = bag_type ty orelse
        (case Lib.total Type.dom_rng ty of SOME (_,range) =>
           same_type range Type.bool
         | NONE => false) orelse
        (not (Type.is_vartype ty) andalso
         List.exists contains_collection (#2 (Type.dest_type ty)))
      fun container ty =
        if Type.is_vartype ty then false else
        let val {Thy,Tyop,...} = Type.dest_thy_type ty
            val arguments = #2 (Type.dest_type ty)
        in if word_type ty then false
           else if Thy = "list" andalso Tyop = "list" then
             List.exists contains_collection arguments
           else if Thy = "min" orelse Thy = "bool" orelse Thy = "num"
               orelse Thy = "integer" orelse Thy = "realax" orelse
               Thy = "words" orelse Thy = "fcp" then
             List.exists container arguments
           else (gap "Uninspected datatype/container collection policy";
             false) end
      val nested = List.exists (container o G.type_of graph) nodes
      (* Strip only the small arity relevant to this policy. Deep application
         spines are not repeatedly flattened or inspected as HOL terms. *)
      fun shape node =
        let fun loop 0 _ _ = NONE
              | loop fuel node arguments = case G.view graph node of
                  G.Application (operator,operand) =>
                    loop (fuel-1) operator (operand :: arguments)
                | G.Constant _ =>
                    let val {Thy,Name,...} = Term.dest_thy_const
                          (G.representative graph node)
                    in SOME (Thy,Name,arguments) end
                | _ => NONE
        in loop 5 node [] end
      fun is_head node thy name = case shape node of
          SOME (actual_thy,actual_name,[]) =>
            actual_thy = thy andalso actual_name = name | _ => false
      fun finite node = case shape node of
          SOME ("bag","FINITE_BAG",[bag]) => SOME (bag,node)
        | _ => NONE
      val evidence = List.mapPartial finite assumptions
      val marked = ref (Redblackmap.mkDict Int.compare)
      fun mark node = if bag_type (G.type_of graph node) then
          marked := Redblackmap.insert (!marked,G.node_id node,node)
        else ()
      fun inspect_node node = case shape node of
          SOME ("bag","BAG_IN",[_,bag]) => mark bag
        | SOME ("bag","BAG_CARD",[bag]) => mark bag
        | SOME ("bag","FINITE_BAG",[bag]) => mark bag
        | SOME ("bag","BAG_INSERT",[_,bag]) => (mark node;mark bag)
        | SOME ("bag",name,[left,right]) =>
            if List.exists (fn wanted => wanted = name)
                ["BAG_UNION","BAG_DIFF","BAG_MERGE","BAG_INTER"] then
              (mark node;mark left;mark right)
            else if name = "SUB_BAG" then (mark left;mark right) else ()
        | SOME ("bag","EMPTY_BAG",[]) => mark node
        | SOME ("min","=",[left,right]) =>
            if bag_type (G.type_of graph left) andalso
                bag_type (G.type_of graph right) then
              (mark left;mark right) else ()
        | _ => ()
      val _ = List.app inspect_node nodes
      val bags = List.map #2 (Redblackmap.listItems (!marked))
      val memo = ref (Redblackmap.mkDict Int.compare)
      datatype work = Visit of G.node | Finish of G.node * G.node list
      fun get node = Redblackmap.find (!memo,G.node_id node)
      fun put node value = memo := Redblackmap.insert
        (!memo,G.node_id node,value)
      fun finite_domain node =
        let val domain = #1 (Type.dom_rng (G.type_of graph node))
        in same_type domain Type.bool orelse
          (case Lib.total wordsSyntax.dest_word_type domain of
             SOME dimension => Lib.can fcpSyntax.dest_numeric_type dimension
           | NONE => false) end
      fun directly_finite node = finite_domain node orelse
        List.exists (fn (bag,_) => bag = node) evidence
      fun children node = case shape node of
          SOME ("bag","BAG_INSERT",[_,tail]) => SOME [tail]
        | SOME ("bag",name,[left,right]) =>
            if List.exists (fn wanted => wanted = name)
                ["BAG_UNION","BAG_DIFF","BAG_MERGE","BAG_INTER"] then
              SOME [left,right] else NONE
        | _ => NONE
      fun loop [] = ()
        | loop (Visit node :: pending) =
            if Option.isSome (Redblackmap.peek (!memo,G.node_id node)) then
              loop pending
            else (case G.view graph node of G.Variable _ =>
                (put node (true,directly_finite node);loop pending)
              | G.AdmittedBinder _ =>
                  (gap "Parsed bag literal policy remains unimplemented";
                   put node (false,false);loop pending)
              | G.OpaqueRetained =>
                  (gap "Opaque bag policy remains unresolved";
                   put node (false,false);loop pending)
              | _ => if is_head node "bag" "EMPTY_BAG" then
                  (put node (true,true);loop pending)
                else case children node of SOME children =>
                  loop (List.map Visit children @
                    Finish (node,children) :: pending)
                | NONE => (put node (false,false);loop pending))
        | loop (Finish (node,children) :: pending) =
            let val values = List.map get children
                val native = List.all #1 values
                val propagated = case (shape node,values) of
                    (SOME ("bag","BAG_DIFF",_),(_,left) :: _) => left
                  | (SOME ("bag","BAG_INTER",_),_) => List.exists #2 values
                  | _ => List.all #2 values
            in put node (native,directly_finite node orelse propagated);
               loop pending end
      val _ = loop (List.map Visit bags)
      val native = not (null bags) andalso not nested andalso
        List.all (fn node => #1 (get node) andalso #2 (get node) andalso
          not (bag_type (#1 (Type.dom_rng (G.type_of graph node))))) bags
      val free_table = ref (Redblackmap.mkDict Int.compare)
      val _ = List.app (fn node => case G.free_variable_nodes graph node of
          NONE => gap "Unknown full sequent free-ID coverage"
        | SOME variables => List.app (fn variable =>
            free_table := Redblackmap.insert
              (!free_table,G.node_id variable,variable)) variables) roots
      val free = List.filter (fn node =>
          same_type (G.type_of graph node) numSyntax.num orelse
          bag_type (G.type_of graph node))
        (List.map #2 (Redblackmap.listItems (!free_table)))
      val _ = List.app (fn node => case G.view graph node of
          G.Variable (G.RigidSource,_) => ()
        | G.Variable (G.Bound,_) => ()
        | _ => gap "Unapproved free numeric declaration kind") free
      val mentions = List.exists (fn node => case G.view graph node of
          G.Variable (_,_) => type_num (G.type_of graph node)
        | G.Constant _ =>
          let val {Thy,Name,...} = Term.dest_thy_const
                (G.representative graph node)
          in type_num (G.type_of graph node) andalso
            (Thy = "arithmetic" andalso List.exists (fn name => name = Name)
              ["*","+","-","<=",">",">=","DIV","EXP","MAX",
               "MIN","MOD"] orelse
             (Thy,Name) = ("num","SUC") orelse
             (Thy,Name) = ("prim_rec","<") orelse
             Thy = "integer" andalso List.exists (fn name => name = Name)
               ["Num","int_of_num","int_exp"] orelse
             (Thy,Name) = ("bag","BAG_CARD") orelse
             (Thy,Name) = ("pred_set","CARD") orelse
             Thy = "realax" andalso List.exists (fn name => name = Name)
               ["NUM_FLOOR","NUM_CEILING"]) end
        | _ => false) nodes
      (* Inspect every actual current root. Word dimensions are not datatype
         collection fields; natural indices and word-derived naturals retain
         the exact ordinary LENGTH exception. Incomplete never proves
         absence. *)
      val words = W.inspect {graph = graph,scope = scope,
        dag_limit = dag_limit,type_limit = type_limit} roots
      val entangled = W.entangled words
      val _ = if W.complete words then () else
        gap "Incomplete owned word/natural dependency inventory"
      val choice = if entangled then Skip else if not (null (!problems)) then
          Unresolved else if not mentions then Skip
        else if preserve_native_bags andalso native then TransferExceptBags
        else TransferAll
      val excluded = if choice = TransferExceptBags then
        List.filter (bag_type o G.type_of graph) free else []
    in Inventory {graph = graph,scope = scope,validation = validation,
      choice = choice,free = free,excluded = excluded,bags = bags,
      evidence = evidence,gaps = List.rev (!problems),words = words} end
    handle TypeBudget => Inventory {graph = graph,scope = scope,
      validation = validation,choice = Unresolved,free = [],excluded = [],
      bags = [],evidence = [],gaps = ["Complete type grammar exceeds quota"],
      words = W.inspect {graph = graph,scope = scope,
        dag_limit = dag_limit,type_limit = type_limit} []}
end
