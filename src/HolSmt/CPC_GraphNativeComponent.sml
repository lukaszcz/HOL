(* Exact public ZERO/INF/NAN laws preserve canonical NaN semantics. *)
structure CPC_GraphNativeComponent :> CPC_GraphNativeComponent =
struct
  open SmtReplayGraph SmtReplayProof SmtReplaySupport SmtReplayRules
    SmtReplayImport smtfloatTheory
  structure G = SmtReplayGraph
  structure P = SmtReplayProof
  structure C = SmtReplaySupport
  structure Rules = SmtReplayRules
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphNativeComponent"
  exception Unsupported
  datatype plan = Plan of
    {graph : G.graph,scope : G.scope,target : G.node,
     certificate : C.certificate,template_limit : int}
  fun active (Plan {graph,scope,...}) = G.validate_scope graph scope
  fun roots (plan as Plan {certificate,...}) =
    (active plan;C.roots certificate)
  fun same node nodes = List.exists (fn other => other = node) nodes
  fun named graph theory name arity node =
    case Rules.spine graph node of SOME (head,args) =>
      if length args = arity andalso Term.same_const head
          (Term.prim_mk_const {Thy = theory,Name = name}) then args
      else raise Unsupported
    | NONE => raise Unsupported
  (* Fixed native schemas are binder-free. No count_body/Beta call. *)
  fun schema_size limit term =
    let fun walk [] n = SOME n
          | walk (term :: rest) n = if n >= limit then NONE else
              if Term.is_abs term then raise Unsupported
              else if Term.is_comb term then
                let val (f,x) = Term.dest_comb term in
                  walk (f :: x :: rest) (n+1) end
              else walk rest (n+1)
    in if limit < 0 then NONE else walk [term] 0 end
  datatype admission = Admission of
    {graph : G.graph,scope : G.scope,execute : unit -> plan}
  fun prepare {graph,scope,target,template_limit,check_type} =
    let
      val _ = G.validate_scope graph scope
      val _ = if template_limit > 0 then () else
        raise ERR "discover" "nonpositive native template limit"
      val (left,right) = case Rules.equality graph target of SOME pair => pair
        | NONE => raise Unsupported
      fun condition node = case named graph "bool" "COND" 3 node of
          [guard,one,zero] => (guard,one,zero)
        | _ => raise Unsupported
      val (predicate,one,zero) = condition left
      val (guard,other_one,other_zero) = condition right
      val (source,law,infinite,nan) =
        case Rules.spine graph predicate of SOME (head,[node]) =>
          if Term.same_const head (Term.prim_mk_const
              {Thy = "smtfloat",Name = "smtfp_is_zero"}) then
            (node,smtfloatTheory.smtfp_is_zero_bits,false,false)
          else if Term.same_const head (Term.prim_mk_const
              {Thy = "smtfloat",Name = "smtfp_is_infinite"}) then
            (node,smtfloatTheory.smtfp_is_infinite_bits,true,false)
          else if Term.same_const head (Term.prim_mk_const
              {Thy = "smtfloat",Name = "smtfp_is_nan"}) then
            (node,smtfloatTheory.smtfp_is_nan_bits,true,true)
          else raise Unsupported
        | _ => raise Unsupported
      val fields = named graph "smtfloat" "smtfp_bits" 3 source
      val (sign,exponent,fraction) = case fields of [s,e,m] => (s,e,m)
        | _ => raise Unsupported
      val (exponent_test,fraction_test) =
        case Rules.operands graph boolSyntax.conjunction 2 guard of
          SOME [e,m] => (e,m) | _ => raise Unsupported
      fun field_test field node = case Rules.equality graph node of
          SOME (actual,zero) => if actual = field then zero
            else raise Unsupported
        | _ => raise Unsupported
      val exponent_zero = field_test exponent exponent_test
      val fraction_comparison = if nan then
          case Rules.operands graph boolSyntax.negation 1 fraction_test of
            SOME [comparison] => comparison | _ => raise Unsupported
        else fraction_test
      val fraction_zero = field_test fraction fraction_comparison
      val literal_roots = [one,zero,other_one,other_zero,
        exponent_zero,fraction_zero]
      val retained_fields = List.filter
        (fn node => not (same node literal_roots)) fields
      val nodes = G.block_reachable graph [target]
      fun visible node =
        if G.scope_visible graph scope (G.node_scope graph node) then () else
          raise ERR "discover" "native component captures an unavailable ID"
      val _ = List.app visible nodes
      val _ = List.app (fn node => case G.view graph node of
          G.OpaqueRetained => raise Unsupported
        | G.AdmittedBinder _ => raise Unsupported
        | G.Variable (G.Bound,_) => raise Unsupported
        | _ => ()) nodes
      (* Exact proof-block context grammar, not unfolded actual operands. *)
      val costs = List.mapPartial (fn node => case G.view graph node of
          G.Constant _ => SOME 5 | G.Application _ => SOME 7
        | _ => NONE) nodes
      val context = if null costs then 1 else
        List.foldl (op +) 0 costs + 3*(length costs-1)
      val sizes = ref (Redblackmap.mkDict Int.compare)
      fun syntax node = if same node retained_fields then 1 else
        case Redblackmap.peek (!sizes,G.node_id node) of SOME n => n
          | NONE =>
              let val n = case G.view graph node of G.Constant _ => 1
                    | G.Application (f,x) =>
                        Int.min (template_limit+1,1+syntax f+syntax x)
                    | _ => raise Unsupported
                  val _ = sizes := Redblackmap.insert
                    (!sizes,G.node_id node,n)
              in n end
      val small_target = syntax target
      fun bound n = if n <= template_limit then () else raise Unsupported
      fun fixed metric = case metric template_limit
          (Thm.concl law) of SOME n => bound n
        | NONE => raise Unsupported
      val _ = List.app fixed [schema_size,
        schema_size]
      (* Rewrite only the fixed schematic NaN RHS. Its sole pattern call
         has two variable operands, so replacing it by the admitted public
         definition adds no more than that whole definition's node count.
         This complete bound precedes actual operand type callbacks. *)
      val nan_definition = smtfloatTheory.smtfp_nan_pattern_def
      val _ = if not nan then () else List.app (fn metric =>
        case (metric template_limit (Thm.concl law),
              metric template_limit (Thm.concl nan_definition)) of
          (SOME left,SOME right) =>
            if 3 + 2*(IntInf.fromInt left + IntInf.fromInt right) <=
                IntInf.fromInt template_limit then () else raise Unsupported
        | _ => raise Unsupported)
        [schema_size,
         schema_size]
      (* All schemas and graph operand names are binder-free here. Both
         complete metrics therefore agree, including prospective ALPHA. *)
      val _ = List.app bound
        [context,context+4,3+2*(context+4),small_target,
         3+2*small_target]
      val _ = List.app (fn node =>
        List.app (fn metric => case G.unfolded_nodes graph metric
            template_limit node of SOME n => bound n
          | NONE => raise Unsupported)
          [G.RawNodes,G.BinderInclusiveNodes]) literal_roots
      val _ = List.app (check_type o G.type_of graph) nodes
      val primitive = SmtWordGraph.new_type_admission ()
      val _ = List.app (SmtWordGraph.admit_primitive_type primitive o
        G.type_of graph) [source,sign,exponent,fraction,left,right]
      fun literal node value ty =
        let val term = G.representative graph node
            val _ = List.app (fn metric => case metric template_limit term of
              SOME _ => () | NONE => raise Unsupported)
              [schema_size,
               schema_size]
        in Type.compare (G.type_of graph node,ty) = EQUAL andalso
          wordsSyntax.is_word_literal term andalso
          wordsSyntax.dest_word_literal term = Arbnum.fromInt value end
      val word1 = ``:word1``
      fun exponent_boundary () = if not infinite then
          literal exponent_zero 0 (G.type_of graph exponent)
        else case G.view graph exponent_zero of G.Constant _ =>
          Term.same_const (G.representative graph exponent_zero)
            (Term.prim_mk_const
            {Thy = "words",Name = "word_T"}) andalso
          Type.compare (G.type_of graph exponent_zero,
            G.type_of graph exponent) = EQUAL
        | _ => false
      val _ = if literal one 1 word1 andalso literal other_one 1 word1 andalso
          literal zero 0 word1 andalso literal other_zero 0 word1 andalso
          exponent_boundary () andalso
          literal fraction_zero 0 (G.type_of graph fraction) then () else
        raise Unsupported
      fun execute () = let
      val _ = G.validate_scope graph scope
      (* Genuine checked law, on fixed schematic fields only. Never rewrite
         or match an expanded actual floating-point source representative. *)
      val law = if nan then Thm.TRANS law
          (Conv.REWR_CONV nan_definition (boolSyntax.rhs (Thm.concl law)))
        else law
      val _ = List.app (fn metric => case metric template_limit
          (Thm.concl law) of SOME n => bound n | NONE => raise Unsupported)
        [SmtReplayImport.bounded_raw_size,
         SmtReplayImport.bounded_binder_size]
      val (zero_pattern,_) = boolSyntax.dest_eq
        (Thm.concl law)
      val (_,source_pattern_args) = boolSyntax.strip_comb zero_pattern
      val source_pattern = case source_pattern_args of [term] => term
        | _ => raise ERR "discover" "unexpected public classification schema"
      fun prove {name,constructor,premise} =
        let
          val memo = ref (Redblackmap.mkDict Int.compare)
          fun expose node = if same node retained_fields then Thm.REFL (name node)
            else case Redblackmap.peek (!memo,G.node_id node) of
                SOME theorem => theorem
              | NONE =>
                  let val theorem = case G.view graph node of
                      G.Constant _ => constructor node
                    | G.Application _ =>
                        (case Rules.spine graph node of SOME (head,args) =>
                          Thm.TRANS (constructor node)
                            (List.foldl (fn (arg,proof) =>
                              Thm.MK_COMB (proof,expose arg))
                              (Thm.REFL head) args)
                        | NONE => raise Unsupported)
                    | _ => raise Unsupported
                      val _ = memo := Redblackmap.insert
                        (!memo,G.node_id node,theorem)
                  in theorem end
          val bits = case Rules.spine graph source of SOME (head,_) => head
            | NONE => raise ERR "discover" "missing owned bits constructor"
          val actual_pattern = List.foldl (fn (node,operator) =>
            Term.mk_comb (operator,
              boolSyntax.rhs (Thm.concl (expose node)))) bits fields
          val classification = Drule.INST_TY_TERM
            (Term.match_term source_pattern actual_pattern)
            law
          val cond = case Rules.spine graph left of SOME (head,_) => head
            | NONE => raise ERR "discover" "missing owned word condition"
          val theorem = Thm.AP_THM (Thm.AP_THM
            (Thm.AP_TERM cond classification)
            (G.representative graph one)) (G.representative graph zero)
          val equation = expose target
          val theorem = Thm.EQ_MP (Thm.ALPHA (Thm.concl theorem)
            (boolSyntax.rhs (Thm.concl equation))) theorem
        in Thm.EQ_MP (Thm.SYM equation) theorem end
      val certificate = C.discover graph scope
        {roots = [target],premises = [],target = target,
         template_limit = template_limit,check_type = check_type,prove = prove}
    in SOME (Plan {graph = graph,scope = scope,target = target,
      certificate = certificate,template_limit = template_limit}) end
      in SOME (Admission {graph = graph,scope = scope,
        execute = fn () => valOf (execute ())}) end
    handle Unsupported => NONE
  fun discover_prepared (Admission {graph,scope,execute}) =
    (G.validate_scope graph scope;execute ())
  fun discover input = case prepare input of NONE => NONE
    | SOME admission => SOME (discover_prepared admission)
    handle Unsupported => NONE
  fun assemble block (plan as Plan {certificate,...}) =
    (active plan;C.assemble block certificate [])
  fun prove input = case discover input of NONE => NONE
    | SOME (plan as Plan {graph,scope,target,template_limit,...}) =>
        let val block = P.freeze graph
              {scope = scope,roots = roots plan,sources = [],
               template_limit = template_limit}
        in SOME (P.realize block target (assemble block plan)) end
end
