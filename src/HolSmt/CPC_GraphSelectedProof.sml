(* Exact native command recipes; checked Support selects actual Hyp before
   lifting. Commands sharing a target retain separate occurrence identities. *)
structure CPC_GraphSelectedProof :> CPC_GraphSelectedProof =
struct
  open SmtReplayGraph SmtReplaySource SmtReplayRules SmtReplaySupport
    CPC_GraphDefinitionHistory
  structure G = SmtReplayGraph
  structure S = SmtReplaySource
  structure Rules = SmtReplayRules
  structure C = SmtReplaySupport
  structure Parser = CPC_ProofParser
  type input =
    {index : int,node : G.node,command_occurrence : int option}
  exception Adapter
  val ERR = Feedback.mk_HOL_ERR "CPC_GraphSelectedProof"
  structure A = CPC_GraphNativeAdmission
  val node = A.node
  val recipe = A.recipe
  val occurrence = A.occurrence
  fun discover_prepared
      {graph,scope,proof : Parser.graph_proof,sources,admission,
       equations : CPC_GraphDefinitionHistory.occurrence list,
       template_limit,check_type} =
    let
      val _ = A.bind admission {graph = graph,scope = scope,proof = proof,
        sources = sources,template_limit = template_limit,
        check_type = check_type}
      val canonical = S.assumption_nodes sources @ [S.denied_goal_node sources]
      val falsehood = G.constant graph scope boolSyntax.F
      val root = A.root admission
      val obligations = A.obligations admission
      val all = A.roots admission
      val _ = if null obligations then () else
        let
          val canonical_index = List.foldl (fn (node,index) =>
            Redblackmap.insert (index,G.node_id node,node))
            (Redblackmap.mkDict Int.compare) canonical
          val equation_index = Portable.HOLSusp.delay (fn () =>
            List.foldl
              (fn ({serial,source,...} : CPC_GraphDefinitionHistory.occurrence,
                   index) =>
                Redblackmap.update (index,(serial,G.node_id source),
                  fn entries => source :: Option.getOpt (entries,[])))
              (Redblackmap.mkDict (Lib.pair_compare (Int.compare,Int.compare)))
              equations)
          fun check_origin (serial,target) =
            let val id = G.node_id target
            in
              if Redblackmap.peek (canonical_index,id) = SOME target orelse
                 List.exists (fn source => source = target) (Option.getOpt
                   (Redblackmap.peek
                     (Portable.HOLSusp.force equation_index,(serial,id)),[]))
              then () else raise ERR "command" "missing actual equation origin"
            end
        in List.app check_origin obligations end
      val count = length canonical
      fun prove ({name,constructor,premise} : C.discovery) =
        let
          (* One memo per discovery and one key per captured command
             occurrence. Equal targets never identify distinct commands. *)
          val memo = ref
            (Redblackmap.mkDict Int.compare : (int,Thm.thm) Redblackmap.dict)
          fun visit fact =
            let val serial = occurrence fact in
              case Redblackmap.peek (!memo,serial) of SOME proof => proof
              | NONE =>
                let
                  val proof = case recipe fact of
                      A.Original index => premise index
                    | A.Pending index => premise (count+index)
                    | A.Reflexive operand => Thm.EQ_MP
                        (Thm.SYM (constructor (node fact)))
                        (Thm.REFL (name operand))
                    | A.Symmetric source =>
                        let val equality = Thm.EQ_MP
                              (constructor (node source)) (visit source)
                        in Thm.EQ_MP (Thm.SYM (constructor (node fact)))
                          (Thm.SYM equality) end
                    | A.Conjunction (left,right) =>
                        Thm.EQ_MP (Thm.SYM (constructor (node fact)))
                          (Thm.CONJ (visit left) (visit right))
                    | A.Selection (index,source) =>
                        let val conjunction = Thm.EQ_MP
                              (constructor (node source)) (visit source)
                        in if index = 0 then Thm.CONJUNCT1 conjunction
                          else Thm.CONJUNCT2 conjunction end
                    | A.Contradiction (positive,negative) =>
                        let val positive_proof = visit positive
                            val negative_proof = Thm.EQ_MP
                              (constructor (node negative)) (visit negative)
                            val contradiction = Thm.MP
                              (Thm.NOT_ELIM negative_proof) positive_proof
                        in Thm.EQ_MP (Thm.SYM (constructor falsehood))
                          contradiction end
                  val _ = memo := Redblackmap.insert (!memo,serial,proof)
                in proof end
            end
        in visit root end
      val count_sources = length canonical+length obligations
      val definitions = List.mapPartial (fn node => case G.view graph node of
          G.Constant _ => SOME 5 | G.Application _ => SOME 7 | _ => NONE)
        (G.block_reachable graph all)
      val context = if null definitions then 1 else
        List.foldl (op +) 0 definitions+3*(length definitions-1)
      val _ = if context+4+3*count_sources <= template_limit then () else
        raise Adapter
      val certificate = C.discover graph scope
        {roots = all,premises = canonical @ List.map #2 obligations,
         target = falsehood,template_limit = template_limit,
         check_type = check_type,prove = prove}
      val inputs = Lib.mapi (fn index => fn node =>
          {index = index,node = node,command_occurrence = NONE}) canonical @
        Lib.mapi (fn index => fn (serial,node) =>
          {index = count+index,node = node,command_occurrence = SOME serial})
          obligations
    in {certificate = certificate,inputs = inputs} end
    handle A.Adapter => raise Adapter
  fun discover
      {graph,scope,proof,sources,equations,template_limit,check_type} =
    discover_prepared {graph = graph,scope = scope,proof = proof,
      sources = sources,equations = equations,template_limit = template_limit,
      check_type = check_type,admission = A.prepare
        {graph = graph,scope = scope,proof = proof,sources = sources,
         template_limit = template_limit,check_type = check_type}}
    handle A.Adapter => raise Adapter
end
