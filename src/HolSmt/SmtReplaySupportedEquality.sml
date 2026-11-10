(* Copyright (c) 2026 The HOL4 contributors. *)

structure SmtReplaySupportedEquality :> SmtReplaySupportedEquality =
struct
  open SmtReplayGraph SmtReplayProof SmtReplaySupport
  structure G = SmtReplayGraph
  structure C = SmtReplaySupport
  val ERR = Feedback.mk_HOL_ERR "SmtReplaySupportedEquality"
  type certificate = C.certificate
  val roots = C.roots
  val selected = C.selected
  val assemble = C.assemble

  (* Only the exact two-application HOL equality spine is accepted. No
     representative operand or retained binder is opened here. *)
  fun equality graph node =
    case G.view graph node of
      G.Application (partial,right) =>
        (case G.view graph partial of
           G.Application (operator,left) =>
             (case G.view graph operator of
                G.Constant _ =>
                  if Term.same_const (G.representative graph operator)
                      boolSyntax.equality then (left,right)
                  else raise ERR "equality" "unsupported relation head"
              | _ => raise ERR "equality" "nonconstant relation head")
         | _ => raise ERR "equality" "nonbinary equality")
    | _ => raise ERR "equality" "nonapplication equality"

  datatype work = Visit of G.node * G.node
    | Join of (G.node * G.node) * (G.node * G.node) * (G.node * G.node)
  fun pair_compare ((a,b),(c,d)) =
    case Int.compare (a,c) of EQUAL => Int.compare (b,d) | order => order

  fun native graph rule target premises
      ({name,constructor,premise} : C.discovery) =
    let
      val (left,right) = equality graph target
      val compact = Lib.mapi (fn index => fn node =>
        (equality graph node,
         Thm.EQ_MP (constructor node) (premise index))) premises
      fun immediate node = case G.view graph node of
          G.Application (operator,operand) =>
            Thm.TRANS (constructor node)
              (Thm.SYM (Thm.AP_THM (constructor operator) (name operand)))
        | _ => raise ERR "immediate" "nonapplication constructor"
      fun ordered () =
        let
          fun chain [] expected proof =
                if expected = right then proof else
                  raise ERR "trans" "ordered endpoint mismatch"
            | chain (((a,b),next) :: rest) expected proof =
                if a = expected then chain rest b (Thm.TRANS proof next)
                else raise ERR "trans" "ordered premise mismatch"
        in if null compact then raise ERR "trans" "empty ordered chain"
          else chain compact left (Thm.REFL (name left)) end
      fun symmetric_chain () =
        let
          val neighbors = ref (Redblackmap.mkDict Int.compare)
          fun add (from,to,proof) =
            let val key = G.node_id from in
              neighbors := Redblackmap.insert (!neighbors,key,
                (to,proof) :: Option.getOpt
                  (Redblackmap.peek (!neighbors,key),[])) end
          val _ = List.app (fn ((a,b),proof) =>
            (add (a,b,proof);add (b,a,Thm.SYM proof))) compact
          fun search [] [] _ =
                raise ERR "trans-star" "no symmetric equality path"
            | search [] back seen = search (List.rev back) [] seen
            | search ((node,path) :: rest) back seen =
                if node = right then path else
                  let
                    fun enqueue ((next,proof),(back,seen)) =
                      if Redblackset.member (seen,G.node_id next) then
                        (back,seen)
                      else ((next,Thm.TRANS path proof) :: back,
                        Redblackset.add (seen,G.node_id next))
                    val (back,seen) = List.foldl enqueue (back,seen)
                      (Option.getOpt (Redblackmap.peek
                        (!neighbors,G.node_id node),[]))
                  in search rest back seen end
        in search [(left,Thm.REFL (name left))] []
          (Redblackset.singleton Int.compare (G.node_id left)) end
      fun congruence () =
        let
          val memo = ref (Redblackmap.mkDict pair_compare)
          fun key (a,b) = (G.node_id a,G.node_id b)
          fun save pair proof =
            memo := Redblackmap.insert (!memo,key pair,proof)
          fun saved pair = Redblackmap.find (!memo,key pair)
          fun leaf (a,b) =
            if a = b then SOME (Thm.REFL (name a)) else
              case List.find (fn ((x,y),_) => x = a andalso y = b) compact of
                SOME (_,proof) => SOME proof
              | NONE => Option.map (Thm.SYM o #2)
                  (List.find (fn ((x,y),_) => x = b andalso y = a) compact)
          fun run [] = saved (left,right)
            | run (Visit (pair as (a,b)) :: pending) =
                if Option.isSome (Redblackmap.peek (!memo,key pair)) then
                  run pending else
                (case leaf pair of
                   SOME proof => (save pair proof;run pending)
                 | NONE =>
                     (case (G.view graph a,G.view graph b) of
                        (G.Application (f,x),G.Application (g,y)) =>
                          run (Visit (f,g) :: Visit (x,y) ::
                            Join (pair,(f,g),(x,y)) :: pending)
                      | _ => raise ERR "cong" "unproved congruence leaf"))
            | run (Join (pair as (a,b),operators,operands) :: pending) =
                let val proof = Thm.TRANS (immediate a)
                      (Thm.TRANS
                        (Thm.MK_COMB (saved operators,saved operands))
                        (Thm.SYM (immediate b)))
                in save pair proof;run pending end
        in run [Visit (left,right)] end
      val proof = case rule of
          "refl" => if null premises andalso left = right then
              Thm.REFL (name left) else
                raise ERR "refl" "invalid reflexivity endpoints or premises"
        | "symm" =>
            (case compact of
               [((a,b),proof)] => if a = right andalso b = left then
                   Thm.SYM proof else
                     raise ERR "symm" "invalid symmetry endpoints"
             | _ => raise ERR "symm" "symmetry expects one premise")
        | "trans" => ordered ()
        | "trans-star" => symmetric_chain ()
        | "cong" => congruence ()
        | _ => raise ERR "native" "unsupported equality rule"
    in Thm.EQ_MP (Thm.SYM (constructor target)) proof end

  fun discover graph scope
      {rule,target,premises,template_limit,check_type} =
    C.discover graph scope
      {roots = [],premises = premises,target = target,
       template_limit = template_limit,check_type = check_type,
       prove = native graph rule target premises}
end
