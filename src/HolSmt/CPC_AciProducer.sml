(* Checked Boolean ACI production. Realized operands are DATA, not proof
   search inputs. In particular, never DISJ_CASES/IMP_ANTISYM, match, or
   substitute in a realized Boolean graph. The sole INST consumes a small
   variable-only schema and inserts opaque Boolean operands simultaneously.

   The caller owns endpoint retention and operation observation:
     produce_with observed_inst target
   returns SOME {template,operands,theorem}; export it using
     retain_producer_conclusion template operands target theorem.
   NONE means no admitted pointer-exact schema was found, not a theorem.
   No global limits or the ordinary transport allowance are changed. *)
structure CPC_AciProducer =
struct
  open HolKernel
  val ERR = Feedback.mk_HOL_ERR "CPC_AciProducer"
  val maximum = SmtResource.max_skeleton_replay_dag_nodes
  exception Declined

  type product =
    {template : term, operands : (term * term) list, theorem : thm}

  (* Pointer-only tables: structural Term.compare is NOT safe for an opaque
     operand, even when that operand is a Boolean connective itself. *)
  fun table () = Array.array (4093, [])
  (* Use only a two-level routing hint, not Resource's deeper metric hash.
     Routing cannot grant permission to traverse an opaque operand. *)
  val bucket_of = SmtReplayImport.pointer_bucket 2 4093
  fun peek buckets term =
    Option.map #2 (List.find
      (fn (saved,_) => Portable.pointer_eq (term,saved))
      (Array.sub (buckets,bucket_of term)))
  fun put buckets term value =
    let val bucket = bucket_of term in
      Array.update (buckets,bucket,(term,value) ::
        List.filter (fn (saved,_) =>
          not (Portable.pointer_eq (term,saved)))
          (Array.sub (buckets,bucket)))
    end
  fun debit remaining =
    if !remaining = 0 then raise Declined
    else remaining := !remaining - 1

  fun constant expected term =
    Term.is_const term andalso Term.same_const term expected

  (* Only inspect this connective's binary outer shell. Do not strip_comb:
     an atom may itself be an application with a very large operator. *)
  fun children conjunction term =
    if conjunction then Lib.total boolSyntax.dest_conj term
    else Lib.total boolSyntax.dest_disj term

  (* Common shallow occurrences are intentional opaque cuts. For example
       (A \/ (B \/ F)) = (A \/ B)
     must not open A or B, even if they are enormous disjunctions. Failure
     with these optional cuts retries without them: e.g. (A \/ B) \/ A =
     A \/ B may require opening the common A \/ B after all. *)
  fun occurrences conjunction depth root =
    let
      val seen = table ()
      val remaining = ref maximum
      fun visit depth term =
        (debit remaining;
         case peek seen term of
           SOME old => if old >= depth then () else descend depth term
         | NONE => descend depth term)
      and descend depth term =
        (put seen term depth;
         if depth = 0 then () else
           case children conjunction term of
             NONE => ()
           | SOME (left,right) =>
               (visit (depth-1) left;visit (depth-1) right))
      val _ = visit depth root
    in seen end

  fun schema conjunction cut_depth left right =
    let
      val common = case cut_depth of
          NONE => (fn _ => false)
        | SOME depth =>
            let
              val ls = occurrences conjunction depth left
              val rs = occurrences conjunction depth right
            in fn term => Option.isSome (peek ls term) andalso
              Option.isSome (peek rs term) end
      val atoms = table ()
      val operands = ref []
      val memo = table ()
      val remaining = ref maximum
      fun atom term = case peek atoms term of SOME variable => variable
        | NONE =>
            let val variable = Term.genvar Type.bool in
              put atoms term variable;
              operands := (variable,term) :: !operands;
              variable
            end
      fun abstract depth term =
        (debit remaining;
         case peek memo term of
           SOME entries =>
             (case List.find (fn (d,_) => d = depth) entries of
                SOME (_,saved) => saved
              | NONE => compute depth term entries)
         | NONE => compute depth term [])
      and compute depth term entries =
        let
          val result =
            if constant boolSyntax.T term then boolSyntax.T
            else if constant boolSyntax.F term then boolSyntax.F
            else if common term then atom term
            else if depth = 0 then
              (case cut_depth of SOME _ => atom term
               | NONE => raise Declined)
            else case children conjunction term of
              NONE => atom term
            | SOME (l,r) =>
                (if conjunction then boolSyntax.mk_conj
                 else boolSyntax.mk_disj)
                  (abstract (depth-1) l,abstract (depth-1) r)
          val _ = put memo term ((depth,result) :: entries)
        in result end
      val depth = Option.getOpt (cut_depth,maximum)
      val template = boolSyntax.mk_eq
        (abstract depth left,abstract depth right)
      (* Physical and native-tree admission BOTH precede theorem effects.
         INST on the standard kernel unfolds its input schema; sharing is
         not permission for unbounded native work. No operand is measured. *)
      val _ = if SmtResource.dag_nodes_up_to maximum template <= maximum
          andalso Option.isSome
            (SmtReplayImport.bounded_raw_size maximum template) then ()
        else raise Declined
    in (template,List.rev (!operands)) end

  (* All terms below are admitted schemas of Boolean constants and fresh
     variables. Native comparisons and derived kernel rules are local to
     that bounded schema, NEVER to the eventual realized graph. *)
  fun prove_schema conjunction template =
    let
      fun falsity target theorem =
        Thm.MP (Thm.SPEC target boolTheory.FALSITY) theorem
      fun conjunction_implication source destination =
        let
          val leaves = ref (Redblackmap.mkDict Term.compare)
          fun collect term theorem =
            if constant boolSyntax.T term then ()
            else case Lib.total boolSyntax.dest_conj term of
              SOME (l,r) =>
                (collect l (Thm.CONJUNCT1 theorem);
                 collect r (Thm.CONJUNCT2 theorem))
            | NONE => leaves := Redblackmap.insert (!leaves,term,theorem)
          val _ = collect source (Thm.ASSUME source)
          fun derive term =
            if constant boolSyntax.T term then boolTheory.TRUTH
            else case Lib.total boolSyntax.dest_conj term of
              SOME (l,r) => Thm.CONJ (derive l) (derive r)
            | NONE => (case Redblackmap.peek (!leaves,term) of
                SOME theorem => theorem
              | NONE => raise Declined)
          val result = case Redblackmap.peek (!leaves,boolSyntax.F) of
              SOME theorem => falsity destination theorem
            | NONE => derive destination
        in Thm.DISCH source result end
      fun disjunction_implication source destination =
        let
          val paths = ref (Redblackmap.mkDict Term.compare)
          fun index term path =
            case Lib.total boolSyntax.dest_disj term of
              SOME (l,r) => (index l (true::path);index r (false::path))
            | NONE => paths := Redblackmap.insert
                (!paths,term,List.rev path)
          val _ = index destination []
          fun place theorem _ [] = theorem
            | place theorem term (branch::rest) =
                let val (l,r) = boolSyntax.dest_disj term in
                  if branch then Thm.DISJ1 (place theorem l rest) r
                  else Thm.DISJ2 l (place theorem r rest)
                end
          fun inject theorem =
            if constant boolSyntax.F (Thm.concl theorem) then
              falsity destination theorem
            else
              case Redblackmap.peek (!paths,boolSyntax.T) of
                SOME path => place boolTheory.TRUTH destination path
              | NONE => (case Redblackmap.peek (!paths,Thm.concl theorem) of
                  SOME path => place theorem destination path
                | NONE => raise Declined)
          fun derive term theorem =
            case Lib.total boolSyntax.dest_disj term of
              SOME (l,r) => Thm.DISJ_CASES theorem
                (derive l (Thm.ASSUME l)) (derive r (Thm.ASSUME r))
            | NONE => inject theorem
        in Thm.DISCH source (derive source (Thm.ASSUME source)) end
      val (left,right) = boolSyntax.dest_eq template
      val implication = if conjunction then conjunction_implication
        else disjunction_implication
    in Drule.IMP_ANTISYM_RULE
      (implication left right) (implication right left) end

  fun produce_with instantiate target : product option =
    let
      fun prepare () =
        let
          val (left,right) = boolSyntax.dest_eq target
          fun attempt conjunction depth =
            let
              val (template,operands) =
                schema conjunction depth left right
              val generic = prove_schema conjunction template
            in SOME {template=template,operands=operands,generic=generic}
            end
            handle Declined => NONE
          fun depths _ [] = NONE
            | depths conjunction (depth::rest) =
                case attempt conjunction depth of
                  NONE => depths conjunction rest
                | result => result
          fun operator conjunction =
            if Option.isSome (children conjunction left) orelse
               Option.isSome (children conjunction right) orelse
               constant (if conjunction then boolSyntax.T
                         else boolSyntax.F) left orelse
               constant (if conjunction then boolSyntax.T
                         else boolSyntax.F) right then
              depths conjunction [SOME 1,SOME 2,SOME 4,SOME 8,NONE]
            else NONE
        in case operator true of NONE => operator false | result => result
        end
        handle Feedback.HOL_ERR error =>
          if SmtResource.is_resource_gate error then
            raise Feedback.HOL_ERR error
          else NONE
      fun work () =
        case prepare () of
          NONE => NONE
        | SOME {template,operands,generic} =>
            let
              val substitutions = List.map
                (fn (variable,operand) => {redex=variable,residue=operand})
                operands
              (* Callback failures are terminal, not schema declines. Keep
                 this outside both preparation handlers, but inside the
                 resource timer. No theorem operation on its result here;
                 the caller retains endpoints with its checked bridge. *)
              val theorem = instantiate substitutions generic
            in SOME {template=template,operands=operands,theorem=theorem}
            end
    in SmtResource.with_resource_step_time "Skeleton" "CPC Boolean ACI"
      work () end

  val produce = produce_with Thm.INST
end
