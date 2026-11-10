structure SmtLib_GraphCarrierScratch :> SmtLib_GraphCarrierScratch =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure H = SmtLib_CarrierHoMatch
  datatype family = Named of string | Private of int
  datatype term = Term of
    {owner:unit ref,id:int,ty:Type.hol_type,
     anchor:Q.carrier option,shape:shape}
  and shape =
      Query of Q.carrier * shape option ref
    | Template of Term.term * shape option ref
    | Var of family * Term.term
    | Const of Term.term
    | App of term * term
    | Abs of term * term
  exception Mismatch of string
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphCarrierScratch"
  type interface =
    {operations:term H.operations,of_query:Q.carrier -> term,
     of_template:Term.term -> term,variant:term list -> term -> term,
     variable_name:term -> string,
     atomic_term:term -> Term.term option}

  fun compare_pair ((a,b),(c,d)) = case Int.compare (a,c) of
      EQUAL => Int.compare (b,d) | result => result
  fun compare_environment ((a,env),(b,other)) =
    case Int.compare (a,b) of
      EQUAL => List.collate Int.compare (env,other) | result => result

  fun create (context:Q.outbound_context) : interface =
    let
      val owner = ref ()
      val next = ref 0
      val next_private = ref 1
      fun alive () = ignore ((#key context) (#goal context))
      fun guard (Term {owner=actual,anchor,...}) =
        (alive ();
         if Portable.pointer_eq (owner,actual) then () else
           raise ERR "guard" "different scratch algebra";
         Option.app (fn current => ignore ((#key context) current)) anchor)
      fun step () = (#step context) ()
      fun key (current as Term {id,...}) = (guard current;id)
      fun type_of (current as Term {ty,...}) = (guard current;ty)
      fun anchor (current as Term {anchor,...}) = (guard current;anchor)
      fun make ty anchor shape =
        let val _ = alive () val _ = step ()
            val id = !next val _ = next := id+1
        in Term {owner=owner,id=id,ty=ty,anchor=anchor,shape=shape} end
      (* Lifetime-only Bool recipes keep their type independent of scratch
         depth. Their syntax is never interpreted by the matcher and gives
         no Source or equality evidence. Q's existing recipe guard checks
         retained operands with its own scope/revision validation cache. *)
      fun query_anchor current =
        let val ty = (#type_of context) current
            val equality = Term.inst [{redex=Type.alpha,residue=ty}]
              boolSyntax.equality
            val head = (#constant context) equality
        in (#mk_comb context) ((#mk_comb context) (head,current),current) end
      fun anchor_conjunction (left,right) =
        let val head = (#constant context) boolSyntax.conjunction
        in (#mk_comb context) ((#mk_comb context) (head,left),right) end
      fun join_anchor (NONE,right) = right
        | join_anchor (left,NONE) = left
        | join_anchor (SOME left,SOME right) =
            if (#key context) left = (#key context) right then SOME left
            else SOME (anchor_conjunction (left,right))
      val query_cache = ref (Redblackmap.mkDict compare_pair)
      val template_cache = ref ([]:(Term.term * term) list)
      val private_query = ref (Redblackmap.mkDict Int.compare)
      fun private_family () =
        let val id = !next_private
        in next_private := id+1;Private id end
      fun query_family current =
        let val identity = (#semantic_key context) current in
          case Redblackmap.peek (!private_query,identity) of
            SOME family => family
          | NONE =>
              let val family = private_family ()
                  val _ = private_query :=
                    Redblackmap.insert (!private_query,identity,family)
              in family end
        end
      fun of_query current =
        let val position = (#key context) current in
          case Redblackmap.peek (!query_cache,position) of
            SOME result => (guard result;result)
          | NONE =>
              let val result = make ((#type_of context) current)
                    (SOME (query_anchor current)) (Query (current,ref NONE))
                  val _ = query_cache :=
                    Redblackmap.insert (!query_cache,position,result)
              in result end
        end
      fun of_template raw =
        (alive ();
         case List.find (fn (saved,_) => Portable.pointer_eq (saved,raw))
             (!template_cache) of
           SOME (_,result) => (guard result;result)
         | NONE =>
             let val result = make (Term.type_of raw) NONE
                   (Template (raw,ref NONE))
                 val _ = template_cache := (raw,result):: !template_cache
             in result end)
      fun expose (current as Term {shape,...}) =
        let
          val _ = guard current
          fun cached cell compute = case !cell of
              SOME shape => shape
            | NONE =>
                let val _ = step () val shape = compute ()
                    val _ = guard current val _ = cell := SOME shape
                in shape end
        in case shape of
            Query (query,cell) => cached cell (fn () =>
              case (#view context) query of
                Q.VariableView (kind,raw) =>
                  Var ((case kind of SmtReplayGraph.RigidSource =>
                          Named (#1 (Term.dest_var raw))
                        | _ => query_family query),raw)
              | Q.ConstantView raw => Const raw
              | Q.ApplicationView (left,right) =>
                  App (of_query left,of_query right)
              | Q.AbstractionView (variable,body) =>
                  Abs (of_query variable,of_query body))
          | Template (raw,cell) => cached cell (fn () =>
              case Term.dest_term raw of
                Term.VAR (name,_) => Var (Named name,raw)
              | Term.CONST _ => Const raw
              | Term.COMB (left,right) =>
                  App (of_template left,of_template right)
              | Term.LAMB (variable,body) =>
                  Abs (of_template variable,of_template body))
          | _ => shape
        end
      fun view current = case expose current of
          Var _ => H.Variable
        | Const raw =>
            let val {Thy,Name,...} = Term.dest_thy_const raw
            in H.Constant {name=Name,theory=Thy} end
        | App pair => H.Application pair
        | Abs pair => H.Abstraction pair
        | _ => raise Fail "scratch exposure retained a deferred constructor"
      fun atomic_term current = case expose current of
          Var (_,raw) => SOME raw | Const raw => SOME raw | _ => NONE
      fun variable_name current = case expose current of
          Var (_,raw) => #1 (Term.dest_var raw)
        | _ => raise Mismatch "variable expected"
      val type_ids = ref (Redblackmap.mkDict Type.compare)
      val next_type = ref 0
      fun type_id ty = case Redblackmap.peek (!type_ids,ty) of
          SOME id => id
        | NONE => let val id = !next_type
                      val _ = next_type := id+1
                      val _ = type_ids :=
                        Redblackmap.insert (!type_ids,ty,id)
                  in id end
      val variable_ids = ref
        (Redblackmap.mkDict (List.collate Int.compare))
      val named_ids = ref (Redblackmap.mkDict String.compare)
      val next_name = ref 0
      val next_variable = ref 0
      fun name_id name = case Redblackmap.peek (!named_ids,name) of
          SOME id => id
        | NONE => let val id = !next_name val _ = next_name := id+1
                      val _ = named_ids :=
                        Redblackmap.insert (!named_ids,name,id)
                  in id end
      fun variable_id current =
        let val shape = case expose current of
                Var (Named name,_) =>
                  [0,name_id name,type_id (type_of current)]
              | Var (Private id,_) => [1,id,type_id (type_of current)]
              | _ => raise Mismatch "variable expected"
        in case Redblackmap.peek (!variable_ids,shape) of
            SOME id => id
          | NONE => let val id = !next_variable
                        val _ = next_variable := id+1
                        val _ = variable_ids :=
                          Redblackmap.insert (!variable_ids,shape,id)
                    in id end
        end
      val constant_ids = ref (Redblackmap.mkDict Term.compare)
      val next_constant = ref 0
      fun constant_id raw = case Redblackmap.peek (!constant_ids,raw) of
          SOME id => id
        | NONE => let val id = !next_constant
                      val _ = next_constant := id+1
                      val _ = constant_ids :=
                        Redblackmap.insert (!constant_ids,raw,id)
                  in id end
      val semantics = ref
        (Redblackmap.mkDict (List.collate Int.compare))
      val semantic_cache = ref (Redblackmap.mkDict compare_environment)
      val next_semantic = ref 0
      fun semantic environment current =
        let val index = (key current,environment) in
          case Redblackmap.peek (!semantic_cache,index) of
            SOME id => id
          | NONE =>
              let
                val _ = step ()
                fun position _ [] _ = NONE
                  | position identity (saved::rest) depth =
                      if identity = saved then SOME depth
                      else position identity rest (depth+1)
                val shape = case expose current of
                    Var _ =>
                      let val identity = variable_id current
                      in case position identity environment 0 of
                          SOME depth => [0,type_id (type_of current),depth]
                        | NONE => [1,identity] end
                  | Const raw => [2,constant_id raw]
                  | App (left,right) =>
                      [3,semantic environment left,semantic environment right]
                  | Abs (variable,body) =>
                      [4,type_id (type_of variable),
                       semantic (variable_id variable::environment) body]
                  | _ => raise Fail "unexposed scratch syntax"
                val id = case Redblackmap.peek (!semantics,shape) of
                    SOME id => id
                  | NONE => let val id = !next_semantic
                                val _ = next_semantic := id+1
                                val _ = semantics :=
                                  Redblackmap.insert (!semantics,shape,id)
                            in id end
                val _ = guard current
                val _ = semantic_cache :=
                  Redblackmap.insert (!semantic_cache,index,id)
              in id end
        end
      fun same (left,right) =
        (guard left;guard right;semantic [] left = semantic [] right)
      val application_cache = ref (Redblackmap.mkDict compare_pair)
      val abstraction_cache = ref (Redblackmap.mkDict compare_pair)
      fun application (left,right) =
        let
          val index = (key left,key right)
          val left_type = type_of left
          val (domain,range) = Type.dom_rng left_type
            handle Feedback.HOL_ERR _ => raise Mismatch "function expected"
          val _ = if Type.compare (domain,type_of right) = EQUAL then () else
            raise Mismatch "application type mismatch"
        in case Redblackmap.peek (!application_cache,index) of
            SOME result => (guard result;result)
          | NONE =>
              let val result = make range
                    (join_anchor (anchor left,anchor right)) (App (left,right))
                  val _ = application_cache :=
                    Redblackmap.insert (!application_cache,index,result)
              in result end
        end
      fun abstraction (variable,body) =
        let val index = (key variable,key body)
            val _ = variable_id variable
        in case Redblackmap.peek (!abstraction_cache,index) of
            SOME result => (guard result;result)
          | NONE =>
              let val result = make (Type.--> (type_of variable,type_of body))
                    (join_anchor (anchor variable,anchor body))
                    (Abs (variable,body))
                  val _ = abstraction_cache :=
                    Redblackmap.insert (!abstraction_cache,index,result)
              in result end
        end
      fun variable_with_type (current,ty) =
        let val _ = guard current in
          if Type.compare (ty,type_of current) = EQUAL then current
          else case expose current of
              Var (family,raw) => make ty (anchor current)
                (Var (family,Term.mk_var (#1 (Term.dest_var raw),ty)))
            | _ => raise Mismatch "variable expected"
        end
      fun fresh_variable ty =
        (alive ();make ty NONE (Var (private_family (),Term.genvar ty)))
      fun variant avoided current =
        let
          val _ = alive () val _ = guard current
          val _ = List.app guard avoided
          fun atom variable = case expose variable of
              Var (_,raw) => raw | _ => raise Mismatch "variable expected"
          val raw = atom current
          val chosen = Term.variant (List.map atom avoided) raw
        in if Term.aconv chosen raw then current else
          let val family = case expose current of
                  Var (Named _,_) => Named (#1 (Term.dest_var chosen))
                | Var (Private _,_) => private_family ()
                | _ => raise Mismatch "variable expected"
          in make (type_of current) (anchor current) (Var (family,chosen)) end
        end
      fun dummy_variable ty =
        (alive ();make ty NONE
          (Var (Private 0,Term.mk_var ("scratch_match_dummy",ty))))
      val free_cache = ref (Redblackmap.mkDict Int.compare)
      fun free_variables input =
        let val index = key input in
          case Redblackmap.peek (!free_cache,index) of
            SOME variables => (List.app guard variables;variables)
          | NONE =>
              let
                val visited = ref (Redblackset.empty compare_environment)
                val seen = ref (Redblackset.empty Int.compare)
                val variables = ref []
                fun walk environment current =
                  let val index = (key current,environment) in
                    if Redblackset.member (!visited,index) then () else
                    (step ();visited := Redblackset.add (!visited,index);
                     case expose current of
                       Var _ =>
                         let val identity = variable_id current in
                           if List.exists (fn id => id=identity) environment
                             orelse Redblackset.member (!seen,identity)
                           then () else
                             (seen := Redblackset.add (!seen,identity);
                              variables := current:: !variables)
                         end
                     | Const _ => ()
                     | App (left,right) =>
                         (walk environment left;walk environment right)
                     | Abs (variable,body) =>
                         walk (variable_id variable::environment) body
                     | _ => raise Fail "unexposed scratch syntax")
                  end
                val _ = walk [] input val _ = guard input
                val result = !variables
                val _ = free_cache :=
                  Redblackmap.insert (!free_cache,index,result)
              in result end
        end
      fun substitute substitutions input =
        let
          val _ = alive () val _ = guard input
          fun check {redex,residue} =
            (guard redex;guard residue;
             if Type.compare (type_of redex,type_of residue) = EQUAL then ()
             else raise Mismatch "substitution type mismatch")
          val _ = List.app check substitutions
          val entries = List.rev substitutions
          fun member variable = List.exists (fn old => same (variable,old))
          fun variable current = case view current of H.Variable => true
            | _ => false
          val all_variables = List.all (variable o #redex) entries
          fun run entries input =
            let
              val memo = ref (Redblackmap.mkDict Int.compare)
              fun visit current =
                let val index = key current in
                  case Redblackmap.peek (!memo,index) of
                    SOME result => (guard result;result)
                  | NONE =>
                      let
                        val _ = step ()
                        val result = case List.find
                            (fn {redex,...} => same (redex,current)) entries of
                            SOME {residue,...} => (guard residue;residue)
                          | NONE =>
                              if all_variables andalso not (List.exists
                                  (fn {redex,...} =>
                                    member redex (free_variables current))
                                  entries) then current
                              else case expose current of
                                  App (left,right) =>
                                    application (visit left,visit right)
                                | Abs (binder,body) =>
                                    let
                                      val entries = List.filter
                                        (fn {redex,...} => not (member binder
                                          (free_variables redex))) entries
                                      val captures = List.exists
                                        (fn {residue,...} => member binder
                                          (free_variables residue)) entries
                                      val (binder,body) = if captures then
                                          let val fresh = fresh_variable
                                                (type_of binder)
                                          in (fresh,substitute
                                            [{redex=binder,residue=fresh}]
                                            body) end
                                        else (binder,body)
                                    in abstraction
                                      (binder,run entries body) end
                                | _ => current
                        val _ = guard current val _ = guard result
                        val _ = memo :=
                          Redblackmap.insert (!memo,index,result)
                      in result end
                end
            in visit input end
          val result = if null entries then input else run entries input
          val _ = guard input val _ = guard result
        in result end
      fun instantiate_type substitutions input =
        let
          val _ = alive () val _ = guard input
          val memo = ref (Redblackmap.mkDict compare_environment)
          fun converted variable environment =
            case List.find (fn (old,_) =>
                variable_id old = variable_id variable) environment of
              SOME (_,result) => (guard result;result)
            | NONE => variable_with_type
                (variable,Type.type_subst substitutions (type_of variable))
          fun visit environment current =
            let val index = (key current,List.concat (List.map
                  (fn (old,new) => [variable_id old,key new]) environment))
            in case Redblackmap.peek (!memo,index) of
                SOME result => (guard result;result)
              | NONE =>
                  let
                    val _ = step ()
                    val result = case expose current of
                        Var _ => converted current environment
                      | Const raw => of_template (Term.inst substitutions raw)
                      | App (left,right) => application
                          (visit environment left,visit environment right)
                      | Abs (binder,body) =>
                          let
                            val proposed = variable_with_type
                              (binder,Type.type_subst substitutions
                                (type_of binder))
                            val other_free = List.filter
                              (fn current => not (same (current,binder)))
                              (free_variables body)
                            val captures = List.exists
                              (fn current => same
                                (converted current environment,proposed))
                              other_free
                            val fresh = if captures then
                                fresh_variable (type_of proposed)
                              else proposed
                          in abstraction (fresh,
                            visit ((binder,fresh)::environment) body) end
                      | _ => raise Fail "unexposed scratch syntax"
                    val _ = guard current val _ = guard result
                    val _ = memo := Redblackmap.insert (!memo,index,result)
                  in result end
            end
          val result = if null substitutions then input else visit [] input
          val _ = guard input val _ = guard result
        in result end
      val operations : term H.operations =
        {view=view,type_of=type_of,same=same,free_variables=free_variables,
         substitute=substitute,instantiate_type=instantiate_type,
         variable_with_type=variable_with_type,fresh_variable=fresh_variable,
         dummy_variable=dummy_variable,application=application,
         abstraction=abstraction,key=key,guard=guard,alive=alive,step=step,
         is_mismatch=fn Mismatch _ => true | _ => false}
      val _ = alive ()
    in {operations=operations,of_query=of_query,of_template=of_template,
        variant=variant,
        variable_name=variable_name,atomic_term=atomic_term} end
end
