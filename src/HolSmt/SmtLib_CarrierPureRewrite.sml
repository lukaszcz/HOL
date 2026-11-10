(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_CarrierPureRewrite :> SmtLib_CarrierPureRewrite =
struct
  structure H = SmtLib_CarrierHoMatch
  type 'term operations =
    {syntax:'term H.operations,
     of_template:Term.term -> 'term,variable_name:'term -> string,
     variant:'term list -> 'term -> 'term,
     part_match:Thm.thm -> 'term ->
       {conditions:'term list,left:'term,right:'term}}
  val ERR = Feedback.mk_HOL_ERR "SmtLib_CarrierPureRewrite"
  exception NoRewrite
  exception OrderingOverflow

  datatype label = Vnet | FVnet of string * int
    | Cnet of string * string * int | Lnet of int
  datatype 'term rule = Rule of
    {theorem:Thm.thm,left:Term.term,permutative:bool,
     control:BoundedRewrites.control,
     instantiate:'term -> {conditions:'term list,left:'term,right:'term}}
  datatype 'term net = Net of
    {edges:(label,'term net) Redblackmap.dict,tips:'term rule list}

  fun compare_label (Vnet,Vnet) = EQUAL
    | compare_label (Vnet,_) = LESS
    | compare_label (_,Vnet) = GREATER
    | compare_label (FVnet (ln,la),FVnet (rn,ra)) =
        (case String.compare (ln,rn) of
           EQUAL => Int.compare (la,ra) | result => result)
    | compare_label (FVnet _,_) = LESS
    | compare_label (_,FVnet _) = GREATER
    | compare_label (Cnet (ln,lt,la),Cnet (rn,rt,ra)) =
        (case String.compare (ln,rn) of
           EQUAL => (case String.compare (lt,rt) of
               EQUAL => Int.compare (la,ra) | result => result)
         | result => result)
    | compare_label (Cnet _,Lnet _) = LESS
    | compare_label (Lnet _,Cnet _) = GREATER
    | compare_label (Lnet left,Lnet right) = Int.compare (left,right)
  fun empty () = Net {edges=Redblackmap.mkDict compare_label,tips=[]}
  fun member raw = List.exists (Term.aconv raw)

  (* This is exactly Ho_Net's declaration labelling, over captured theorem
     syntax only. A schematic head consumes its whole pattern as Vnet. *)
  fun stored (rigid,term) =
    let val (head,arguments) = boolSyntax.strip_comb term
        val children = List.map (fn term => (rigid,term)) arguments
    in
      if Term.is_const head then
        let val {Name,Thy,...} = Term.dest_thy_const head
        in (Cnet (Name,Thy,length arguments),children) end
      else if Term.is_abs head then
        let val (binder,body) = Term.dest_abs head
        in (Lnet (length arguments),
          (List.filter (fn term => not (Term.aconv binder term)) rigid,body)
            :: children) end
      else if Term.is_var head then
        if member head rigid then
          (FVnet (#1 (Term.dest_var head),length arguments),children)
        else (Vnet,[])
      else raise ERR "stored" "invalid captured rewrite head"
    end
  fun insert rule [] (Net {edges,tips}) =
        Net {edges=edges,tips=rule::tips}
    | insert rule (term::remaining) (Net {edges,tips}) =
        let val (label,children) = stored term
            val child = Option.getOpt (Redblackmap.peek (edges,label),empty ())
            val child = insert rule (children @ remaining) child
        in Net {edges=Redblackmap.insert (edges,label,child),tips=tips} end

  fun variable_permutation (left,right) =
    let
      fun shape (left,right) =
        if Term.is_var left andalso Term.is_var right then
          Type.compare (Term.type_of left,Term.type_of right) = EQUAL
        else if Term.is_abs left andalso Term.is_abs right then
          shape (#2 (Term.dest_abs left),#2 (Term.dest_abs right))
        else if Term.is_comb left andalso Term.is_comb right then
          let val (lf,la) = Term.dest_comb left
              val (rf,ra) = Term.dest_comb right
          in shape (lf,rf) andalso shape (la,ra) end
        else Term.aconv left right
      val lf = Term.free_vars left val rf = Term.free_vars right
    in shape (left,right) andalso length lf = length rf andalso
      List.all (fn term => member term rf) lf end

  fun normalize ({syntax,of_template,variable_name,variant,part_match}:
      'term operations) theorem input =
    let
      val {view,type_of,same,free_variables,substitute,instantiate_type,
           variable_with_type,fresh_variable,dummy_variable,application,
           abstraction,key,guard,alive,step,is_mismatch} = syntax
      val _ = alive () val _ = guard input val _ = step ()
      (* Calling && processes the REAL stock directives. No query target
         enters this native declaration programme. The actual TypeBase
         selector has already excluded conclusion-marker Cong/AC/SF etc.;
         this interface does not claim to run arbitrary user conversions. *)
      val captured = (simpLib.&&) (pureSimps.pure_ss,[theorem])
      val facts = List.concat
        (List.map simpLib.frag_rewrites (simpLib.ssfrags_of captured))
      (* Traverse.add_context retains the hypothesis variables of the
         processed rewrite programme. Opening uses their native names
         when avoiding capture under abstractions. These are declaration
         atoms; no Query body is converted to a native term. *)
      val context_variables = Term.free_varsl
        (List.concat (List.map Thm.hyp facts))
      val context_syntax = List.map of_template context_variables
      fun atomic_variable current =
        Term.mk_var (variable_name current,type_of current)
      fun opens_context binder =
        member (atomic_variable binder) context_variables
      fun open_body (binder,body) =
        let val avoid = context_syntax @ free_variables body
            val variable = variant avoid binder
        in (variable,substitute [{redex=binder,residue=variable}] body) end
      val controlled = List.map BoundedRewrites.dest_tagged_rewrite facts
      val canonical = List.concat (List.map Cond_rewr.mk_cond_rewrs controlled)
      fun compile (theorem,control) =
        let
          val description =
            (let val theorem = Drule.SPEC_ALL theorem
                 val equation = #2 (boolSyntax.strip_imp (Thm.concl theorem))
                 val (left,right) = boolSyntax.dest_eq equation
             in SOME (theorem,left,variable_permutation (left,right)) end
             handle Feedback.HOL_ERR _ => NONE)
        in case description of NONE => NONE
          | SOME (theorem,left,permutative) =>
              (* Prepare HO_PART_MATCH once per canonical rule. Its live
                 algebra guards stay OUTSIDE the pure metadata handler. *)
              let val instantiate = part_match theorem
              in SOME (Rule {theorem=theorem,left=left,control=control,
                permutative=permutative,instantiate=instantiate}) end
        end
      val rules = List.mapPartial compile canonical
      fun add (rule as Rule {theorem,left,...},net) =
        insert rule [(HOLset.listItems (Thm.hyp_frees theorem),left)] net
      (* simpLib.net_add_convs uses itlist: fold RIGHT, then prepend tips. *)
      val index = List.foldr add (empty ()) rules
      val revision = ref 0
      fun enabled (Rule {control=BoundedRewrites.UNBOUNDED,...}) = true
        | enabled (Rule {control=BoundedRewrites.BOUNDED count,...}) =
            !count <> 0
      fun bounded (Rule {control=BoundedRewrites.UNBOUNDED,...}) = false
        | bounded _ = true
      fun succeeded (Rule {control=BoundedRewrites.UNBOUNDED,...}) = ()
        | succeeded (Rule {control=BoundedRewrites.BOUNDED count,...}) =
            (count := !count-1;revision := !revision+1)
      fun decline NoRewrite = true
        | decline OrderingOverflow = true
        | decline (H.Mismatch _) = true
        | decline primary = is_mismatch primary
      fun strip current =
        let fun loop current arguments = case view current of
                H.Application (function,argument) =>
                  loop function (argument::arguments)
              | _ => (current,arguments)
        in loop current [] end
      fun label current =
        let val (head,arguments) = strip current
        in case view head of
            H.Variable =>
              (FVnet (variable_name head,length arguments),arguments)
          | H.Constant {name,theory} =>
              (Cnet (name,theory,length arguments),arguments)
          | H.Abstraction (_,body) =>
              (Lnet (length arguments),body::arguments)
          | H.Application _ => raise ERR "label" "invalid carrier spine"
        end
      fun follow [] (Net {tips,...}) = tips
        | follow (current::remaining) (Net {edges,...}) =
            let val (actual,children) = label current
                val specific = case Redblackmap.peek (edges,actual) of
                    NONE => []
                  | SOME child => follow (children @ remaining) child
                val general = case Redblackmap.peek (edges,Vnet) of
                    NONE => [] | SOME child => follow remaining child
            in specific @ general end

      (* Cond_rewr.ac_term_ord, including unfolded size, is evaluated with
         DAG memo tables. Only the isolated native size addition can become
         an ordinary ordering decline; callback/resource errors escape. *)
      val sizes = ref (Redblackmap.mkDict Int.compare)
      fun plus (left,right) = left+right
        handle Overflow => raise OrderingOverflow
      fun size current =
        let val id = key current
        in case Redblackmap.peek (!sizes,id) of
            SOME answer => (guard current;answer)
          | NONE =>
              let val answer = case view current of
                      H.Application (left,right) => plus (size left,size right)
                    | H.Abstraction (_,body) => plus (1,size body)
                    | _ => 1
                  val _ = guard current
                  val _ = sizes := Redblackmap.insert (!sizes,id,answer)
              in answer end
        end
      val comparisons = ref (Redblackmap.mkDict (List.collate Int.compare))
      fun binding environment variable =
        case List.find (fn (saved,_) => same (saved,variable)) environment of
          NONE => NONE | SOME (_,depth) => SOME depth
      fun header environment current = case view current of
          H.Variable =>
            (case binding environment current of
               NONE => ((variable_name current,"",0),type_of current)
             | SOME depth => (("","",~depth),Type.alpha))
        | H.Constant {name,theory} => ((name,theory,1),type_of current)
        | H.Abstraction (binder,_) => (("","",2),type_of binder)
        | H.Application _ => (("","",3),Type.alpha)
      fun compare_header (((ln,lt,lk),lty),((rn,rt,rk),rty)) =
        case String.compare (ln,rn) of
          EQUAL => (case String.compare (lt,rt) of
              EQUAL => (case Int.compare (lk,rk) of
                  EQUAL => Type.compare (lty,rty) | result => result)
            | result => result)
        | result => result
      fun ordering depth left_env right_env (left,right) =
        let
          val left_id = key left val right_id = key right
          fun environment values = List.concat
            (List.map (fn (variable,level) => [key variable,level]) values)
          val identity = left_id :: right_id :: depth ::
            (length left_env :: environment left_env @
             (length right_env :: environment right_env))
        in case Redblackmap.peek (!comparisons,identity) of
            SOME result => (guard left;guard right;result)
          | NONE =>
              let
                fun compare_arguments ([],[]) = EQUAL
                  | compare_arguments ([],_) = LESS
                  | compare_arguments (_,[]) = GREATER
                  | compare_arguments (l::ls,r::rs) =
                      (case ordering depth left_env right_env (l,r) of
                         EQUAL => compare_arguments (ls,rs)
                       | result => result)
                fun compare_spines () =
                  let val (lf,la) = strip left val (rf,ra) = strip right
                  in case compare_header
                      (header left_env lf,header right_env rf) of
                      EQUAL => (case Int.compare (length la,length ra) of
                          EQUAL => compare_arguments (la,ra)
                        | result => result)
                    | result => result end
                val result = case Int.compare (size left,size right) of
                    EQUAL =>
                      (case (view left,view right) of
                         (H.Abstraction (lb,lbody),
                          H.Abstraction (rb,rbody)) =>
                           (case Type.compare (type_of lb,type_of rb) of
                              EQUAL => ordering (depth+1)
                                ((lb,depth)::left_env)
                                ((rb,depth)::right_env) (lbody,rbody)
                            | result => result)
                       | (H.Abstraction _,_) => GREATER
                       | (_,H.Abstraction _) => LESS
                       | _ => compare_spines ())
                  | result => result
                val _ = guard left val _ = guard right
                val _ = comparisons :=
                  Redblackmap.insert (!comparisons,identity,result)
              in result end
        end

      val truth = of_template boolSyntax.T
      val memo = ref (Redblackmap.mkDict (List.collate Int.compare))
      fun walk stack current =
        let
          val _ = alive () val _ = guard current
          val _ = List.app guard stack
          val initial_revision = !revision
          val identity = initial_revision :: key current :: List.map key stack
        in case Redblackmap.peek (!memo,identity) of
            SOME result => (guard (#term result);result)
          | NONE =>
              let
                val _ = step ()
                fun attempt (rule as Rule {instantiate,permutative,...})
                    target =
                  if not (enabled rule) then raise NoRewrite else
                    let
                      val _ = step ()
                      val {conditions,left,right} = instantiate target
                      val _ = if List.exists (fn condition =>
                          List.exists (fn old => same (condition,old)) stack)
                          conditions then raise NoRewrite else ()
                      val _ = if length stack + length conditions >
                          !Cond_rewr.stack_limit then raise NoRewrite else ()
                      val _ = if same (left,right) then raise NoRewrite else ()
                      val _ = if permutative andalso
                          ordering 0 [] [] (left,right) <> GREATER andalso
                          not (bounded rule)
                        then raise NoRewrite else ()
                      val pending = conditions @ stack
                      fun solve condition =
                        let val result = walk pending condition
                        in if #converted result andalso
                            same (#term result,truth) then ()
                           else raise NoRewrite end
                      val _ = List.app solve conditions
                      (* Cond_rewr's final ALPHA/TRANS can still decline.
                         Its condition rewrites have already consumed any
                         bounded counters at this point; do not roll back. *)
                      val _ = if same (left,target) then () else
                        raise NoRewrite
                      val _ = guard right val _ = succeeded rule
                    in right end
                fun high target =
                  let
                    fun first [] = NONE
                      | first (rule::remaining) =
                          (SOME (attempt rule target) handle primary =>
                            if decline primary then first remaining
                            else raise primary)
                  in alive ();guard target;first (follow [target] index) end
                fun repeat target converted = case high target of
                    NONE => {term=target,converted=converted}
                  | SOME next => repeat next true
                fun descend target = case view target of
                    H.Application (left,right) =>
                      let val l = walk stack left val r = walk stack right
                          val converted = #converted l orelse #converted r
                          val result = if key (#term l) = key left andalso
                              key (#term r) = key right then target
                            else application (#term l,#term r)
                      in {term=result,converted=converted} end
                  | H.Abstraction (binder,body) =>
                      let val (opened,inside) = if opens_context binder
                            then open_body (binder,body) else (binder,body)
                          val result = walk stack inside
                      in {term=if not (#converted result) then target
                          else if key opened = key binder andalso
                              key (#term result) = key body then target
                            else abstraction (opened,#term result),
                        converted= #converted result} end
                  | _ => {term=target,converted=false}
                val initial = repeat current false
                val descended = descend (#term initial)
                val result = if #converted descended then
                    (case high (#term descended) of
                       NONE => {term= #term descended,converted=true}
                     | SOME next =>
                         let val result = walk stack next
                         in {term= #term result,converted=true} end)
                  else initial
                val _ = guard (#term result) val _ = guard current
                (* Failed conditions may consume OTHER bounded rules. A
                   cache entry never erases or replays such state changes. *)
                val _ = if initial_revision = !revision then
                    memo := Redblackmap.insert (!memo,identity,result)
                  else ()
              in result end
        end
      val result = walk [] input
      val _ = alive () val _ = guard input val _ = guard (#term result)
    in result end

  fun reduces (operations as {syntax,...}:'term operations) theorem current =
    let val result = normalize operations theorem current
        val _ = (#alive syntax) ()
    in not ((#same syntax) (current,#term result)) end
end
