(* Carrier port of HolKernel's higher-order matching implementation. *)
structure SmtLib_CarrierHoMatch :> SmtLib_CarrierHoMatch =
struct
  datatype 'term view =
      Variable
    | Constant of {name:string,theory:string}
    | Application of 'term * 'term
    | Abstraction of 'term * 'term
  type 'term substitution = {redex:'term,residue:'term} list
  type type_substitution =
    {redex:Type.hol_type,residue:Type.hol_type} list
  type 'term operations =
    {view:'term -> 'term view,type_of:'term -> Type.hol_type,
     same:'term * 'term -> bool,free_variables:'term -> 'term list,
     substitute:'term substitution -> 'term -> 'term,
     instantiate_type:type_substitution -> 'term -> 'term,
     variable_with_type:'term * Type.hol_type -> 'term,
     fresh_variable:Type.hol_type -> 'term,
     dummy_variable:Type.hol_type -> 'term,
     application:'term * 'term -> 'term,
     abstraction:'term * 'term -> 'term,
     key:'term -> int,guard:'term -> unit,alive:unit -> unit,step:unit -> unit,
     is_mismatch:exn -> bool}
  exception Mismatch of string
  exception Missing
  type 'term result =
    {beta_counts:{redex:'term,residue:int} list,
     terms:'term substitution,types:type_substitution}

  fun beta_normalise (ops:'term operations) input =
    let
      val _ = (#alive ops) ()
      val memo = ref (Redblackmap.mkDict Int.compare)
      fun remember index value =
        ((#guard ops) value;
         memo := Redblackmap.insert (!memo,index,value);value)
      fun visit current =
        let val _ = (#guard ops) current val index = (#key ops) current in
          case Redblackmap.peek (!memo,index) of
            SOME value => ((#guard ops) value;value)
          | NONE =>
              let
                val _ = (#step ops) ()
                val value = case (#view ops) current of
                    Application (function,argument) =>
                      (case (#view ops) function of
                         Abstraction (binder,body) => visit
                           ((#substitute ops)
                             [{redex=binder,residue=argument}] body)
                       | _ =>
                           let val changed = visit function in
                             if not ((#same ops) (function,changed)) then
                               visit ((#application ops) (changed,argument))
                             else
                               let val changed = visit argument in
                                 if (#same ops) (argument,changed) then current
                                 else (#application ops) (function,changed)
                               end
                           end)
                  | Abstraction (binder,body) =>
                      let val changed = visit body in
                        if (#same ops) (body,changed) then current
                        else (#abstraction ops) (binder,changed)
                      end
                  | _ => current
              in remember index value end
        end
      val result = visit input
      val _ = (#guard ops) input val _ = (#guard ops) result
    in result end

  fun all_abconv (ops:'term operations) pair =
    let
      val _ = (#alive ops) ()
      fun compare ([],[]) = true
        | compare (left::ls,right::rs) =
            (#same ops) (beta_normalise ops left,beta_normalise ops right)
              andalso compare (ls,rs)
        | compare _ = false
      val _ = List.app (#guard ops) (#1 pair @ #2 pair)
    in compare pair end

  fun match_first_order (ops:'term operations)
      {rigid_types,rigid_variables,pattern,target} =
    let
      val {view,type_of,same,free_variables,variable_with_type,guard,
           alive,step,...} = ops
      val _ = alive () val _ = guard pattern val _ = guard target
      val _ = List.app guard rigid_variables
      fun member current = List.exists (fn old => same (current,old))
      fun find current [] = NONE
        | find current ({redex,residue}::rest) =
            if same (current,redex) then SOME residue else find current rest
      fun type_match source target state =
        Type.raw_match_type source target state handle Feedback.HOL_ERR _ =>
          raise Mismatch "first-order type mismatch"
      fun visit environment pat actual (bindings,identities,types) =
        (guard pat;guard actual;step ();
         case view pat of
           Variable =>
             (case find pat environment of
                SOME binder =>
                  (case view actual of Variable =>
                     if same (actual,binder) then (bindings,identities,types)
                     else raise Mismatch "first-order bound variable"
                   | _ => raise Mismatch "first-order bound shape")
              | NONE =>
                  let
                    val _ = if List.exists
                      (fn variable => List.exists
                        (fn {redex,residue} => same (variable,residue))
                        environment) (free_variables actual) then
                        raise Mismatch "first-order binder capture" else ()
                    val previous = case find pat bindings of SOME held =>
                          SOME held
                      | NONE => if member pat identities then SOME pat
                          else NONE
                    val (bindings,identities) = case previous of
                        SOME held =>
                          if same (held,actual) then (bindings,identities)
                          else raise Mismatch "first-order double binding"
                      | NONE => if same (pat,actual) then
                          (bindings,pat::identities)
                        else ({redex=pat,residue=actual}::bindings,identities)
                    val source = type_of pat val destination = type_of actual
                  in (bindings,identities,
                    type_match source destination types) end)
         | Constant {name,theory} =>
             let val source = type_of pat in case view actual of
               Constant {name=actual_name,theory=actual_theory} =>
                 let val destination = type_of actual in
                   if name<>actual_name orelse theory<>actual_theory then
                     raise Mismatch "first-order constant"
                   else if not (Type.polymorphic source) then
                     if Type.polymorphic destination orelse
                         Type.compare (source,destination)<>EQUAL then
                       raise Mismatch "first-order ground constant"
                     else (bindings,identities,types)
                   else (bindings,identities,
                     type_match source destination types)
                 end
             | _ => raise Mismatch "first-order constant shape" end
         | Application (pf,pa) =>
             (case view actual of Application (af,aa) =>
                visit environment pa aa
                  (visit environment pf af (bindings,identities,types))
              | _ => raise Mismatch "first-order application shape")
         | Abstraction (pv,pbody) =>
             (case view actual of Abstraction (av,abody) =>
                let val source = type_of pv val destination = type_of av
                    val types = type_match source destination types
                in visit ({redex=pv,residue=av}::environment) pbody abody
                  (bindings,identities,types) end
              | _ => raise Mismatch "first-order abstraction shape"))
      val (bindings,_,(types,_)) = visit [] pattern target
        ([],rigid_variables,([],rigid_types))
      val terms = List.foldl
        (fn ({redex,residue},known) =>
          let val variable = variable_with_type
                (redex,Type.type_subst types (type_of redex))
          in if same (residue,variable) then known
             else {redex=variable,residue=residue}::known end) [] bindings
      val _ = guard pattern val _ = guard target
      val _ = List.app
        (fn {redex,residue} => (guard redex;guard residue)) terms
    in {terms=terms,types=types} end

  fun match (ops:'term operations)
      {rigid_types,rigid_variables,pattern,target} =
    let
      val _ = (#alive ops) ()
      val {view,type_of,same,free_variables,substitute,instantiate_type,
           variable_with_type,fresh_variable,dummy_variable,application,
           abstraction,guard,step,...} = ops
      fun expected primary =
        case primary of Mismatch _ => true | _ => (#is_mismatch ops) primary
      fun attempt first fallback = first () handle primary =>
        if expected primary then fallback () else raise primary
      fun metadata thunk = thunk () handle Feedback.HOL_ERR _ =>
        raise Mismatch "type matching"
      fun observe current = (guard current;step ())
      fun variable current = case view current of Variable => true | _ => false
      fun dest_application current = case view current of
          Application pair => pair | _ => raise Mismatch "application"
      fun dest_abstraction current = case view current of
          Abstraction pair => pair | _ => raise Mismatch "abstraction"
      fun strip current =
        let fun walk current arguments = case view current of
                Application (function,argument) => walk function
                  (argument::arguments)
              | _ => (current,arguments)
        in walk current [] end
      fun applications function arguments =
        List.foldl (fn (argument,function) => application (function,argument))
          function arguments
      fun abstractions variables body =
        List.foldr (fn (variable,body) => abstraction (variable,body))
          body variables
      fun member current = List.exists (fn old => same (current,old))
      fun find current [] = raise Missing
        | find current ({redex,residue}::rest) =
            if same (current,redex) then residue else find current rest
      fun in_domain current = List.exists
        (fn {redex,residue} => same (current,redex))
      fun insert (entry as {redex,residue}) bindings =
        ((if same (residue,find redex bindings) then bindings
          else raise Mismatch "inconsistent substitution")
         handle Missing => entry::bindings)
      fun dummy source destination bindings =
        insert {redex=dummy_variable source,
          residue=dummy_variable destination} bindings
      fun partial environment pat actual (sofar as (bindings,higher)) =
        (observe pat;observe actual;
         case view pat of
           Variable =>
             ((if same (find pat environment,actual) then sofar
               else raise Mismatch "bound variable")
              handle Missing =>
                if member pat rigid_variables then
                  if same (actual,pat) then sofar
                  else raise Mismatch "rigid variable"
                else (insert {redex=pat,residue=actual} bindings,higher))
         | Constant {name,theory} =>
             let val pattern_type = type_of pat in case view actual of
                Constant {name=actual_name,theory=actual_theory} =>
                  let val actual_type = type_of actual in
                  if name=actual_name andalso theory=actual_theory then
                    if Type.compare (actual_type,pattern_type)=EQUAL then
                      sofar
                    else (dummy pattern_type actual_type bindings,higher)
                  else raise Mismatch "constant"
                  end
              | _ => raise Mismatch "constant shape" end
         | Abstraction (pv,pbody) =>
             let val (av,abody) = dest_abstraction actual
                 val next = (dummy (type_of pv) (type_of av) bindings,higher)
             in partial ({redex=pv,residue=av}::environment)
               pbody abody next end
         | Application _ =>
             let val (head,_) = strip pat in
               if variable head andalso not (member head rigid_variables)
                   andalso not (in_domain head environment) then
                 let val pattern_type = type_of pat
                     val actual_type = type_of actual
                     val bindings =
                       if Type.compare (pattern_type,actual_type)=EQUAL
                         then bindings
                       else dummy pattern_type actual_type bindings
                 in (bindings,(environment,actual,pat)::higher) end
               else
                 let
                   fun spine pat actual sofar = case view pat of
                       Application (pf,pa) =>
                         let val (af,aa) = dest_application actual
                             val next = spine pf af sofar
                         in partial environment pa aa next end
                     | _ => partial environment pat actual sofar
                 in spine pat actual sofar end
             end)
      fun type_bindings bindings (types,identities) =
        let
          fun union [] known = known
            | union remaining [] = remaining
            | union (ty::rest) known = union rest
                (if List.exists (fn old => Type.compare (ty,old)=EQUAL) known
                 then known else ty::known)
          val identities = union rigid_types identities
        in List.foldr
          (fn ({redex,residue},state) =>
            let val source = case view redex of
                    Variable => type_of redex
                  | _ => raise Mismatch "type binding redex"
                val target = type_of residue
            in metadata (fn () => Type.raw_match_type source target state)
            end) (types,identities) bindings end
      fun type_find current (bindings,identities) =
        if List.exists (fn old => Type.compare (current,old)=EQUAL) identities
          then current
        else
          let fun find [] = raise Missing
                | find ({redex,residue}::rest) =
                    if Type.compare (current,redex)=EQUAL then residue
                    else find rest
          in find bindings end
      fun type_insert (entry as {redex,residue}) (state as (types,ids)) =
        ((if Type.compare (type_find redex state,residue)=EQUAL then state
          else raise Mismatch "type binding clash")
         handle Missing =>
           if Type.compare (redex,residue)=EQUAL then (types,redex::ids)
           else (entry::types,ids))
      fun frees terms =
        let fun union [] known = known
              | union remaining [] = remaining
              | union (variable::rest) known = union rest
                  (if member variable known then known else variable::known)
        in List.foldr (fn (term,known) => union (free_variables term) known)
          [] terms end
      fun higher types (bindings,[]) = bindings
        | higher types (bindings,(environment,actual,pat)::rest) =
            (observe pat;observe actual;
             if variable pat then
               if same (actual,pat) then higher types (bindings,rest)
               else higher
                 (type_insert {redex=type_of pat,residue=type_of actual} types)
                 ({redex=pat,residue=actual}::bindings,rest)
             else
               let
                 val (head,arguments) = strip pat
                 val variables = frees arguments
                 val inst = instantiate_type (#1 types)
                 fun lookup variable =
                   find variable environment handle Missing =>
                   find variable bindings handle Missing =>
                   if member variable rigid_variables then variable
                   else raise Mismatch "unbound higher-order argument"
                 fun direct () =
                   let
                     val replacements = List.map
                       (fn variable =>
                         {redex=inst variable,residue=lookup variable})
                       variables
                     val instances = List.map inst arguments
                     val patterns = List.map (substitute replacements)
                       instances
                     val head' = inst head
                     val _ = applications head' patterns
                     val (actual_head,actual_arguments) = strip actual
                     val next =
                       if all_abconv ops (actual_arguments,patterns) then
                         if same (actual_head,head) then bindings
                         else insert {redex=head,residue=actual_head} bindings
                       else
                         let val replacements = List.map
                               (fn pattern => {redex=pattern,
                                 residue=if variable pattern then pattern
                                   else fresh_variable (type_of pattern)})
                               patterns
                             val body = substitute replacements actual
                             val variables = List.map #residue replacements
                             val value = abstractions variables body
                             val next = insert {redex=head,residue=value}
                               bindings
                             val instantiated = applications head' variables
                         in {redex=instantiated,residue=body}::next end
                   in higher types (next,rest) end
                 fun structural () =
                   let val (af,aa) = dest_application actual
                       val (pf,pa) = dest_application pat
                       val next = partial environment pa aa
                         (bindings,(environment,af,pf)::rest)
                       val types = type_bindings (#1 next) ([],[])
                   in higher types next end
               in attempt direct structural end)
      val _ = guard pattern val _ = guard target
      val _ = List.app guard rigid_variables
      val initial = partial [] pattern target ([],[])
      val types = type_bindings (#1 initial) ([],[])
      val bindings = higher types initial
      val (real_bindings,patterns) = List.partition
        (fn {redex,residue} => variable redex) bindings
      fun beta_insert (entry as {redex,residue}) bindings =
        ((if find redex bindings=residue then bindings
          else raise Mismatch "inconsistent beta counts")
         handle Missing => entry::bindings)
      val counts = List.foldr
        (fn ({redex,residue},known) =>
          attempt
            (fn () => let val (head,args) = strip redex
              in beta_insert {redex=head,residue=List.length args} known end)
            (fn () =>
              (Feedback.HOL_WARNING "" ""
                 "Inconsistent patterning in h.o. match";
               known))) [] patterns
      val types = type_bindings real_bindings ([],[])
      val terms = List.mapPartial
        (fn {redex,residue} =>
          let val variable = variable_with_type
                (redex,Type.type_subst (#1 types) (type_of redex))
          in if same (residue,variable) then NONE
             else SOME {redex=variable,residue=residue} end) real_bindings
      val _ = guard pattern val _ = guard target
      val _ = List.app
        (fn {redex,residue} => (guard redex;guard residue)) terms
    in {beta_counts=counts,terms=terms,types= #1 types} end
end
