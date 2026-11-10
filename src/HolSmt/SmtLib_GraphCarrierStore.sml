structure SmtLib_GraphCarrierStore :> SmtLib_GraphCarrierStore =
struct
  structure Q = SmtLib_GraphQueryAnalysis
  structure D = SmtLib_OutputSchedule
  structure F = SmtLib_OutputFragments
  val ERR = Feedback.mk_HOL_ERR "SmtLib_GraphCarrierStore"

  type carrier = Q.carrier
  datatype origin =
      Ordinary of carrier
    | Fallback of {dependencies:carrier list,expression:carrier}
  datatype key = Key of
    {owner:unit ref,identity:int,arity:int,syntax:carrier,origin:origin}
  type binding = {identity:int,syntax:carrier,name:string}
  datatype bounds = Bounds of
    {owner:unit ref,bindings:(int,binding) Redblackmap.dict}
  datatype region = Region of
    {owner:unit ref,root:int,path:(int * int) list,
     environment:(int * string) list}
  type declaration = {key:key,name:string}
  type encoding =
    {input:carrier,head:carrier,atomic_head:Term.term option,
     smt_symbol:string,arity:int}
  datatype terms = Terms of
    {owner:unit ref,symbols:(key,declaration) Redblackmap.dict,
     sorts:(key,key * (string list * string)) Redblackmap.dict,
     order:key list,helpers:string list,encodings:encoding list,
     documents:(region,int * int) D.state}
  type symbol =
    {name:string,arity:int,syntax:carrier,origin:origin,
     graph_node:Q.scoped_node option,sorts:(string list * string) option}
  type interface =
    {operations:(carrier,bounds,terms,key)
       SmtLib.outbound_term_store_operations,
     empty_bounds:bounds,empty_terms:terms,
     region:int * bounds -> region,
     region_at:int * (int * int) list * bounds -> region,
     find_document:terms * region * carrier -> F.doc option,
     bind_document:terms * region * carrier * F.doc -> terms * F.doc,
     wrap_document:terms * region * F.doc -> F.doc,
     symbols:terms -> symbol list,encodings:terms -> encoding list}

  fun compare_key (Key {identity=left,arity=la,...},
      Key {identity=right,arity=ra,...}) =
    case Int.compare (left,right) of
      EQUAL => Int.compare (la,ra) | result => result
  fun compare_position ((ls,ln),(rs,rn)) =
    case Int.compare (ls,rs) of
      EQUAL => Int.compare (ln,rn) | result => result
  fun compare_binding_id ((left,ln),(right,rn)) =
    case Int.compare (left,right) of
      EQUAL => String.compare (ln,rn) | result => result
  fun compare_region (Region {root=left,path=lp,environment=le,...},
      Region {root=right,path=rp,environment=re,...}) =
    case Int.compare (left,right) of
      EQUAL =>
        (case List.collate compare_position (lp,rp) of
           EQUAL => List.collate compare_binding_id (le,re)
         | result => result)
    | result => result

  fun create (context:Q.outbound_context) {prefix} : interface =
    let
      val owner = ref ()
      fun alive () = ignore ((#key context) (#goal context))
      fun owned actual =
        (alive ();
         if Portable.pointer_eq (owner,actual) then ()
         else raise ERR "store" "different borrowed query store")
      fun guard current = ignore ((#key context) current)
      fun guard_key (Key {owner,syntax,origin,...}) =
        (owned owner;guard syntax;
         case origin of
           Ordinary original => guard original
         | Fallback {dependencies,expression} =>
             (List.app guard dependencies;guard expression))
      fun check_bounds (Bounds {owner,bindings}) =
        (owned owner;bindings)
      fun check_terms (state as Terms {owner,...}) =
        (owned owner;state)
      fun check_region (Region {owner,...}) = owned owner
      fun bound_peek (bounds,current) =
        let val bindings = check_bounds bounds
            val identity = (#semantic_key context) current
        in case Redblackmap.peek (bindings,identity) of
            NONE => NONE
          | SOME {syntax,name,...} =>
              (guard syntax;guard current;SOME name)
        end
      fun bound_find input = case bound_peek input of
          SOME name => name | NONE => raise Redblackmap.NotFound
      fun bound_insert (bounds,current,name) =
        let val bindings = check_bounds bounds
            val identity = (#semantic_key context) current
            val binding = {identity=identity,syntax=current,name=name}
        in Bounds {owner=owner,
          bindings=Redblackmap.insert (bindings,identity,binding)} end
      fun ordered_bounds bounds =
        let
          val bindings = check_bounds bounds
          fun decorate (_,binding as {syntax,...}:binding) =
            let val leaf = case (#view context) syntax of
                    Q.VariableView (_,raw) => SOME raw
                  | _ => NONE
            in (leaf,binding) end
          fun tie (left:binding,right:binding) =
            Int.compare (#identity left,#identity right)
          fun compare ((SOME left,lb),(SOME right,rb)) =
                (case Term.compare (left,right) of
                   EQUAL => tie (lb,rb) | result => result)
            | compare ((SOME _,_),(NONE,_)) = LESS
            | compare ((NONE,_),(SOME _,_)) = GREATER
            | compare ((NONE,left),(NONE,right)) = tie (left,right)
          val entries = List.map decorate (Redblackmap.listItems bindings)
        in List.map #2 (Listsort.sort compare entries) end
      fun bound_items bounds = List.map
        (fn {syntax,name,...}:binding => (syntax,name))
        (ordered_bounds bounds)
      fun bound_count bounds = Redblackmap.numItems (check_bounds bounds)
      fun ordinary_key (current,arity) =
        (alive ();
         Key {owner=owner,identity=(#semantic_key context) current,arity=arity,
           syntax=current,origin=Ordinary current})
      fun fallback_key (dependencies,expression) =
        let val _ = alive ()
            val syntax = (#list_mk_abs context) (dependencies,expression)
        in Key {owner=owner,identity=(#semantic_key context) syntax,
          arity=List.length dependencies,syntax=syntax,
          origin=Fallback {dependencies=dependencies,expression=expression}}
        end
      fun term_peek (terms,key) =
        let val Terms {symbols,...} = check_terms terms
            val _ = guard_key key
        in case Redblackmap.peek (symbols,key) of
            NONE => NONE
          | SOME {key=saved,name} => (guard_key saved;SOME name)
        end
      fun term_find input = case term_peek input of
          SOME name => name | NONE => raise Redblackmap.NotFound
      fun term_insert (terms,key,name) =
        let val Terms {symbols,sorts,order,helpers,encodings,documents,...} =
              check_terms terms
            val _ = guard_key key
            val order = if not (Option.isSome
                (Redblackmap.peek (symbols,key))) then
                key :: order else order
        in Terms {owner=owner,
          symbols=Redblackmap.insert (symbols,key,{key=key,name=name}),
          sorts=sorts,order=order,helpers=helpers,encodings=encodings,
          documents=documents} end
      fun term_count terms =
        let val Terms {symbols,...} = check_terms terms
        in Redblackmap.numItems symbols end
      fun record_sorts (terms,key,value) =
        let val Terms {symbols,sorts,order,helpers,encodings,documents,...} =
              check_terms terms
            val _ = guard_key key
        in Terms {owner=owner,symbols=symbols,
          sorts=Redblackmap.insert (sorts,key,(key,value)),
          order=order,helpers=helpers,encodings=encodings,
          documents=documents} end
      fun record_encoding (terms,{input,smt_symbol,arity}) =
        let val Terms {symbols,sorts,order,helpers,encodings,documents,...} =
              check_terms terms
            val _ = guard input
            val (head,_) = (#strip_comb context) input
            val atomic_head = case (#view context) head of
                Q.ConstantView atom => SOME atom
              | Q.VariableView (_,atom) => SOME atom | _ => NONE
            val _ = guard input val _ = guard head
            val encoding : encoding =
              {input=input,head=head,atomic_head=atomic_head,
               smt_symbol=smt_symbol,arity=arity}
        in Terms {owner=owner,symbols=symbols,sorts=sorts,order=order,
          helpers=helpers,encodings=encoding::encodings,
          documents=documents} end
      fun reserve_helper (terms,name) =
        let val Terms {symbols,sorts,order,helpers,encodings,documents,...} =
              check_terms terms
        in if List.exists (fn saved => saved=name) helpers then (terms,false)
          else (Terms {owner=owner,symbols=symbols,sorts=sorts,order=order,
            helpers=name::helpers,encodings=encodings,
            documents=documents},true) end
      fun region_at (root,path,bounds) = Region
        {owner=owner,root=root,path=path,environment=List.map
          (fn {identity,name,...}:binding => (identity,name))
          (ordered_bounds bounds)}
      fun region (root,bounds) = region_at (root,[],bounds)
      fun find_document (terms,region,current) =
        let val Terms {documents,...} = check_terms terms
            val _ = check_region region
            val position = (#key context) current
        in D.find (documents,region,position) end
      fun bind_document (terms,region,current,expression) =
        let val Terms {symbols,sorts,order,helpers,encodings,documents,...} =
              check_terms terms
            val _ = check_region region
            val position = (#key context) current
            val (documents,reference) =
              D.bind (documents,region,position,expression)
        in (Terms {owner=owner,symbols=symbols,sorts=sorts,
          order=order,helpers=helpers,encodings=encodings,
          documents=documents},reference) end
      fun wrap_document (terms,region,body) =
        let val Terms {documents,...} = check_terms terms
            val _ = check_region region
        in D.wrap (documents,region,body) end
      fun symbols terms =
        let val Terms {symbols,sorts,order,...} = check_terms terms
            fun describe key =
              let val {key=key as Key {syntax,origin,arity,...},name} =
                      Redblackmap.find (symbols,key)
                  val _ = guard_key key
                  val recorded = case Redblackmap.peek (sorts,key) of
                      NONE => NONE
                    | SOME (saved,value) => (guard_key saved;SOME value)
              in {name=name,arity=arity,syntax=syntax,origin=origin,
                graph_node=(#graph_node context) syntax,sorts=recorded}
              end
        in List.map describe (List.rev order) end
      fun encodings terms =
        let val Terms {encodings,...} = check_terms terms
            val _ = List.app (fn {input,head,...}:encoding =>
              (guard input;guard head)) encodings
        in List.rev encodings end
      val operations =
        {bound_find=bound_find,bound_peek=bound_peek,
         bound_insert=bound_insert,bound_items=bound_items,
         bound_count=bound_count,ordinary_key=ordinary_key,
         fallback_key=fallback_key,term_find=term_find,term_peek=term_peek,
         term_insert=term_insert,term_count=term_count,
         record_sorts=record_sorts,record_encoding=record_encoding,
         reserve_helper=reserve_helper}
      val _ = alive ()
    in
      {operations=operations,
       empty_bounds=Bounds {owner=owner,
         bindings=Redblackmap.mkDict Int.compare},
       empty_terms=Terms {owner=owner,
         symbols=Redblackmap.mkDict compare_key,
         sorts=Redblackmap.mkDict compare_key,order=[],helpers=[],encodings=[],
         documents=D.create {compare_region=compare_region,
           compare_key=compare_position,prefix=prefix}},
       region=region,region_at=region_at,find_document=find_document,
       bind_document=bind_document,wrap_document=wrap_document,symbols=symbols,
       encodings=encodings}
    end
end
