(* Exact raw compatibility grammar, shared by graph and Value receivers. *)
structure SmtReplayRawClause :> SmtReplayRawClause =
struct
  structure C=SmtReplayNamedClause
  datatype 'node expression_key=RawNamed of 'node|RawTrue|RawFalse
    | RawNot of IntInf.int|RawOr of IntInf.int * IntInf.int
  type ('node,'tree,'key) operations =
    {tick:unit -> unit,header:unit -> unit,error:string -> exn,
     boolean:'node -> unit,constructor:'node -> unit,
     constant:Term.term -> 'node -> bool,
     operands:Term.term -> int -> 'node -> 'node list option,
     node_key:'node -> 'key,compare_node:'node * 'node -> order,
     compare_key:'key * 'key -> order,
     compare_ordinal:IntInf.int * IntInf.int -> order,
     root:'tree -> 'node,
     view:'tree -> ('node,'tree) C.tree_view,
     literal:{node:'node,atom:'node,negative:bool} -> 'tree,
     disjunction:{node:'node,left:'tree,right:'tree} -> 'tree,
     copy:unit -> unit,write:unit -> unit}
  type 'tree expression_row = 'tree * IntInf.int
  datatype ('tree,'key) expression_cache =
      Small of 'tree expression_row list
    | Indexed of ('key,'tree expression_row list) Redblackmap.dict *
        'tree expression_row
  fun discover
      ({tick,header,error,boolean,constructor,constant,operands,
        node_key,compare_node,compare_key,compare_ordinal,root,view,
        literal,disjunction,copy,write}:('node,'tree,'key)operations)
      {head,units,unit_tree,target} =
    let
      fun fail text=raise error text
      fun tag(RawNamed _)=0|tag RawTrue=1|tag RawFalse=2
        | tag(RawNot _)=3|tag(RawOr _)=4
      fun compare(a,b)=
        (tick();case Int.compare(tag a,tag b)of EQUAL=>
          (case(a,b)of(RawNamed x,RawNamed y)=>compare_node(x,y)
           |(RawNot x,RawNot y)=>compare_ordinal(x,y)
           |(RawOr(a,b),RawOr(c,d))=>
               (case compare_ordinal(a,c)of EQUAL=>compare_ordinal(b,d)
                 | answer=>answer)
           | _=>EQUAL)
         | answer=>answer)
      val _=write()val _=write()
      val keys=ref(Redblackmap.mkDict compare:
        ('node expression_key,IntInf.int)Redblackmap.dict)
      val _=write()val next=ref(0:IntInf.int)
      fun intern value=
        (tick();case Redblackmap.peek(!keys,value)of SOME id=>id
         | NONE=>let val id= !next val _=copy()val _=write()
             val _=next:=id+1
             val _=write()val _=keys:=Redblackmap.insert(!keys,value,id)
           in id end)
      fun named node=(boolean node;copy();intern(RawNamed node))
      fun atom node=
        if constant boolSyntax.T node then intern RawTrue
        else if constant boolSyntax.F node then intern RawFalse
        else named node
      (* Root keys select buckets only. Distinct occurrences of the same
         root can have different clause trees, so require pointer identity
         for every hit. Small caches and hits on the most recently inserted
         row avoid key lookup. *)
      val _ = write ()
      val expressions = ref (Small [])
      fun compare_roots (left,right) = (tick ();compare_key (left,right))
      fun bucket table key =
        (tick ();Option.getOpt (Redblackmap.peek (table,key),[]))
      fun root_key tree = node_key (root tree)
      fun insert table (row as (tree,_)) =
        let
          val key = root_key tree
          val rows = bucket table key
        in copy ();write ();Redblackmap.insert (table,key,row :: rows) end
      fun same tree (saved,_) = (tick ();Portable.pointer_eq (saved,tree))
      fun lookup table tree =
        List.find (same tree) (bucket table (root_key tree))
      fun seek tree = case !expressions of
          Indexed (table,recent) =>
            if same tree recent then SOME recent else lookup table tree
        | Small [] => NONE
        | Small (rows as newest :: _) =>
            let
              fun scan _ [] = NONE
                | scan 0 _ =
                    let
                      val _ = write ()
                      val table = List.foldr
                        (fn (row,table) => insert table row)
                        (Redblackmap.mkDict compare_roots) rows
                      val _ = write ()
                      val _ = expressions := Indexed (table,newest)
                    in lookup table tree end
                | scan left (row :: rest) =
                    if same tree row then SOME row else scan (left-1) rest
            in scan 48 rows end
      fun save row = case !expressions of
          Small rows => expressions := Small (row :: rows)
        | Indexed (table,_) =>
            expressions := Indexed (insert table row,row)
      fun expression tree=
        (tick();case seek tree of
         SOME(_,id)=>id|NONE=>
         let val id=case view tree of C.ClauseFalse node=>
               if constant boolSyntax.F node then intern RawFalse
               else fail "actual F occurrence changed"
             | C.ClauseLiteral{atom=node,negative,...}=>
                 let val key=atom node
                 in if negative then (copy();intern(RawNot key))
                   else key end
             | C.ClauseOr{left,right,...}=>
                 let val a=expression left val b=expression right
                 in copy();intern(RawOr(a,b))end
             val _=copy()val _=copy()val _=write()
             val _=save (tree,id)
         in id end)
      fun compare_dictionary(a,b)=(tick();compare_ordinal(a,b))
      val _=write()val _=write()
      val dictionary=ref(Redblackset.empty compare_dictionary)
      fun put id=(tick();write();
        dictionary:=Redblackset.add(!dictionary,id))
      fun contains id=(tick();Redblackset.member(!dictionary,id))
      fun target_entries tree=
        (put(expression tree);put(named(root tree));
         case view tree of C.ClauseOr{left,right,...}=>
           (target_entries left;target_entries right)|_=>())
      val target_tree=target()
      val _=target_entries target_tree
      fun unit saved=
        let val _=copy()val tree=unit_tree saved
            val complement=case view tree of
                C.ClauseLiteral{atom=node,negative=true,...}=>atom node
              | _=>let val key=expression tree
                   in copy();intern(RawNot key)end
        in put complement end
      val _=List.app unit units
      val _=put(intern RawFalse)
      fun shallow_literal node=
        let val _=boolean node
        in case operands boolSyntax.negation 1 node of SOME[child]=>
             (boolean child;constructor node;
              if constant boolSyntax.T child orelse
                  constant boolSyntax.F child then constructor child
                else();copy();literal
                  {node=node,atom=child,negative=true})
         | _=>(if constant boolSyntax.T node orelse
               constant boolSyntax.F node then constructor node else();
             copy();literal{node=node,atom=node,negative=false})
        end
      val _=write()val fallback=ref([]:'tree list)
      fun compare_done((a,b),(c,d))=
        (tick();case compare_key(a,c)of EQUAL=>compare_ordinal(b,d)
          | answer=>answer)
      val _=write()val _=write()val done=ref(Redblackset.empty compare_done)
      fun solve tree=
        let val node=root tree
            val _=boolean node
            val key=expression tree val alias=named node
            val _=copy()val memo=(node_key node,key)
            val _=tick()
        in if Redblackset.member(!done,memo)then header()else
          let
            val _=if contains key orelse contains alias then ()else
              case view tree of C.ClauseOr{left,right,...}=>
                  (solve left;solve right)
                | C.ClauseLiteral{negative=false,...}=>
                  (case operands boolSyntax.disjunction 2 node of
                     SOME[a,b]=>
                       let val _=constructor node
                           val left=shallow_literal a
                           val right=shallow_literal b
                           val _=copy()
                           val expanded=disjunction
                             {node=node,left=left,right=right}
                           val _=solve expanded
                           val _=copy()val _=write()
                       in fallback:=expanded:: !fallback end
                   | _=>fail "raw resolution unmatched literal")
                | _=>fail "raw resolution unmatched literal"
            val _=tick()val _=write()
            val _=done:=Redblackset.add(!done,memo)
            val _=header()
          in ()end
        end
      val _=solve(head())
    in !fallback end
end
