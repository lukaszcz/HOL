(* Fixed comparator tables.
   Planning records every constructor instruction in original evaluation order.
   No generic Redblack table/comparator can be wrapped by this API. *)
structure ReplayRedblackPrivateWork :> ReplayRedblackPrivateWork =
struct
  datatype color = R | B
  datatype ('k,'a) tree = E | T of color * ('k,'a) tree * 'k * 'a *
                                             ('k,'a) tree
  datatype 'a int_map = IntMap of int * (int,'a) tree
  datatype string_set = StringSet of int * (string,unit) tree
  type cost = {work : IntInf.int, views : IntInf.int,
    comparisons : IntInf.int, string_bytes : IntInf.int,
    plan_nodes : IntInf.int, finish_nodes : IntInf.int}
  exception Limit
  exception StalePlan
  (* A coupled private counter adapter, not an invocation or quote grant.
     Work constructs this with its OWN original counter and never accepts
     a caller adapter. Typed G/Backend programs have no callbacks. *)
  datatype scope_meter = ScopeMeter of
    {identity:unit ref,limit:int,charged:int ref}
    | PolicyScopeMeter of
    {identity:unit ref,limit:SmtReplayResourcePolicy.limit,
     charged:IntInf.int ref}
  fun new_scope_meter {limit,charged} =
    ScopeMeter {identity=ref (),limit=limit,charged=charged}
  fun same_scope_meter (ScopeMeter {identity=left,...},
                        ScopeMeter {identity=right,...}) = left = right
    | same_scope_meter (PolicyScopeMeter {identity=left,...},
                        PolicyScopeMeter {identity=right,...}) =
        left = right
    | same_scope_meter _ = false
  fun scope_meter_charge (ScopeMeter {limit,charged,...}) amount =
    if amount >= 0 andalso amount <= IntInf.fromInt (limit - !charged) then
      charged := !charged + IntInf.toInt amount
    else raise Limit
    | scope_meter_charge (PolicyScopeMeter {limit,charged,...}) amount =
        if amount >= 0 andalso
            SmtReplayResourcePolicy.allows limit (!charged+amount) then
          charged := !charged+amount else raise Limit
  fun scope_meter_charged (ScopeMeter {charged,...}) = !charged
    | scope_meter_charged (PolicyScopeMeter _) = raise Domain
  (* Exact private fixed-tree traversal, charged BEFORE its instructions.
     It neither allocates a second ledger nor runs an arbitrary comparator.
     All existing ordinary and planned table methods stay literal. *)
  fun scope_lookup_int meter (IntMap(_,tree),key) =
    let
      val _ = scope_meter_charge meter 4
      fun walk current =
        (scope_meter_charge meter 1;
         case current of E => NONE
         | T(_,left,saved,value,right) =>
           (scope_meter_charge meter 2;
            case Int.compare (key,saved) of
                LESS => (scope_meter_charge meter 1;walk left)
              | GREATER => (scope_meter_charge meter 1;walk right)
              | EQUAL => (scope_meter_charge meter 1;SOME value)))
    in walk tree end

  datatype ledger = Ledger of {ceiling : IntInf.int option,
    meter : scope_meter option,
    work : IntInf.int ref, views : IntInf.int ref,
    comparisons : IntInf.int ref, string_bytes : IntInf.int ref,
    plan_nodes : IntInf.int ref, finish_nodes : IntInf.int ref}
  fun ledger_with_meter cap meter =
    (* Fixed setup is admitted before the six counter references/record.
       Arithmetic/primitive string representation costs remain qualified.
       Coupling is only to the original typed meter, never a payer callback. *)
    if (case cap of SOME c => c < 16 | NONE => false) then raise Limit
    else
      (case meter of NONE => () | SOME m => scope_meter_charge m 16;
       Ledger {ceiling=cap,meter=meter,work=ref 16,views=ref 0,
         comparisons=ref 0,string_bytes=ref 0,plan_nodes=ref 0,
         finish_nodes=ref 0})
  fun ledger cap = ledger_with_meter cap NONE
  fun spend (Ledger {ceiling,meter,work,...}) n =
    let val next = !work + n in
      if n < 0 orelse (case ceiling of SOME c => next > c | NONE => false)
      then raise Limit
      else
        (case meter of NONE => () | SOME m => scope_meter_charge m n;
         work := next)
    end
  (* Every coupled debit precedes its effects, including future-finish
     reservations. Refusal retains prior debits; abandonment or a stale
     finish never refunds them. Finish methods do not charge again. *)
  fun counter l r n = (spend l n;r := !r+n)
  fun view_tick (l as Ledger {views,...}) = counter l views 1
  fun compare_tick (l as Ledger {comparisons,...}) = counter l comparisons 1
  fun cost (Ledger {work,views,comparisons,string_bytes,
                    plan_nodes,finish_nodes,...}) : cost =
    {work= !work,views= !views,comparisons= !comparisons,
     string_bytes= !string_bytes,plan_nodes= !plan_nodes,
     finish_nodes= !finish_nodes}
  fun int_compare l pair = (compare_tick l;Int.compare pair)
  fun string_compare (l as Ledger {string_bytes,...}) (a,b) =
    let
      val _ = compare_tick l
      val _ = spend l 2
      val na = String.size a
      val nb = String.size b
      fun loop i =
        (spend l 1;
         if i = na then if i = nb then EQUAL else LESS
         else if i = nb then GREATER
         else
           let val _ = counter l string_bytes 2
               val x = String.sub(a,i)
               val y = String.sub(b,i)
           in spend l 1;
              case Char.compare(x,y) of EQUAL => loop(i+1) | order => order
           end)
    in loop 0 end

  datatype 'a datum = Known of 'a | Input of int
  datatype ('k,'a) link = Held of ('k,'a) tree
    | Future of {color : color, left : ('k,'a) link, key : 'k,
        datum : 'a datum, right : ('k,'a) link,
        result : ('k,'a) tree option ref}
  datatype ('k,'a) exposed = Empty
    | Node of color * ('k,'a) link * 'k * 'a datum * ('k,'a) link
  fun expose l link =
    (view_tick l;
     case link of
       Held E => Empty
     | Held(T(c,a,k,v,b)) =>
         (spend l 4;Node(c,Held a,k,Known v,Held b))
     | Future {color,left,key,datum,right,...} =>
         (spend l 1;Node(color,left,key,datum,right)))
  fun node (l as Ledger {plan_nodes,finish_nodes,...}) instructions
           (c,a,k,v,b) =
    let
      (* One plan record, ref, link and program cons; replay includes reverse
         cons, instruction visit, two child slots, datum, T, slot and case. *)
      val _ = spend l 4
      val _ = plan_nodes := !plan_nodes+1
      val _ = spend l 10
      val _ = finish_nodes := !finish_nodes+1
      val link = Future {color=c,left=a,key=k,datum=v,right=b,result=ref NONE}
      val _ = instructions := link :: !instructions
    in link end
  fun root_black l instructions tree =
    case expose l tree of
      Empty => raise Fail "cannot be empty here"
    | Node(_,a,k,v,b) => node l instructions (B,a,k,v,b)
  fun map_insert l instructions compare root key value =
    let
      val _ = spend l 1
      val fresh = ref false
      fun make args = node l instructions args
      fun ins s =
        case expose l s of
          Empty => (fresh := true;make(R,Held E,key,value,Held E))
        | Node(color,a,yk,y,b) =>
          (spend l 1;
           case compare(key,yk) of
             EQUAL => make(color,a,key,value,b)
           | LESS =>
             (case expose l a of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(color,make(R,c,key,value,d),yk,y,b)
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,e,wk,w,f),zk,z,make(B,d,yk,y,b))
                         | _ => make(B,make(R,next,zk,z,d),yk,y,b)
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,c,zk,z,e),wk,w,make(B,f,yk,y,b))
                         | _ => make(B,make(R,c,zk,z,next),yk,y,b)
                       end)
              | _ => make(B,ins a,yk,y,b))
           | GREATER =>
             (case expose l b of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(color,a,yk,y,make(R,c,key,value,d))
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,a,yk,y,e),wk,w,make(B,f,zk,z,d))
                         | _ => make(B,a,yk,y,make(R,next,zk,z,d))
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,a,yk,y,c),zk,z,make(B,e,wk,w,f))
                         | _ => make(B,a,yk,y,make(R,c,zk,z,next))
                       end)
              | _ => make(B,a,yk,y,ins b)))
    in
      ((
        case expose l root of
          Empty => (fresh := true;make(B,Held E,key,value,Held E))
        | Node(color,a,yk,y,b) =>
          (spend l 1;
           case compare(key,yk) of
             EQUAL => make(B,a,key,value,b)
           | LESS =>
             (case expose l a of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(B,make(R,c,key,value,d),yk,y,b)
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,e,wk,w,f),zk,z,make(B,d,yk,y,b))
                         | _ => make(B,make(R,next,zk,z,d),yk,y,b)
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,c,zk,z,e),wk,w,make(B,f,yk,y,b))
                         | _ => make(B,make(R,c,zk,z,next),yk,y,b)
                       end)
              | _ => make(B,ins a,yk,y,b))
           | GREATER =>
             (case expose l b of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(B,a,yk,y,make(R,c,key,value,d))
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,a,yk,y,e),wk,w,make(B,f,zk,z,d))
                         | _ => make(B,a,yk,y,make(R,next,zk,z,d))
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,a,yk,y,c),zk,z,make(B,e,wk,w,f))
                         | _ => make(B,a,yk,y,make(R,c,zk,z,next))
                       end)
              | _ => make(B,a,yk,y,ins b)))
       ),!fresh)
    end

  fun set_insert l instructions compare root key =
    let
      val _ = spend l 1
      val fresh = ref false
      fun make args = node l instructions args
      fun lbalance z left right =
        case expose l left of
          Node(R,y,b,_,c) =>
            (case expose l y of
               Node(R,a,x,_,d) =>
                 make(R,make(B,a,x,Known(),d),b,Known(),
                      make(B,c,z,Known(),right))
             | _ =>
                (case expose l c of
                   Node(R,d,k,_,e) =>
                     make(R,make(B,y,b,Known(),d),k,Known(),
                          make(B,e,z,Known(),right))
                 | _ => make(B,left,z,Known(),right)))
        | _ => make(B,left,z,Known(),right)
      fun rbalance x left right =
        case expose l right of
          Node(R,b,y,_,c) =>
            (case expose l c of
               Node(R,d,z,_,e) =>
                 make(R,make(B,left,x,Known(),b),y,Known(),
                      make(B,d,z,Known(),e))
             | _ =>
                (case expose l b of
                   Node(R,d,k,_,e) =>
                     make(R,make(B,left,x,Known(),d),k,Known(),
                          make(B,e,y,Known(),c))
                 | _ => make(B,left,x,Known(),right)))
        | _ => make(B,left,x,Known(),right)
      fun ins tree =
        case expose l tree of
          Empty => (fresh := true;make(R,Held E,key,Known(),Held E))
        | Node(color,left,x,_,right) =>
          (spend l 1;
           case compare(key,x) of
             EQUAL => make(color,left,key,Known(),right)
           | LESS => let val next=ins left in
                (spend l 1;
                 if color=B then lbalance x next right
                else make(R,next,x,Known(),right)) end
           | GREATER => let val next=ins right in
                (spend l 1;
                 if color=B then rbalance x left next
                else make(R,left,x,Known(),next)) end)
      val next=ins root
      val answer=case expose l next of
          Node(R,left,x,v,right) => make(B,left,x,v,right)
        | _ => next
    in (answer,!fresh) end

  fun same_int pair = Portable.pointer_eq pair
  fun same_string pair = Portable.pointer_eq pair
  fun empty_int () = IntMap(0,E)
  fun empty_string () = StringSet(0,E)
  datatype 'a int_lookup = IntLookup of
    {base : 'a int_map,answer : 'a option,cost : cost,used : bool ref}
  datatype string_lookup = StringLookup of
    {base : string_set,answer : bool,cost : cost,used : bool ref}
  fun search l compare tree key =
    (view_tick l;
     case tree of E => NONE
     | T(_,left,k,v,right) =>
       (spend l 1;
        case compare(key,k) of
          LESS => search l compare left key
        | GREATER => search l compare right key
        | EQUAL => (spend l 1;SOME v)))
  fun plan_lookup_int cap meter (base as IntMap(_,tree),key) =
    let val l=ledger_with_meter cap meter
        val answer=search l (int_compare l) tree key
        val _=spend l 8
    in IntLookup {base=base,answer=answer,cost=cost l,used=ref false} end
  fun lookup_int (base,key,ceiling) =
    plan_lookup_int (SOME ceiling) NONE (base,key)
  fun scope_plan_lookup_int meter args =
    plan_lookup_int NONE (SOME meter) args
  fun plan_lookup_string cap meter (base as StringSet(_,tree),key) =
    let val l=ledger_with_meter cap meter
        val answer=Option.isSome(search l (string_compare l) tree key)
        val _=spend l 8
    in StringLookup {base=base,answer=answer,cost=cost l,used=ref false} end
  fun lookup_string (base,key,ceiling) =
    plan_lookup_string (SOME ceiling) NONE (base,key)
  fun scope_plan_lookup_string meter args =
    plan_lookup_string NONE (SOME meter) args
  fun int_lookup_cost (IntLookup {cost,...}) = cost
  fun string_lookup_cost (StringLookup {cost,...}) = cost
  fun retire same (current,base,used) =
    if !used then raise StalePlan
    else (used := true;if same(current,base) then () else raise StalePlan)
  fun int_lookup_value (current,IntLookup {base,answer,used,...}) =
    (retire same_int (current,base,used);answer)
  fun string_lookup_value (current,StringLookup {base,answer,used,...}) =
    (retire same_string (current,base,used);answer)

  datatype 'a int_batch = IntBatch of
    {base : 'a int_map,root : (int,'a) link,
     instructions : (int,'a) link list,count : int,payloads : int,
     cost : cost,used : bool ref}
  type 'a int_insertion = 'a int_batch
  datatype string_insertion = StringInsertion of
    {base : string_set,root : (string,unit) link,
     instructions : (string,unit) link list,count : int,
     cost : cost,used : bool ref}
  fun plan_batch_with_meter cap meter (base as IntMap(count,tree),keys) =
    let
      val l=ledger_with_meter cap meter
      val _=spend l 2
      val instructions=ref []
      fun loop remaining root count ordinal =
        (spend l 1;
         case remaining of
           [] => (root,count,ordinal)
         | key::rest =>
           let val _=spend l 1
               val (next,fresh)=map_insert l instructions
                 (int_compare l) root key (Input ordinal)
               val _=spend l 2
           in loop rest next (if fresh then count+1 else count) (ordinal+1)
           end)
      val (root,count,n)=loop keys (Held tree) count 0
      (* Exact bounded payload scan, array cells and wrapper, final table,
         plan fields/ref and one-shot identity/retirement checks. *)
      val _=spend l (IntInf.fromInt n*3+16)
    in IntBatch {base=base,root=root,instructions= !instructions,count=count,
      payloads=n,cost=cost l,used=ref false} end
  fun plan_batch cap args = plan_batch_with_meter cap NONE args
  fun insert_int_batch (base,keys,ceiling) =
    plan_batch (SOME ceiling) (base,keys)
  fun insert_int (base,key,ceiling) =
    plan_batch (SOME ceiling) (base,[key])
  fun scope_plan_insert_int_batch meter args =
    plan_batch_with_meter NONE (SOME meter) args
  fun scope_plan_insert_int meter (base,key) =
    scope_plan_insert_int_batch meter (base,[key])
  fun int_batch_cost (IntBatch {cost,...}) = cost
  val int_insertion_cost = int_batch_cost
  fun read_link (Held tree) = tree
    | read_link (Future {result,...}) =
        case !result of SOME tree => tree | NONE => raise StalePlan
  fun replay instructions payloads =
    let
      fun step (Future {color,left,key,datum,right,result}) =
            let val data=case datum of Known v => v
                  | Input i => Array.sub(payloads,i)
                val tree=T(color,read_link left,key,data,read_link right)
            in result := SOME tree end
        | step _ = raise StalePlan
    in List.app step (List.rev instructions) end
  fun exact_payloads 0 [] = ()
    | exact_payloads n (_::rest) =
        if n>0 then exact_payloads (n-1) rest else raise StalePlan
    | exact_payloads _ _ = raise StalePlan
  fun finish_int_batch
      (current,IntBatch {base,root,instructions,count,payloads,used,...},values) =
    (retire same_int (current,base,used);
     exact_payloads payloads values;
     replay instructions (Array.fromList values);
     IntMap(count,read_link root))
  fun finish_int (current,plan,value) = finish_int_batch(current,plan,[value])
  fun plan_string_with_meter cap meter (base as StringSet(count,tree),key) =
    let
      val l=ledger_with_meter cap meter
      val _=spend l 2
      val instructions=ref []
      val (root,fresh)=set_insert l instructions (string_compare l)
                                      (Held tree) key
      val _=spend l 16
    in StringInsertion {base=base,root=root,instructions= !instructions,
      count=if fresh then count+1 else count,cost=cost l,used=ref false} end
  fun plan_string cap args = plan_string_with_meter cap NONE args
  fun insert_string (base,key,ceiling) =
    plan_string (SOME ceiling) (base,key)
  fun scope_plan_insert_string meter args =
    plan_string_with_meter NONE (SOME meter) args
  fun string_insertion_cost (StringInsertion {cost,...}) = cost
  fun finish_string
      (current,StringInsertion {base,root,instructions,count,used,...}) =
    (retire same_string(current,base,used);
     replay instructions (Array.fromList []);
     StringSet(count,read_link root))

  (* Deliberate ordinary operations on fixed handles. No quota claim;
     planner primitives above have no caller-supplied comparator or callbacks. *)
  fun peek_int (IntMap(_,tree),key) =
    let fun walk E = NONE
          | walk (T(_,left,current,value,right)) =
              (case Int.compare (key,current) of
                  LESS => walk left
                | GREATER => walk right
                | EQUAL => SOME value)
    in walk tree end
  fun member_string (StringSet(_,tree),key) =
    let fun walk E = false
          | walk (T(_,left,current,_,right)) =
              (case String.compare (key,current) of
                  LESS => walk left
                | GREATER => walk right
                | EQUAL => true)
    in walk tree end
  (* Ordinary updates expose no cost or plan and have no coupled meter.
     Use the SAME constructor/rotation programme directly, avoiding a
     temporary ledger, Future tree and replay. Metered/planned operations
     above remain literal. Exact tree shape matters to their later costs. *)
  fun direct_map_insert compare root key value =
    let
      val fresh = ref false
      fun make args = T args
      fun ins s =
        case s of
          E => (fresh := true;make(R,E,key,value,E))
        | T(color,a,yk,y,b) =>
          (
           case compare(key,yk) of
             EQUAL => make(color,a,key,value,b)
           | LESS =>
             (case a of
                T(R,c,zk,z,d) =>
                  (
                   case compare(key,zk) of
                     EQUAL => make(color,make(R,c,key,value,d),yk,y,b)
                   | LESS =>
                       let val next = ins c in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(R,make(B,e,wk,w,f),zk,z,make(B,d,yk,y,b))
                         | _ => make(B,make(R,next,zk,z,d),yk,y,b)
                       end
                   | GREATER =>
                       let val next = ins d in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(R,make(B,c,zk,z,e),wk,w,make(B,f,yk,y,b))
                         | _ => make(B,make(R,c,zk,z,next),yk,y,b)
                       end)
              | _ => make(B,ins a,yk,y,b))
           | GREATER =>
             (case b of
                T(R,c,zk,z,d) =>
                  (
                   case compare(key,zk) of
                     EQUAL => make(color,a,yk,y,make(R,c,key,value,d))
                   | LESS =>
                       let val next = ins c in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(R,make(B,a,yk,y,e),wk,w,make(B,f,zk,z,d))
                         | _ => make(B,a,yk,y,make(R,next,zk,z,d))
                       end
                   | GREATER =>
                       let val next = ins d in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(R,make(B,a,yk,y,c),zk,z,make(B,e,wk,w,f))
                         | _ => make(B,a,yk,y,make(R,c,zk,z,next))
                       end)
              | _ => make(B,a,yk,y,ins b)))
    in
      ((
        case root of
          E => (fresh := true;make(B,E,key,value,E))
        | T(color,a,yk,y,b) =>
          (
           case compare(key,yk) of
             EQUAL => make(B,a,key,value,b)
           | LESS =>
             (case a of
                T(R,c,zk,z,d) =>
                  (
                   case compare(key,zk) of
                     EQUAL => make(B,make(R,c,key,value,d),yk,y,b)
                   | LESS =>
                       let val next = ins c in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(B,make(B,e,wk,w,f),zk,z,make(B,d,yk,y,b))
                         | _ => make(B,make(R,next,zk,z,d),yk,y,b)
                       end
                   | GREATER =>
                       let val next = ins d in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(B,make(B,c,zk,z,e),wk,w,make(B,f,yk,y,b))
                         | _ => make(B,make(R,c,zk,z,next),yk,y,b)
                       end)
              | _ => make(B,ins a,yk,y,b))
           | GREATER =>
             (case b of
                T(R,c,zk,z,d) =>
                  (
                   case compare(key,zk) of
                     EQUAL => make(B,a,yk,y,make(R,c,key,value,d))
                   | LESS =>
                       let val next = ins c in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(B,make(B,a,yk,y,e),wk,w,make(B,f,zk,z,d))
                         | _ => make(B,a,yk,y,make(R,next,zk,z,d))
                       end
                   | GREATER =>
                       let val next = ins d in
                         case next of
                           T(R,e,wk,w,f) =>
                             make(B,make(B,a,yk,y,c),zk,z,make(B,e,wk,w,f))
                         | _ => make(B,a,yk,y,make(R,c,zk,z,next))
                       end)
              | _ => make(B,a,yk,y,ins b)))
       ),!fresh)
    end

  fun direct_set_insert compare root key =
    let
      val fresh = ref false
      fun make args = T args
      fun lbalance z left right =
        case left of
          T(R,y,b,_,c) =>
            (case y of
               T(R,a,x,_,d) =>
                 make(R,make(B,a,x,(),d),b,(),
                      make(B,c,z,(),right))
             | _ =>
                (case c of
                   T(R,d,k,_,e) =>
                     make(R,make(B,y,b,(),d),k,(),
                          make(B,e,z,(),right))
                 | _ => make(B,left,z,(),right)))
        | _ => make(B,left,z,(),right)
      fun rbalance x left right =
        case right of
          T(R,b,y,_,c) =>
            (case c of
               T(R,d,z,_,e) =>
                 make(R,make(B,left,x,(),b),y,(),
                      make(B,d,z,(),e))
             | _ =>
                (case b of
                   T(R,d,k,_,e) =>
                     make(R,make(B,left,x,(),d),k,(),
                          make(B,e,y,(),c))
                 | _ => make(B,left,x,(),right)))
        | _ => make(B,left,x,(),right)
      fun ins tree =
        case tree of
          E => (fresh := true;make(R,E,key,(),E))
        | T(color,left,x,_,right) =>
          (
           case compare(key,x) of
             EQUAL => make(color,left,key,(),right)
           | LESS => let val next=ins left in
                (
                 if color=B then lbalance x next right
                else make(R,next,x,(),right)) end
           | GREATER => let val next=ins right in
                (
                 if color=B then rbalance x left next
                else make(R,left,x,(),next)) end)
      val next=ins root
      val answer=case next of
          T(R,left,x,v,right) => make(B,left,x,v,right)
        | _ => next
    in (answer,!fresh) end

  fun put_int (IntMap(count,tree),key,value) =
    let val (next,fresh) = direct_map_insert Int.compare tree key value
    in IntMap(if fresh then count+1 else count,next) end
  fun add_string (StringSet(count,tree),key) =
    let val (next,fresh) = direct_set_insert String.compare tree key
    in StringSet(if fresh then count+1 else count,next) end
  fun list_int (IntMap(_,tree)) =
    let fun walk E rest = rest
          | walk (T(_,a,k,v,b)) rest = walk a ((k,v)::walk b rest)
    in walk tree [] end

  (* Ordered list plans retain actual paths/slots; no payload inspection. *)
  datatype 'a list_value = HeldValue of 'a
    | ProducedValue of (int,'a) tree option ref
  datatype 'a int_listing = IntListing of
    {base : 'a int_map,rows : (int * 'a list_value) list,
     cost : cost,used : bool ref}
  datatype 'a listing_phase = ListingPrepared
    | ListingBound of 'a int_map | ListingDead
  datatype 'a int_batch_listing = IntBatchListing of
    {batch : 'a int_batch,rows : (int * 'a list_value) list,
     cost : cost,phase : 'a listing_phase ref}

  fun listing_rows l link =
    let
      (* Every actual tree/link visit, including empty children, is charged.
         Per nonempty row: value-location + pair + retained cons, then
         future row case + value access + returned pair + returned cons.
         No table cardinality or abstract height estimate supplies this. *)
      fun visit current rest =
        (view_tick l;
         case current of
           Held E => rest
         | Held(T(_,left,key,value,right)) =>
             let val _=spend l 2
                 val a=Held left val b=Held right
                 val tail=visit b rest
                 val _=spend l 3
                 val _=spend l 4
                 val row=(key,HeldValue value)::tail
             in visit a row end
         | Future {left,key,right,result,...} =>
             let val tail=visit right rest
                 val _=spend l 3
                 val _=spend l 8
                 val row=(key,ProducedValue result)::tail
             in visit left row end)
    in visit link [] end

  fun plan_list_int cap meter (base as IntMap(_,tree)) =
    let val l=ledger_with_meter cap meter
        (* Held root link, final record/wrapper/ref; future empty-list case,
           one-shot state/identity/retirement and result field accesses. *)
        val _=spend l 10
        val rows=listing_rows l (Held tree)
    in IntListing {base=base,rows=rows,cost=cost l,used=ref false} end
  fun list_int_plan (base,ceiling) =
    plan_list_int (SOME ceiling) NONE base
  fun scope_plan_list_int meter base =
    plan_list_int NONE (SOME meter) base
  fun int_listing_cost (IntListing {cost,...}) = cost
  fun copy_listing [] = []
    | copy_listing ((key,HeldValue value)::rest) =
        (key,value)::copy_listing rest
    | copy_listing ((key,ProducedValue result)::rest) =
        (case !result of
           SOME(T(_,_,held,value,_)) =>
             if held=key then (key,value)::copy_listing rest
             else raise StalePlan
         | _ => raise StalePlan)
  fun finish_list_int (current,IntListing {base,rows,used,...}) =
    (retire same_int(current,base,used);copy_listing rows)

  fun plan_list_int_batch cap meter (batch as IntBatch {root,used,...}) =
    let val l=ledger_with_meter cap meter
        (* Final captured batch plan/phase reference, future two phase
           guards/state writes/binding wrapper and final empty-list case.
           Underlying batch finish has its OWN retained authentic cost. *)
        val _=spend l 24
        val _=if !used then raise StalePlan else ()
        val rows=listing_rows l root
    in IntBatchListing {batch=batch,rows=rows,cost=cost l,
      phase=ref ListingPrepared} end
  fun list_int_batch_plan (batch,ceiling) =
    plan_list_int_batch (SOME ceiling) NONE batch
  fun scope_plan_list_int_batch meter batch =
    plan_list_int_batch NONE (SOME meter) batch
  fun int_batch_listing_cost (IntBatchListing {cost,...}) = cost
  fun finish_int_batch_with_listing
      (current,IntBatchListing {batch,phase,...},values) =
    ((case !phase of ListingPrepared => () | _ => raise StalePlan;
      phase := ListingDead;
      let val table=finish_int_batch(current,batch,values)
      in phase := ListingBound table;table end)
     handle primary => (phase := ListingDead;raise primary))
  fun finish_batch_list_int
      (current,IntBatchListing {rows,phase,...}) =
    ((case !phase of
        ListingBound held =>
          (phase := ListingDead;
           if same_int(current,held) then copy_listing rows
           else raise StalePlan)
      | _ => (phase := ListingDead;raise StalePlan))
     handle primary => (phase := ListingDead;raise primary))
  fun new_scope_meter_with_policy {limit,charged} =
    if !charged >= 0 andalso
        SmtReplayResourcePolicy.allows limit (!charged) then
      PolicyScopeMeter {identity=ref (),limit=limit,charged=charged}
    else raise Limit
  fun scope_meter_charged_policy (PolicyScopeMeter {charged,...}) = !charged
    | scope_meter_charged_policy (ScopeMeter {charged,...}) =
        IntInf.fromInt (!charged)
  fun table_policy_ceiling SmtReplayResourcePolicy.Uncapped=NONE
    | table_policy_ceiling (SmtReplayResourcePolicy.AtMost maximum)=
        SOME maximum
  fun lookup_int_with_policy (base,key,maximum) =
    plan_lookup_int (table_policy_ceiling maximum) NONE (base,key)
  fun insert_int_batch_with_policy (base,keys,maximum)=
    plan_batch (table_policy_ceiling maximum) (base,keys)
  fun insert_int_with_policy (base,key,maximum)=
    plan_batch (table_policy_ceiling maximum) (base,[key])
  fun insert_string_with_policy (base,key,maximum)=
    plan_string (table_policy_ceiling maximum) (base,key)
  fun lookup_string_with_policy (base,key,maximum) =
    plan_lookup_string (table_policy_ceiling maximum) NONE (base,key)
  fun list_int_plan_with_policy (base,maximum) =
    plan_list_int (table_policy_ceiling maximum) NONE base
  fun list_int_batch_plan_with_policy (batch,maximum) =
    plan_list_int_batch (table_policy_ceiling maximum) NONE batch
  fun reachable_plan_node (l as Ledger {plan_nodes,finish_nodes,...}) instructions
           (c,a,k,v,b) =
    let
      (* One plan record, ref, link and program cons; replay includes reverse
         cons, instruction visit, two child slots, datum, T, slot and case. *)
      val _ = spend l 4
      val _ = plan_nodes := !plan_nodes+1
      val link = Future {color=c,left=a,key=k,datum=v,right=b,result=ref NONE}
      val _ = instructions := link :: !instructions
    in link end
  fun map_insert_reachable l instructions compare root key value =
    let
      val _ = spend l 1
      val fresh = ref false
      fun make args = reachable_plan_node l instructions args
      fun ins s =
        case expose l s of
          Empty => (fresh := true;make(R,Held E,key,value,Held E))
        | Node(color,a,yk,y,b) =>
          (spend l 1;
           case compare(key,yk) of
             EQUAL => make(color,a,key,value,b)
           | LESS =>
             (case expose l a of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(color,make(R,c,key,value,d),yk,y,b)
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,e,wk,w,f),zk,z,make(B,d,yk,y,b))
                         | _ => make(B,make(R,next,zk,z,d),yk,y,b)
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,c,zk,z,e),wk,w,make(B,f,yk,y,b))
                         | _ => make(B,make(R,c,zk,z,next),yk,y,b)
                       end)
              | _ => make(B,ins a,yk,y,b))
           | GREATER =>
             (case expose l b of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(color,a,yk,y,make(R,c,key,value,d))
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,a,yk,y,e),wk,w,make(B,f,zk,z,d))
                         | _ => make(B,a,yk,y,make(R,next,zk,z,d))
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(R,make(B,a,yk,y,c),zk,z,make(B,e,wk,w,f))
                         | _ => make(B,a,yk,y,make(R,c,zk,z,next))
                       end)
              | _ => make(B,a,yk,y,ins b)))
    in
      ((
        case expose l root of
          Empty => (fresh := true;make(B,Held E,key,value,Held E))
        | Node(color,a,yk,y,b) =>
          (spend l 1;
           case compare(key,yk) of
             EQUAL => make(B,a,key,value,b)
           | LESS =>
             (case expose l a of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(B,make(R,c,key,value,d),yk,y,b)
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,e,wk,w,f),zk,z,make(B,d,yk,y,b))
                         | _ => make(B,make(R,next,zk,z,d),yk,y,b)
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,c,zk,z,e),wk,w,make(B,f,yk,y,b))
                         | _ => make(B,make(R,c,zk,z,next),yk,y,b)
                       end)
              | _ => make(B,ins a,yk,y,b))
           | GREATER =>
             (case expose l b of
                Node(R,c,zk,z,d) =>
                  (spend l 1;
                   case compare(key,zk) of
                     EQUAL => make(B,a,yk,y,make(R,c,key,value,d))
                   | LESS =>
                       let val next = ins c in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,a,yk,y,e),wk,w,make(B,f,zk,z,d))
                         | _ => make(B,a,yk,y,make(R,next,zk,z,d))
                       end
                   | GREATER =>
                       let val next = ins d in
                         case expose l next of
                           Node(R,e,wk,w,f) =>
                             make(B,make(B,a,yk,y,c),zk,z,make(B,e,wk,w,f))
                         | _ => make(B,a,yk,y,make(R,c,zk,z,next))
                       end)
              | _ => make(B,a,yk,y,ins b)))
       ),!fresh)
    end

  (* NEW private discovery programme. Returns reverse postorder, so the
     literal existing replay's List.rev executes child Futures first.
     Held subtrees are already materialized and are NEVER descended into.
     Parameter/meter transport and R billing-counter admin retain the
     explicit existing terminating primitive model, not whole CPU pricing. *)
  fun reachable_finish_instructions (l as Ledger {finish_nodes,...}) root =
    let
      val _ = spend l 1 (* Actual invocation-local recursive closure. *)
      fun visit current rest =
        (view_tick l; (* Actual link tag/case before inspection. *)
         case current of
             Held _ => rest
           | Future _ =>
               let
                 (* Second tag/payload, left/right projections+holds6. *)
                 val _ = spend l 6
                 val Future {left,right,...} = current
                 val _ = spend l 3 (* Left recursive apps2 + held answer1. *)
                 val after_left = visit left rest
                 val _ = spend l 3 (* Right recursive apps2 + held answer1. *)
                 val after_right = visit right after_left
                 val _ = spend l 1 (* Actual reachable-program list cons. *)
                 (* SAME original10 future replay programme, now only for
                    an actually retained Future; no old charge/refund. *)
                 val _ = spend l 10
                 val _ = finish_nodes := !finish_nodes+1
               in current :: after_right end)
      val _ = spend l 2 (* Actual initial visit applications. *)
    in visit root [] end

  fun plan_batch_reachable cap (base as IntMap(count,tree),keys) =
    let
      val l=ledger cap
      val _=spend l 2
      val instructions=ref []
      fun loop remaining root count ordinal =
        (spend l 1;
         case remaining of
           [] => (root,count,ordinal)
         | key::rest =>
           let val _=spend l 1
               val (next,fresh)=map_insert_reachable l instructions
                 (int_compare l) root key (Input ordinal)
               val _=spend l 2
           in loop rest next (if fresh then count+1 else count) (ordinal+1)
           end)
      val (root,count,n)=loop keys (Held tree) count 0
      (* Actual outer discovery applications2 + result hold1. *)
      val _ = spend l 3
      val live = reachable_finish_instructions l root
      (* Actual private history-ref replacement; no public token escapes. *)
      val _ = spend l 1
      val _ = instructions := live
      (* Exact bounded payload scan, array cells and wrapper, final table,
         plan fields/ref and one-shot identity/retirement checks. *)
      val _=spend l (IntInf.fromInt n*3+16)
    in IntBatch {base=base,root=root,instructions= !instructions,count=count,
      payloads=n,cost=cost l,used=ref false} end
  (* NEW API ONLY: existing single/string/batch APIs remain byte-literal. *)
  fun insert_int_batch_reachable (base,keys,ceiling) =
    plan_batch_reachable (SOME ceiling) (base,keys)

  (* Authentic post-debit remaining query on a genuine policy meter.
     The original counter/limit stay opaque here. The bounded pre-charge
     metadata and debit primitive are the explicit nonrecursive base.
     No productive Graph effect or remaining snapshot precedes payment. *)
  fun scope_meter_remaining_with_policy meter =
    case meter of
        ScopeMeter _ => raise Domain
      | PolicyScopeMeter {limit,charged,...} =>
          let
            val local_fee = case limit of
                SmtReplayResourcePolicy.Uncapped => 35
              | SmtReplayResourcePolicy.AtMost _ => 45
            val _ = scope_meter_charge meter local_fee
            val current = !charged
          in SmtReplayResourcePolicy.remaining limit current end



  (* Additive fixed vocabulary. Restricting to the first two constructors
     reproduces G.type_compare; the last three reproduce G.key_compare.
     Cross-domain order is auxiliary and grants no G/type/native authority. *)
  datatype graph_key =
      GraphTypeVariable of string
    | GraphTypeOperator of KernelSig.kernelid * int list
    | GraphVariable of int * int * string * int
    | GraphConstant of KernelSig.kernelid * int
    | GraphApplication of int * int * int
  datatype 'a graph_key_map =
    GraphKeyMap of int * (graph_key,'a) tree

  fun graph_key_tag (GraphTypeVariable _) = 0
    | graph_key_tag (GraphTypeOperator _) = 1
    | graph_key_tag (GraphVariable _) = 2
    | graph_key_tag (GraphConstant _) = 3
    | graph_key_tag (GraphApplication _) = 4

  (* Same byte-lexicographic programme as the private string planner,
     charged on the supplied real counter BEFORE each named operation.
     Primitive arithmetic/representation CPU is not a full-tariff claim. *)
  fun scope_graph_string_compare meter (left,right) =
    let
      val _ = scope_meter_charge meter 16
      val _ = scope_meter_charge meter 2
      val nl = String.size left
      val nr = String.size right
      fun loop i =
        (scope_meter_charge meter 1;
         if i = nl then if i = nr then EQUAL else LESS
         else if i = nr then GREATER
         else
           let
             val _ = scope_meter_charge meter 2
             val a = String.sub(left,i)
             val b = String.sub(right,i)
             val _ = scope_meter_charge meter 1
           in case Char.compare(a,b) of
               EQUAL => loop(i+1)
             | order => order
           end)
    in loop 0 end

  fun scope_graph_int_compare meter pair =
    (scope_meter_charge meter 1;Int.compare pair)

  fun scope_graph_id_compare meter (left,right) =
    let
      (* Conservative fixed Source-admin/getter reservations, not quotes
         for arbitrary kernel operations. Immutable public getters only. *)
      val _ = scope_meter_charge meter 16
      val ln = KernelSig.name_of left
      val rn = KernelSig.name_of right
    in case scope_graph_string_compare meter (ln,rn) of
        EQUAL =>
          let
            val _ = scope_meter_charge meter 16
            val lt = KernelSig.seg_of left
            val rt = KernelSig.seg_of right
          in case scope_graph_string_compare meter (lt,rt) of
              EQUAL =>
                let
                  val _ = scope_meter_charge meter 12
                  val le = KernelSig.epoch_of left
                  val re = KernelSig.epoch_of right
                in scope_graph_int_compare meter (le,re) end
            | order => order
          end
      | order => order
    end

  fun scope_graph_int_list_compare meter (left,right) =
    (scope_meter_charge meter 16;
     case (left,right) of
         ([],[]) => EQUAL
       | ([],_) => LESS
       | (_,[]) => GREATER
       | (x::xs,y::ys) =>
           (case scope_graph_int_compare meter (x,y) of
               EQUAL => scope_graph_int_list_compare meter (xs,ys)
             | order => order))

  fun scope_compare_graph_key meter (left,right) =
    let
      (* Fixed tag views/calls, including branch reception. *)
      val _ = scope_meter_charge meter 16
      val a = graph_key_tag left
      val b = graph_key_tag right
    in case scope_graph_int_compare meter (a,b) of
        EQUAL =>
          (scope_meter_charge meter 24;
           case (left,right) of
               (GraphTypeVariable x,GraphTypeVariable y) =>
                 scope_graph_string_compare meter (x,y)
             | (GraphTypeOperator(x,xs),GraphTypeOperator(y,ys)) =>
                 (case scope_graph_id_compare meter (x,y) of
                     EQUAL => scope_graph_int_list_compare meter (xs,ys)
                   | order => order)
             | (GraphVariable(s,k,n,t),GraphVariable(s',k',n',t')) =>
                 (case scope_graph_int_compare meter (s,s') of
                     EQUAL =>
                       (case scope_graph_int_compare meter (k,k') of
                           EQUAL =>
                             (case scope_graph_string_compare meter (n,n') of
                                 EQUAL =>
                                   scope_graph_int_compare meter (t,t')
                               | order => order)
                         | order => order)
                   | order => order)
             | (GraphConstant(x,t),GraphConstant(y,t')) =>
                 (case scope_graph_id_compare meter (x,y) of
                     EQUAL => scope_graph_int_compare meter (t,t')
                   | order => order)
             | (GraphApplication(s,l,r),GraphApplication(s',l',r')) =>
                 (case scope_graph_int_compare meter (s,s') of
                     EQUAL =>
                       (case scope_graph_int_compare meter (l,l') of
                           EQUAL => scope_graph_int_compare meter (r,r')
                         | order => order)
                   | order => order)
             | _ => raise StalePlan)
      | order => order
    end

  fun scope_empty_graph_key meter =
    (scope_meter_charge meter 4;GraphKeyMap(0,E))

  fun scope_same_graph_key meter pair =
    (scope_meter_charge meter 4;Portable.pointer_eq pair)

  fun scope_graph_key_count meter (GraphKeyMap(count,_)) =
    (scope_meter_charge meter 4;count)

  fun scope_lookup_graph_key meter (GraphKeyMap(_,root),key) =
    let
      val _ = scope_meter_charge meter 16
      fun walk tree =
        (scope_meter_charge meter 16;
         case tree of
             E => NONE
           | T(_,left,saved,value,right) =>
               (case scope_compare_graph_key meter (key,saved) of
                   LESS => walk left
                 | GREATER => walk right
                 | EQUAL =>
                     (scope_meter_charge meter 2;SOME value)))
    in walk root end

  (* Closed persistent RB insertion. Nodes are allocated only after a
     successful real-meter debit. A failed branch leaves the supplied
     opaque root unchanged; local partial trees do not escape.
     There is no callback, virtual ledger, raw map adoption or refund. *)
  fun scope_put_graph_key meter (GraphKeyMap(count,root),key,value) =
    let
      val _ = scope_meter_charge meter 16
      val fresh = ref false
      fun make args =
        (scope_meter_charge meter 8;T args)
      fun balance args =
        (scope_meter_charge meter 64;
         case args of
             (B,T(R,T(R,a,x,xv,b),y,yv,c),z,zv,d) =>
               make(R,make(B,a,x,xv,b),y,yv,make(B,c,z,zv,d))
           | (B,T(R,a,x,xv,T(R,b,y,yv,c)),z,zv,d) =>
               make(R,make(B,a,x,xv,b),y,yv,make(B,c,z,zv,d))
           | (B,a,x,xv,T(R,T(R,b,y,yv,c),z,zv,d)) =>
               make(R,make(B,a,x,xv,b),y,yv,make(B,c,z,zv,d))
           | (B,a,x,xv,T(R,b,y,yv,T(R,c,z,zv,d))) =>
               make(R,make(B,a,x,xv,b),y,yv,make(B,c,z,zv,d))
           | fields => make fields)
      fun ins tree =
        (scope_meter_charge meter 16;
         case tree of
             E =>
               (scope_meter_charge meter 2;
                fresh := true;make(R,E,key,value,E))
           | T(color,left,saved,held,right) =>
               (case scope_compare_graph_key meter (key,saved) of
                   LESS =>
                     balance(color,ins left,saved,held,right)
                 | GREATER =>
                     balance(color,left,saved,held,ins right)
                 | EQUAL => make(color,left,key,value,right)))
      val next = ins root
      val _ = scope_meter_charge meter 16
      val black = case next of
          T(R,left,saved,held,right) => make(B,left,saved,held,right)
        | _ => next
      val _ = scope_meter_charge meter 8
      val total = if !fresh then count+1 else count
    in GraphKeyMap(total,black) end


  (* Closed directly funded FIRST-only roots. Keep the whole argument as
     DATA until the real original meter has admitted the local programme.
     No quote/planner/private Ledger, callback, traversal or name copy. *)
  fun scope_singletons_from_empty meter arguments =
    (scope_meter_charge meter 64;
     case arguments of
         (IntMap(0,E),StringSet(0,E),key,value,name) =>
           (IntMap(1,T(B,E,key,value,E)),
            StringSet(1,T(B,E,name,(),E)))
       | _ => raise StalePlan)


  (* Closed int-only FIRST root. The original meter pays BEFORE the
     tuple/root match. No name/string root is inspected or constructed. *)
  fun scope_int_singleton_from_empty meter arguments =
    (scope_meter_charge meter 64;
     case arguments of
         (IntMap(0,E),key,value) => IntMap(1,T(B,E,key,value,E))
       | _ => raise StalePlan)

  (* Fixed persistent table constructors used only by the closed int and
     string programmes below. The enclosing paid visit/balance owns the
     tuple arguments before this constructor's own debit. *)
  fun scope_table_make meter fields =
    (scope_meter_charge meter 8;T fields)

  fun scope_table_balance meter fields =
    (scope_meter_charge meter 128;
     case fields of
         (B,T(R,T(R,a,x,xv,b),y,yv,c),z,zv,d) =>
           scope_table_make meter
             (R,scope_table_make meter (B,a,x,xv,b),y,yv,
                scope_table_make meter (B,c,z,zv,d))
       | (B,T(R,a,x,xv,T(R,b,y,yv,c)),z,zv,d) =>
           scope_table_make meter
             (R,scope_table_make meter (B,a,x,xv,b),y,yv,
                scope_table_make meter (B,c,z,zv,d))
       | (B,a,x,xv,T(R,T(R,b,y,yv,c),z,zv,d)) =>
           scope_table_make meter
             (R,scope_table_make meter (B,a,x,xv,b),y,yv,
                scope_table_make meter (B,c,z,zv,d))
       | (B,a,x,xv,T(R,b,y,yv,T(R,c,z,zv,d))) =>
           scope_table_make meter
             (R,scope_table_make meter (B,a,x,xv,b),y,yv,
                scope_table_make meter (B,c,z,zv,d))
       | values => scope_table_make meter values)

  (* The second argument remains opaque until its original meter admits
     setup. Every old tree is immutable; refusal exposes no partial root.
     Comparators are fixed private programmes, never caller callbacks. *)
  fun scope_put_int meter arguments =
    (scope_meter_charge meter 64;
     let
       val (IntMap(count,root),key,value) = arguments
       val fresh = ref false
       fun ins tree =
         (scope_meter_charge meter 64;
          case tree of
              E =>
                (scope_meter_charge meter 2;
                 fresh := true;scope_table_make meter (R,E,key,value,E))
            | T(color,left,saved,held,right) =>
                (case scope_graph_int_compare meter (key,saved) of
                    LESS => scope_table_balance meter
                      (color,ins left,saved,held,right)
                  | GREATER => scope_table_balance meter
                      (color,left,saved,held,ins right)
                  | EQUAL =>
                      scope_table_make meter (color,left,key,value,right)))
       val next = ins root
       val _ = scope_meter_charge meter 32
       val black = case next of
           T(R,left,saved,held,right) =>
             scope_table_make meter (B,left,saved,held,right)
         | _ => next
       val _ = scope_meter_charge meter 16
       val total = if !fresh then count+1 else count
     in IntMap(total,black) end)

  fun scope_add_string meter arguments =
    (scope_meter_charge meter 64;
     let
       val (StringSet(count,root),key) = arguments
       val fresh = ref false
       fun ins tree =
         (scope_meter_charge meter 64;
          case tree of
              E =>
                (scope_meter_charge meter 2;
                 fresh := true;scope_table_make meter (R,E,key,(),E))
            | T(color,left,saved,held,right) =>
                (case scope_graph_string_compare meter (key,saved) of
                    LESS => scope_table_balance meter
                      (color,ins left,saved,held,right)
                  | GREATER => scope_table_balance meter
                      (color,left,saved,held,ins right)
                  | EQUAL =>
                      scope_table_make meter (color,left,key,(),right)))
       val next = ins root
       val _ = scope_meter_charge meter 32
       val black = case next of
           T(R,left,saved,held,right) =>
             scope_table_make meter (B,left,saved,held,right)
         | _ => next
       val _ = scope_meter_charge meter 16
       val total = if !fresh then count+1 else count
     in StringSet(total,black) end)

  fun scope_member_string meter arguments =
    (scope_meter_charge meter 32;
     let
       val (StringSet(_,root),key) = arguments
       fun walk tree =
         (scope_meter_charge meter 16;
          case tree of
              E => false
            | T(_,left,saved,_,right) =>
                (case scope_graph_string_compare meter (key,saved) of
                    LESS => walk left
                  | GREATER => walk right
                  | EQUAL => true))
     in walk root end)
end
