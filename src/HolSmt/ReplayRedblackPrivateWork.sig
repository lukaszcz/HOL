(* Fixed-comparator persistent tables; no generic table conversion. *)
signature ReplayRedblackPrivateWork =
sig
  type cost = {work : IntInf.int, views : IntInf.int,
    comparisons : IntInf.int, string_bytes : IntInf.int,
    plan_nodes : IntInf.int, finish_nodes : IntInf.int}
  exception Limit
  (* Only Work couples this adapter to its original private counter.
     No caller-created adapter is accepted by an owned consumer. Creating
     a standalone meter confers no Work ownership or pricing authority. *)
  type scope_meter
  val new_scope_meter : {limit:int,charged:int ref} -> scope_meter
  val same_scope_meter : scope_meter * scope_meter -> bool
  val scope_meter_charge : scope_meter -> IntInf.int -> unit
  val scope_meter_charged : scope_meter -> int
  exception StalePlan
  type 'a int_map
  val scope_lookup_int : scope_meter -> 'a int_map * int -> 'a option
  type string_set
  type 'a int_lookup
  type string_lookup
  type 'a int_insertion
  type string_insertion
  type 'a int_batch
  val peek_int : 'a int_map * int -> 'a option
  val member_string : string_set * string -> bool
  val put_int : 'a int_map * int * 'a -> 'a int_map
  val add_string : string_set * string -> string_set
  val list_int : 'a int_map -> (int * 'a) list
  val insert_int_batch : 'a int_map * int list * IntInf.int -> 'a int_batch
  val int_batch_cost : 'a int_batch -> cost
  val finish_int_batch : 'a int_map * 'a int_batch * 'a list -> 'a int_map
  val empty_int : unit -> 'a int_map
  val empty_string : unit -> string_set
  val same_int : 'a int_map * 'a int_map -> bool
  val same_string : string_set * string_set -> bool
  val lookup_int : 'a int_map * int * IntInf.int -> 'a int_lookup
  val int_lookup_cost : 'a int_lookup -> cost
  val int_lookup_value : 'a int_map * 'a int_lookup -> 'a option
  val lookup_string : string_set * string * IntInf.int -> string_lookup
  val string_lookup_cost : string_lookup -> cost
  val string_lookup_value : string_set * string_lookup -> bool
  val insert_int : 'a int_map * int * IntInf.int -> 'a int_insertion
  val int_insertion_cost : 'a int_insertion -> cost
  val finish_int : 'a int_map * 'a int_insertion * 'a -> 'a int_map
  val insert_string : string_set * string * IntInf.int -> string_insertion
  val string_insertion_cost : string_insertion -> cost
  val finish_string : string_set * string_insertion -> string_set
  (* Fixed ordered traversal. Costs include future pair/list copies.
     No caller fold/comparator or numItems estimate is priced. *)
  type 'a int_listing
  type 'a int_batch_listing
  val list_int_plan : 'a int_map * IntInf.int -> 'a int_listing
  val int_listing_cost : 'a int_listing -> cost
  val finish_list_int : 'a int_map * 'a int_listing -> (int * 'a) list
  (* Traversal of the SAME retained symbolic batch root before payload mint.
     ONLY this finish binds the listing to the exact returned table object.
     An independently finished batch leaves the listing unbound. *)
  val list_int_batch_plan : 'a int_batch * IntInf.int -> 'a int_batch_listing
  val int_batch_listing_cost : 'a int_batch_listing -> cost
  val finish_int_batch_with_listing :
    'a int_map * 'a int_batch_listing * 'a list -> 'a int_map
  val finish_batch_list_int :
    'a int_map * 'a int_batch_listing -> (int * 'a) list
  val new_scope_meter_with_policy :
    {limit:SmtReplayResourcePolicy.limit,charged:IntInf.int ref} -> scope_meter
  val scope_meter_charged_policy : scope_meter -> IntInf.int
  val lookup_int_with_policy :
    'a int_map * int * SmtReplayResourcePolicy.limit -> 'a int_lookup
  (* Same real plans, instructions, costs, and one-shot finish methods.
     Uncapped is an absent planning ceiling, not a maximum integer. *)
  val insert_int_batch_with_policy : 'a int_map * int list *
    SmtReplayResourcePolicy.limit -> 'a int_batch
  val insert_int_with_policy : 'a int_map * int *
    SmtReplayResourcePolicy.limit -> 'a int_insertion
  val insert_string_with_policy : string_set * string *
    SmtReplayResourcePolicy.limit -> string_insertion
  val lookup_string_with_policy : string_set * string *
    SmtReplayResourcePolicy.limit -> string_lookup
  val list_int_plan_with_policy : 'a int_map *
    SmtReplayResourcePolicy.limit -> 'a int_listing
  val list_int_batch_plan_with_policy : 'a int_batch *
    SmtReplayResourcePolicy.limit -> 'a int_batch_listing
  val insert_int_batch_reachable :
    'a int_map * int list * IntInf.int -> 'a int_batch

  (* Real same-counter snapshot AFTER this query's successful debit.
     Ordinary integer ScopeMeter is unsupported and raises Domain. *)
  val scope_meter_remaining_with_policy :
    scope_meter -> SmtReplayResourcePolicy.limit



  (* Fixed G interning vocabulary; no caller comparator or fee. *)
  datatype graph_key =
      GraphTypeVariable of string
    | GraphTypeOperator of KernelSig.kernelid * int list
    | GraphVariable of int * int * string * int
    | GraphConstant of KernelSig.kernelid * int
    | GraphApplication of int * int * int
  type 'a graph_key_map
  val scope_compare_graph_key : scope_meter -> graph_key * graph_key -> order
  val scope_empty_graph_key : scope_meter -> 'a graph_key_map
  val scope_same_graph_key :
    scope_meter -> 'a graph_key_map * 'a graph_key_map -> bool
  val scope_graph_key_count : scope_meter -> 'a graph_key_map -> int
  val scope_lookup_graph_key :
    scope_meter -> 'a graph_key_map * graph_key -> 'a option
  val scope_put_graph_key :
    scope_meter -> 'a graph_key_map * graph_key * 'a -> 'a graph_key_map


  (* Direct original-meter admission before inspecting either input root.
     Only two empty count0/E roots accepted; other roots raise StalePlan
     after the nonrefundable local64. No planning ledger or callback. *)
  val scope_singletons_from_empty : scope_meter ->
    'a int_map * string_set * int * 'a * string -> 'a int_map * string_set


  (* Original-meter local64 before tuple/root inspection. Empty count0/E
     only; nonempty raises StalePlan after payment. No string/name effect. *)
  val scope_int_singleton_from_empty : scope_meter ->
    'a int_map * int * 'a -> 'a int_map

  (* Direct same-meter persistent insertion/lookup, including populated
     roots. Each fixed view/comparison/allocation follows its real debit;
     a refused insertion leaves the supplied root unchanged. *)
  val scope_put_int : scope_meter -> 'a int_map * int * 'a -> 'a int_map
  val scope_add_string : scope_meter -> string_set * string -> string_set
  val scope_member_string : scope_meter -> string_set * string -> bool
end
