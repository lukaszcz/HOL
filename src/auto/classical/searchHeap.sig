signature searchHeap =
sig

  type 'a heap

  val empty : ('a * 'a -> order) -> 'a heap
  val add : 'a -> 'a heap -> 'a heap
  val is_empty : 'a heap -> bool
  val min : 'a heap -> 'a
  val delete_min : 'a heap -> 'a heap
  val delete_all_min : 'a heap -> 'a list * 'a heap
  val size : 'a heap -> int

end
