(* The frontier heap of the BEST_FIRST driver.

   The leftist min-heap itself is mlibHeap.  This structure adds
   delete_all_min, which BEST_FIRST needs in order to expand every
   equal-cost minimum together (Pure/search.ML lines 180--199), and so
   retains the comparator that mlibHeap does not expose. *)
structure searchHeap :> searchHeap =
struct

  datatype 'a heap = Heap of ('a * 'a -> order) * 'a mlibHeap.heap

  fun empty compare = Heap (compare, mlibHeap.empty compare)

  fun add x (Heap (compare, heap)) = Heap (compare, mlibHeap.add x heap)

  fun is_empty (Heap (_, heap)) = mlibHeap.is_empty heap

  (* Raises Empty on an empty heap. *)
  fun delete_min (Heap (compare, heap)) =
    let val (value, remaining) = mlibHeap.remove heap
    in (value, Heap (compare, remaining)) end

  (* Raises Empty on an empty heap. *)
  fun delete_all_min (Heap (compare, heap)) =
    let
      val (first, rest) = mlibHeap.remove heap

      fun take values heap =
        if mlibHeap.is_empty heap then (List.rev values, heap)
        else
          let
            val (next, remaining) = mlibHeap.remove heap
          in
            if compare (next, first) = EQUAL then
              take (next :: values) remaining
            else (List.rev values, heap)
          end

      val (values, remaining) = take [first] rest
    in
      (values, Heap (compare, remaining))
    end

end
