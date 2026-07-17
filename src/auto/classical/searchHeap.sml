(* A purely functional leftist min-heap, following Okasaki's design. *)
structure searchHeap :> searchHeap =
struct

  datatype 'a node = E | T of int * 'a * 'a node * 'a node

  datatype 'a heap =
    Heap of ('a * 'a -> order) * int * 'a node

  fun rank E = 0
    | rank (T (r, _, _, _)) = r

  fun make_node (x, left, right) =
    if rank left >= rank right then
      T (rank right + 1, x, left, right)
    else
      T (rank left + 1, x, right, left)

  fun merge compare =
    let
      fun mrg (tree, E) = tree
        | mrg (E, tree) = tree
        | mrg (tree1 as T (_, x, left1, right1),
               tree2 as T (_, y, left2, right2)) =
            (case compare (x, y) of
                 GREATER => make_node (y, left2, mrg (tree1, right2))
               | _ => make_node (x, left1, mrg (right1, tree2)))
    in
      mrg
    end

  fun empty compare = Heap (compare, 0, E)

  fun add x (Heap (compare, n, tree)) =
    Heap (compare, n + 1, merge compare (T (1, x, E, E), tree))

  fun is_empty (Heap (_, _, E)) = true
    | is_empty _ = false

  fun min (Heap (_, _, E)) = raise Empty
    | min (Heap (_, _, T (_, x, _, _))) = x

  fun delete_min (Heap (_, _, E)) = raise Empty
    | delete_min (Heap (compare, n, T (_, _, left, right))) =
        Heap (compare, n - 1, merge compare (left, right))

  fun delete_all_min (Heap (_, _, E)) = raise Empty
    | delete_all_min (Heap (compare, n, tree as T (_, first, _, _))) =
        let
          fun take (count, values, E) = (count, rev values, E)
            | take (count, values, root as T (_, x, left, right)) =
                if compare (x, first) = EQUAL then
                  take (count + 1, x :: values,
                        merge compare (left, right))
                else
                  (count, rev values, root)
          val (count, values, rest) = take (0, [], tree)
        in
          (values, Heap (compare, n - count, rest))
        end

  fun size (Heap (_, n, _)) = n

end
