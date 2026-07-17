open testutils searchHeap

fun test (name, check) =
  (tprint name;
   if check () then OK () else die "failed")

fun int_compare (x : int, y : int) =
  if x < y then LESS else if x > y then GREATER else EQUAL

fun from_list compare values =
  List.foldl (fn (x, heap) => add x heap) (empty compare) values

fun drain heap =
  if is_empty heap then [] else min heap :: drain (delete_min heap)

val _ =
  test
    ("heap returns values in ascending order",
     fn () =>
       let
         val heap = from_list int_compare [5, 1, 4, 2, 3]
       in
         size heap = 5 andalso drain heap = [1, 2, 3, 4, 5]
       end)

fun key_compare ((key1, _) : int * string, (key2, _)) =
  int_compare (key1, key2)

val duplicate_heap =
  from_list key_compare [(2, "c"), (1, "a"), (3, "d"), (1, "b")]

val _ =
  test
    ("heap preserves entries with duplicate keys",
     fn () =>
       size duplicate_heap = 4 andalso
       map #1 (drain duplicate_heap) = [1, 1, 2, 3])

val _ =
  test
    ("delete_all_min pops every entry with the minimal key",
     fn () =>
       let
         val (entries, rest) = delete_all_min duplicate_heap
         val payloads = map #2 entries
       in
         length entries = 2 andalso
         List.all (fn (key, _) => key = 1) entries andalso
         List.exists (fn value => value = "a") payloads andalso
         List.exists (fn value => value = "b") payloads andalso
         size rest = 2 andalso min rest = (2, "c")
       end)

fun raises_empty f =
  (f (); false) handle Empty => true | _ => false

val _ =
  test
    ("empty heap operations fail",
     fn () =>
       let
         val heap : int heap = empty int_compare
       in
         raises_empty (fn () => ignore (min heap)) andalso
         raises_empty (fn () => ignore (delete_min heap)) andalso
         raises_empty (fn () => ignore (delete_all_min heap))
       end)
