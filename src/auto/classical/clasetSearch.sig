signature clasetSearch =
sig
  type node = clasetGoal.node
  type expansion = node -> node seq.seq

  (* Zero or a negative value disables the frontier-search bound. *)
  val node_limit : int ref
  val node_count : unit -> int
  val pruning_count : unit -> int

  val DEPTH_FIRST : (node -> bool) -> expansion -> expansion
  val DEPTH_SOLVE : expansion -> expansion
  val BEST_FIRST : (node -> bool) -> expansion -> expansion
  val ASTAR : (node -> bool) -> expansion -> expansion

  (* Restart [bounded] at start, start + inc, ... .  Once one bound has
     a result, all of that bound's results are retained and no later bound
     is attempted. *)
  val DEEPEN : int * int -> (int -> expansion) -> int -> expansion
end
