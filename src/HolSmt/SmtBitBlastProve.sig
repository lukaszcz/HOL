signature SmtBitBlastProve =
sig
  type context
  (* Callers retain their existing schematic input and Type admissions.
     The positive bit cache retains at most 8192 total theorem DAG nodes;
     source guards and cache capacity only select the legacy fallback. *)
  val new_context : unit -> context
  val new_context_with_bit_conversion : (Conv.conv -> Conv.conv) -> context
  (* Shares the same bounded cache; leaves Boolean solving to the caller. *)
  val convert_atomic : context -> Conv.conv
  val prove_boolean : context -> Conv.conv
  val convert : context -> Conv.conv
  val prove : context -> Conv.conv
  val new_context_with_for_test :
    {bit:Conv.conv -> Conv.conv,boolean:Conv.conv -> Conv.conv} -> context
  val stats_for_test : context ->
    {hits:int,misses:int,evictions:int,retained_dag_nodes:int}
end
