load "hhEval";

val base = hhConfig.snapshot ();
val options : hhConfig.hh_options =
  {timeout = 30, max_proofs = 4,
   provers = ["e", "vampire", "zipperposition"],
   slices = 24, cores = 24, filter = "", max_facts = NONE,
   format = "", type_enc = "", lam_trans = "", mono_iters = 3,
   mono_instances = NONE, minimize = true,
   preplay_timeout = #preplay_timeout base,
   minimize_timeout = #minimize_timeout base,
   cache = false, cache_dir = #cache_dir base,
   cache_max_entries = #cache_max_entries base, debug_dir = NONE};
val schedule = hhSlice.mk_schedule options;
val output_path =
  case OS.Process.getEnv "HHEVAL_SCHEDULE_OUTPUT" of
      SOME path => path
    | NONE => raise Fail "HHEVAL_SCHEDULE_OUTPUT is not set";
val output = TextIO.openOut output_path;

fun indexed items =
  let
    fun loop _ [] = []
      | loop index (item :: rest) =
          (index, item) :: loop (index + 1) rest;
  in
    loop 1 items
  end;

fun one (index, (_, slice : hhProver.slice)) =
  TextIO.output (output, String.concatWith "\t"
    [Int.toString index, #prover slice, #filter slice, #format slice,
     #type_enc slice, #lam_trans slice, Int.toString (#nfacts slice),
     Int.toString (#slice_size slice),
     Real.toString (hhSlice.slice_budget (length schedule) options slice)] ^
    "\n");

val _ = List.app one (indexed schedule);
val _ = TextIO.closeOut output;
val _ = if length schedule = 24 then ()
  else raise Fail "Phase 3 schedule does not contain 24 slices";
