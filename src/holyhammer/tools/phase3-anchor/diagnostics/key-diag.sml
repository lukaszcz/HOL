load "hhCache";
val problem =
  case OS.Process.getEnv "HHEVAL_KEY_DIAG_PROBLEM" of
    SOME path => path
  | NONE => raise Fail "HHEVAL_KEY_DIAG_PROBLEM is required";
val key = hhCache.key_of
  {prover = "vampire", version = SOME "5.0.1",
   argv = ["--mode", "portfolio", "--schedule", "casc",
     "--input_syntax", "tptp", "--proof", "tptp",
     "--output_axiom_names", "on", "-t", "30", "--input_file", problem],
   problem = problem};
val _ = print ("KEY=" ^ key ^ "\n");
