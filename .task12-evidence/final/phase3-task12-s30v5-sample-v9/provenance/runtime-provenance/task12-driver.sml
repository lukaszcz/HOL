val _ =
  ((load "BasicProvers"; load "hhEval")
   handle error =>
     (TextIO.output
        (TextIO.stdErr, "TASK12 runtime load failed: " ^
         General.exnMessage error ^ "\n");
      OS.Process.exit OS.Process.failure));

val _ =
  (let
     fun required name =
       case OS.Process.getEnv name of
           SOME value => value
         | NONE => raise Fail (name ^ " is not set")

     fun natural name =
       case Int.fromString (required name) of
           SOME value =>
             if value >= 0 then value
             else raise Fail (name ^ " must be nonnegative")
         | NONE => raise Fail (name ^ " is not an integer")

     fun trim_line line =
       let
         fun trim character text =
           if size text > 0 andalso
              String.sub (text, size text - 1) = character then
             String.substring (text, 0, size text - 1)
           else text
       in
         trim #"\r" (trim #"\n" line)
       end

     fun goal_ids path theory =
       let
         val input = TextIO.openIn path
         fun loop acc =
           case TextIO.inputLine input of
               NONE => rev acc
             | SOME line =>
                 (case String.fields (fn c => c = #"\t")
                         (trim_line line) of
                      [row_theory, goal_id] =>
                        loop (if row_theory = theory then goal_id :: acc
                              else acc)
                    | _ => raise Fail "invalid canonical goal inventory")
         val result = loop []
         val _ = TextIO.closeIn input
       in
         if null result then
           raise Fail ("canonical goal inventory omits " ^ theory)
         else result
       end

     fun write_text path text =
       let val output = TextIO.openOut path in
         TextIO.output (output, text);
         TextIO.closeOut output
       end

     val condition : hhEval.condition =
       {cond_id = "s30-v5", regime = hhEval.Chainy,
        selector = hhEval.PerSlice,
        engine = hhEval.Sched
          {provers = ["e", "vampire", "zipperposition"],
           slices = 24, cores = 24, max_proofs = 4},
        timeout = 30, reconstruct = true}
     val theory = required "HHEVAL_THEORY"
     val theory_dir = required "HHEVAL_THEORY_DIR"
     val inventory = required "HHEVAL_GOAL_INVENTORY"
     val mode = required "HHEVAL_TASK12_MODE"
     val expdir = required "HHEVAL_EXPDIR"
     val selected =
       case mode of
           "measure" => goal_ids inventory theory
         | "cache-seed" => goal_ids inventory theory
         | "cache-witness" => goal_ids inventory theory
         | _ => raise Fail ("unknown TASK12 mode: " ^ mode)
     val _ = OS.FileSys.chDir theory_dir
     val _ = load (theory ^ "Theory")
     val _ = Feedback.quiet_messages Theory.new_theory
       ("hheval_task12_" ^ theory ^ "_" ^ required "HHEVAL_PART")
     val _ = hhEval.set_worker_settings
       {conditions = [condition], sample = 1}
     val _ = hhEval.set_worker_goal_ids selected
     val _ =
       if mode = "measure" then
         hhEval.set_worker_partition
           {part = natural "HHEVAL_PART", parts = natural "HHEVAL_PARTS"}
       else ()
     val _ = hhProver.reset_spawn_count ()
     val _ = hhEval.eval_thy expdir theory
     val spawns = hhProver.spawn_count ()
     val _ =
       if hhEval.worker_theory_complete expdir theory then ()
       else raise Fail "TASK12 worker journal is incomplete"
     val _ =
       case OS.Process.getEnv "HHEVAL_SPAWN_OUTPUT" of
           NONE => ()
         | SOME path => write_text path (Int.toString spawns ^ "\n")
     val _ =
       if mode = "cache-witness" andalso spawns <> 0 then
         raise Fail "TASK12 cache witness spawned a prover"
       else ()
   in
     ()
   end)
  handle error =>
    (TextIO.output
       (TextIO.stdErr, "TASK12 worker failed: " ^
        General.exnMessage error ^ "\n");
     OS.Process.exit OS.Process.failure);
