val _ =
  ((load "BasicProvers"; load "hhEval")
   handle error =>
     (TextIO.output
        (TextIO.stdErr, "TASK11 runtime load failed: " ^
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

     fun goal_ids path theory =
       let
         val input = TextIO.openIn path
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

     fun condition prover count filter : hhEval.condition =
       {cond_id = "f30-" ^ prover ^ "-" ^ filter,
        regime = hhEval.Chainy,
        selector =
          (case filter of
               "knn" => hhEval.Knn count
             | "mepo" => hhEval.Mepo count
             | "mash" => hhEval.Mash count
             | "mesh" => hhEval.Mesh count
             | _ => raise Fail ("unknown filter " ^ filter)),
        engine = hhEval.Prover prover,
        timeout = 30,
        reconstruct = true}

     val theory = required "HHEVAL_THEORY"
     val theory_dir = required "HHEVAL_THEORY_DIR"
     val filters = ["knn", "mepo", "mash", "mesh"]
     val conditions =
       map (condition "vampire" 96) filters @
       map (condition "e" 128) filters
     val part = natural "HHEVAL_PART"
     val parts = natural "HHEVAL_PARTS"
     val expdir = required "HHEVAL_EXPDIR"
     val inventory = required "HHEVAL_GOAL_INVENTORY"
     val _ = OS.FileSys.chDir theory_dir
     val _ = load (theory ^ "Theory")
     val _ = Feedback.quiet_messages Theory.new_theory
       ("hheval_task11_" ^ theory ^ "_" ^ required "HHEVAL_PART")
     val _ =
       hhEval.set_worker_settings {conditions = conditions, sample = 1}
     val _ = hhEval.set_worker_goal_ids (goal_ids inventory theory)
     val _ = hhEval.set_worker_partition {part = part, parts = parts}
     val _ = hhEval.eval_thy expdir theory
   in
     if hhEval.worker_theory_complete expdir theory then ()
     else raise Fail "TASK11 worker journal is incomplete"
   end)
  handle error =>
    (TextIO.output
       (TextIO.stdErr, "TASK11 worker failed: " ^
        General.exnMessage error ^ "\n");
     OS.Process.exit OS.Process.failure);
