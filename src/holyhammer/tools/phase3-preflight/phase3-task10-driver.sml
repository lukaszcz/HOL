load "hhEval";

fun required_env name =
  case OS.Process.getEnv name of
      SOME value => value
    | NONE => raise Fail (name ^ " is not set");

fun parse_positive name text =
  case Int.fromString text of
      SOME value =>
        if value > 0 then value
        else raise Fail (name ^ " must be positive")
    | NONE => raise Fail (name ^ " is not an integer");

fun prover_condition prover count filter : hhEval.condition =
  {cond_id = "p-f30-" ^ prover ^ "-" ^ filter,
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
   reconstruct = true};

val filters = ["knn", "mepo", "mash", "mesh"];

val f30_conditions =
  map (prover_condition "vampire" 96) filters @
  map (prover_condition "e" 128) filters;

val s30_condition : hhEval.condition =
  {cond_id = "p-s30-v5", regime = hhEval.Chainy,
   selector = hhEval.PerSlice,
   engine = hhEval.Sched
     {provers = ["e", "vampire", "zipperposition"],
      slices = 24, cores = 24, max_proofs = 4},
   timeout = 30, reconstruct = true};

val expname = required_env "HHEVAL_EXPNAME";
val variant = required_env "HHEVAL_VARIANT";
val mode = required_env "HHEVAL_MODE";
val conditions =
  case variant of
      "f30" => f30_conditions
    | "s30v5" => [s30_condition]
    | _ => raise Fail ("unknown HHEVAL_VARIANT: " ^ variant);
val theories = hhEval.stdlib_theories ();

fun checked_theory name =
  if List.exists (fn theory => theory = name) theories then name
  else raise Fail ("unknown stdlib theory: " ^ name);

val _ =
  case mode of
      "theory" =>
        hhEval.run_eval
          {expname = expname,
           ncore = parse_positive "HHEVAL_NCORE"
             (required_env "HHEVAL_NCORE"),
           thyl = [checked_theory (required_env "HHEVAL_THEORY")],
           conditions = conditions}
    | "report" => hhEval.report (hhEval.experiment_dir expname)
    | _ => raise Fail ("unknown HHEVAL_MODE: " ^ mode);
