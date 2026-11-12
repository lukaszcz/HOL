(* The kind's work of the load and registry probes (T33_KIND, T33_MODULE).
   Basis and kernel names only, no T33 support code: the timing probe
   compiles it inside the measured process, so it is kept this small.  The
   caller defines t33_probe and t33_switches (a JSON object text).  The
   module name comes only from the environment, so Holdep sees no
   simplifier dependency in any source. *)
val t33_kind = case OS.Process.getEnv "T33_KIND" of
    SOME k => k | NONE => raise Fail "T33: missing T33_KIND"
fun t33_q s = "\"" ^ String.translate
  (fn #"\"" => "\\\"" | #"\\" => "\\\\"
    | c => if Char.ord c < 32 then " " else str c) s ^ "\""
fun t33_real r = String.map (fn #"~" => #"-" | c => c)
  (Real.fmt (StringCvt.SCI (SOME 12)) r)
fun t33_emit record fields =
  (print ("@@T33\t{\"record\":" ^ t33_q record ^ ",\"probe\":" ^
          t33_q t33_probe ^ ",\"kind\":" ^ t33_q t33_kind ^
          String.concat (map (fn (k, v) => ",\"" ^ k ^ "\":" ^ v) fields) ^
          "}\n");
   TextIO.flushOut TextIO.stdOut)
fun t33_check label ok value =
  (t33_emit "check" [("check", t33_q label),
                     ("ok", if ok then "true" else "false"),
                     ("value", t33_q value)];
   if ok then () else raise Fail ("T33 check failed: " ^ label))
fun t33_time label f = let
  val cpu = Timer.startCPUTimer ()
  val real = Timer.startRealTimer ()
  val r = f ()
  val {usr, sys} = Timer.checkCPUTimer cpu
  val wall = Timer.checkRealTimer real
in
  t33_emit "time" [("label", t33_q label),
                   ("cpu", t33_real (Time.toReal usr + Time.toReal sys)),
                   ("wall", t33_real (Time.toReal wall))];
  r
end
fun t33_same (a, b) = Term.aconv (Thm.concl a) (Thm.concl b) andalso
  HOLset.equal (Thm.hypset a, Thm.hypset b)
(* A tactic run on a goal in the present context (no current theory). *)
fun t33_solve tac goal = let
  val (gl, vf) = tac goal (Context.snapshot ())
in if null gl then vf [] else raise Fail "T33: tactic left goals" end

val t33_module =
  if String.isPrefix "load-" t33_kind then
    SOME (case OS.Process.getEnv "T33_MODULE" of
              SOME m => m | NONE => raise Fail "T33: missing T33_MODULE")
  else NONE
val _ = t33_emit "probe"
  [("holdir", t33_q Systeml.HOLDIR), ("switches", t33_switches),
   ("params", "{\"module\":" ^
              (case t33_module of NONE => "null" | SOME m => t33_q m) ^ "}")]
fun t33_loading name checks =
  (if t33_module = SOME name then () else raise Fail "T33: bad T33_MODULE";
   t33_time "load" (fn () => Meta.load name);
   QUse.use checks)
val _ = case t33_kind of
    "state0-empty" => ()
  | "state-empty" => ()
  | "load-simpLib" => t33_loading "simpLib" "T33CheckSimp.ML"
  | "load-congLib" => t33_loading "congLib" "T33CheckCong.ML"
  | "first-use" => QUse.use "T33CheckFirst.ML"
  | _ => raise Fail ("T33: bad T33_KIND " ^ t33_kind)
