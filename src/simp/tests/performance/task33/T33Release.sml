(* Probe: R1, residual live words of discarded ordinary objects.  T33_M
   cycles per kind after one warm cycle, then M objects held; the weak
   probe of RuntimeMetrics (unchanged) runs once at the end.  T33_LEAK
   keeps every discarded object except the floor kind's (a control). *)
open HolKernel boolLib simpLib

fun rules tag i = List.tabulate (4, fn j => let
  val s = "t33_" ^ tag ^ Int.toString i ^ "_" ^ Int.toString j
in ASSUME (mk_eq (mk_var (s, bool), T)) end)
fun first rs = lhs (concl (hd rs))
fun named tag i rs = ListPair.zip (List.tabulate (length rs, fn j =>
  {Thy = "bool", Name = "t33_" ^ tag ^ Int.toString i ^ "_" ^ Int.toString j}),
  rs)
val pure = pureSimps.pure_ss
fun apply cv rs = fn () => ignore (Conv.QCONV cv (first rs))
fun conv_kind tag mk = (tag, fn i => let val rs = rules tag i
  in apply (mk rs) rs end)

(* The leading no-op kind is the in-process noise floor of the residuals
   (T33.floor_kind); T33_LEAK does not retain its objects. *)
val kinds =
  [(T33.floor_kind, fn _ => fn () => ()),
   ("simpset", fn i => T33.hold (boolSimps.bool_ss ++ rewrites (rules "s" i))),
   conv_kind "conversion" (fn rs => SIMP_CONV (pure ++ rewrites rs) []),
   ("tactic", fn i => let
      val rs = rules "t" i
      val tac = SIMP_TAC (pure ++ rewrites rs) []
    in fn () => ignore (T33.solve tac ([concl (hd rs)], first rs)) end),
   ("traversedata", fn i => let
      val rs = rules "d" i
      val td = traversedata_for_ss (pure ++ rewrites rs)
    in apply (Traverse.TRAVERSE td []) rs end),
   ("exclusion", fn i => let
      val rs = rules "x" i
      val ss = (pure ++ rewrites_with_names (named "x" i rs)) -*
               [#Name (#1 (hd (named "x" i rs)))]
    in apply (SIMP_CONV ss []) rs end),
   ("removed", fn i => let
      val rs = rules "r" i
      val ss = remove_ssfrags ["t33_frag"]
                 (pure ++ named_rewrites "t33_frag" rs)
    in apply (SIMP_CONV ss []) rs end),
   conv_kind "cong" (fn rs => congLib.CONGRUENCE_EQ_SIMP_CONV
     (congLib.mk_congset [congLib.csfrag_rewrites rs]) pure [])]

val m = T33.need_int "T33_M" 1
val _ = T33.start ("release", "release", [("m", T33.ji m)])
val _ = T33.live "start"
val _ = List.app (T33.release m) kinds
val {retained, collected, fullGCs, status, ...} = RuntimeMetrics.release ()
val _ = T33.emit "weak"
  [("scope", T33.js "controlled-simpset-ref-closure"),
   ("retained", T33.jb retained), ("collected", T33.jb collected),
   ("full_gcs", T33.ji fullGCs), ("status", T33.js status)]
val _ = T33.finish ()
