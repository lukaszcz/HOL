(* Probe: the residual compile cost of a timing probe.  Prints the header
   and the end record only; run on a startup kind next to T33Load. *)
val _ = let
  val k = case OS.Process.getEnv "T33_KIND" of
      SOME k => k | NONE => raise Fail "T33: missing T33_KIND"
  fun line r rest = print ("@@T33\t{\"record\":\"" ^ r ^
    "\",\"probe\":\"trivial\",\"kind\":\"" ^ k ^ "\"" ^ rest ^ "}\n")
in line "probe" (",\"holdir\":\"" ^ Systeml.HOLDIR ^
                 "\",\"switches\":{\"graph_extra\":false,\"leak\":false," ^
                 "\"hook\":false},\"params\":{\"module\":null}");
   line "done" "" end
