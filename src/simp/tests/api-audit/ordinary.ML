(* Runtime-only: retain the actual ordinary control/hook identities before
   importing anything from the extension layer. *)
val original_stack_limit = Cond_rewr.stack_limit;
val original_trace_level = Trace.trace_level;
val original_trace_hook = Trace.trace_hook;
val original_trace_listeners = Listener.listeners Trace.trace_hook;
val ordinary_input = boolSyntax.mk_conj
  (boolSyntax.T,mk_var ("audit_p",bool));
val ordinary_expected = mk_var ("audit_p",bool);
val ordinary_proof = simpLib.SIMP_CONV boolSimps.bool_ss [] ordinary_input;
val _ = check "ordinary BOOL produces a closed kernel equality"
  (null (hyp ordinary_proof) andalso
   aconv (concl ordinary_proof)
     (boolSyntax.mk_eq (ordinary_input,ordinary_expected)));
