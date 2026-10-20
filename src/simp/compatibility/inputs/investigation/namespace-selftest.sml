open HolKernel testutils
val _ = tprint "simpLib loads after a user registers attribute split"
val _ = if ThmAttribute.is_attribute "split" then
          raise Fail "test precondition: split already registered"
        else ()
val _ = ThmAttribute.register_attribute
  ("split", {localf=fn _ => (), storedf=fn _ => ()})
val outcome =
  ((load (valOf (OS.Process.getEnv "SIMP_COMPAT_PATH")); true)
   handle e => (print (General.exnMessage e ^ "\n"); false))
val _ = if outcome then OK () else die "loading simpLib raised"
val _ = OS.Process.exit
  (if outcome then OS.Process.success else OS.Process.failure)
