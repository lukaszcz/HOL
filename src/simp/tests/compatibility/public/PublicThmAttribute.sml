(* Full original interface; the runner uses hol.state.min for this fixture
   because ThmAttribute is already in hol.state0. *)
structure PublicAttribute : LegacyThmAttribute = ThmAttribute
val _ = Paired.check "complete ThmAttribute ascription" true
val calls = ref ([] : string list)
fun callback stage
      {name, attrname, args, thm} =
  if name = "public_thm" andalso attrname = "publicattr" andalso
     args = ["argument"] andalso null (Thm.hyp thm)
  then calls := !calls @ [stage] else raise Fail "attribute payload"
val handlers : PublicAttribute.attrfuns =
  {localf = callback "local", storedf = callback "stored"}
val _ = PublicAttribute.register_attribute ("publicattr", handlers)
val _ = PublicAttribute.reserve_word "publicreserved"
val abbreviation : PublicAttribute.abbrevinfo =
  {abbrev = "publicabbr", expansion = [("publicattr", ["argument"])]}
val _ = PublicAttribute.define_abbreviation abbreviation
val block : PublicAttribute.attrblock = PublicAttribute.extract_attributes
  "public_thm[publicabbr,publicreserved,publicunknown]"
val {thmname, attrs, reserved, unknown} = block
val _ = Paired.check "original attribute records and registry"
  (thmname = "public_thm" andalso attrs = [("publicattr", ["argument"])]
   andalso reserved = [("publicreserved", [])]
   andalso unknown = [("publicunknown", [])]
   andalso PublicAttribute.is_attribute "publicattr"
   andalso List.exists (fn s => s = "publicattr")
     (PublicAttribute.all_attributes ())
   andalso List.exists (fn {abbrev, expansion} => abbrev = "publicabbr")
     (PublicAttribute.current_abbreviations ()))
val arg = {name = "public_thm", attrname = "publicattr",
           args = ["argument"], thm = boolTheory.TRUTH}
val localf : PublicAttribute.attrfun = PublicAttribute.local_attribute
val _ = localf arg
val _ = PublicAttribute.store_at_attribute arg
val _ = PublicAttribute.remove_abbreviation "publicabbr"
val _ = Paired.check "original attribute callbacks and formatting"
  (!calls = ["local", "stored"] andalso
   PublicAttribute.toString ("public_thm", ["publicattr"]) =
     "public_thm[publicattr]" andalso
   PublicAttribute.insert_attribute {attr = "publicattr"} "public_thm" =
     "public_thm[publicattr]" andalso
   not (List.exists (fn {abbrev, expansion} => abbrev = "publicabbr")
     (PublicAttribute.current_abbreviations ())))
