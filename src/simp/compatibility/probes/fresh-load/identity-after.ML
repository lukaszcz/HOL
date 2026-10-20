fun same_option (NONE,NONE) = true
  | same_option (SOME a,SOME b) = Portable.pointer_eq (a,b)
  | same_option _ = false;
val _ = check "ordinary load preserves exact foreign handler records"
  (same_option (foreign_attribute_before,
                ThmAttribute.attribute_fns "split") andalso
   same_option (foreign_exporter_before,
                ThmSetData.data_exportfns {settype="split"}));
