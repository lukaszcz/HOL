(* Native ownership inspection only; never a pinned-develop dependency. *)
val foreign_attribute_before = ThmAttribute.attribute_fns "split";
val foreign_exporter_before = ThmSetData.data_exportfns {settype="split"};
