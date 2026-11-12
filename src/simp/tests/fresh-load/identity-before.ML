(* Native ownership inspection only; never a pinned-develop dependency. *)

fun split_attribute_now () =
  ThmAttribute.attribute_fns_of (Context.snapshot ()) "split"

val foreign_attribute_before = split_attribute_now ();
val foreign_exporter_before = ThmSetData.data_exportfns {settype="split"};

val listeners_before = Listener.listeners Theory.delta_hook;
