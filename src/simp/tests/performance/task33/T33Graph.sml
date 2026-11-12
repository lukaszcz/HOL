(* Probe: retained graph words at the declared sizes (T33_SIZES). *)
val _ = (T33.start ("graph", "graph",
           [("sizes", T33.jl T33.ji (T33GraphLib.sizes ()))]);
         T33GraphLib.run (); T33.finish ())
