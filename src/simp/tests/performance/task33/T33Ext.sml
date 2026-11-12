(* Probe (candidate only): explicit extension use, its lifetime (E2 b),
   then the ordinary graph work again in the same process (E2 a). *)
val _ = T33.start ("ext", "ext",
  [("m", T33.ji (T33.need_int "T33_M" 1)),
   ("sizes", T33.jl T33.ji (T33GraphLib.sizes ()))])
val _ = Meta.load "simpExtLib"
val _ = QUse.use "T33ExtUse.ML"
val _ = T33GraphLib.run ()
val _ = T33.registry ()
val _ = T33.finish ()
