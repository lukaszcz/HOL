functor Task08Reject (I : Task08API) =
struct
  fun bad (cs : I.G.congset) = congLib.CONGRUENCE_EQ_SIMP_CONV cs
end
