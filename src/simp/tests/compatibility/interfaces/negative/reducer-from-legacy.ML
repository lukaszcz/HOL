functor Task08Reject (I : Task08API) =
struct
  fun bad (r : Traverse.reducer) = I.S.dproc_ss r
end
