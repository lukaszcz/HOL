functor Task08Reject (I : Task08API) =
struct
  fun bad (r : I.T.reducer) = simpLib.dproc_ss r
end
