functor Task08Reject (I : Task08API) =
struct
  fun bad (f : simpLib.ssfrag) = I.S.++ (I.S.empty_ss,f)
end
