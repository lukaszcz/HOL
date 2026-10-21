functor Task08Reject (I : Task08API) =
struct
  fun bad (f : I.S.ssfrag) = simpLib.++ (simpLib.empty_ss,f)
end
