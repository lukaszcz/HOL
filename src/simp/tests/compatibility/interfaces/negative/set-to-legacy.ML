functor Task08Reject (I : Task08API) =
struct
  fun bad (ss : I.S.simpset) = simpLib.SIMP_CONV ss
end
