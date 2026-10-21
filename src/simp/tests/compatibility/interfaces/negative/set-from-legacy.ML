functor Task08Reject (I : Task08API) =
struct
  fun bad (ss : simpLib.simpset) = I.S.rewrite_source_handles ss
end
