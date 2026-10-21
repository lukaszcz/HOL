functor Task08Reject (I : Task08API) =
struct
  fun bad (ss : simpLib.simpset) = I.Default.build {seed=fn () => ss,steps=[]}
end
