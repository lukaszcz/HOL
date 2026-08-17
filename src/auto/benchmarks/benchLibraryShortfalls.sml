structure benchLibraryShortfalls =
struct

val translation : benchLib.shortfall list = []

fun classified classification ids : benchLib.shortfall list =
  map
    (fn id =>
      {id = id, cause = benchLib.EngineLimitation,
       date = "2026-08-16",
       note = classification ^
         ": assigned tactic does not yet close from general inputs"})
    ids

val execution : benchLib.shortfall list = []

end
