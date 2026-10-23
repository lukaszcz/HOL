val rejectedOrdinaryUpdate = trackedSimpDefaults.Update
  (fn (ss : simpLib.simpset) => simpLib.++ (ss,boolSimps.BOOL_ss))
