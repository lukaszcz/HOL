(* Match combinSimps's immutable inputs and order, not its compiled objects. *)
structure combinSimpsExt :> combinSimpsExt =
struct

open combinTheory

val COMBIN_ss = simpExtLib.SSFRAG {
      name = SOME "COMBIN", convs = [], congs = [], filter = NONE, ac = [],
      dprocs = [],
      rewrs = map (fn s => (SOME {Thy="combin",Name=s}, DB.fetch "combin" s)) [
        "I_THM", "I_o_ID", "K_THM", "S_THM", "o_ASSOC'", "o_THM", "W_THM",
        "C_THM", "K_o_THM", "UPDATE_EQ", "UPDATE_APPLY_ID_RWT", "UPDATE_APPLY1"
      ]
    }

end
