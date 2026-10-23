(* Construct tracked recipes from public conversions, not ordinary fragments.
   Default-provider callers install this explicitly at the logged step. *)
structure listSimpsExt :> listSimpsExt =
struct

open HolKernel

local
  val (_,Term) = Parse.parse_from_grammars
    (valOf (Parse.grammarDB {thyname="list"}))
in
  val LIST_EQ_ss = simpExtLib.register_frag
    (simpExtLib.name_ss "list EQ"
      (simpExtLib.conv_ss
        {name = "LIST_EQ_SIMP_CONV",
         trace = 2,
         key = SOME ([],Term `l1:'a list = l2:'a list`),
         conv = K (K (Conv.CHANGED_CONV listSimps.LIST_EQ_SIMP_CONV))}))
end

end
