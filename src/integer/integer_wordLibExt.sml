(* The public conversion owns word-size computation; only its original
   patterns and names are repeated, not ordinary fragments or logs. *)
structure integer_wordLibExt :> integer_wordLibExt =
struct

local
  val (_,Term) = Parse.parse_from_grammars
    (valOf (Parse.grammarDB {thyname="integer_word"}))
in
  val INT_SIZES_ss = simpExtLib.register_frag
    (simpExtLib.name_ss "int sizes"
      (simpExtLib.std_conv_ss
        {name = "INT_SIZES_CONV", conv = integer_wordLib.INT_SIZES_CONV,
         pats = [Term `integer_word$INT_MIN(:'a)`,
                 Term `integer_word$INT_MAX(:'a)`,
                 Term `integer_word$UINT_MAX(:'a)`]}))
end

end
