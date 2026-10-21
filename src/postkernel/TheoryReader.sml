(* ========================================================================== *)
(* FILE          : TheoryReader.sml                                           *)
(* DESCRIPTION   : Read theory data from disk                                 *)
(*                                                                            *)
(* AUTHOR        : Thibault Gauthier, University of Innsbruck                 *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure TheoryReader :> TheoryReader =
struct

type thm      = Thm.thm;
type term     = Term.term
type hol_type = Type.hol_type

open HolKernel SharingTables RawTheory_dtype RawTheoryReader

fun temp_encoded_update sdata thyname {data,ty} =
    Theory.LoadableThyData.temp_encoded_update {
      thy = thyname,
      thydataty = ty,
      shared_readmaps = {strings = read_string sdata, terms = read_term sdata},
      data = data
    }


(* This immutable fact is minted only from this instance's successful
   default decoder output. It is not current declaration validity or Work
   credit. The actual canonical H vector is retained after disk_thm. *)
datatype bool_left_decode_origin = BoolLeftDecodeOrigin of
  {proof: Thm.thm, statement: Term.term,
   hypotheses: Term.term list, hypothesis_count: int}
val captured_bool_left_decode_origin =
  ref (NONE: bool_left_decode_origin option)

fun bool_left_decode_origin () = !captured_bool_left_decode_origin
fun bool_left_decode_origin_matches
    (BoolLeftDecodeOrigin held) {proof,statement} =
  Portable.pointer_eq (#proof held,proof) andalso
  Portable.pointer_eq (#statement held,statement)
fun bool_left_decode_origin_counts (BoolLeftDecodeOrigin held) =
  {hypotheses = #hypothesis_count held}


fun load_thydata_from_dat (r as {thyname,path,hash}) =
    let
      open HOLsexp
      val rawthy as {parents,tables,exports,name=stored_name,...} =
            load_raw_thydata {path=path}
      fun mungename {thy,hash} = (thy,hash)
      val _ = thyname = stored_name orelse
              raise TheoryReader
                    ("reading at " ^ path ^ " for theory " ^ thyname ^
                     " and got theory called " ^ stored_name ^ " instead")
      val _ = Theory.link_parents (thyname, hash) (map mungename parents)
      val {types=new_types,consts=new_consts} = #newsig rawthy
      fun before_types () = Theory.incorporate_types thyname new_types
      fun before_terms tyv =
          Theory.incorporate_consts
            thyname
            (map (fn (n,i) => (n,Vector.sub(tyv,i))) new_consts)
      val share_data =
            dec_sdata {
              before_types = before_types,
              before_terms = before_terms,
              tables = tables,
              exports = exports
            }
    val {theorems = named_thms,...} = export_from_sharing_data share_data

    val thmdict =
        List.foldl (fn ((n,th,i), D) => Symtab.update (n, (th,i)) D)
                   Symtab.empty
                   named_thms
    val _ = DB.bindl thyname named_thms
    val _ =
        app (temp_encoded_update share_data thyname) (
          force "thydata" (
            Option.map (map (fn (ty,d) => {data=d,ty=ty})) o
            list_decode(pair_decode(string_decode, SOME))
          )
          (#thydata rawthy)
        )
    (* Only this successful PRIVATE default loader mints the fact. Every
       thmdict entry is from actual read_raw C/H ports and disk_thm. This
       fixed selection does not accept an externally supplied theorem. *)
    val _ = if thyname <> "bool" then () else
      (case Symtab.lookup thmdict "LEFT_FORALL_IMP_THM" of
         NONE => captured_bool_left_decode_origin := NONE
       | SOME (proof,_) =>
           let
             val statement = Thm.concl proof
             val hypotheses = Thm.hyp proof
             val hypothesis_count = List.length hypotheses
           in
             captured_bool_left_decode_origin := SOME (BoolLeftDecodeOrigin
               {proof=proof,statement=statement,hypotheses=hypotheses,
                hypothesis_count=hypothesis_count})
           end)
  in
    thmdict
  end handle Interrupt => raise Interrupt
           | e => raise TheoryReader ("Exception raised: " ^
                                      General.exnMessage e)

(* Hook for alternative theorem sources. Default is to read from .dat files. *)
val load_thydata_fn :
    ({thyname:string,path:string,hash:string} ->
     (Thm.thm * DB_dtype.thminfo) Symtab.table) ref
    = ref load_thydata_from_dat

fun load_thydata args = (!load_thydata_fn) args

end;  (* TheoryReader *)
