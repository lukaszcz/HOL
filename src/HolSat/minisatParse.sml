
structure minisatParse =
struct

local

open Globals Parse HolKernel boolSyntax boolTheory (* HOL4 term parsers etc *)
open Array (* ML *)
open satCommonTools minisatResolve SatSolvers


in

fun sat_fileopen s = BinIO.openIn s

fun sat_fileclose is = BinIO.closeIn is

local open Word in

(*read in the next byte*)
fun sat_getChar is =
    let val v = BinIO.input1 is
    in if isSome v
       then Word8.toLargeWord(valOf v)
       else raise Domain end

infix orb
infix andb
infix <<
infix >>

(* adapted from Minisat-p_v1.14::File::getUInt*)
(* reads the next int, which may be encoded in 8, 16, 32 or 64 bits*)
(* FIXME: Currently this is untested and will likely crash on 64 bit archs*)
fun sat_getint_using next_byte =
 let val  byte0 = next_byte ()
 in  if ((byte0 andb (0wx80))=(0wx0)) (* 8 *)
        then toInt(byte0)
        else
        case toInt((byte0 andb (0wx60)) >> (Word.fromInt 5)) of
         0 => let val byte1 = next_byte ()
              in toInt(((byte0 andb (0wx1F)) << (Word.fromInt 8)) orb byte1)
              end (* 16 *)
        | 1 => let val byte1 = next_byte ()
                   val byte2 = next_byte ()
               in  toInt((((byte0 andb (0wx1F)) << (Word.fromInt 16))
                            orb (byte1 << (Word.fromInt 8))) orb byte2)
               end
        | 2 => let val byte1 = next_byte ()
                   val byte2 = next_byte ()
                   val byte3 = next_byte ()
               in toInt(((((byte0 andb (0wx1F)) << (Word.fromInt 24))
                            orb (byte1 << (Word.fromInt 16)))
                           orb (byte2 << (Word.fromInt 8))) orb byte3)
               end
        (* default case is only place where int64 is needed since we
           do a << 32*)
        | _ => let val byte0 = next_byte ()
                   val byte1 = next_byte ()
                   val byte2 = next_byte ()
                   val byte3 = next_byte ()
                   val byte4 = next_byte ()
                   val byte5 = next_byte ()
                   val byte6 = next_byte ()
                   val byte7 = next_byte ()
               in toInt((((byte0 << (Word.fromInt 24))
                              orb (byte1 << (Word.fromInt 16))
                              orb (byte2 << (Word.fromInt 8))
                              orb byte3) << (Word.fromInt 32))
                            orb ((byte4 << (Word.fromInt 24))
                                     orb (byte5 << (Word.fromInt 16))
                                     orb (byte6 << (Word.fromInt 8)) orb byte7))
            end
        end

fun sat_getint is = sat_getint_using (fn () => sat_getChar is)
end

(* bitwise rightshift by 1 bit*)
fun rshift w = Word.toInt((op Word.>>) (Word.fromInt w,Word.fromInt 1))

(* parse resolution chain *)
fun getIntBranch_using next id h =
    let
        fun loop acc len =
            let val v = (next ())-1
              (*-1 is purely a decoding step (i.e. not translating b/w HolSat
                and ms)*)
            in if v=(~1) then ((v,h)::(rev acc),len+1)
               else let val ci = id-(next ())
                    in loop ((v,ci)::acc) (len+1) end
            end
        val res = loop [] 0
     in res  end

fun getIntBranch fin id h =
    getIntBranch_using (fn () => sat_getint fin) id h

(* parse and resolve a chain : assumes all dependencies already calculated *)
(* the var component of the first pair is a dummy value ~1 *)
fun addBranch_using next consume lfn cl sva tc id =
    let val (br,brl) = getIntBranch_using next id (id-(rshift tc))
        val _ = if brl <= 1 then () else
          (count "derived-clauses" 1; count "resolution-edges" (brl - 1))
        val res = if brl=1 (*(tl br = []) *)
                  then false (* delete *)
                  else
                      ((*print "\nB ";print( (int_to_string id)^": ");
                       List.app (fn (i,j) =>
                                    print (int_to_string i ^ "," ^
                                           int_to_string j ^" ")) br; *)
                      resolveChain lfn sva cl (br,brl) id;
                      List.app (fn (_,ci) => consume ci) br; true) (* resolve *)
    in res end

fun addBranch lfn cl sva fin tc id =
    addBranch_using (fn () => sat_getint fin) (fn _ => ())
      lfn cl sva tc id

(* Parse a root clause. Final result is int list of literals *)
fun getIntRoot_using next idx =
    let
        fun loop idx' acc =
            let val v = next ()
            in if v=0 then idx::(rev acc) else loop (idx'+v) ((idx'+v)::acc) end
        val res = loop idx []
     in res  end

fun getIntRoot fin idx = getIntRoot_using (fn () => sat_getint fin) idx

(* Parse a root clause and add it to the sr stack
   This advances the file read pointer
        but we pick up the actual clause term from the vector
        of clauses we already have, using the orc value.
   This is because minisat-p removes duplicate literals and sorts the
   literals so I can't efficiently find the corresponding clause term in HOL

   So this is faster (time and space) than building the clause term from the
   proof log.
*)
fun addClause_using next lfn roots cl sva vc clauseth lit1 id =
    let val orc = (rshift lit1)-1
          (*-1 because right now orc's in proof log start at 1*)
        val l = getIntRoot_using next (next ())
        val _ = if not (!sat_profile) then () else
          (count "root-clauses" 1;
           count "root-literal-occurrences" (List.length l))
          (*val _ = (print "\nR ";
                     print(int_to_string orc ^ "~" ^ int_to_string id)^ ": ");
                     List.app (fn i => print (int_to_string i ^ " ")) l) *)
    in case l of
           []  => failwith
                    ("addClause:Failed parsing clause "^Int.toString id^"\n")
         | _ => prepareRootClause lfn roots orc clauseth cl id
    end

fun addClause lfn roots cl sva vc clauseth fin lit1 id =
    addClause_using (fn () => sat_getint fin) lfn roots cl sva vc clauseth
                    lit1 id

(* SML equivalent of  C-style eval of v&1=0 *)
fun isRoot v =
    Word.compare(Word.andb(Word.fromInt v,Word.fromInt 1),(Word.fromInt 0)) =
    EQUAL

fun readTrace_using next ended consume advance
                    lfn roots cl sva vc clauseth id =
    if ended () then id
    else
      let val tmp = next ()
          fun continue id = readTrace_using next ended consume advance
                              lfn roots cl sva vc clauseth id
      in
        if isRoot tmp then
          (addClause_using next lfn roots cl sva vc clauseth tmp id;
           advance id; continue (id+1))
        else if addBranch_using next (consume id)
                  lfn cl sva tmp id then
          (advance id; continue (id+1))
        else continue id
      end

(* Preserve the public streaming reader and its caller-owned clause cache. *)
fun readTrace lfn roots cl sva vc clauseth fin id =
    readTrace_using (fn () => sat_getint fin)
      (fn () => BinIO.endOfStream fin) (fn _ => fn _ => ()) (fn _ => ())
      lfn roots cl sva vc clauseth id

exception Trivial

(*build the clause/chain list *)
fun parseTrace_using reader make_roots cl sva nr fname solver vc clauseth
                     lfn proof =
    let
        val path = if isSome proof then valOf proof
                   else fname^"."^(getSolverName solver)^".proof"
        val fin = sat_fileopen path
        (* Open first: a missing certificate must select the old fallback
           without constructing an unused compact root context. *)
        val result = Exn.capture (fn () =>
          let val roots = make_roots ()
          in (reader path lfn roots cl sva vc clauseth fin 0, roots) end) ()
        val _ = case result of
            Exn.Res _ => sat_fileclose fin
          | Exn.Exn _ => (sat_fileclose fin handle _ => ())
     in SOME (Exn.release result) end
handle e as Io _ => if dimacsTools.is_terminal e then raise e else NONE

fun parseTrace_with_roots make_roots cl sva nr fname solver vc clauseth lfn
                          proof =
    parseTrace_using (fn _ => readTrace) make_roots cl sva nr fname solver
                     vc clauseth lfn proof

fun parseTrace roots cl sva nr fname solver vc clauseth lfn proof =
    Option.map #1 (parseTrace_with_roots (fn () => roots) cl sva nr fname
                    solver vc clauseth lfn proof)

local

(* The native driver owns regular proof files. Read bytes in bounded blocks
   without changing the public BinIO reader's position/streaming contract. *)
fun buffered_input fin =
    let
      val buffer = ref (Word8Vector.fromList [])
      val position = ref 0
      fun byte () =
          (if !position < Word8Vector.length (!buffer) then ()
           else (buffer := BinIO.inputN (fin,8192); position := 0);
           if !position = Word8Vector.length (!buffer) then raise Domain
           else let val value = Word8Vector.sub (!buffer,!position)
                in position := !position+1; Word8.toLargeWord value end)
      fun ended () = !position = Word8Vector.length (!buffer) andalso
                     BinIO.endOfStream fin
    in {next=fn () => sat_getint_using byte,ended=ended} end

exception Unordered

(* Deletions are advisory: older accepted traces can use a clause again.
   Count actual references instead, retaining the original streaming path
   for non-files and noncausal traces. No proof step is skipped. *)
fun count_uses path =
    let
      val fin = sat_fileopen path
      val {next,ended} = buffered_input fin
      val uses = Dynarray.array (256,0)
      fun reference id ci =
          if ci < 0 orelse ci >= id then raise Unordered
          else Dynarray.update (uses,ci,Dynarray.sub (uses,ci)+1)
      (* Metadata needs only counts, not temporary literal/branch lists.
         A deletion has no pivot and therefore consumes no head clause. *)
      fun root_tail () = if next ()=0 then () else root_tail ()
      fun branch id head =
          if next ()=0 then false
          else
            let
              val _ = reference id head
              fun tail () =
                  (reference id (id-next ());
                   if next ()=0 then () else tail ())
            in tail (); true end
      fun loop id =
          if ended () then uses else
          let val tag = next () in
            if isRoot tag then
              (next (); root_tail (); loop (id+1))
            else if branch id (id-rshift tag) then loop (id+1)
            else loop id
          end
      val result = Exn.capture loop 0
      val _ = case result of Exn.Res _ => sat_fileclose fin
            | Exn.Exn _ => (sat_fileclose fin handle _ => ())
    in SOME (Exn.release result) end
    (* Metadata supplies hints only. Replay the original stream after a
       failed prepass, preserving an earlier checked replay exception. *)
    handle error =>
      if dimacsTools.is_terminal error then raise error else NONE

fun read_live_trace path lfn roots cl sva vc clauseth fin id =
    let
      val bytes = OS.FileSys.fileSize path handle OS.SysErr _ => 0
      val uses = if bytes > 0 then count_uses path else NONE
      val {next,ended} = if bytes > 65536 then buffered_input fin
        else {next=fn () => sat_getint fin,
              ended=fn () => BinIO.endOfStream fin}
          fun release ci = case uses of NONE => () | SOME table =>
              if ci < 0 orelse Dynarray.sub (table,ci) <> 0 then ()
              else if Portable.pointer_eq (Dynarray.sub (cl,ci),TRUTH) then ()
              else (Dynarray.update (cl,ci,TRUTH);
                    count "last-use-releases" 1)
          fun consume _ ci = case uses of NONE => () | SOME table =>
              let val remaining = Dynarray.sub (table,ci)-1
                  val _ = if remaining < 0 then
                    failwith "resolution trace changed during replay" else ()
              in Dynarray.update (table,ci,remaining); release ci end
          (* Keep the latest result even with zero future references: it is
             the driver's result at EOF, including after deletion records. *)
          fun advance current = if current = 0 then ()
                                else release (current-1)
    in readTrace_using next ended consume advance
         lfn roots cl sva vc clauseth id end

in

(*
nr: number of root clauses
fname: filename of proof log
vc: number of variables (includes variables added by def CNF conversion)
clauseth: root clause vector. clauseth[i] is i'th root clause from original
          problem
*)
fun replayProof sva nr fname solver vc clauseth lfn proof =
    let val _ = (minisatResolve.counter:=0)
        val cl = Dynarray.array((Array.length clauseth) * 2,TRUTH)
        fun trace message =
          if OS.Process.getEnv "HOL4_SAT_TRACE" = SOME "1" then
            (Feedback.HOL_MESG ("HOL SAT: " ^ message);
             TextIO.flushOut TextIO.stdOut)
          else ()
        fun make_roots () =
          if RBM.numItems lfn = 0 then
            {conjunction = T, projections = Termtab.empty}
          else
            let val _ = trace "resolution roots start"
                val roots = profile_stage "replay-roots"
                  minisatResolve.root_context clauseth
                val _ = trace "resolution roots done"
            in roots end
        val _ = trace "resolution trace start"
    in case profile_stage "replay-trace"
        (parseTrace_using read_live_trace make_roots cl sva nr fname solver vc
           clauseth lfn) proof of
           SOME (id, roots) =>
             let val _ = trace "resolution trace done"
                 val result = profile_stage "replay-finish"
                   (minisatResolve.finish_resolution roots lfn clauseth)
                   (Dynarray.sub(cl,id-1))
                 val _ = trace "resolution finish done"
             in SOME result end
         | NONE => NONE
    end

end (* local native reader *)

end
end
