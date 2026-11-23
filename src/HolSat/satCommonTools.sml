
(* miscellaneous useful stuff that doesn't fit in anywhere else *)
structure satCommonTools =
struct

local

open Globals HolKernel Parse boolSyntax Term Drule
open satTheory

in

structure RBM = Redblackmap

fun rbapply m k = RBM.find(m,k)

fun tryrbapplyd m k d = rbapply m k handle NotFound => d


fun pair_map f (x,y) = (f x,f y)

(*********** terms **************)

val mk_var = Term.mk_var;

val land = rand o rator

fun dest_binary_application tm =
    if is_comb tm then
      let val (operator,right) = dest_comb tm in
        if is_comb operator then
          let val (head,left) = dest_comb operator
          in SOME (head,left,right) end
        else NONE
      end
    else NONE

fun dest_disjunction tm =
    case dest_binary_application tm of
        SOME (head,left,right) =>
          if same_const disjunction head then SOME (left,right) else NONE
      | NONE => NONE

(* A bounded pointer set for depth-first visits to shared terms. *)
fun recent_terms () =
    let
      val terms = Array.array (32,T)
      val size = ref 0
      val cursor = ref 0
      fun contains term i =
          i < !size andalso
          (Portable.pointer_eq (term,Array.sub (terms,i)) orelse
           contains term (i+1))
      fun seen term =
          contains term 0 orelse
          (Array.update (terms,!cursor,term);
           if !size < Array.length terms then size := !size + 1 else ();
           cursor := (!cursor + 1) mod Array.length terms;
           false)
    in seen end

(* Visit atoms left to right, removing one outer negation per literal. *)
fun fold_clause_atoms step clause initial =
    let
      fun walk literal pending acc =
          if is_comb literal then
            let val (operator,right) = dest_comb literal in
              if is_comb operator then
                let val (head,left) = dest_comb operator in
                  if same_const disjunction head then
                    walk left (right :: pending) acc
                  else add literal pending acc
                end
              else if same_const negation operator then add right pending acc
              else add literal pending acc
            end
          else add literal pending acc
      and add atom pending acc =
          let val acc = step (atom,acc) in
            case pending of [] => acc
              | next :: rest => walk next rest acc
          end
    in walk clause [] initial end

fun is_T tm = Term.compare(tm,T)=EQUAL

fun is_F tm = Term.compare(tm,F)=EQUAL

fun termFromFile fname =
    let val ins        = TextIO.openIn (fname^".term")
        val res        = TextIO.inputAll ins
        val _          = TextIO.closeIn ins
    in Term [QUOTE res] end

fun termToFile fname t =
let val fout = TextIO.openOut (fname^".term")
    val _ =
        TextIO.output (
          fout,
          HOLFlags.with_bflags [(Parse.show_types,true)] term_to_string t
        )
    val _ = TextIO.flushOut fout
    val _ = TextIO.closeOut fout
in () end

(************ HOL **************)

local
    val t = mk_var("t",bool)
    val NOT_NOT2 = SPEC_ALL NOT_NOT
in
fun NOT_NOT_CONV tm = INST [t|->rand(rand tm)] NOT_NOT2
end

(* Like CONJUNCTS but assumes the conjunct is bracketed right-assoc. *)
(* Not tail recursive. Here only as a reference implementation *)
fun NTL_CONJUNCTSR th =
    if is_conj (concl th)
    then
        let val (th1,th2) = CONJ_PAIR th
        in th1::(NTL_CONJUNCTSR th2) end
    else [th]

(* CPS version of NTL_CONJUNCTSR. Does not grow call stack. *)
fun CONJUNCTSR th =
    let fun CPS_CONJUNCTSR th k =
            if is_conj (concl th)
            then let val (th1,th2) = CONJ_PAIR th
                 in CPS_CONJUNCTSR th2 (fn ret => k (th1::ret)) end
            else k [th]
    in CPS_CONJUNCTSR th I end

end
end
