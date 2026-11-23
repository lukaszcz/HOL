
(* Non-logical definitional CNF, due to John Harrison.            *)
(* Ported from HOL Light by Hasan Amjad, with HOL4 specific mods. *)

structure def_cnf :> def_cnf =
struct

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback
     boolSyntax

open satCommonTools satTheory

val presimp_conv =
    QCONV (GEN_REWRITE_CONV REDEPTH_CONV empty_rewrites
            [NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES,
             COND_EXPAND, COND_CLAUSES])

(* Raised by to_cnf when boolean simplification of one of the top-level
   conjuncts of the input term reduces to F: the input is unsatisfiable
   without help from the SAT solver. The carried theorem is |- ~tm where
   tm is the term passed to to_cnf. *)
exception to_cnf_unsat of thm

(* A bounded structural sample only selects a bucket. Reuse requires
   physical identity, even when two terms have the same sample. *)
val source_bucket_mask = 0w1023

fun source_hint tm =
    let
      fun sample 0 _ = 0w7
        | sample n t =
            if is_comb t then
              let val (f,x) = dest_comb t
              in 0w31 * sample (n-1) f + 0w17 * sample (n-1) x end
            else if is_var t then
              CharVector.foldl
                (fn (c,h) => 0w33 * h + Word.fromInt (Char.ord c))
                0w13 (#1 (dest_var t))
            else if is_const t then
              Word.fromInt (KernelSig.epoch_of (#Name (dest_thy_constid t)))
            else 0w5
    in Word.toInt (Word.andb (sample 5 tm,source_bucket_mask)) end

fun source_table () =
    Array.array (Word.toInt source_bucket_mask + 1,(0,[],[]))

fun source_lookup source (_,recent,older) =
    let fun same (saved,_) = Portable.pointer_eq (source,saved)
    in case List.find same recent of
           NONE => List.find same older
         | found => found
    end

(* Keep probing bounded when many distinct terms have identical samples.
   Rotating two groups avoids walking or copying a list on insert. *)
fun source_add_at table key entry (count,recent,older) =
    Array.update (table,key,
      if count = 64 then (1,[entry],recent)
      else (count+1,entry :: recent,older))

fun source_add table (entry as (source,_)) =
    let val key = source_hint source
    in source_add_at table key entry (Array.sub (table,key)) end

(* Avoid caching applications with only one compound argument at ordinary
   arities. For wider applications, stop before rescanning a shared operator
   prefix for each of its uses. *)
fun branching_application operator operand =
    let
      fun scan 0 _ _ = true
        | scan remaining seen t =
          if is_comb t then
            let val (f,x) = dest_comb t in
              if is_comb x then seen orelse scan (remaining-1) true f
              else scan (remaining-1) seen f
            end
          else false
    in scan 8 (is_comb operand) operator end

fun branching_source t =
    let val (f,x) = dest_comb t in branching_application f x end

(* ------------------------------------------------------------------------- *)
(* Split up a theorem according to conjuncts, in a general sense.            *)
(* ------------------------------------------------------------------------- *)
local
val p_tm = mk_var("p",bool)
val q_tm = mk_var("q",bool)
fun is_literal tm = is_var tm orelse (is_neg tm andalso is_var(rand tm))
fun is_clausal tm =
    case dest_disjunction tm of
        SOME (left,right) => is_literal left andalso is_clausal right
      | NONE => is_literal tm

(* The test is independent of binders. Build a visited set only for
   subterms that exceed the initial traversal budget. *)
fun contains_constant tm =
    let
      fun scan seen initial budget [] = false
        | scan seen initial budget (pending as t :: rest) =
            if same_const T t orelse same_const F t then true
            else if is_comb t then
              if budget = 0 then
                if initial then scan (recent_terms ()) false 4096 pending
                else memo_scan pending
              else
                let val (operator,operand) = dest_comb t
                    val next = if budget < 0 then budget else budget - 1
                in
                  if not initial andalso is_comb operator andalso
                     is_comb operand andalso
                     (budget >= 0 orelse
                      branching_application operator operand) andalso
                     seen t then
                    scan seen initial next rest
                  else scan seen initial next (operator :: operand :: rest)
                end
            else if is_abs t then
              scan seen initial budget (snd (dest_abs t) :: rest)
            else scan seen initial budget rest
      and memo_scan pending =
          let
            val visited = source_table ()
            fun seen t =
                let
                  val key = source_hint t
                  val bucket = Array.sub (visited,key)
                in
                  case source_lookup t bucket of
                      SOME _ => true
                    | NONE =>
                        (source_add_at visited key (t,()) bucket;
                         false)
                end
          in scan seen false ~1 pending end
    in scan (fn _ => false) true 128 [tm] end
in
val GCONJUNCTS  =
    let
      fun GCONJUNCTS' th acc =
          let val (opr,args) = strip_comb (concl th)
          in
            if not (is_const opr) then th::acc else
             case fst (dest_const opr) of
                 "~" =>
                 let val  (opr,args) = strip_comb (hd args)
                 in if not (is_const opr) then th::acc else
                    (case fst (dest_const opr) of
                        "==>" =>
                        let val (p,q) = (hd args,last args)
                        in GCONJUNCTS'
                             (MP (INST [p_tm|->p,q_tm|->q] pth_ni1) th)
                             (GCONJUNCTS'
                                (MP (INST [p_tm|->p,q_tm|->q] pth_ni2) th)
                                acc)
                        end
                      | "\\/" =>
                        let val (p,q) = (hd args,last args)
                        in GCONJUNCTS'
                             (MP (INST [p_tm|->p,q_tm|->q] pth_no1) th)
                             (GCONJUNCTS' (MP (INST [p_tm|->p,q_tm|->q]
                                                    pth_no2) th) acc)
                        end
                      | "~" =>
                        GCONJUNCTS' (MP (INST [p_tm|->hd args] pth_nn) th) acc
                      | _ => th::acc)
                 end
               | "/\\" =>
                 GCONJUNCTS' (CONJUNCT1 th)
                             (GCONJUNCTS' (CONJUNCT2 th) acc)
               | _ => th::acc
          end
        fun GCONJUNCTS'' th = GCONJUNCTS' th []
    in fn tm => fn th =>
          let open Uref
              val ths0 = if is_neg tm andalso is_neg (rand tm)
                         then CONJUNCTSR (CONV_RULE NOT_NOT_CONV th) else [th]
              val ths1 = List.map GCONJUNCTS'' ths0
              val is_cnf = Uref.new true
              (* A clause of variable literals contains no T or F. *)
              fun classify th =
                  let val clause = concl th in
                    if is_clausal clause then (true,th)
                    else (is_cnf := false;
                          (false,if contains_constant clause
                                 then CONV_RULE presimp_conv th else th))
                  end
              val ths2 = List.map classify (List.concat ths1)
          in (!is_cnf,ths2) end
    end
end

(* ------------------------------------------------------------------------- *)
(* Generate fresh variable names (could just use genvars).                   *)
(* ------------------------------------------------------------------------- *)

fun propvar cnfv i = mk_var(cnfv^(int_to_string i),bool)

(* ------------------------------------------------------------------------- *)
(* Set up the basic definitional arrangement.                                *)
(* ------------------------------------------------------------------------- *)

local
datatype source_probe = Unprobed | SkipMemo | Bucket of int
in
fun localdefs cnfv tm state =
    let val rollbacks = ref 0
        val empty = (T,T)
        val newest = ref empty
        val older = ref empty
        val memo = ref NONE

        fun extend source body (n,defs,lfn) =
          let val next = n + 1
              val v = propvar cnfv next
          in (next,v,RBM.insert (defs,body,v),RBM.insert (lfn,v,source)) end

        fun observe_source lfn source v =
          if not (isSome (!memo)) andalso
             Portable.pointer_eq (source,rbapply lfn v) then
            let val table = source_table () in
              source_add table (!older);
              source_add table (!newest);
              memo := SOME table
            end
          else ()

        fun intern source body (state as (n,defs,lfn)) =
          case RBM.peek (defs,body) of
              SOME v =>
                (if is_comb source then observe_source lfn source v else ();
                 (n,v,defs,lfn))
            | NONE => extend source body state

        (* The recent results handle local sharing. Build the full memo
           only after revisiting the original source of a definition. *)
        fun walk tm (state as (n,defs,lfn)) =
          if is_comb tm then
            let
              val (s1,v1) = !newest
              val (s2,v2) = !older
            in
              if Portable.pointer_eq (s1,tm) then (n,v1,defs,lfn)
              else if Portable.pointer_eq (s2,tm) then (n,v2,defs,lfn)
              else
                case !memo of
                    NONE => remember tm state Unprobed
                  | SOME table =>
                      if branching_source tm then
                        let val key = source_hint tm in
                          case source_lookup tm (Array.sub (table,key)) of
                              SOME (_,v) => (n,v,defs,lfn)
                            | NONE => remember tm state (Bucket key)
                        end
                      else remember tm state SkipMemo
            end
          else define tm state
        and remember tm state probe =
          let val before_define = !rollbacks
              val (result as (_,v,_,_)) = define tm state
          in
            if before_define = !rollbacks then
              (older := !newest; newest := (tm,v);
               case !memo of
                   NONE => ()
                 | SOME table =>
                     case probe of
                         SkipMemo => ()
                       | Bucket key =>
                           (* Children may have updated this bucket. *)
                           source_add_at table key (tm,v)
                             (Array.sub (table,key))
                       | Unprobed =>
                           if branching_source tm then source_add table (tm,v)
                           else ())
            else ();
            result
          end
        and define tm (n,defs,lfn) =
          if is_neg tm then
              let val (n1,v1,defs1,lfn1) = walk (rand tm) (n,defs,lfn)
              in intern tm (mk_neg v1) (n1,defs1,lfn1) end
          else if is_conj tm orelse is_disj tm orelse
                  is_imp tm orelse is_eq tm then
              let val (n1,v1,defs1,lfn1) = walk (land tm) (n,defs,lfn)
                  val (n2,v2,defs2,lfn2) = walk (rand tm) (n1,defs1,lfn1)
                  val tm' = mk_comb (mk_comb (rator (rator tm),v1),v2)
              in intern tm tm' (n2,defs2,lfn2) end
          else if is_cond tm then
              let val (opr,args) = strip_comb tm
                  val (n1,v1,defs1,lfn1) =
                      walk (List.nth(args,0)) (n,defs,lfn)
                  val (n2,v2,defs2,lfn2) =
                      walk (List.nth(args,1)) (n1,defs1,lfn1)
                  val (n3,v3,defs3,lfn3) =
                      walk (List.nth(args,2)) (n2,defs2,lfn2)
                  val tm' = mk_comb(mk_comb(mk_comb(opr,v1),v2),v3)
              in case RBM.peek (defs3,tm') of
                     SOME v =>
                       (if Portable.pointer_eq (defs2,defs3) then
                          observe_source lfn3 tm v
                        else (newest := empty; older := empty;
                              memo := NONE;
                              rollbacks := !rollbacks + 1);
                        (n3,v,defs2,lfn3))
                   | NONE => extend tm tm' (n3,defs3,lfn3)
              end
          else intern tm tm (n,defs,lfn)
    in walk tm state end
end

(* ------------------------------------------------------------------------- *)
(* Just translate to fresh variables, but otherwise leave unchanged.         *)
(* ------------------------------------------------------------------------- *)

fun transvar_var cnfv (n,tm,vdefs,lfn) =
    (n,rbapply vdefs tm,vdefs,lfn)
    handle NotFound =>
           let val n1 = n + 1
               val v1 = propvar cnfv n1
           in (n1,v1,RBM.insert(vdefs,tm,v1),RBM.insert(lfn,v1,tm)) end

fun transvar_lit cnfv (n,tm,vdefs,lfn) =
    if is_neg tm then
        let val (n1,tm1,vdefs1,lfn1) = transvar_var cnfv (n,rand tm,vdefs,lfn)
        in (n1,mk_neg tm1,vdefs1,lfn1) end
    else transvar_var cnfv (n,tm,vdefs,lfn)

fun transvar_clause cnfv (n,tm,vdefs,lfn) =
    let
      fun rename (literal,(n,clause,vdefs,lfn)) =
          let val (n',literal',vdefs',lfn') =
                transvar_lit cnfv (n,literal,vdefs,lfn)
          in (n',mk_disj (literal',clause),vdefs',lfn') end
      (* is_clausal has already checked the literal left operands. *)
      fun walk clause pending =
          case dest_disjunction clause of
              SOME (left,right) => walk right (left :: pending)
            | NONE =>
                List.foldl rename
                  (transvar_lit cnfv (n,clause,vdefs,lfn)) pending
    in walk tm [] end

(* ------------------------------------------------------------------------- *)
(* Check if something is clausal (slightly stupid).                          *)
(* ------------------------------------------------------------------------- *)

(* convert tm to CNF, assuming that it is of the form v =  v' op v'' *)
(* where all the v's are vars, and op is one of [~,\/,/\,==>,=]      *)
(* of course when op is ~, there is only one argument               *)
local
val p_tm = mk_var("p",bool)
val q_tm = mk_var("q",bool)
val r_tm = mk_var("r",bool)
val s_tm = mk_var("s",bool)
in
fun to_cnf' tm =
    let
      val (l,r) = dest_eq tm
      val (opr,args) = strip_comb r
      val (i, th) =
          case fst (dest_const opr) of
              "~" => ([p_tm |-> l, q_tm |-> (hd args)], dc_neg)
            | "\\/" => ([p_tm |-> l, q_tm |-> hd args, r_tm |-> last args],
                        dc_disj)
            | "/\\" => ([p_tm |-> l, q_tm |-> hd args, r_tm |-> last args],
                        dc_conj)
            | "==>" => ([p_tm |-> l, q_tm |-> hd args, r_tm |-> last args],
                        dc_imp)
         | "=" => ([p_tm |-> l, q_tm |-> hd args, r_tm |-> last args], dc_eq)
         | "COND" => ([p_tm |-> l, q_tm |-> hd args, r_tm |-> hd (tl args),
                       s_tm |-> (last args)], dc_cond)
         | _ => failwith("to_cnf': "^(fst (dest_const opr)))
    in
      INST i th
    end
end

val cnfv_ref = ref "SP"

fun clausify tm lfn eq cls =
    let val fvs = free_vars eq
        val eth = to_cnf' eq
        val tth = INST (map (fn v => v |-> rbapply lfn v) fvs) eth
        val xth = ADD_ASSUM tm (EQ_MP tth (REFL(rbapply lfn (land eq))))
    in zip (strip_conj(rand(concl eth))) (CONJUNCTS xth) @ cls end

(* DIMACS numbers name the distinct propositional atoms of the clauses,
   not just their free HOL variables.  An already-CNF problem can contain a
   compound Boolean atom, and counting FVL alone underallocates the reverse
   map used by termToDimacs. *)
fun cnf_atom_count clause_of clauses =
    let
      fun add_atom (atom, atoms) = HOLset.add (atoms, atom)
      fun add_clause (clause, atoms) =
        fold_clause_atoms add_atom (clause_of clause) atoms
    in HOLset.numItems
         (List.foldl add_clause (HOLset.empty Term.compare) clauses)
    end

fun explicit_cnf known_count tm =
    let
      val cnf = dest_neg tm
      fun collect [] clauses = List.rev clauses
        | collect (th :: rest) clauses =
            let val clause = concl th in
              if is_conj clause then
                let val (left,right) = CONJ_PAIR th
                in collect (left :: right :: rest) clauses end
              else collect rest ((clause,th) :: clauses)
            end
      val clauses = collect [ASSUME cnf] []
      val count = case known_count of SOME count => count
                                    | NONE => cnf_atom_count fst clauses
    in (NONE, count, RBM.mkDict Term.var_compare,
        Array.fromList clauses) end

fun to_cnf is_cnf tm =
    if is_cnf then explicit_cnf NONE tm else let
        val th = ASSUME tm
        val (is_cnf,ths) = GCONJUNCTS tm th
        val (cnfv,vc,eqs,tops,lfn) =
            if is_cnf then
            let val tops = List.map (fn (_,th) => (concl th,th)) ths
            in (NONE, cnf_atom_count fst tops,
                [],tops,RBM.mkDict Term.var_compare) end else
            let
                val cnfv = (!cnfv_ref)
                val (n,tops,defs,lfn) =
                    itlist (fn (ic,th) =>
                            fn (m,tops,defs,lfn) =>
                               let val t = concl th
                               in if is_T t then (m,tops,defs,lfn)
                                  else if is_F t then
                                    (* th : tm |- F, so |- ~tm *)
                                    raise to_cnf_unsat
                                            (NOT_INTRO (DISCH tm th))
                                  else
                                  let val (n,v,defs',lfn') =
                                          if ic then
                                            transvar_clause cnfv (m,t,defs,lfn)
                                          else localdefs cnfv t (m,defs,lfn)
                                  in (n,(v,th)::tops,defs',lfn') end
                               end) ths
                           (~1,[],RBM.mkDict Term.compare,
                            RBM.mkDict Term.var_compare)
                val eqs = RBM.foldl
                  (fn (body,v,rest) =>
                    if is_var body then rest else mk_eq (v,body) :: rest)
                  [] defs
                val vc = (n + 1)
            in (SOME cnfv,vc,eqs,tops,lfn) end
        val all_clauses = itlist (clausify tm lfn) eqs tops
     in (cnfv,vc,lfn,Array.fromList all_clauses) end

end
