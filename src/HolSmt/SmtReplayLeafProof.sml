(* Checked atomic occurrence transport. Metadata never proves equality. *)
structure SmtReplayLeafProof =
struct
  (* A programme switch, NOT an admission allowance. Native equal-Type
     comparison unfolds the annotation tree. Keep the old route through
     2^31-1 incidences, including P21/P24; above that use the checked redex
     route. The cold full-GC cost of sharing must be measured too, not hidden
     behind a Type-DAG-only work claim. No resource limit is changed here. *)
  val native_tree_switch : IntInf.int = 2147483647

  (* Bounded routing hint followed by an exact-pointer DAG summary. Charge
     each observation/probe before doing it; collisions never imply equality.
     Saturation is only for choosing a programme, not refusing a Type. *)
  fun large_type debit ty =
    let
      fun walk 0 _ = NONE
        | walk fuel ty =
            (debit (4 : IntInf.int);
             if Type.is_vartype ty then SOME (fuel - 1)
             else children (fuel - 1) (#2 (Type.dest_type ty)))
      and children fuel [] = SOME fuel
        | children fuel (ty :: rest) =
            case walk fuel ty of NONE => NONE
              | SOME remaining => children remaining rest
      val physical = ref ([] : (Type.hol_type * IntInf.int) list)
      fun find _ [] = NONE
        | find ty ((saved,size) :: rest) =
            (debit 2;
             if Portable.pointer_eq (ty,saved) then SOME size
             else find ty rest)
      fun summary ty =
        case find ty (!physical) of SOME size => size
        | NONE =>
          let
            val _ = debit 4
            val children = if Type.is_vartype ty then []
              else List.map summary (#2 (Type.dest_type ty))
            fun add (size,total) =
              IntInf.min (native_tree_switch + 1, size + total)
            val size = List.foldl add 1 children
            val _ = debit 1
            val _ = physical := (ty,size) :: !physical
          in size end
    in case walk 64 ty of SOME _ => false
      | NONE => summary ty > native_tree_switch
    end

  (* Built-in Type equality (unlike experimental Type.compare) stops on
     shared subtrees, not just shared roots. Summarize PAIRS, retaining their
     unfolded multiplicities but stopping at every exact shared pointer.
     Otherwise a large Type with a cheap shared suffix could force full GC. *)
  fun large_type_pair (debit : IntInf.int -> unit) left right =
    let
      val memo = ref []
      fun find _ _ [] = NONE
        | find left right ((l,r,n) :: rest) =
            (debit 3;
             if Portable.pointer_eq (left,l) andalso
                Portable.pointer_eq (right,r) then SOME n
             else find left right rest)
      fun visit left right =
        (debit 2;
         if Portable.pointer_eq (left,right) then 1 else
         case find left right (!memo) of SOME n => n
         | NONE =>
           let
             val _ = debit 4
             val ls = if Type.is_vartype left then []
               else #2 (Type.dest_type left)
             val rs = if Type.is_vartype right then []
               else #2 (Type.dest_type right)
             fun children [] [] n = n
               | children (l::ls) (r::rs) n =
                   (debit 1; children ls rs (IntInf.min
                     (native_tree_switch + 1, n + visit l r)))
               | children _ _ _ = 1
             val n = children ls rs 1
             val _ = debit 1
             val _ = memo := (left,right,n) :: !memo
           in n end)
    in visit left right > native_tree_switch end

  (* Separately interned function/argument representatives can have equal
     but independent annotations even without any source bridge. Share only
     for the same hard comparison class; mk_comb still checks the Types.
     Its separately compiled public constructor rereads the native fields
     after sharing, rather than a caller's retained annotation roots. *)
  fun application debit operator operand =
    let
      val (domain,_) = Type.dom_rng (Term.type_of operator)
      val argument_type = Term.type_of operand
      val _ = if not (Portable.pointer_eq (domain,argument_type)) andalso
          large_type_pair debit domain argument_type then
        PolyML.shareCommonData (operator,operand) else ()
    in Term.mk_comb (operator,operand) end

  fun shared_variable left right =
    let
      (* Experimental aconv unfolds even a physically shared Type. Beta's
         built-in variable equality instead short-circuits on that pointer.
         f s --> s --> right and f s --> f right --> left form a diamond.
         No equality at the synthesized function Type is constructed. *)
      val ty = Term.type_of left
      val z = Term.mk_var (#1 (Term.dest_var left) ^ "'", ty)
      val f = Term.mk_abs (left, left)
      val s = Term.mk_comb (Term.mk_abs (z, z), right)
      val inner = Thm.BETA_CONV s
      val direct = Thm.TRANS
        (Thm.BETA_CONV (Term.mk_comb (f, s))) inner
      val lifted = Thm.AP_TERM f inner
      val (_, target) = Term.dest_eq (Thm.concl lifted)
      val other = Thm.TRANS lifted (Thm.BETA_CONV target)
    in Thm.TRANS (Thm.SYM other) direct end

  fun same_atom left right =
    if Term.is_var left andalso Term.is_var right then
      #1 (Term.dest_var left) = #1 (Term.dest_var right)
    else Term.is_const left andalso Term.is_const right andalso
      KernelSig.id_compare (#Name (Term.dest_thy_constid left),
        #Name (Term.dest_thy_constid right)) = EQUAL

  (* Call only after the caller's original admission/negative checks. Both
     beta theorems are proved BEFORE sharing. Fresh redex child fields can
     coalesce, while the theorem RHS fields retain the supplied endpoints.
     TRANS still checks the middle terms: sharing is not proof evidence.
     This operation forces full GC, possibly including adaptive whole-heap
     sharing. It changes no runtime policy and is not local-DAG-only work. *)
  fun redex_equality left right =
    let
      val name = if Term.is_var left then
          #1 (Term.dest_var left) ^ "'" else "smt_leaf_bridge"
      val marker = Term.mk_var (name, Type.bool)
      fun redex leaf = Term.mk_comb
        (Term.mk_abs (marker, leaf), boolSyntax.T)
      val left_redex = redex left
      val right_redex = redex right
      val left_beta = Thm.BETA_CONV left_redex
      val right_beta = Thm.BETA_CONV right_redex
      val _ = PolyML.shareCommonData (left_redex, right_redex)
    in Thm.TRANS (Thm.SYM left_beta) right_beta end
end
