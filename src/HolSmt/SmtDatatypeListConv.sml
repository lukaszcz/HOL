(* Copyright (c) 2026 The HOL4 contributors. *)

(* Checked, invocation-local port of listSimps.LIST_EQ_SIMP_CONV. *)
structure SmtDatatypeListConv :>
sig
  val procedures : (Term.term -> unit) ->
    {equality: Conv.conv, normalise: Conv.conv}
  val conversion : (Term.term -> unit) -> Conv.conv
end =
struct

open HolKernel boolSyntax Drule listSyntax

fun procedures check =
let
  (* Search handlers must never reinterpret a rejected admission as a miss. *)
  exception AdmissionFailure of exn
  fun admit t = check t handle e => raise AdmissionFailure e
  fun theorem th =
    (admit (Thm.concl th); List.app admit (Thm.hyp th); th)
  fun checked c t = (admit t; theorem (c t))
  fun rule f th = theorem (f (theorem th))
  (* Only source schemas are memoized, by actual theorem identity. Keep
     these small tables local to this procedures call; never memoize target
     admissions or instantiated conversion results. Failed work is not saved.
     Hits still check the saved theorem through the protected observer. *)
  fun lookup entries th =
    List.find (fn (saved, _) => Portable.pointer_eq (saved, th)) (!entries)
  fun save entries th result =
    entries := (th, result) ::
      List.take (!entries, Int.min (31, length (!entries)))
  fun schema f =
    let val entries = ref []
    in
      fn (th : Thm.thm) =>
        case lookup entries th of
          SOME (_, result) => theorem result
        | NONE =>
            let val result = f th
            in save entries th result; result end
    end
  (* Project with the kernel before admission: the unused conjunct may
     contain operators outside the admitted fragment. *)
  val first = schema (fn th => theorem (CONJUNCT1 th))
  val second = schema (fn th => theorem (CONJUNCT2 th))
  val spec_all = schema (rule SPEC_ALL)
  fun trans a b = theorem (TRANS (theorem a) (theorem b))
  fun mp a b = theorem (MP (theorem a) (theorem b))
  val refl = checked REFL
  val eqt = rule EQT_INTRO
  val eqf = rule EQF_INTRO
  fun ispec t th =
    (admit t; theorem (ISPEC t (theorem th)))
  fun part_match select th t =
    let
      val th = spec_all th
      val _ = admit (select (Thm.concl th))
      val _ = admit t
    in theorem (PART_MATCH select th t) end
  val rewriters = ref ([] : (Thm.thm * Conv.conv) list)
  fun rewr th t =
    let
      val th = spec_all th
      val _ = admit (lhs (Thm.concl th))
      val _ = admit t
    in
      case lookup rewriters th of
        SOME (_, c) => theorem (c t)
      | NONE =>
          let
            val c = Conv.REWR_CONV th
            val result = theorem (c t)
          in save rewriters th c; result end
    end

  infix 3 THENC ORELSEC
  fun (c THENC d) t =
    checked (Conv.THENC (checked c, checked d)) t
  fun (c ORELSEC d) t =
    checked (Conv.ORELSEC (checked c, checked d)) t
  fun rand c = checked (Conv.RAND_CONV (checked c))
  fun rator c = checked (Conv.RATOR_CONV (checked c))
  fun lhs_conv c = rator (rand c)
  fun rhs_conv c = rand c
  fun eq_conv c = lhs_conv c THENC rhs_conv c
  fun changed c = checked (Conv.CHANGED_CONV (checked c))
  fun qchanged c = checked (Conv.QCHANGED_CONV (checked c))
  fun all t = (admit t; raise Conv.UNCHANGED)
  fun no t = (admit t; Conv.NO_CONV t)
  fun try c = c ORELSEC all

  (* Keep traversal joins checked too, rather than just checking the result
     of a native recursive traversal. *)
  fun abs_rule v th =
    (admit v; theorem (ABS v (theorem th)))
  fun abs_conv c t =
    let
      val _ = admit t
      val (v, b) = dest_abs t
      val th = checked c b
    in
      abs_rule v th
      handle HOL_ERR _ =>
        let
          val fresh = genvar (type_of v)
          val a = checked (Drule.ALPHA_CONV fresh) t
          val body = #2 (dest_abs (rhs (Thm.concl a)))
          val b = abs_rule fresh (checked c body)
          val target = rhs (Thm.concl b)
          val v' = variant (free_vars target) v
          val d = checked (Drule.ALPHA_CONV v') target
        in trans (trans a b) d end
    end
  fun sub c t =
    (admit t;
     if is_comb t then (rator c THENC rand c) t
     else if is_abs t then abs_conv c t
     else raise Conv.UNCHANGED)
  fun repeat c t =
    let val th = checked c t
    in
      trans th (repeat c (rhs (Thm.concl th)))
      handle Conv.UNCHANGED => th
    end
    handle HOL_ERR _ => raise Conv.UNCHANGED
  fun depth c t = (sub (depth c) THENC repeat c) t
  fun top_depth c t =
    (repeat c THENC
     try (changed (sub (top_depth c)) THENC
          try (checked c THENC top_depth c))) t
  fun once_depth c t = try (checked c ORELSEC sub (once_depth c)) t
  fun conv_rule c th =
    let val th = theorem th
    in
      theorem (EQ_MP (checked c (Thm.concl th)) th)
      handle Conv.UNCHANGED => th
    end
  (* Native SYM_CONV/GSYM hide instantiations of EQ_SYM_EQ. Use the same
     law through the checked root rewriter and checked traversal instead. *)
  fun sym t = rewr boolTheory.EQ_SYM_EQ t
  fun gsym th = conv_rule (once_depth sym) th
  (* Dynamic uses of gsym below still traverse and check their fresh results.
     Only reversed source laws, and source fact introductions, are shared. *)
  val source_gsym = schema gsym
  val source_eqt = schema eqt
  val source_eqf = schema eqf

  (* A syntax-only conservative filter, not a generic matcher. This keeps
     unrelated laws (especially reversed laws) out of admission entirely.
     Actual matching below receives admitted theorems and targets. *)
  fun possible p t =
    if is_var p then true
    else if is_const p then
      is_const t andalso
      let val a = dest_thy_const p
          val b = dest_thy_const t
      in #Thy a = #Thy b andalso #Name a = #Name b end
    else if is_comb p then
      is_comb t andalso
      let val (f, x) = dest_comb p
          val (g, y) = dest_comb t
      in possible f g andalso possible x y end
    else is_abs t andalso
         possible (#2 (dest_abs p)) (#2 (dest_abs t))
  fun candidate flip body t =
    if is_forall body then candidate flip (#2 (dest_forall body)) t
    else if is_conj body then
      let val (a, b) = dest_conj body
      in candidate flip a t orelse candidate flip b t end
    else if is_eq body then
      possible ((if flip then rhs else lhs) body) t
    else if is_neg body then
      let
        val p = dest_neg body
        val p = if flip andalso is_eq p then
                  mk_eq (rhs p, lhs p)
                else p
      in possible p t end
    else possible body t

  (* Like Rewrite.mk_rewrites, but every projection, specialization and
     negative/positive fact introduction has an admission boundary. *)
  fun root_fact th t =
    let
      val th = spec_all th
      val body = Thm.concl th
    in
      if is_conj body then
        ((fn u => root_fact (first th) u) ORELSEC
         (fn u => root_fact (second th) u)) t
      else if is_eq body then rewr th t
      else if is_neg body then rewr (source_eqf th) t
      else if aconv body T then no t
      else rewr (source_eqt th) t
    end
  fun root [] t = no t
    | root ((flip, th) :: rest) t =
        if candidate flip (Thm.concl th) t then
          ((fn u => root_fact (if flip then source_gsym th else th) u)
           ORELSEC root rest) t
        else root rest t
  fun pure ths = top_depth (root ths)
  (* Read only; no simpset or TypeBase updates, and no eager admission. *)
  val implicit = List.map (fn th => (false, th))
    (Rewrite.dest_rewrites (Rewrite.implicit_rewrites ()))
  fun rewrite ths = pure (ths @ implicit)
  fun forward th = (false, th)
  fun backward th = (true, th)

  fun append_eval t =
    pure (map forward [listTheory.APPEND_NIL, listTheory.APPEND]) t
  fun norm_cons_step t =
    ((fn u => rewr (second listTheory.APPEND) u) THENC
     rand norm_cons_step ORELSEC
     (fn u => rewr (first listTheory.APPEND) u)) t
  fun norm_cons t =
    let
      val _ = admit t
      val (elements, tail) = strip_cons t
      val _ = if null elements orelse is_nil tail then
                raise Conv.UNCHANGED else ()
      val target = mk_append
        (mk_list (elements, type_of (hd elements)), tail)
    in gsym (checked norm_cons_step target) end
  fun append_simple t =
    let
      val _ = admit t
      val (a, b) = dest_append t
      val _ = if is_list a andalso is_list b then ()
              else raise Conv.UNCHANGED
    in append_eval t end
    handle HOL_ERR _ => raise Conv.UNCHANGED
  fun append_simple_assoc t =
    let
      val _ = admit t
      val (a, b) = dest_append t
      val (_, suffix) = dest_append a
      val _ = if is_list b andalso is_list suffix then ()
              else raise Conv.UNCHANGED
    in
      ((fn u => rewr (source_gsym listTheory.APPEND_ASSOC) u) THENC
       rand append_eval) t
    end
    handle HOL_ERR _ => raise Conv.UNCHANGED
  fun norm_no_eval t =
    (top_depth norm_cons THENC
     pure (map forward
       [listTheory.APPEND_NIL, listTheory.APPEND_ASSOC,
        listTheory.REVERSE_APPEND, listTheory.REVERSE_DEF]) THENC
     depth (qchanged append_simple_assoc ORELSEC
            qchanged append_simple)) t
  fun norm t = (norm_no_eval THENC append_eval) t

  fun nonempty t = is_list t andalso not (is_nil t)
  fun right_cons a b = nonempty (last a) andalso nonempty (last b)
  fun right_same a b =
    length a + length b > 2 andalso aconv (last a) (last b)
  fun left_nil t =
    (admit t;
     if is_append t then raise Conv.UNCHANGED
     else ispec t (source_gsym (first listTheory.APPEND)))

  fun right_elim conv t =
    let
      val _ = admit t
      val (a, b) = dest_eq t
      val as_ = strip_append a
      val bs = strip_append b
    in
      if right_same as_ bs then
        (eq_conv left_nil THENC
         (fn u => rewr (second listTheory.APPEND_11) u) THENC
         right_elim conv) t
      else if right_cons as_ bs then
        let
          val (a, _) = dest_list (last as_)
          val (b, _) = dest_list (last bs)
          val n = length a
          val m = length b
          val (turn, b, n, m) =
            if n <= m then (false, b, n, m) else (true, a, m, n)
          val th0 =
            ((if turn then sym else all) THENC eq_conv left_nil) t
            handle Conv.UNCHANGED => refl t
          val th1 = if n = m then th0 else
            let
              val (front, back) = Lib.split_after (m - n) b
              val ty = type_of (hd front)
              val target = mk_append (mk_list (front, ty),
                                      mk_list (back, ty))
              val split = gsym (append_eval target)
            in
              conv_rule (rhs_conv (rhs_conv
                (rand (checked (K split)) THENC
                 (fn u => rewr listTheory.APPEND_ASSOC u)))) th0
            end
          val th2a = part_match (lhs o Term.rand)
            (second listTheory.APPEND_11_LENGTH) (rhs (Thm.concl th1))
          val th2b = conv_rule (rator (rand
            (rewrite (map forward
              [listTheory.LENGTH, prim_recTheory.INV_SUC_EQ])))) th2a
          val th2 = trans th1 (mp th2b (theorem boolTheory.TRUTH))
          val th3 = if turn then
            conv_rule (rhs_conv (rator (rand sym))) th2 else th2
        in
          conv_rule (rhs_conv (rator (rand (right_elim conv)))) th3
        end
      else checked conv t
    end
    handle HOL_ERR _ => raise Conv.UNCHANGED

  fun left_cons a b = nonempty (hd a) andalso nonempty (hd b)
  fun left_same a b =
    length a + length b > 2 andalso aconv (hd a) (hd b)
  fun right_nil t =
    (admit t;
     if is_append t then raise Conv.UNCHANGED
     else ispec t (source_gsym listTheory.APPEND_NIL))

  fun left_elim conv t =
    let
      val _ = admit t
      val (a, b) = dest_eq t
      val as_ = strip_append a
      val bs = strip_append b
    in
      if left_same as_ bs then
        (eq_conv right_nil THENC
         (fn u => rewr (first listTheory.APPEND_11) u) THENC
         left_elim conv) t
      else if left_cons as_ bs then
        let
          val (a, _) = dest_list (hd as_)
          val (b, _) = dest_list (hd bs)
          val n = length a
          val m = length b
          val (turn, b, n, m) =
            if n <= m then (false, b, n, m) else (true, a, m, n)
          val th0 =
            ((if turn then sym else all) THENC eq_conv right_nil) t
            handle Conv.UNCHANGED => refl t
          val th1 = if n = m then th0 else
            let
              val (front, back) = Lib.split_after n b
              val ty = type_of (hd front)
              val target = mk_append (mk_list (front, ty),
                                      mk_list (back, ty))
              val split = gsym (append_eval target)
            in
              conv_rule (rhs_conv (rhs_conv
                (rator (rand (checked (K split))) THENC
                 (fn u =>
                   rewr (source_gsym listTheory.APPEND_ASSOC) u)))) th0
            end
          val th2a = part_match (lhs o Term.rand)
            (first listTheory.APPEND_11_LENGTH) (rhs (Thm.concl th1))
          val th2b = conv_rule (rator (rand
            (rewrite (map forward
              [listTheory.LENGTH, prim_recTheory.INV_SUC_EQ])))) th2a
          val th2 = trans th1 (mp th2b (theorem boolTheory.TRUTH))
          val th3 = if turn then
            conv_rule (rhs_conv (once_depth sym)) th2 else th2
        in conv_rule (rhs_conv (rand (left_elim conv))) th3 end
      else checked conv t
    end
    handle HOL_ERR _ => raise Conv.UNCHANGED

  fun internal t =
    let
      val _ = admit t
      val (a, b) = dest_eq t
    in
      if aconv a b then eqt (refl a)
      else right_elim
        (pure [backward listTheory.APPEND_ASSOC] THENC left_elim norm) t
    end
    handle HOL_ERR _ => raise Conv.UNCHANGED
  fun conv t =
    (eq_conv norm_no_eval THENC internal THENC
     rewrite [forward listTheory.APPEND_eq_NIL,
              forward listTheory.NOT_CONS_NIL,
              backward listTheory.NOT_CONS_NIL,
              forward listTheory.CONS_11]) t
  fun main t =
    let
      val _ = admit t
      val (a, b) = dest_eq t
      val _ = if is_list_type (type_of a) then ()
              else raise Conv.UNCHANGED
    in
      (* No normalization laws are needed for reflexivity. *)
      if aconv a b then eqt (refl a)
      else if not (can (find_term (fn u => is_cons u orelse
          is_append u orelse is_snoc u orelse is_reverse u)) t) then
        raise Conv.UNCHANGED
      else
        let
          val th = pure [forward listTheory.SNOC_APPEND] t
          val target = rhs (Thm.concl th)
        in trans th (changed conv target) end
        handle Conv.UNCHANGED => conv t
             | HOL_ERR _ => raise Conv.UNCHANGED
    end
  fun normalise t =
    if is_snoc t then rewr listTheory.SNOC_APPEND t
    else if is_append t then append_simple_assoc t
    else raise Conv.UNCHANGED
  fun protect conv t = checked conv t
    handle AdmissionFailure e => raise e
in
  {equality=protect main,normalise=protect normalise}
end

fun conversion check = #equality (procedures check)

end
