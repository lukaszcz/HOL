(* Replay-local bounded FP conversion schema cache regressions. *)
structure Z3_ReplaySchemaTests =
struct
open HolKernel Parse;
fun assert (condition,message) =
  if condition then () else raise Fail message;
fun check_oracle_tags name theorem =
  Library.check_oracle_tags "Z3_ReplaySchemaTests" name theorem;
fun expect_hol_error_contains name text action =
  ((action (); raise Fail (name ^ ": unexpectedly accepted"))
   handle Feedback.HOL_ERR detail =>
     assert (String.isSubstring text (Feedback.exn_to_string
       (Feedback.HOL_ERR detail)),name ^ ": wrong diagnostic"));
(* Exercise the actual shortcut independently of full FP circuit discovery.
   Rebuilt exponent occurrences must still use checked source transport. *)
fun run_alignment () =
let
  fun check producer source expected =
    let
      val theorem=producer source
      val _=assert (Thm.concl theorem ~~ boolSyntax.mk_eq (source,expected),
        "equal-exponent alignment changed its exact endpoints")
      val _=assert (List.null (Thm.hyp theorem),
        "equal-exponent alignment introduced a hypothesis")
    in check_oracle_tags "equal-exponent alignment" theorem end
  fun cases producer = List.app (fn (source,expected)=>
    check producer source expected)
    [(``smtfp_word_retained_scale (e:word6) e``,``e:word6``),
     (``smtfp_word_bounded_align (e:word6) e (v:word9)``,``v:word9``),
     (``smtfp_word_bounded_align
          (smtfp_word_retained_scale (e:word6) e) e (v:word9)``,``v:word9``),
     (``smtfp_word_retained_scale (e:word3) e``,``e:word3``),
     (``smtfp_word_bounded_align (e:word3) e (v:word4)``,``v:word4``)]
  val producer=Z3_ProofReplay.new_fp_alignment_rewriter_for_test ()
  val _=cases producer
  val _=cases producer
  val _=cases (Z3_ProofReplay.new_fp_alignment_rewriter_for_test ())
  fun decline source =
    ((ignore (producer source); raise Fail "unsupported alignment accepted")
     handle Conv.UNCHANGED => ())
  val _=List.app decline
    [``smtfp_word_retained_scale (e:word6) f``,
     ``smtfp_word_bounded_align (e:word6) f (v:word9)``,
     ``smtfp_word_bounded_align
          (smtfp_word_retained_scale (e:word6) f) e (v:word9)``,
     ``smtfp_word_bounded_align
          (smtfp_word_retained_scale (f:word6) e) e (v:word9)``,
     ``v:word9``]
  val template=``smtfp_word_bounded_align (e:word6) e (v:word9)``
  val (head,args)=boolSyntax.strip_comb template
  val exponent=hd args
  val value=List.nth (args,2)
  val (name,ty)=Term.dest_var exponent
  val rebuilt=Term.mk_var (name,ty)
  val _=assert (not (Portable.pointer_eq (exponent,rebuilt)),
    "alignment occurrence test unexpectedly shares its exponent")
  val _=check producer (Term.list_mk_comb
    (head,[exponent,rebuilt,value])) value
  (* Native INST touches only the compact law, then retains this shared DAG.
     No unfolded-circuit ALPHA comparison may be needed to prove the result. *)
  fun shared 0 term=term
    | shared depth term =
        let val child=shared (depth-1) term
        in wordsSyntax.mk_word_add (child,child) end
  val large=shared 48 exponent
  val _=check producer
    (Term.list_mk_comb (head,[large,large,value])) value
  fun injected hook () =
    SmtResource.with_e0_diagnostic_hook_for_test hook
      (SmtResource.with_e0_invocation_for_test producer) template
  val interrupted =
    ((ignore (injected (fn _=>raise Interrupt) ()); false)
     handle Interrupt => true)
  val _=assert (interrupted,"alignment shortcut swallowed Interrupt")
  val _=expect_hol_error_contains "alignment first resource error"
    "task57-alignment-first-error" (fn () => ignore
      (injected (fn _=>SmtResource.check_term_size_for "FloatingPoint"
        "task57-alignment-first-error"
        (SmtResource.max_bitblast_term_nodes+1)) ()))
  val _=check producer template value
  fun shared_type 0 = Type.bool
    | shared_type depth =
        let val child=shared_type (depth-1) in child --> child end
  val scale_law=smtfloatReplayAddSubWordTheory.smtfp_word_retained_scale_def
  val (_,generic) = boolSyntax.strip_forall (Thm.concl scale_law)
  val (scale,_) = boolSyntax.strip_comb (boolSyntax.lhs generic)
  val large_word=wordsSyntax.mk_word_type (shared_type 8)
  val typed_scale=Term.inst
    (Type.match_type (Term.type_of scale)
      (large_word --> large_word --> large_word)) scale
  val typed_exponent=Term.mk_var ("alignment_large_type",large_word)
  val _=decline (Term.list_mk_comb
    (typed_scale,[typed_exponent,typed_exponent]))
in () end;
(* The two-bit count law is checked before native INST inserts either a
   large arithmetic DAG or a payload with an independently chosen width. *)
fun run_narrow_alignment () =
let
  val source=``smtfp_word_bounded_align
    (smtfp_word_retained_scale
      (smtfp_word_addsub_exp (e:word3):word4)
      (smtfp_word_addsub_exp (f:word3):word4))
    (smtfp_word_addsub_exp e:word4) (v:word9)``
  val result=``if (smtfp_word_addsub_exp (f:word3):word4) <=+
      smtfp_word_addsub_exp (e:word3) then
    smtfp_word_lsl_bv (v:word9)
      (w2w (if (smtfp_word_addsub_exp e:word4) -
                   smtfp_word_addsub_exp f <=+ 3w then
                (smtfp_word_addsub_exp e:word4) - smtfp_word_addsub_exp f
             else 3w):word2)
    else if (smtfp_word_addsub_exp f:word4) -
                 smtfp_word_addsub_exp e <=+ 3w then v
    else smtfp_word_jam_bv v
      (w2w ((smtfp_word_addsub_exp f:word4) -
              smtfp_word_addsub_exp e - 3w):word2)``
  val right_source=``smtfp_word_bounded_align
    (smtfp_word_retained_scale
      (smtfp_word_addsub_exp (e:word3):word4)
      (smtfp_word_addsub_exp (f:word3):word4))
    (smtfp_word_addsub_exp f:word4) (v:word9)``
  val right_result=Term.subst
    [``e:word3`` |-> ``f:word3``,``f:word3`` |-> ``e:word3``] result
  val scale_source=``smtfp_word_retained_scale
    (smtfp_word_addsub_exp (e:word3):word4)
    (smtfp_word_addsub_exp (f:word3):word4)``
  val scale_result=``(w2w
    (if (smtfp_word_addsub_exp (f:word3):word3) <=+
          smtfp_word_addsub_exp (e:word3) then
       if (smtfp_word_addsub_exp e:word3) -
            smtfp_word_addsub_exp f <=+ 3w then
         (smtfp_word_addsub_exp f:word3)
       else smtfp_word_addsub_exp e - 3w
     else if (smtfp_word_addsub_exp f:word3) -
               smtfp_word_addsub_exp e <=+ 3w then smtfp_word_addsub_exp e
     else smtfp_word_addsub_exp f - 3w):word4)``
  fun check producer (source,result) =
    let val theorem=producer source
    in assert (Thm.concl theorem ~~ boolSyntax.mk_eq (source,result),
         "narrow alignment changed its exact endpoints" ^
         (if SmtResource.term_nodes_up_to 1000 source<1000 then
            "\nsource: " ^ Library.term_to_string source ^
            "\nactual: " ^ Library.term_to_string (Thm.concl theorem) ^
            "\nexpected: " ^ Library.term_to_string result else ""));
       assert (List.null (Thm.hyp theorem),"narrow alignment retained Hyp");
       check_oracle_tags "narrow alignment" theorem
    end
  val producer=Z3_ProofReplay.new_fp_alignment_rewriter_for_test ()
  val cases=[(source,result),(right_source,right_result),
    (scale_source,scale_result)]
  val _=List.app (check producer) cases
  val _=List.app (check producer) cases
  val _=List.app (check
    (Z3_ProofReplay.new_fp_alignment_rewriter_for_test ())) cases
  val (head,args)=boolSyntax.strip_comb source
  val exponent=List.nth (args,1)
  val value=List.nth (args,2)
  val (exp_head,exp_args)=boolSyntax.strip_comb exponent
  val (name,ty)=Term.dest_var (hd exp_args)
  val rebuilt=Term.mk_comb (exp_head,Term.mk_var (name,ty))
  val _=assert (not (Portable.pointer_eq (exponent,rebuilt)),
    "narrow alignment test unexpectedly shares exponent occurrences")
  val _=check producer (Term.list_mk_comb
    (head,[hd args,rebuilt,value]),result)
  fun shared 0 term=term
    | shared depth term =
        let val child=shared (depth-1) term
        in wordsSyntax.mk_word_add (child,child) end
  val operands=[``e:word3`` |-> shared 48 ``e:word3``,
    ``v:word9`` |-> shared 48 ``v:word9``]
  val _=check producer (Term.subst operands source,Term.subst operands result)
  val binder_subst=[``v:word9`` |->
    ``if (!b:bool. b) then (v:word9) else u``]
  val _=check producer
    (Term.subst binder_subst source,Term.subst binder_subst result)
  val width_subst=[``v:word9`` |-> ``w2w (payload:word5):word9``]
  val _=check producer
    (Term.subst width_subst source,Term.subst width_subst result)
  (* The payload type is independent of the exponent arithmetic type. *)
  val other_source=``smtfp_word_bounded_align
    (smtfp_word_retained_scale
      (smtfp_word_addsub_exp (e:word3):word4)
      (smtfp_word_addsub_exp (f:word3):word4))
    (smtfp_word_addsub_exp e:word4) (v:word5)``
  val other_result=``if (smtfp_word_addsub_exp (f:word3):word4) <=+
      smtfp_word_addsub_exp (e:word3) then
    smtfp_word_lsl_bv (v:word5)
      (w2w (if (smtfp_word_addsub_exp e:word4) -
                   smtfp_word_addsub_exp f <=+ 3w then
                (smtfp_word_addsub_exp e:word4) - smtfp_word_addsub_exp f
             else 3w):word2)
    else if (smtfp_word_addsub_exp f:word4) -
                 smtfp_word_addsub_exp e <=+ 3w then v
    else smtfp_word_jam_bv v
      (w2w ((smtfp_word_addsub_exp f:word4) -
              smtfp_word_addsub_exp e - 3w):word2)``
  val _=check producer (other_source,other_result)
  fun decline source =
    ((ignore (producer source); raise Fail "unsupported narrow alignment")
     handle Conv.UNCHANGED => ())
  val _=List.app decline
    [``smtfp_word_bounded_align
        (smtfp_word_retained_scale (smtfp_word_addsub_exp (e:word4):word5)
          (smtfp_word_addsub_exp (f:word4):word5))
        (smtfp_word_addsub_exp e:word5) (v:word9)``,
     ``smtfp_word_bounded_align
        (smtfp_word_retained_scale (smtfp_word_addsub_exp (e:word3):word4)
          (smtfp_word_addsub_exp (f:word3):word4))
        (smtfp_word_addsub_exp g:word4) (v:word9)``]
  fun shared_type 0 = Type.bool
    | shared_type depth =
        let val child=shared_type (depth-1) in child --> child end
  val generic=``smtfp_word_bounded_align
    (smtfp_word_retained_scale
      (smtfp_word_addsub_exp (e:word3):word4)
      (smtfp_word_addsub_exp (f:word3):word4))
    (smtfp_word_addsub_exp e:word4) (v:'payload word)``
  val _=decline (Term.inst
    [``:'payload`` |-> shared_type 8] generic)
  val _=new_constant ("task57_narrow_alignment_signature",Type.bool)
  val _=List.app (check producer) cases
  fun injected hook = SmtResource.with_e0_diagnostic_hook_for_test hook
    (SmtResource.with_e0_invocation_for_test producer) source
  val interrupted=((ignore (injected (fn _=>raise Interrupt)); false)
    handle Interrupt=>true)
  val _=assert (interrupted,"narrow alignment swallowed Interrupt")
  val _=expect_hol_error_contains "narrow alignment first resource error"
    "task57-narrow-first-error" (fn () => ignore (injected
      (fn _=>SmtResource.check_term_size_for "FloatingPoint"
        "task57-narrow-first-error" (SmtResource.max_bitblast_term_nodes+1))))
  val _=check producer (source,result)
  (* One count bit is false: a gap of two would wrap to zero. *)
  val wrong=``smtfp_word_bounded_align
    (smtfp_word_retained_scale (smtfp_word_addsub_exp (3w:word3):word4)
      (smtfp_word_addsub_exp (0w:word3):word4))
    (smtfp_word_addsub_exp (3w:word3):word4) (1w:word9) <>
    smtfp_word_lsl_bv (1w:word9) (w2w (2w:word4):word1)``
  val counterexample=Drule.EQT_ELIM (bossLib.EVAL wrong)
  val _=assert (Thm.concl counterexample ~~ wrong andalso
    List.null (Thm.hyp counterexample),"one-bit count control changed")
  val _=check_oracle_tags "one-bit count counterexample" counterexample
in () end;
(* The GRS conversion is optional and must retain the old QRD relationship,
   including wrapped counts, before inserting actual field graphs. *)
fun run_self_add () =
let
  val producer=Z3_ProofReplay.new_fp_self_add_rewriter_for_test ()
  val source=``smtfp_word_addsub_fields F RNE
    (s:word1) (e:word3) (f:word4) s e f (:4) (:9)``
  val expected=``if e=7w then
      if f=0w then (s:word1,7w:word3,0w:word4) else (0w,7w,1w)
    else (s,if e=6w then 7w else
               if e=0w then (if f ' 3 then 1w else 0w) else e+1w,
             if e=6w then 0w else if e=0w then f << 1 else f)``
  fun check input output =
    let val theorem=producer input
        val expected=boolSyntax.rhs (Thm.concl
          (Conv.QCONV (simpLib.SIMP_CONV bossLib.pure_ss []) output))
    in assert (Thm.concl theorem ~~ boolSyntax.mk_eq (input,expected),
         "self-add conversion changed endpoints");
       assert (null (Thm.hyp theorem),"self-add retained Hyp");
       check_oracle_tags "self-add" theorem end
  val _=check source expected
  val _=check source expected
  val _=check ``FST (SND ^source)`` ``FST (SND ^expected)``
  val wrapped=``smtfp_word_addsub_fields F
    (smtfp_unpack_rounding (smtfp_pack_rounding RNE))
    (s:word1) (e:word3) (f:word4) s e f (:4) (:9)``
  val _=check wrapped expected
  fun concrete (sign,exponent,fraction) =
    let val substitution=
          [``s:word1`` |-> wordsSyntax.mk_wordii (sign,1),
           ``e:word3`` |-> wordsSyntax.mk_wordii (exponent,3),
           ``f:word4`` |-> wordsSyntax.mk_wordii (fraction,4)]
        val input=Term.subst substitution source
        val output=Term.subst substitution expected
        val _=check input output
        val original=bossLib.EVAL input
        val converted=bossLib.EVAL output
    in assert (boolSyntax.rhs (Thm.concl original) ~~
         boolSyntax.rhs (Thm.concl converted),
         "self-add changed zero, NaN, subnormal or overflow") end
  val _=List.app concrete [(0,0,0),(1,0,0),(0,0,7),(1,0,8),
    (0,0,15),(1,1,0),(0,5,15),(1,6,15),(0,7,0),(1,7,1)]
  fun decline input =
    ((ignore (producer input); raise Fail "unsupported self-add accepted")
     handle Conv.UNCHANGED=>())
  val _=List.app decline
    [``smtfp_word_addsub_fields T RNE
        (s:word1) (e:word3) (f:word4) s e f (:4) (:9)``,
     ``smtfp_word_addsub_fields F RNA
        (s:word1) (e:word3) (f:word4) s e f (:4) (:9)``,
     ``smtfp_word_addsub_fields F RNE
        (s:word1) (e:word3) (f:word4) t e f (:4) (:9)``,
     ``smtfp_word_addsub_fields F RNE
        (s:word1) (e:word3) (f:word4) s g f (:4) (:9)``,
     ``smtfp_word_addsub_fields F RNE
        (s:word1) (e:word3) (f:word4) s e h (:4) (:9)``,
     ``smtfp_word_addsub_fields F RNE
        (s:word1) (e:word4) (f:word4) s e f (:5) (:9)``]
  val _=new_constant ("task57_self_add_signature",Type.bool)
  val _=check source expected
  fun injected hook = SmtResource.with_e0_diagnostic_hook_for_test hook
    (SmtResource.with_e0_invocation_for_test producer) source
  val interrupted=((ignore (injected (fn _=>raise Interrupt)); false)
    handle Interrupt=>true)
  val _=assert (interrupted,"self-add swallowed Interrupt")
  val _=expect_hol_error_contains "self-add first resource error"
    "task57-self-add-first-error" (fn () => ignore (injected
      (fn _=>SmtResource.check_term_size_for "FloatingPoint"
        "task57-self-add-first-error"
        (SmtResource.max_bitblast_term_nodes+1))))
  val _=check source expected
in () end;

fun run_grs () =
let
  val producer=Z3_ProofReplay.new_fp_grs_rewriter_for_test ()
  fun check source =
    let val theorem=producer source
    in assert (boolSyntax.lhs (Thm.concl theorem) ~~ source,
         "GRS conversion lost its exact source");
       assert (List.null (Thm.hyp theorem),"GRS conversion retained Hyp");
       check_oracle_tags "GRS conversion" theorem; theorem
    end
  fun evaluated source =
    let val theorem=check source
        val result=Thm.TRANS theorem
          (bossLib.EVAL (boolSyntax.rhs (Thm.concl theorem)))
    in check_oracle_tags "evaluated GRS conversion" result;
       boolSyntax.rhs (Thm.concl result)
    end
  fun round (mode,sign_number,data_number,count_number,expected) =
    let
      val sign=wordsSyntax.mk_wordii (sign_number,1)
      val data=wordsSyntax.mk_wordii (data_number,9)
      val count=wordsSyntax.mk_wordii (count_number,4)
      val source=``smtfp_word_round_qrd_up ^mode ^sign ^data ^count``
      val old=``smtfp_word_round_up ^mode ^sign
        (smtfp_word_lsr_bv ^data ^count)
        (^data - smtfp_word_lsl_bv (smtfp_word_lsr_bv ^data ^count) ^count)
        (smtfp_word_lsl_bv (1w:word9) ^count)``
      val value=evaluated source
      val old_value=bossLib.EVAL old
      val _=check_oracle_tags "original QRD control" old_value
    in assert (value ~~ (if expected then boolSyntax.T else boolSyntax.F)
        andalso value ~~ boolSyntax.rhs (Thm.concl old_value),
      "GRS rounding changed mode, sign, count or wrapped-word semantics") end
  val _=List.app round
    [(``RNE``,0,1,1,false),(``RNE``,0,3,1,true),
     (``RNA``,0,1,1,true),(``RTP``,0,1,1,true),
     (``RTP``,1,1,1,false),(``RTN``,0,1,1,false),
     (``RTN``,1,1,1,true),(``RTZ``,0,511,1,false),
     (``RNE``,0,256,8,false),(``RNE``,0,384,8,true),
     (``RNE``,0,256,9,false),(``RNE``,0,257,9,true),
     (``RNA``,0,256,9,true),(``RNE``,0,511,15,true)]
  val _=List.app (fn mode=>round (mode,0,511,0,false))
    [``RNE``,``RNA``,``RTP``,``RTN``,``RTZ``]
  fun encoding mode scale data =
    ``smtfp_word_encode_fields ^mode (0w:word1) (ARB:(4,3)smtfp)
      ^scale ^data``
  fun fields (mode,expected_fraction) =
    let
      val source=encoding mode ``3w:word4`` ``137w:word9``
      val expected=pairSyntax.mk_pair (``6w:word3``,
        wordsSyntax.mk_wordii (expected_fraction,4))
    in assert (evaluated source ~~ expected,
         "GRS field encoding changed rounding");
       assert (evaluated ``FST ^source`` ~~ ``6w:word3`` andalso
         evaluated ``SND ^source`` ~~ wordsSyntax.mk_wordii
           (expected_fraction,4),"GRS projection lost its field")
    end
  val _=List.app fields
    [(``RNE``,1),(``RNA``,1),(``RTP``,2),(``RTN``,1),(``RTZ``,1)]
  val _=assert (evaluated (encoding ``RNE`` ``7w:word4`` ``1w:word9``)
      ~~ ``(3w:word3,0w:word4)``,"GRS encoding changed left normalization")
  val _=assert (evaluated (encoding ``RNE`` ``7w:word4`` ``0w:word9``)
      ~~ ``(0w:word3,0w:word4)``,"GRS encoding changed zero")
  val template=``smtfp_word_encode_fields mode sign (ARB:(4,3)smtfp)
    (scale:word4) (data:word9)``
  val _=ignore (check template)
  val _=ignore (check template)
  val (_,arguments)=boolSyntax.strip_comb template
  val _=ignore (check (Term.list_mk_comb
    (#1 (boolSyntax.strip_comb template),
      List.take (arguments,4) @ [Term.mk_var ("data",``:word9``)])))
  fun shared 0 term=term
    | shared depth term =
        let val child=shared (depth-1) term
        in wordsSyntax.mk_word_add (child,child) end
  val _=ignore (check (Term.subst
    [``data:word9`` |-> shared 48 ``data:word9``] template))
  val _=ignore (check (Term.subst [``data:word9`` |->
    ``if (!b:bool. b) then (data:word9) else other``] template))
  fun decline source =
    ((ignore (producer source); raise Fail "unsupported GRS conversion")
     handle Conv.UNCHANGED=>())
  val _=List.app decline
    [``smtfp_word_round_up mode sign (q:word9) (r:word9) (d:word9)``,
     ``smtfp_word_encode_fields mode sign (ARB:(4,3)smtfp)
        (scale:word3) (data:word9)``,
     ``smtfp_word_encode_fields mode sign (ARB:(4,3)smtfp)
        (scale:word4) (data:word8)``]
  val _=ignore (check ``smtfp_word_encode_fields mode sign (ARB:(5,3)smtfp)
    (scale:word4) (data:word9)``)
  fun shared_type 0 = Type.bool
    | shared_type depth =
        let val child=shared_type (depth-1) in child --> child end
  val generic=``smtfp_word_encode_fields mode sign
    (format:('fraction,'exponent)smtfp) (scale:word4) (data:word9)``
  val _=decline (Term.inst [``:'fraction`` |-> shared_type 8] generic)
  val _=new_constant ("task57_grs_signature",Type.bool)
  val _=ignore (check template)
  fun injected hook = SmtResource.with_e0_diagnostic_hook_for_test hook
    (SmtResource.with_e0_invocation_for_test producer) template
  val interrupted=((ignore (injected (fn _=>raise Interrupt)); false)
    handle Interrupt=>true)
  val _=assert (interrupted,"GRS conversion swallowed Interrupt")
  val _=expect_hol_error_contains "GRS first resource error"
    "task57-grs-first-error" (fn () => ignore (injected
      (fn _=>SmtResource.check_term_size_for "FloatingPoint"
        "task57-grs-first-error" (SmtResource.max_bitblast_term_nodes+1))))
  val _=ignore (check template)
in () end;
fun run () =
let
  val cached = Z3_ProofReplay.new_fp_field_cache_for_test ()
  val calls = ref 0
  fun refl source () = (calls := !calls+1; Thm.REFL source)
  fun request source =
    let val theorem = cached source (refl source)
    in
      assert (Term.aconv (Thm.concl theorem)
        (boolSyntax.mk_eq (source,source)),
        "field cache lost the exact typed source");
      assert (List.null (Thm.hyp theorem), "field cache retained hypotheses");
      check_oracle_tags "FP field schema cache" theorem
    end
  val shapes = [``(x:word3) = (x:word3)``,
    ``(x:word3) = (y:word3)``,
    ``(x:word4) = (x:word4)``,
    ``(x:word3) = (0w:word3)``,
    ``(x:word3) = (1w:word3)``]
  val _ = List.app request shapes
  val _ = List.app request shapes
  val _ = assert (!calls=List.length shapes,
    "field cache confused types, literals, or alias roles")
  val packing =
    ``smtfp_pack_bv (smtfp_bits s e f : (4,3) smtfp)``
  val packing_calls = ref 0
  fun packing_law () =
    (packing_calls := !packing_calls+1;
     simpLib.SIMP_CONV (bossLib.srw_ss())
       [smtfloatTheory.smtfp_pack_bv_def,
        smtfloatTheory.smtfp_rep_bits,smtfloatTheory.canon_def,
        smtfloatTheory.float_canon_qnan_def,
        binary_ieeeTheory.float_is_nan_def,boolTheory.COND_RAND] packing)
  val packed = cached packing packing_law
  val repeated = cached packing packing_law
  val _ = assert (!packing_calls=1 andalso
      Term.aconv (Thm.concl packed) (Thm.concl repeated),
    "typed FP packing law was not proved just once")
  val _ = assert (List.null (Thm.hyp repeated),
    "typed FP packing law retained hypotheses")
  val _ = check_oracle_tags "typed FP packing law" repeated
  val source = hd shapes
  val _ = new_constant ("task57_fp_field_cache_signature",Type.bool)
  val _ = request source
  val _ = assert (!calls=List.length shapes+1,
    "field cache survived a signature change")
  val fresh = Z3_ProofReplay.new_fp_field_cache_for_test ()
  val _ = ignore (fresh source (refl source))
  val _ = assert (!calls=List.length shapes+2,
    "independent replay contexts shared a field certificate")
  val invalid = Z3_ProofReplay.new_fp_field_cache_for_test ()
  val _ = expect_hol_error_contains "FP field cache hypotheses"
    "bounded closed conversion" (fn () => ignore (invalid source
      (fn () => Drule.ADD_ASSUM boolSyntax.T (Thm.REFL source))))
  val _ = expect_hol_error_contains "FP field cache oracle tags"
    "oracle" (fn () => ignore (invalid source (fn () =>
      Thm.mk_oracle_thm "task57_field_negative"
        ([],boolSyntax.mk_eq (source,source)))))
  val _ = ignore (invalid source (refl source))
  val _ = assert (!calls=List.length shapes+3,
    "a rejected field theorem poisoned its cache key")
  val first_error = Z3_ProofReplay.new_fp_field_cache_for_test ()
  val _ = expect_hol_error_contains "FP field cache first resource error"
    "task57-field-cache-first-error" (fn () => ignore (first_error source
      (fn () => (SmtResource.check_term_size_for "FloatingPoint"
        "task57-field-cache-first-error"
        (SmtResource.max_bitblast_term_nodes+1); Thm.REFL source))))
  val interrupted = ((ignore (first_error source (fn () => raise Interrupt));
      false) handle Interrupt => true)
  val _ = assert (interrupted,"field cache swallowed Interrupt")
  val _ = ignore (first_error source (refl source))
  fun shared 0 = boolSyntax.T
    | shared n = let val child=shared (n-1)
        in boolSyntax.mk_conj (child,child) end
  val previous_calls = !calls
  val _ = expect_hol_error_contains "FP field cache bounded admission"
    "unbounded conversion schema" (fn () => ignore
      (cached (shared 14) (refl boolSyntax.T)))
  val _ = assert (!calls=previous_calls,
    "field schema producer ran before bounded admission")
  val binder = Term.mk_abs (Term.mk_var ("field_bound",Type.bool),
    Term.mk_var ("field_bound",Type.bool))
  val _ = expect_hol_error_contains "FP field cache binder boundary"
    "unbounded conversion schema" (fn () => ignore
      (cached binder (refl binder)))
  val _ = assert (!calls=previous_calls,
    "field schema producer ran before binder admission")
  val _ = expect_hol_error_contains "FP field cache bounded output"
    "bounded closed conversion" (fn () => ignore
      (first_error boolSyntax.F (fn () => Thm.REFL (shared 14))))
  val wrong_source =
    ((ignore (first_error boolSyntax.F (fn () => Thm.REFL boolSyntax.T));
      false) handle Feedback.HOL_ERR detail =>
        not (SmtResource.is_resource_gate detail))
  val _ = assert (wrong_source,"field cache accepted a different source")
  val _ = ignore (first_error boolSyntax.F (fn () => Thm.REFL boolSyntax.F))
  val bounded = Z3_ProofReplay.new_fp_field_cache_for_test ()
  val capacity_calls = ref 0
  fun number n = numSyntax.mk_numeral (Arbnum.fromInt n)
  fun produce term () =
    (capacity_calls := !capacity_calls+1; Thm.REFL term)
  fun fill n = let val term=number n
    in ignore (bounded term (produce term)) end
  val _ = List.app fill (List.tabulate (2049,fn i=>i))
  val _ = fill 0
  val _ = fill 2048
in
  assert (!capacity_calls=2050,
    "field schema cache did not retain its bounded first 2048 entries")
end
end
