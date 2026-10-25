(* Copyright (c) 2026 The HOL4 contributors. *)
structure SmtLib_GraphScalarTests =
struct
  open HolKernel boolLib testutils
  structure B = SmtLib_GraphBackend
  structure G = SmtReplayGraph
  structure P = SmtLib_Parser
  structure R = SmtLib_GraphTheories
  structure PV = SmtLib_GraphParserValue
  structure RP = SmtReplayResourcePolicy
  val limits = {template_limit=4096,index_limit=256,
                operand_limit=256,token_limit=256}
  val policy = {template_limit=RP.AtMost 4096,index_limit=RP.AtMost 256,
                operand_limit=RP.AtMost 256,token_limit=RP.AtMost 256}
  fun ensure text yes = if yes then () else raise Fail text
  fun tokens text =
    let val position = ref 0 in
      P.make_cpc_proof_tokenizer_from_input (fn () =>
        if !position = String.size text then NONE
        else let val c = String.sub (text,!position)
             in position := !position+1; SOME c end)
    end
  val symbol_key = ref P.proof_symbol_text
  fun key token = (!symbol_key) token
  val cfg : P.parser_cfg =
    {mk_let_bindings=P.smtlib_mk_let_bindings,mk_let=P.smtlib_mk_let,
     mk_bound_var=Term.mk_var,lookup_binder_list=fn _ => NONE,
     record_binder_block=fn _ => (),symbol_key=key,
     type_symbol_key=Lib.I,parse_choice=false,parse_lambda=true}
  fun options backend frame : 'a P.construction_cfg =
    {backend=backend,frame=frame,symbol_key=key,
     type_symbol_key=Lib.I,index_limit=256,parse_choice=false,
     parse_lambda=true,lookup_binder_list=fn _ => NONE,
     binder_reference=fn _ => fn _ => raise Fail "binder alias",
     record_binder_block=fn _ => (),
     ascribed_symbol=fn _ => fn _ => raise Fail "ascription",
     coerce_arguments=R.coerce_arguments backend}
  fun policy_options backend frame : 'a P.policy_construction_cfg =
    {backend=backend,frame=frame,symbol_key=key,
     type_symbol_key=Lib.I,index_limit=RP.AtMost 256,parse_choice=false,
     parse_lambda=true,lookup_binder_list=fn _ => NONE,
     binder_reference=fn _ => fn _ => raise Fail "binder alias",
     record_binder_block=fn _ => (),
     ascribed_symbol=fn _ => fn _ => raise Fail "ascription",
     coerce_arguments=R.coerce_arguments backend}
  fun ordinary logic text = P.parse_term_with_cfg cfg (tokens text)
    (SmtLib_Logics.parsedicts_of_solver_logic "cvc5" logic)
  fun parsed backend exact logic text =
    if exact then P.parse_term_with_policy
      (policy_options backend (B.root backend)) (tokens text)
      (#dictionaries (R.select_with_policy_no_override backend policy
        {logic=logic,solver=SOME "cvc5"}))
    else P.parse_term_with_backend
      (options backend (B.root backend)) (tokens text)
      (#dictionaries (R.select backend limits
        {logic=logic,solver=SOME "cvc5"}))
  fun with_graph action =
    let val graph=G.new () val scope=G.root_scope graph
        val backend=B.graphs {graph=graph,scope=scope,import_limit=4096,
                             literal_limit=4096,binder_limit=4096}
        val result=Exn.capture (fn () => action graph backend) ()
        val _=G.close_scope graph scope
    in Exn.release result end
  fun with_values action =
    let val graph=G.new () val scope=G.root_scope graph
        val context=PV.create {graph=graph,scope=scope,
          validate=fn () => (),spend=fn _ => (),retire=fn () => ()}
        val held=B.values_with_policy {context=context,graph=graph,
          scope=scope,import_limit=RP.AtMost 4096,
          literal_limit=RP.AtMost 4096,binder_limit=RP.AtMost 4096}
        val result=Exn.capture (fn () => action graph context
          (#backend held)) ()
        val _=(#close held) () val _=G.close_scope graph scope
    in Exn.release result end
  (* Only bounded fixtures are interpreted for a checked comparison. This
     is test code, never a production builder or parser callback. *)
  fun small backend value =
    let val left=ref 4096 val frame=B.root backend
        fun walk value =
          (left := !left-1; ensure "expanded test fixture" (!left>=0);
           case B.view backend frame value of
             B.Atom term => term
           | B.Apply (f,x) => Term.mk_comb (walk f,walk x)
           | B.Opaque => raise Fail "opaque test fixture")
    in walk value end
  fun bridge original result =
    let val reduced=Conv.QCONV
          (simpLib.SIMP_CONV pureSimps.pure_ss [boolTheory.LET_THM]
           THENC DEPTH_CONV BETA_CONV) original
        val rhs=boolSyntax.rhs (Thm.concl reduced)
        val equality=if Term.aconv rhs result then Thm.ALPHA rhs result
          else
            (ensure "expanded semantic test bridge"
               (Option.isSome (SmtReplayImport.bounded_raw_size 4096 rhs)
                andalso Option.isSome
                  (SmtReplayImport.bounded_raw_size 4096 result));
             blastLib.BBLAST_PROVE (boolSyntax.mk_eq (rhs,result)))
        val th=Thm.TRANS reduced equality
    in ensure "builder changed types/Hyp" (null (Thm.hyp th) andalso
         Type.compare (Term.type_of original,Term.type_of result)=EQUAL);
       Library.check_oracle_tags "GraphScalarTests" "bridge" th
    end
  val fp="(_ +zero 5 11)"
  val other="(_ -oo 5 11)"
  fun fp1 name = "("^name^" "^fp^")"
  fun fp2 name = "("^name^" "^fp^" "^other^")"
  fun fpr name = "("^name^" RNE "^fp^")"
  fun fpr2 name = "("^name^" RNE "^fp^" "^other^")"
  val examples =
    [("QF_UF",["true","false","(not true)","(=> true false true)",
      "(and true false true)","(or true false true)",
      "(xor true false true)","(= true false true)",
      "(distinct true false true)","(ite true false true)"]),
     ("QF_LIA",["0","123","(- 4)","(- 4 2 1)","(+ 1 2 3)",
      "(* 1 2 3)","(** 2 3)","(div 7 2 1)","(mod 7 2 1)",
      "(abs (- 3))","((_ divisible 3) 9)","(< 1 2 3)",
      "(<= 1 2 3)","(> 3 2 1)","(>= 3 2 1)",
      "(let ((i 3)) ((_ divisible i) 9))",
      "((_ divisible (let ((i 3)) i)) 9)",
      "(forall ((i Int)) ((_ divisible i) 9))"]),
     ("QF_LRA",["123","1.2500","(- 1.2)","(- 3.0 2.0 1.0)",
      "(+ 1.0 2.0 3.0)","(* 1.0 2.0 3.0)","(/ 3.0 2.0 1.0)",
      "(< 1.0 2.0 3.0)","(<= 1.0 2.0 3.0)",
      "(> 3.0 2.0 1.0)","(>= 3.0 2.0 1.0)"]),
     ("AUFLIRA",["(+ 1 2.0)","(= 1 1.0)","(to_real 3)",
      "(to_int 1.5)","(is_int 1.5)"]),
     ("QF_BV",["#b0101","#x3a","(_ bv12 8)",
      "(concat #b01 #b100)","((_ extract 2 1) #b1010)",
      "((_ @bit_of 0) #b1)","((_ repeat 3) #b10)",
      "((_ zero_extend 2) #b10)","((_ sign_extend 2) #b10)",
      "((_ zero_extend (! 2 :named width)) #b10)",
      "((_ rotate_left 2) #b101)","((_ rotate_right 2) #b101)",
      "(ubv_to_int #b101)","(sbv_to_int #b101)",
      "((_ int_to_bv 3) 5)",
      "(@bbterm true false true)",
      "(forall ((p Bool) (q Bool)) (= (@bbterm p q) #b00))",
      "(forall ((w (_ BitVec 2))) (= (@bbterm ((_ @bit_of 0) w) "^
        "((_ @bit_of 1) w)) w))",
      "(forall ((w (_ BitVec 2))) (= (@bbterm "^
        "(not ((_ @bit_of 0) w)) (not ((_ @bit_of 1) w))) (bvnot w)))"] @
      List.map (fn name => "("^name^" #b101 #b011)")
        ["bvand","bvor","bvxor","bvxnor","bvadd","bvmul",
         "bvudiv","bvurem","bvsub","bvnand","bvnor","bvcomp",
         "bvsdiv","bvsrem","bvsmod","bvshl","bvlshr","bvashr",
         "bvult","bvule","bvugt","bvuge","bvslt","bvsle","bvsgt",
         "bvsge","bvuaddo","bvsaddo","bvumulo","bvsmulo","bvusubo",
         "bvssubo","bvsdivo"] @
      List.map (fn name => "("^name^" #b101)") ["bvnot","bvneg","bvnego"]),
     ("QF_FP",SmtLib_Theories.FloatingPoint.rounding_modes @
      List.map (fn name => "(_ "^name^" 5 11)")
        ["+zero","-zero","+oo","-oo","NaN"] @
      ["(fp #b0 #b00000 #b0000000000)",
       "(fp.fma RNE "^fp^" "^other^" "^fp^")",
       "((_ to_fp 5 11) #x0000)",
       "((_ to_fp 5 11) RNE "^fp^")",
       "((_ to_fp 5 11) RNE 3.25)",
       "((_ to_fp 5 11) RNE 3)",
       "((_ to_fp 5 11) RNE #b101)",
       "((_ to_fp_unsigned 5 11) RNE #b101)",
       "((_ fp.to_ubv 8) RTZ "^fp^")",
       "((_ fp.to_sbv 8) RTZ "^fp^")"] @
      List.map fp1 ["fp.abs","fp.neg","fp.to_real","fp.isNormal",
        "fp.isSubnormal","fp.isZero","fp.isInfinite","fp.isNaN",
        "fp.isNegative","fp.isPositive"] @
      List.map fp2 ["fp.rem","fp.min","fp.max","fp.eq","fp.leq",
        "fp.lt","fp.geq","fp.gt"] @
      List.map fpr ["fp.sqrt","fp.roundToIntegral"] @
      List.map fpr2 ["fp.add","fp.sub","fp.mul","fp.div"])]
  val malformed =
    [("QF_LIA",["01","1.2.3","(+ 1)","((_ divisible 2 3) 1)","(abs true)",
      "(forall ((x MissingSort)) true)"]),
     ("QF_BV",["#b","#b2","#xg","(_ bvbad 3)",
      "(let ((i 2)) ((_ zero_extend i) #b10))",
      "((_ zero_extend (let ((i 2)) i)) #b10)",
      "((_ zero_extend (forall ((p Bool)) p)) #b10)",
      "((_ zero_extend (let ((i 2)) i) 3) #b10)",
      "((_ zero_extend (let ((i 2)) i)))",
      "((_ zero_extend (bvnot)) #b10)",
      "((_ zero_extend (bvadd #b1 true)) #b10)",
      "((_ zero_extend ((_ extract 1) #b10)) #b10)",
      "((_ zero_extend (forall ((p MissingSort)) p)) #b10)",
      "((_ zero_extend (exists ((p Bool)) p)) #b10)",
      "((_ zero_extend (forall ((p Bool)) 2)) #b10)",
      "((_ zero_extend (lambda ((i Int)) i)) #b10)",
      "(let ((i 2)) ((_ zero_extend (let ((j i)) j)) #b10))",
      "(let ((i 2)) ((_ zero_extend (+ i 1)) #b10))",
      "((_ zero_extend (let ((|i i| 2)) |i i|)) #b10)",
      "((_ zero_extend (+ (let ((i 2)) i) 1)) #b10)",
      "((_ extract (let ((i 2)) i) 0) #b101)",
      "((_ zero_extend (let ((i 2)) (let ((i 3)) i))) #b10)",
      "(let ((i 2) (j 1)) ((_ extract i j) #b1010))",
      "(bvnot)","(bvadd #b1)","((_ extract 1) #b00)",
      "((_ zero_extend 1 2) #b0)","(bvadd #b1 #b00)",
      "(@bbterm)","(@bbterm 1)","((_ @bbterm 1) true)",
      "(forall ((x (_ BitVec))) true)"]),
     ("QF_FP",["RoundingGarbage","(forall ((x (Float16 Int))) true)",
      "(let ((e 5) (s 11)) (_ +zero e s))",
      "(_ +zero (let ((e 5)) e) 11)",
      "(_ +zero (forall ((p Bool)) p) 11)",
      "(_ +zero (let ((e 5)) e))",
      "((_ to_fp (let ((e 5)) e) 11) #x0000)",
      "((_ fp.to_ubv (let ((i 8)) i)) RTZ "^fp^")",
      "(_ +zero 1 11)","(_ NaN 5 1)","(fp.abs)",
      "((_ to_fp 5 11) #b0)","((_ to_fp_unsigned 5 11) RNE true)",
      "(fp.add true "^fp^" "^fp^")",
      "(fp.eq "^fp^" (_ +zero 8 24))",
      "(forall ((x (_ FloatingPoint 1 11))) true)"])]
  fun failure action = (ignore (action ());NONE)
    handle Feedback.HOL_ERR e => SOME
      (Feedback.top_structure_of e,Feedback.top_function_of e,
       Feedback.message_of e)
    | exn => SOME (General.exnName exn,"",General.exnMessage exn)
  fun dialect_indices () =
    let
      val registry_parsed = parsed
      fun second _ [] [_,y] = y
        | second token _ _ = SmtLib_Theories.decline token "two operands"
      (* The CPC @bvsize recipe is type-directed, not an application head. *)
      fun width _ [] [word] = intSyntax.mk_injected (numSyntax.mk_numeral
            (fcpLib.index_to_num (wordsSyntax.dim_of word)))
        | width token _ _ = SmtLib_Theories.decline token "one word"
      val extras = [("@bvsize",width),("@second",second)]
      val (sorts,dict) = SmtLib_Logics.parsedicts_of_solver_logic "cvc5" "QF_BV"
      val dict = List.foldl Library.extend_dict dict extras
      fun ordinary text = P.parse_term_with_cfg cfg (tokens text) (sorts,dict)
      fun parsed backend exact text =
        let
          val selected = if exact then
              #2 (#dictionaries (R.select_with_policy_no_override backend
                policy {logic="QF_BV",solver=SOME "cvc5"}))
            else #2 (#dictionaries (R.select backend limits
                {logic="QF_BV",solver=SOME "cvc5"}))
          val dict = List.foldl (fn ((name,parse),dict) =>
            Library.extend_dict ((name,if exact then
              R.recipe_parsefn_with_policy backend policy parse
              else R.recipe_parsefn backend limits parse),dict)) selected extras
        in if exact then P.parse_term_with_policy
             (policy_options backend (B.root backend)) (tokens text)
             (sorts,dict)
           else P.parse_term_with_backend
             (options backend (B.root backend)) (tokens text) (sorts,dict)
        end
      fun word 0 = "w"
        | word n = "(let ((w (bvadd w w))) "^word (n-1)^")"
      fun indexed 0 = "#b1"
        | indexed n = "((_ zero_extend (@bvsize "^indexed (n-1)^")) #b1)"
      val good =
        ["((_ zero_extend (@bvsize "^indexed 160^")) #b10)",
         "((_ zero_extend (@bvsize (let ((w #b10)) "^word 80^"))) #b10)",
         "((_ zero_extend (forall () (@bvsize #b10))) #b10)",
         "((_ zero_extend (@bvsize #b10)) #b10)",
         "((_ zero_extend (@bvsize (let ((w #b10)) w))) #b10)",
         "((_ zero_extend (@second (let ((i 2)) i) 2)) #b10)"]
      val bad =
        ["((_ zero_extend (let () (@bvsize #b10))) #b10)",
         "((_ zero_extend (@bvsize (let () #b10))) #b10)",
         "((_ zero_extend (let ((w #b10)) (@bvsize w))) #b10)",
         "((_ zero_extend (@second 2 (let ((i 2)) i))) #b10)"]
      val huge = "#b" ^ String.implode (List.tabulate (300,fn _ => #"1"))
      fun resource backend exact =
        let
          val direct = failure (fn () => registry_parsed backend exact "ALL"
            ("(_ divisible "^huge^")"))
          val nested = failure (fn () => registry_parsed backend exact "ALL"
            ("((_ zero_extend (_ divisible "^huge^")) #b10)"))
        in ensure "compound index swallowed admission failure"
          (direct = SOME ("SmtLib_Parser","parse_indexed_term",
             "index literal exceeds its bounded import contract") andalso
           nested = direct)
        end
      fun check backend interpret exact =
        (resource backend exact;
         List.app (fn text =>
           (print ("DIALECT "^SmtResource.bounded_text 200 text^"\n");
            bridge (ordinary text) (interpret (parsed backend exact text))))
           good;
         List.app (fn text =>
           let val expected=failure (fn () => ordinary text)
               val actual=failure (fn () => parsed backend exact text)
               fun show NONE="ACCEPTED"
                 | show (SOME (s,f,m))=s^"."^f^": "^m
               val _=print ("DIALECT_NEGATIVE "^text^"\n"^
                 show expected^"\n"^show actual^"\n")
           in ensure "dialect index classification changed"
             (expected=actual) end) bad)
      val _=tprint "Compound indices retain exact dialect callback provenance"
      val _=List.app (fn exact =>
        (with_graph (fn graph => fn backend =>
           check backend (G.representative graph) exact);
         with_values (fn _ => fn _ => fn backend =>
           check backend (small backend) exact))) [false,true]
    in OK () end

  fun identities () =
    let
      val width=Arbnum.fromInt 2
      val w=wordsSyntax.mk_word (Arbnum.one,width)
      val x=Term.mk_var ("recipe_word",Term.type_of w)
      val y=Term.mk_var ("recipe_other",Term.type_of w)
      fun bits word=List.map (fn n => wordsSyntax.mk_word_bit
        (numSyntax.mk_numeral (Arbnum.fromInt n),word)) [0,1]
      val xs=bits x val ys=bits y
      fun zip mk=ListPair.map mk (xs,ys)
      fun neg xs=List.map boolSyntax.mk_neg xs
      fun xor (a,b)=Term.list_mk_comb
        (Term.prim_mk_const {Thy="HolSmt",Name="xor"},[a,b])
      val separate=List.map (fn n => wordsSyntax.mk_word_bit
        (numSyntax.mk_numeral (Arbnum.fromInt n),
         wordsSyntax.mk_word_add (x,y))) [0,1]
      val cases=[xs,separate,neg xs,zip boolSyntax.mk_conj,
        zip boolSyntax.mk_disj,zip xor,zip boolSyntax.mk_eq,
        List.map (boolSyntax.mk_neg o boolSyntax.mk_eq)
          (ListPair.zip (xs,ys)),neg (neg (neg xs)),
        neg (neg (neg (neg xs))),List.rev xs,
        [boolSyntax.T,List.hd xs],
        [Term.mk_var ("p",Type.bool),Term.mk_var ("q",Type.bool)]]
      fun check backend interpret bs =
        let val (_,dict)= #dictionaries (R.select backend limits
              {logic="QF_BV",solver=SOME "cvc5"})
            val parse=List.hd (Redblackmap.find (dict,"@bbterm"))
            val values=List.map (B.source backend (B.root backend)) bs
            val value=parse (B.root backend) "@bbterm" [] values
        in bridge (SmtLib_Theories.mk_bbterm bs) (interpret value) end
      val _=tprint "ID-aware bbterm retains normalization and fallback syntax"
      val _=List.app (fn bs =>
        (with_graph (fn graph => fn backend =>
           check backend (G.representative graph) bs);
         with_values (fn _ => fn _ => fn backend =>
           check backend (small backend) bs))) cases
      val _=OK ()
      val _=tprint "Constructor slices do not relax atomic graph leaves"
      val _=with_values (fn graph => fn context => fn backend =>
        let val term=numSyntax.mk_numeral (Arbnum.fromInt 5)
            val value=B.source backend (B.root backend) term
            val _=B.view backend (B.root backend) value
            val node= #node (G.import graph (G.root_scope graph) 4096 term)
            val child=case G.view graph node of
                G.Application (_,x) => x | _ => raise Fail "numeral spine"
        in ensure "constructor child cache relaxed atomic leaf admission"
          (Option.isSome (failure (fn () =>
            PV.graph_leaf context (G.root_scope graph) child))) end)
      val _=OK ()
      val _=tprint "Polymorphic FP operands retain exact declared types"
      val poly_ty=Type.mk_thy_type {Thy="smtfloat",Tyop="smtfp",
        Args=[Type.mk_vartype "'m",Type.mk_vartype "'e"]}
      val poly=Term.mk_var ("polymorphic_fp",poly_ty)
      fun poly_check backend interpret =
        let val (_,dict)= #dictionaries (R.select backend limits
              {logic="QF_FP",solver=NONE})
            val value=B.source backend (B.root backend) poly
            fun check name args originals =
              let val parse=List.hd (Redblackmap.find (dict,name))
                  val original=(List.hd (Redblackmap.find
                    (SmtLib_Theories.FloatingPoint.tmdict,name)))
                      name [] originals
              in bridge original
                (interpret (parse (B.root backend) name [] args)) end
        in check "fp.abs" [value] [poly];
           check "fp.eq" [value,value] [poly,poly] end
      val _=with_graph (fn graph => fn backend =>
        poly_check backend (G.representative graph))
      val _=with_values (fn _ => fn _ => fn backend =>
        poly_check backend (small backend))
      val _=OK ()
      (* All graph routes must tolerate exponential unfolded scalar syntax.
         Only small fixtures above are interpreted as native Terms. *)
      fun growth backend logic name seed =
        let val (_,dict)= #dictionaries (R.select backend limits
              {logic=logic,solver=SOME "cvc5"})
            val parses=Redblackmap.find (dict,name)
            val frame=B.root backend
            val start=parsed backend false logic seed
            fun choose values=(List.hd parses) frame name [] values
            val rm=if name="fp.add" then
              SOME (parsed backend false logic "RNE") else NONE
            fun grow 0 value=value
              | grow n value=grow (n-1) (choose
                  (case rm of NONE => [value,value]
                   | SOME rm => [rm,value,value]))
            val result=grow 80 start
            val _=if logic<>"QF_LIA" then () else
              let val divide=List.hd (Redblackmap.find (dict,"divisible"))
                  val divided=divide frame "divisible"
                    [P.ValueIndex (result,"shared_index")] [start]
              in ensure "shared semantic index changed result type"
                (Type.compare (B.type_of backend divided,Type.bool)=EQUAL)
              end
        in ensure "shared scalar result type changed"
             (Type.compare (B.type_of backend result,
               B.type_of backend start)=EQUAL);
           result
        end
      val _=tprint "Shared80 numeric/BV/FP operands never enter term builders"
      val _=List.app (fn (logic,name,seed) =>
        (with_graph (fn graph => fn backend =>
           let val value=growth backend logic name seed
           in ensure "shared scalar graph expanded or lost raw metric"
             (G.dag_nodes graph [value]<500 andalso
              G.unfolded_nodes graph G.RawNodes 200000 value=SOME 200001)
           end);
         with_values (fn graph => fn _ => fn backend =>
           let val (_,stats)=G.with_node_statistics graph
                 (G.root_scope graph)
                 (fn () => growth backend logic name seed)
           in ensure "value scalar route expanded into native graph"
             (#node_creations stats<100) end)))
        [("QF_LIA","+","1"),("QF_BV","bvadd","#b01"),
         ("QF_FP","fp.add",fp)]
      fun nest 0 = "x"
        | nest n = "(let ((x (+ x x))) "^nest (n-1)^")"
      val text = "((_ divisible (let ((x 1)) "^nest 80^")) 3)"
      val _=List.app (fn exact =>
        (with_graph (fn graph => fn backend =>
           let val value=parsed backend exact "QF_LIA" text
           in ensure "compound semantic index was expanded"
             (G.dag_nodes graph [value]<500 andalso
              G.unfolded_nodes graph G.RawNodes 200000 value=SOME 200001)
           end);
         with_values (fn graph => fn _ => fn backend =>
           let val (_,stats)=G.with_node_statistics graph (G.root_scope graph)
                 (fn () => parsed backend exact "QF_LIA" text)
           in ensure "compound value index was realized"
             (#node_creations stats<100) end))) [false,true]
      val _=OK ()
    in () end
  fun uncapped () =
    let
      val cap=RP.Uncapped
      val contracts={template_limit=cap,index_limit=cap,
                     operand_limit=cap,token_limit=cap}
      fun check backend interpret text =
        let val selected=R.select_with_policy_no_override backend contracts
              {logic="ALL",solver=SOME "cvc5"}
            val value=P.parse_term_with_policy
              (policy_options backend (B.root backend)) (tokens text)
              (#dictionaries selected)
        in bridge (ordinary "ALL" text) (interpret value) end
      val texts=["(let ((i 3)) ((_ divisible i) 9))",
        "(@bbterm true false true)","((_ to_fp 5 11) RNE 3)"]
      val _=tprint "Uncapped graph/value recipes retain small checked results"
      val graph=G.new () val scope=G.root_scope graph
      val backend=B.graphs_with_policy {graph=graph,scope=scope,
        import_limit=cap,literal_limit=cap,binder_limit=cap}
      val _=List.app (check backend (G.representative graph)) texts
      val _=G.close_scope graph scope
      val graph=G.new () val scope=G.root_scope graph
      val context=PV.create {graph=graph,scope=scope,validate=fn () => (),
        spend=fn _ => (),retire=fn _ => ()}
      val held=B.values_with_policy {context=context,graph=graph,scope=scope,
        import_limit=cap,literal_limit=cap,binder_limit=cap}
      val _=List.app (check (#backend held) (small (#backend held))) texts
      val _=(#close held) () val _=G.close_scope graph scope
      val _=OK ()
    in () end
  fun run () =
    let
      val _=dialect_indices ()
      fun positive logic text =
        let val _=print ("SCALAR "^logic^" "^text^"\n")
            val original=ordinary logic text
            val reduced=boolSyntax.rhs (Thm.concl (Conv.QCONV
              (simpLib.SIMP_CONV pureSimps.pure_ss [boolTheory.LET_THM]
               THENC DEPTH_CONV BETA_CONV) original))
            (* Bounded binder fixtures use native graph realization; the
               value carrier's binders stay closures and are tested by31. *)
            val _=with_graph (fn graph => fn backend =>
              List.app (fn exact => bridge original
                (G.representative graph (parsed backend exact logic text)))
                [false,true])
        in if Term.is_abs reduced orelse String.isPrefix "(forall" text
          then () else with_values (fn _ => fn _ => fn backend =>
            List.app (fn exact => bridge original
              (small backend (parsed backend exact logic text))) [false,true])
        end
      fun negative logic text =
        let val expected=failure (fn () => ordinary logic text)
            val outcomes=with_graph (fn _ => fn backend =>
              List.map (fn exact => failure (fn () =>
                parsed backend exact logic text)) [false,true]) @
              with_values (fn _ => fn _ => fn backend =>
                List.map (fn exact => failure (fn () =>
                  parsed backend exact logic text)) [false,true])
            fun show NONE="ACCEPTED"
              | show (SOME (s,f,m))=s^"."^f^": "^m
            val _=print ("NEGATIVE "^text^"\n"^show expected^"\n"^
              String.concatWith "\n" (List.map show outcomes)^"\n")
        in ensure "malformed builder classification changed"
          (Option.isSome expected andalso
           List.all (fn actual => actual=expected) outcomes) end
      val _=tprint "Scalar/BV/FP selected recipes checked against term backend"
      val _=List.app (fn (logic,texts) => List.app (positive logic) texts)
        examples
      val _=OK ()
      val _=tprint "Scalar/BV/FP malformed classifications remain exact"
      val _=List.app (fn (logic,texts) => List.app (negative logic) texts)
        malformed
      val _=OK ()
      val _=tprint "Quoted lexical index roles retain legacy rejection"
      val _=symbol_key := Lib.I
      val _=negative "QF_BV"
        "(let ((|i| 2)) ((_ zero_extend |i|) #b10))"
      val _=symbol_key := P.proof_symbol_text
      val _=OK ()
      val _=identities ()
      val _=uncapped ()
    in () end
end
