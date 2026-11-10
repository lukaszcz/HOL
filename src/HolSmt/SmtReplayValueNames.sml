(* Actual hygienic native atom names only; no Source/proof admission. *)
structure SmtReplayValueNames :> SmtReplayValueNames =
struct
  structure PV=SmtLib_GraphParserValue
  structure N=SmtReplayNamedContext
  type value=PV.value
  type syntax=PV.proof_term
  type ('a,'b) mapper=('a -> 'b) -> 'a list -> 'b list
  fun allocate guard step spend context key
      (native:SmtReplayNativeContract.limits) check_type error
      append_values append_terms copy_values copy_schemas
      all_formals roots source_values reachable =
    let
      fun pay amount=(guard ();spend amount)
      fun compare_int (a,b)=(pay 1;Int.compare (a,b))
      val names=ref (Redblackmap.mkDict compare_int)
      fun compare_name (left,right)=
        (pay (1+IntInf.fromInt (String.size left)+
          IntInf.fromInt (String.size right));
         String.compare (left,right))
      val forbidden=ref (Redblackset.empty compare_name)
      fun forbid term=
        let val _=step ()
            val (spelling,_)=Term.dest_var term
            val _=pay (1+IntInf.fromInt (String.size spelling))
        in forbidden:=Redblackset.add (!forbidden,spelling) end
      (* Free-ID metadata is already admitted by the real Value
         factory. In particular this covers free variables retained
         behind unopened original graph syntax, without traversing a
         native operand. Traverse authentic opened binder views only
         to retain their local atomic spellings as well. *)
      fun free_names []=()
        | free_names (value::rest)=
            let val _=step ()
                val variables=PV.free_variables context value
                fun add []=()
                  | add (variable::tail)=
                      (step ();case PV.view context variable of
                          PV.Variable (_,atom)=>(forbid atom;add tail)
                        | _=>raise error "prepare"
                            "nonvariable free-ID metadata")
                val _=add variables
            in free_names rest end
      val _=free_names (append_values all_formals roots)
      val hygiene_seen=ref (Redblackset.empty compare_int)
      fun hygienic []=()
        | hygienic (current::rest)=
            let val _=step () val id=key current
            in if Redblackset.member (!hygiene_seen,id) then
                hygienic rest
              else
                let val _=hygiene_seen:=Redblackset.add
                      (!hygiene_seen,id)
                in case PV.proof_view context current of
                    PV.ProofVariable (_,atom)=>
                      (forbid atom;hygienic rest)
                  | PV.ProofApplication (left,right)=>
                      hygienic (left::right::rest)
                  | PV.ProofAbstraction {binder,body,...}=>
                      hygienic (binder::body::rest)
                  | _=>hygienic rest
                end
            end
      val _=hygienic
        (append_terms source_values
            (copy_values (PV.proof_term context) roots))
      (* These are bounded declaration schemas, not query operands.
         Their local/free names are kept out of the compact namespace.
         Any later binder realization must extend this inventory with
         its own actual schema before mixing expanded semantic terms. *)
      fun schema_names []=()
        | schema_names (current::rest)=
            (step ();if Term.is_var current then
                (forbid current;schema_names rest)
              else if Term.is_comb current then
                let val (left,right)=Term.dest_comb current
                in schema_names (left::right::rest) end
              else if Term.is_abs current then
                let val (binder,body)=Term.dest_abs current
                in forbid binder;schema_names (body::rest) end
              else schema_names rest)
      val _=schema_names (copy_schemas Thm.concl
        [satTheory.dc_neg,satTheory.dc_conj,satTheory.dc_disj,
         satTheory.dc_imp,satTheory.dc_eq,satTheory.dc_cond,
         SmtCircuitSat.true_cnf,SmtCircuitSat.false_cnf,
         SmtCircuitSat.atom_cnf,boolTheory.TRUTH])
      val next_name=ref (0:IntInf.int)
      fun fresh ty=
        let val _=step () val serial= !next_name
            val _=next_name:=serial+1
            val digits=IntInf.toString serial
            val _=pay (1+IntInf.fromInt (String.size digits))
            val spelling="__holsmt_value_proof_" ^ digits
            val _=pay (1+IntInf.fromInt (String.size spelling))
        in if Redblackset.member (!forbidden,spelling) then fresh ty
          else
            (forbidden:=Redblackset.add (!forbidden,spelling);
             Term.mk_var (spelling,ty))
        end
      fun allocate value=
        let val _=step () val ty=PV.proof_type_of context value
            val _=ignore (N.type_weight_using pay (error "native")
              (IntInf.fromInt (#type_work_limit native)) ty)
            val _=check_type ty val _=guard ()
            val name=fresh ty
            val _=pay 1
        in names:=Redblackmap.insert (!names,key value,name) end
      val _=List.app allocate reachable
    in fn value=>Redblackmap.find(!names,key value)end
end
