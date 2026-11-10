(* Registry and command/argument checks are shared; plans are syntax DATA. *)
structure Z3_SharedReplayPlan :> Z3_SharedReplayPlan =
struct
  structure Z = Z3_GraphProofParser
  structure Registry = Z3_Proof
  datatype resolution_mode=RecordedResolution|LegacyRawResolution
  datatype ('node,'syntax) plan=Original of 'node
    | OriginalSlot of int * 'node
    | Alias of Z.proof_id
    | Equality of string * 'node * Z.proof_id list
    | Boolean of 'node * Z.proof_id list
    | Resolution of 'node * Z.proof_id list *
        'syntax SmtLib_GraphFrontend.constructed_term
    | RawResolution of 'node * Z.proof_id list *
        'syntax SmtLib_GraphFrontend.constructed_term
    | ScopedEquality of 'node * Z.proof_id
    | Quantified of
        {source:'node,instance:'node,target:'node,arguments:'node list}
  type observer =
    {registry:Z3_Proof.registry_observer,
     rule_comparison:Z3_Proof.proof_rule * Z3_Proof.proof_rule -> unit,
     normalization_character:unit -> unit,
     premises:Z3_GraphProofParser.proof_id list -> unit,
     argument_copy:unit -> unit,kept_item:unit -> unit,
     copied_roots:unit -> unit}
  type ('node,'syntax) operations =
    {observer:observer,prior:Z.proof_id -> 'node,
     located:'syntax SmtLib_GraphFrontend.constructed_term -> 'node,
     processed:'node -> bool,original_slot:'node -> int,
     operands:Term.term -> int -> 'node -> 'node list option,
     keep:'node -> unit,error:string -> string -> exn}
  val silent_observer:observer =
    {registry=Z3_Proof.silent_registry_observer,
     rule_comparison=fn _=>(),normalization_character=fn()=>(),
     premises=fn _=>(),argument_copy=fn()=>(),kept_item=fn()=>(),
     copied_roots=fn()=>()}
  fun normalize (observer:observer) text=String.translate
    (fn character=>
      (#normalization_character observer ();
       if character= #"_" then "-" else String.str character)) text
  fun canonical (observer:observer) error version
      (rule:Registry.proof_rule) =
    case Registry.lookup_rule_observed (#registry observer)
        version (#name rule) of
      SOME held=>
        (#rule_comparison observer (held,rule);
         if held=rule then normalize observer (#replay_handler held) else
           raise error "packet" "proof rule differs from actual registry")
    | NONE=>raise error "packet" "proof rule is outside actual version"
  val canonical_name=canonical
  fun classify_using bindings
      (operations:('node,'syntax) operations) {version,mode} command =
    case command of Z.Alias other=>
                  ((#prior operations) other,Alias other)
              | Z.Bind _=>raise (#error operations) "packet"
                "unexpected proof-bind"
              | Z.Rule{rule,conclusion,premises,arguments,metadata,...}=>
                let val target=(#located operations) conclusion
                    val name=canonical (#observer operations)
                      (#error operations) version rule
                    val _= #premises (#observer operations) premises
                    val n=List.length premises
                    val _=case #premise_shape rule of
                        Registry.ZeroPremises=>if n=0 then ()else
                          raise (#error operations) "packet"
                            "zero-premise arity differs"
                      | Registry.OnePremise=>if n=1 then ()else
                          raise (#error operations) "packet"
                            "one-premise arity differs"
                      | Registry.TwoPremises=>if n=2 then ()else
                          raise (#error operations) "packet"
                            "two-premise arity differs"
                      | Registry.ListPremises=>()
                      | Registry.TermArguments=>if name="quant-inst"
                          andalso n=0 then ()else raise (#error operations)
                            "packet"
                            "indexed native argument programme pending"
                      | _=>raise (#error operations) "packet"
                          "native argument programme pending"
                    val _=if (name="quant-inst" orelse null arguments)
                        andalso not(Option.isSome metadata)
                      then ()else raise (#error operations) "packet"
                        "actual native/theory arguments need owned programme"
                    fun quantified()=
                          let
                            val(left,instance)=case (#operands operations)
                                boolSyntax.disjunction 2 target of
                                SOME[a,b]=>(a,b)
                              | _=>raise (#error operations) "quant-inst"
                                  "actual conclusion is not binary OR"
                            val source=case (#operands operations)
                                boolSyntax.negation 1 left of
                                SOME[a]=>a
                              | _=>raise (#error operations) "quant-inst"
                                  "actual first disjunct is not a negation"
                            val _=case (#operands operations)
                                boolSyntax.universal 1 source of
                                SOME[_]=>()
                              | _=>raise (#error operations) "quant-inst"
                                  "actual negated source is not universal"
                            val actual=List.map (fn value=>
                              (#argument_copy (#observer operations) ();
                               (#located operations) value)) arguments
                            val _=if null actual then raise (#error
                              operations) "quant-inst"
                                "no actual indexed specialization arguments"
                              else ()
                            val _= #copied_roots (#observer operations) ()
                            val _=List.app (fn value=>
                              (#kept_item (#observer operations) ();
                               (#keep operations) value))
                              (source::instance::actual)
                          in Quantified{source=source,instance=instance,
                            target=target,arguments=actual}end
                        val programme=case name of
                            "quant-intro"=>if bindings then
                              (case premises of [bound]=>
                                 (#copied_roots(#observer operations) ();
                                  ScopedEquality(target,bound))
                               | _=>raise (#error operations) "quant_intro"
                                   "expected one immediate proof-bind")
                            else raise (#error operations) "packet"
                              "actual rule programme has not been migrated"
                          | "quant-inst"=>quantified()
                          | "asserted"=>if (#processed operations) target
                            then Original target else
                          raise (#error operations) "packet"
                            "assertion outside processed Source prefix"
                      | "hypothesis"=>if (#processed operations) target
                        then Original target else
                          OriginalSlot ((#original_slot operations)
                            target,target)
                      | "refl"=>Equality("refl",target,premises)
                      | "symm"=>Equality("symm",target,premises)
                      | "trans"=>Equality("trans",target,premises)
                      | "trans-star"=>Equality("trans-star",target,premises)
                      | "monotonicity"=>Equality("cong",target,premises)
                      | "and-elim"=>Boolean(target,premises)
                      | "iff-false"=>Boolean(target,premises)
                      | "iff-true"=>Boolean(target,premises)
                      | "unit-resolution"=>
                          if null premises then raise (#error operations)
                            "unit-resolution"
                            "empty actual ordered premises"else
                            (case mode of RecordedResolution=>
                               Resolution(target,premises,conclusion)
                             | LegacyRawResolution=>
                               RawResolution(target,premises,conclusion))
                      | "mp"=>Boolean(target,premises)
                      | "mp-eq"=>Boolean(target,premises)
                      | "not-or-elim"=>Boolean(target,premises)
                      | "true-axiom"=>Boolean(target,premises)
                      | "def-axiom"=>Boolean(target,premises)
                      | "commutativity"=>Boolean(target,premises)
                      | "rewrite"=>Boolean(target,premises)
                      | _=>raise (#error operations) "packet"
                          "actual rule programme has not been migrated"
                in(target,programme)end
  fun classify operations options command=
    classify_using false operations options command
  fun classify_with_bindings operations options command=
    classify_using true operations options command
end
