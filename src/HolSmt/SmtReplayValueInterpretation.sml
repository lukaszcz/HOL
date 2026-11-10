(* Typed cell syntax/constructor worker only; no native/proof admission. *)
structure SmtReplayValueInterpretation :> SmtReplayValueInterpretation =
struct
  structure G=SmtReplayGraph
  datatype cell_body = Borrowed of G.node | Atomic of Term.term
    | Application of (int * int) * (int * int)
  type cell =
    {key:int * int,name:Term.term,hol_type:Type.hol_type,body:cell_body}
  fun interpret valid tick graph scope typed same_type terms error cells
      replacements =
    let
         fun interpret [] replacements=(valid ();replacements)
           | interpret ((row:cell)::rest) replacements=
               let
                 val _=tick ()
                 val (actual,actual_type)=case #body row of
                     Borrowed node=>
                       (ignore (G.closure_root graph scope node);
                        (G.representative graph node,G.type_of graph node))
                   | Atomic value=>
                       if Term.is_var value orelse Term.is_const value then
                         (value,Term.type_of value)
                       else raise error "execute" "non-atomic leaf plan"
                   | Application(left,right)=>
                       let val (f,fty)=typed left val (x,xty)=typed right
                           val (domain,range)=Type.dom_rng fty
                           val _=if same_type domain xty andalso
                               same_type range (#hol_type row) then () else
                             raise error "execute" "typed App plan changed"
                           val _=tick ()
                           val result=Term.mk_comb (f,x)
                           val _=valid ()
                       in (result,range) end
                 val _=if same_type actual_type (#hol_type row)
                     then () else raise error "execute" "Value Type changed"
                 val _=tick ()
                 val _=terms:=Redblackmap.insert
                   (!terms,#key row,(actual,actual_type))
                 val _=tick ()
               in interpret rest
                 ({redex= #name row,residue=actual}::replacements) end
    in interpret cells replacements end
end
