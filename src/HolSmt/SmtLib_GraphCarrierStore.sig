(* Persistent symbols, declaration metadata and lexical output DATA. *)
signature SmtLib_GraphCarrierStore =
sig
  type carrier = SmtLib_GraphQueryAnalysis.carrier
  type bounds
  type terms
  type key
  type region
  datatype origin =
      Ordinary of carrier
    | Fallback of {dependencies:carrier list,expression:carrier}
  type symbol =
    {name:string,arity:int,syntax:carrier,origin:origin,
     graph_node:SmtLib_GraphQueryAnalysis.scoped_node option,
     sorts:(string list * string) option}
  type encoding =
    {input:carrier,head:carrier,atomic_head:Term.term option,
     smt_symbol:string,arity:int}
  type interface =
    {operations:(carrier,bounds,terms,key)
       SmtLib.outbound_term_store_operations,
     empty_bounds:bounds,empty_terms:terms,
     region:int * bounds -> region,
     region_at:int * (int * int) list * bounds -> region,
     find_document:terms * region * carrier ->
       SmtLib_OutputFragments.doc option,
     bind_document:terms * region * carrier * SmtLib_OutputFragments.doc ->
       terms * SmtLib_OutputFragments.doc,
     wrap_document:terms * region * SmtLib_OutputFragments.doc ->
       SmtLib_OutputFragments.doc,
     symbols:terms -> symbol list,encodings:terms -> encoding list}

  (* One live borrow and fixed query backend per instance. Prefix must be a
     fresh valid SMT identifier prefix. Symbols, sort records, document
     memo, definitions and counters travel in the SAME immutable terms
     value, so dispatcher rollback discards all their speculative changes.
     Symbol naming counts only symbols. Cache keys reuse Q's typed alpha
     analysis; they confer no equality, Source or parser authority.

     encodings returns successful builtin observations in committed operand
     postorder, including synthesized operands. It is not the legacy native
     metadata scan of all input subterms. Each event keeps the original
     encoder input (which can be a whole literal), its stripped head, the
     original HOL argument count and any genuine atomic head metadata.
     Events share the persistent accumulator's speculative rollback. Like
     symbols, their carriers must be exported/frozen DURING the borrow;
     atomic_head alone never grants emission or proof authority.

     Bound variable dependency order uses Term.compare on variable LEAVES,
     with exact semantic IDs breaking spelling ties. Nonvariable LET
     patterns follow variables; they cannot occur in the FV dependency
     subset. Lookup preserves exact typed alpha identity. The caller must
     transport function-LET parameter instantiations before expecting a
     composite pattern to bind a distinct source argument; this store does
     not identify free and Bound variables by their spelling.

     Root occurrence numbers distinguish assertions. Region environments
     retain every ordered bound ID/name pair. region_at additionally takes
     the lexical entry path of enclosing carrier keys, innermost first;
     repeated bindings can have identical environments at distinct entries.
     region is region_at with an empty path. Close each binder/LET body
     region at its lexical boundary; LET RHS uses the incoming region.
     Export symbols while the borrow is live. A retained graph_node is
     metadata only and still requires the parser's normal authentication
     and checked definition/original-source transport. *)
  val create : SmtLib_GraphQueryAnalysis.outbound_context ->
    {prefix:string} -> interface
end
