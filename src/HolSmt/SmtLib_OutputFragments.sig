(* Immutable output fragments for the shared outbound dispatcher. *)
signature SmtLib_OutputFragments =
sig
  type doc

  val text : string -> doc
  val concat : doc list -> doc
  val join : string -> doc list -> doc

  (* Structured references are distinct from opaque text. Free reference
     sets are cached immutably; text is never reparsed for identifiers.
     A let's value uses the incoming environment, while its name binds only
     in its body. References remaining free may belong to a parent region. *)
  val reference : string -> doc
  val mentions_reference : doc * string -> bool
  val let_binding : string * doc * doc -> doc

  (* Render the concatenated bytes to a sink, in order. Chunk boundaries
     are unspecified. Sink exceptions propagate unchanged. The traversal
     uses an explicit stack, including for deeply nested concatenations;
     it does not construct intermediate concatenated strings.

     Documents are immutable and may share child documents. Each occurrence
     is rendered: choosing lexical lets to bound the final output belongs
     to the query scheduler, not this byte-preserving fragment algebra.
     There is no global allocation counter, cache, or mutable state. *)
  val render : (string -> unit) -> doc -> unit
end
