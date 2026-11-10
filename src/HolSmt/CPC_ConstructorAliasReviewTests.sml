(* Standalone regression snippets; the unit-suite owner registers run. *)
structure CPC_ConstructorAliasReviewTests =
struct
  open CPC_Proof
  structure P = CPC_SharedReplayPlan
  structure C = CPC_ProofParser
  fun require message condition = if condition then () else raise Fail message
  val atom = AtomicProvenance
  fun alias body = ApplicationProvenance ("<alias>",[body])
  fun disjunction children = ApplicationProvenance ("or",children)

  (* Nodes 0 and 1 are recorded ORs; node 1 is a compound alias operand
     of node 0. Root inspection must not flatten that operand. *)
  fun recorded count node = case (count,node) of
      (2,0) => SOME [1,4]
    | (2,1) => SOME [2,3]
    | _ => NONE
  fun children (ApplicationProvenance ("or",entries)) = SOME entries
    | children _ = NONE
  fun entries node provenance = P.aggregate_entries
    {children=children,recorded=recorded,length=List.length,
     push=fn {node,provenance} => fn rest => (node,provenance)::rest,
     reverse=List.rev,
     start=fn (nodes,provenances,rest) =>
       ListPair.zip (nodes,provenances) @ rest,
     initial=fn pair => [pair],check=fn _ => (),error=Fail}
    node provenance
  fun metadata () =
    let
      val inner = disjunction [atom,atom]
      val root = disjunction [alias inner,atom]
      val _ = require "explicit OR alias lost constructor operands"
        (entries 0 (alias root) = [(1,alias inner),(4,atom)])
      val _ = require "direct nested OR stopped flattening"
        (entries 0 (disjunction [inner,atom]) =
          [(2,atom),(3,atom),(4,atom)])
      val selected = P.selected
        {children=fn provenance => case children provenance of
             SOME entries => entries | NONE => raise Fail "missing OR",
         recorded=fn _ => recorded,length=List.length,node_at=List.nth,
         provenance_at=List.nth,error=Fail}
      val result = P.not_or_elim
        {require_one=fn _ => fn [premise] => premise
             | _ => raise Fail "expected one premise",
         node= #1,negated=fn 9 => SOME 0 | _ => NONE,
         provenance= #2,selected=selected,index=fn () => 0,
         negate=fn node => ~node,current=fn node => fn p => (node,p),
         error=fn where_ => fn message => Fail (where_ ^ ": " ^ message)}
        [(9,ApplicationProvenance ("not",[alias root]))]
      val _ = require "not_or_elim lost selected alias boundary"
        (result = (~1,ApplicationProvenance ("not",[alias inner])))
      val rejected = (ignore (entries 0 atom);false) handle Fail _ => true
    in require "missing constructor metadata was invented" rejected end

  fun parse text =
    let val input = TextIO.openString text
    in Portable.finally (fn () => TextIO.closeIn input)
      (C.parse_stream_with_version
        (SmtLib_Logics.parsedicts_of_logic "ALL") "1.3.4") input end
  fun private_proof count = parse ("(" ^ String.concat
    (List.tabulate (count,fn i =>
      "(define @k" ^ Int.toString i ^ " () (@fp.SIGN (_ BitVec 1)))")) ^
    "(assume @p true))")
  fun identities () =
    let
      val first = private_proof 256
      val declarations = C.cpc_fp_private_unbound_markers ()
      val markers = List.map #1 declarations
      val second = private_proof 1
      val other = #1 (hd (C.cpc_fp_private_unbound_markers ()))
      fun scope proof action = C.with_cpc_fp_private_proof proof action ()
      fun lookup marker =
        let val spent = ref 0
            val found = C.is_cpc_fp_private_marker_observed
              (fn () => spent := !spent+1) marker
            val name_bytes = String.size (#1 (Term.dest_var marker))
        in require "identity lookup was not paid/logarithmic"
          (found andalso !spent > 1 andalso
           !spent <= 40 * (name_bytes+2)) end
      val _ = scope first (fn () =>
        let
          val _ = List.app lookup markers
          val marker = hd markers
          val (name,ty) = Term.dest_var marker
          val copy = Term.mk_var
            (String.implode (String.explode name),ty)
          val bytes = ref 0
          val _ = require "copied typed identity was lost"
            (C.is_cpc_fp_private_marker_observed
              (fn () => bytes := !bytes+1) copy)
          val _ = require "identity name bytes were not paid"
            (!bytes >= String.size name)
          val namesake = Term.mk_var (name,Type.bool)
          val _ = require "typed namesake acquired private authority"
            (not (C.is_cpc_fp_private_marker namesake))
          val _ = require "another proof's marker acquired authority"
            (not (C.is_cpc_fp_private_marker other))
          val _ = scope second (fn () =>
            require "nested proof identity scope leaked"
              (C.is_cpc_fp_private_marker other andalso
               not (C.is_cpc_fp_private_marker marker)))
        in require "outer proof identity scope was not restored"
          (C.is_cpc_fp_private_marker marker) end)
    in require "ambient proof identity scope was not restored"
      (C.is_cpc_fp_private_marker other andalso
       not (C.is_cpc_fp_private_marker (hd markers))) end

  (* Full parser/replay fixtures for an existing CPC Boolean harness. *)
  val fixtures =
    [("cnf_or_pos reference",
      "((define @o () (or true false)) " ^
      "(step @p :rule cnf_or_pos :args (@o)))"),
     ("cnf_or_neg reference",
      "((define @o () (or true false)) " ^
      "(step @p :rule cnf_or_neg :args (@o 0)))"),
     ("not_or_elim reference",
      "((define @o () (or (not false) true)) " ^
      "(assume @a (not @o)) " ^
      "(step @p (not (not false)) :rule not_or_elim " ^
      ":premises (@a) :args (0)) " ^
      "(step @done false :rule not_not_elim :premises (@p)))")]

  fun run () =
    (testutils.tprint "CPC explicit OR constructor alias metadata";
     metadata ();testutils.OK ();
     testutils.tprint "CPC proof-local paid private identity index";
     identities ();testutils.OK ())
end
