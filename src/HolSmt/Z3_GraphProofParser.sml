(* Copyright (c) 2026 The HOL4 contributors. *)
structure Z3_GraphProofParser =
struct
  open Z3_Proof SmtLib_GraphFrontend SmtLib_Parser SmtReplayGraph
    SmtLib_GraphProof SmtLib_GraphTranslation
  structure F = SmtLib_GraphFrontend
  structure P = SmtLib_Parser
  structure G = SmtReplayGraph
  val ERR = Feedback.mk_HOL_ERR "Z3_GraphProofParser"

  datatype proof_id = Named of int | Anonymous of int
  datatype 'a constructed_value = ProofId of proof_id
    | ProofLambda of proof_id
    | Term of 'a F.constructed_term
  type value = G.node constructed_value
  datatype 'a constructed_step = Rule of
    {rule : proof_rule, premises : proof_id list,
     conclusion : 'a F.constructed_term,
     arguments : 'a F.constructed_term list,
     metadata : th_lemma_metadata option, accepts_bind : bool}
    | Alias of proof_id
    | Bind of {binding : 'a F.constructed_scoped_session, body : proof_id,
               lambda_blocks : int list}
  type step = G.node constructed_step
  type 'a constructed_proof =
    {steps : (proof_id, 'a constructed_step) Redblackmap.dict,
     root : proof_id,vars : 'a list,z3_version : string,close : unit -> unit}
  type proof = G.node constructed_proof
  datatype syntax = Atom of string | List of syntax list

  fun compare_id (Named left, Named right) = Int.compare (left, right)
    | compare_id (Anonymous left, Anonymous right) = Int.compare (left, right)
    | compare_id (Named _, Anonymous _) = LESS
    | compare_id (Anonymous _, Named _) = GREATER
  fun read tokens = case tokens () of
      "(" =>
        let fun entries acc = case tokens () of
              ")" => List (List.rev acc)
            | token => entries
                (read (Library.undo_look_ahead [token] tokens) :: acc)
        in entries [] end
    | ")" => raise ERR "read" "unexpected closing delimiter"
    | token => Atom token
  fun token_list (Atom token) = [token]
    | token_list (List entries) =
        "(" :: List.concat (List.map token_list entries) @ [")"]
  fun buffered raw action =
    let val pending = ref (token_list raw)
        fun next () = case !pending of
            token :: rest => (pending := rest; token)
          | [] => raise ERR "buffered" "incomplete expression"
        val result = action next
        val _ = if null (!pending) then () else
          raise ERR "buffered" "trailing expression syntax"
    in result end
  fun atom context (Atom token) = P.proof_symbol_text token
    | atom context _ = raise ERR context "expected an atomic symbol"
  fun list context (List entries) = entries
    | list context _ = raise ERR context "expected parenthesized entries"
  fun shadow_name aliases name =
    if Redblackmap.inDomain (aliases, name) then
      #1 (Redblackmap.remove (aliases, name))
    else aliases
  (* Binder names shadow both retained term syntax and proof aliases.
     Use descriptor text, just as alias lookup does, including quoted names. *)
  fun shadow_aliases aliases binders =
    List.foldl (fn ((_, name, _), aliases) =>
      shadow_name aliases name) aliases binders
  fun alias_value aliases name =
    Redblackmap.peek (aliases, P.proof_symbol_text name)
  fun named_id text =
    if String.isPrefix "@x" text then
      case Int.fromString (String.extract (text, 2, NONE)) of
        SOME number => if number > 0 then Named number else
          raise ERR "proof_id" "integer less than 1 found"
      | NONE => raise ERR "proof_id" "'@x' not followed by an integer"
    else raise ERR "proof_id" "'@x' prefix expected"

  (* Metadata stays lexical data. Numeric index normalization is bounded by
     the input token; it never walks an actual graph term representative. *)
  fun index_text raw =
    let val text = atom "rule_index" raw
        val n = String.size text
        fun digits limit index = index >= limit orelse
          (Char.isDigit (String.sub (text, index)) andalso
           digits limit (index + 1))
        val integer_suffix = n > 1 andalso String.sub (text, n-1) = #"i"
          andalso (digits (n-1) 0 orelse
            (n > 2 andalso
             (String.sub (text, 0) = #"-" orelse
              String.sub (text, 0) = #"~") andalso digits (n-1) 1))
    in if integer_suffix then String.substring (text, 0, n-1) else text end

  fun let_entry (List [Atom name, rhs]) =
        if Option.isSome (P.proof_string_token name) then
          raise ERR "parse" "string literal used as a let binding name"
        else (name, rhs)
    | let_entry _ = raise ERR "parse" "malformed let binding"

  type 'a policy_observations =
    {type_of:'a -> Type.hol_type,same_identity:'a * 'a -> bool,
     guard_alias_scope:G.scope * 'a -> unit,
     alias_entry:G.scope * 'a -> {key:int,visible:unit -> bool}}

  fun graph_observations graph : G.node policy_observations =
    {type_of=G.type_of graph,same_identity=op=,
     guard_alias_scope=fn (active,_) => G.validate_scope graph active,
     alias_entry=fn (active,node) =>
       let val declared = G.node_scope graph node
           val _ = G.validate_scope graph declared
           val id = G.node_id node
       in {key=id,visible=fn () =>
         G.scope_visible graph active declared} end}

  fun policy_description version =
    {solver = "Z3", version = version, policy = F.Z3,
     reserved_names = List.map #1
       (Z3_ProofConstructors.entries @ Z3_ProofFpConstructors.entries)}

  fun configure_terms (terms : 'a F.constructed_session) fp word =
    (List.app (#add_recipe_parser terms)
       (("=", Z3_ProofConstructors.equality) :: Z3_ProofConstructors.entries);
     List.app (#add_recipe_parser terms) fp;
     (#add_literal_parser terms) Z3_ProofLiterals.numeric;
     (#add_literal_parser terms) word;
     terms)

  (* One grammar serves finite, policy and Value sessions. Constructor and
     literal registration remain entry-point-specific, including finite FP
     bounds. Observations and packet ownership belong to the actual carrier;
     this programme grants no Source or inference authority. *)
  fun create_using_session (observations:'a policy_observations) publish
      requested_version make_token check_complete make_terms =
    let
      val version = resolve_version requested_version
      val tokenizer = make_token ()
      val terms : 'a F.constructed_session = make_terms version tokenizer
      val steps = ref
        (Redblackmap.mkDict compare_id :
          (proof_id, 'a constructed_step) Redblackmap.dict)
      val counter = ref 0
      val variables = ref ([] : 'a list)
      val closures = ref ([] : (unit -> unit) list)
      fun close () =
        let
          val saved = !closures
          (* Detach before callbacks: repeated/reentrant close cannot run a
             closure twice. One failed child must not strand its siblings
             or parents; explicit close still reports the FIRST failure. *)
          val _ = closures := []
          fun drain [] primary =
                (case primary of NONE => () | SOME error => raise error)
            | drain (action::rest) primary =
                (case Exn.capture action () of
                   Exn.Res () => drain rest primary
                 | Exn.Exn error => drain rest
                     (case primary of NONE => SOME error | _ => primary))
        in drain saved NONE end
      fun error message = raise ERR "parse" message
      fun term session aliases raw =
        buffered raw (#parse_from (session : 'a F.constructed_session))
      fun sort session raw = buffered raw
        (#parse_sort (session : 'a F.constructed_session))
      fun proof (ProofId id) = id
        | proof (ProofLambda _) =
            error "a proof lambda requires proof-bind"
        | proof (Term _) = error "a graph term cannot be a proof premise"
      fun boolean (Term value) =
            if Type.compare ((#type_of observations) (#node value),
                Type.bool) = EQUAL then value else
              error "proof conclusion must have Boolean type"
        | boolean (ProofId _) = error
            "LegacyDecimal proof reference used as a term conclusion"
        | boolean (ProofLambda _) = error
            "proof lambda used as a term conclusion"
      fun save value =
        let val _ = counter := !counter + 1
            val id = Anonymous (!counter)
        in steps := Redblackmap.insert (!steps, id, value); id end
      fun key (session : 'a F.constructed_session) token =
        (#symbol_key session) token
      fun descriptors session raw =
        List.map (fn entry => case entry of
            List [Atom name, ty] =>
              if Option.isSome (P.proof_string_token name) then
                error "string literal used as bound-variable name"
              else (key session name, P.proof_symbol_text name,
                    sort session ty)
          | _ => error "malformed sorted variable")
          (list "lambda_binders" raw)
      fun scope session binders =
        let
          val binding as F.ScopedSession {close = end_scope, ...} =
            (#open_binders (session : 'a F.constructed_session)) binders
          val _ = closures := end_scope :: !closures
        in binding end
      fun binding_session (F.ScopedSession {session, ...}) = session
      (* Classify only the result spine before opening a proof LET/lambda.
         Ordinary term LETs/lambdas go to the frontend: no speculative
         graph construction, binder opening or extra admission is needed.
         This is syntax routing, never a semantic equality decision. It must
         be total even on malformed syntax: normal left-to-right parsing,
         not this lookahead, owns every diagnostic. *)
      fun proof_result aliases raw =
        let
          fun kind local_names (Atom name) =
                (case Redblackmap.peek
                    (local_names, P.proof_symbol_text name) of
                   SOME result => result
                 | NONE => case alias_value aliases name of
                     SOME (ProofId _) => true
                   | SOME (ProofLambda _) => true
                   | _ => false)
            | kind local_names (List [Atom "let", bindings, body]) =
                let val values = List.map (fn (name, rhs) =>
                      (P.proof_symbol_text name, kind local_names rhs))
                      (case bindings of List entries => List.mapPartial
                        (fn List [Atom name, rhs] => SOME (name, rhs)
                          | _ => NONE) entries | _ => [])
                in kind (List.foldl (fn ((name, value), names) =>
                  Redblackmap.insert (names, name, value))
                  local_names values) body end
            | kind local_names (List (Atom "!" :: body :: _)) =
                kind local_names body
            | kind local_names (List [Atom "lambda", binders, body]) =
                let fun shadow (List [Atom name, _], names) =
                          Redblackmap.insert
                            (names, P.proof_symbol_text name, false)
                      | shadow (_, names) = names
                in kind (List.foldl shadow local_names
                  (case binders of List entries => entries | _ => []))
                  body end
            | kind local_names (List (head :: _)) =
                let val name = case head of Atom name => name
                      | List (Atom "_" :: Atom name :: _) => name
                      | _ => ""
                in name = "th-lemma" orelse Option.isSome
                  (lookup_rule version (P.proof_symbol_text name)) end
            | kind _ _ = false
        in kind (Redblackmap.mkDict String.compare) raw end
      fun parse_value session aliases raw =
        case raw of
          Atom name => (case alias_value aliases name of
              SOME (value as ProofId _) => value
            | SOME (value as ProofLambda _) => value
            | SOME (Term retained) =>
                let
                  (* Reparse through the actual current lexical dictionary.
                     Only that exact owned alias may retain its RHS syntax. *)
                  val actual = term session aliases raw
                  val active = #scope actual
                  val _ = (#guard_alias_scope observations)
                    (active,#node actual)
                  val _ = if (#same_identity observations)
                      (#node actual,#node retained) then () else
                    error "recorded term alias changed its owned node"
                  val seen = ref (Redblackset.empty Int.compare)
                  fun validate node =
                    let
                      val {key=id,visible} =
                        (#alias_entry observations) (active,node)
                    in if Redblackset.member (!seen,id) then () else
                      let val _ = if visible () then () else
                            error "recorded alias child escapes scope"
                      in seen := Redblackset.add (!seen,id) end
                    end
                  (* Lookup checks the actual frame and exact alias node.
                     Inspect only syntax used by clause_occurrences/literal;
                     unused let RHSs and binder interiors stay boundaries. *)
                  fun literal (P.ConstructionOccurrence
                      {value,role,token,children,...}) =
                    (validate value;
                     case (role,token,children) of
                       (P.ConstructionApplication,"not",[child]) =>
                         validate (P.construction_value child)
                     | (P.ConstructionApplication,"~",[child]) =>
                         validate (P.construction_value child)
                     | _ => ())
                  fun clause (entry as P.ConstructionOccurrence
                      {value,role,token,children,...}) =
                    (validate value;
                     case role of P.ConstructionLet _ =>
                       (case List.rev children of body :: _ => clause body
                        | [] => literal entry)
                     | P.ConstructionAnnotation =>
                       (case children of [body] => clause body
                        | _ => literal entry)
                     | P.ConstructionApplication =>
                       if token = "or" then List.app literal children
                       else literal entry
                     | _ => literal entry)
                  val _ = clause (#occurrence retained)
                in Term {node = #node actual,scope = #scope actual,
                  binder_blocks = #binder_blocks actual, source_syntax = NONE,
                  occurrence = #occurrence retained} end
            | NONE => Term (term session aliases raw))
        | List [Atom "let", bindings, body] =>
            (* A term LET substitutes values, not operand occurrences. Its
               lexical uses must stay atomic, even for an OR-valued RHS.
               Only a proof LET retains RHS occurrences in the proof alias
               table; in particular its asserted OR keeps its recorded
               boundary. Route before construction, never reparse values. *)
            if proof_result aliases raw then
              parse_let session aliases bindings body
            else Term (term session aliases raw)
        | List (Atom "!" :: body :: _) =>
            (* Attributes are inert S-expressions, including proof names.
               Preserve the body's value kind; term occurrences still keep
               the annotation boundary used by clause/literal consumers. *)
            (case parse_value session aliases body of
               Term value => Term
                 {node = #node value, scope = #scope value,
                  binder_blocks = #binder_blocks value, source_syntax = NONE,
                  occurrence = P.ConstructionOccurrence
                    {value = #node value, role = P.ConstructionAnnotation,
                     token = "!", children = [#occurrence value]}}
             | value => value)
        | List [Atom "lambda", _, _] =>
            if proof_result aliases raw then parse_lambda session aliases raw
            else Term (term session aliases raw)
        | List (head :: operands) =>
            let val (name, indices) = case head of
                  Atom name => (P.proof_symbol_text name, [])
                | List (Atom "_" :: Atom name :: indices) =>
                    (P.proof_symbol_text name, indices)
                | _ => ("", [])
            in if name = "proof-bind" then
                (case operands of [body] => parse_bind session aliases body
                 | _ => error "proof-bind expects one operand")
              else if name = "th-lemma" then
                parse_lemma session aliases indices operands
              else case lookup_rule version name of
                  SOME rule =>
                    parse_rule session aliases rule NONE indices operands
                | NONE =>
                    if Option.isSome (List.find (rule_matches name)
                        proof_rule_registry) then
                      error (registry_lookup_failure version name)
                    else Term (term session aliases raw)
            end
        | List [] => error "empty proof or term expression"
      and parse_outer session aliases raw = case raw of
          List [Atom "let", bindings, body] =>
            if List.length (list "outer_let" bindings) = 1 then
              parse_let_using true parse_outer session aliases bindings body
            else error "outer Z3 proof let expects one definition"
        | _ => parse_value session aliases raw
      and parse_let session aliases bindings body =
        parse_let_using false parse_value session aliases bindings body
      and parse_let_using unique parse_body session aliases bindings body =
        let
          val entries = list "let_bindings" bindings
          val _ = if null entries then error "empty let binding list" else ()
          (* RHSs all see the incoming environment, but validation remains
             left-to-right: a later bad name cannot replace an earlier RHS
             exception. Unused RHSs are still parsed and typechecked. *)
          val values = List.map (fn entry =>
            let val (name, rhs) = let_entry entry
            in (name, parse_value session aliases rhs) end) entries
          val term_values = List.mapPartial (fn (name, value) =>
            case value of Term value => SOME (name, value) | _ => NONE) values
          val blocked = List.mapPartial (fn (name, value) =>
            case value of Term _ => NONE | _ => SOME name) values
          val F.ScopedSession {session = child, close, ...} =
            (#open_mixed_bindings (session : 'a F.constructed_session))
              term_values blocked
          val _ = closures := close :: !closures
          fun install ((name, value), (aliases, names)) =
            let
              val name_text = P.proof_symbol_text name
              val _ = if HOLset.member (names, name_text) then
                error "duplicate simultaneous let variable" else ()
              val _ = if unique andalso
                  (Redblackmap.inDomain (aliases, name_text) orelse
                   HOLset.member (#source_terms ((#namespace session) ()),
                     key session name) orelse
                   HOLset.member (#reserved ((#namespace session) ()),
                     key session name)) then
                error ("duplicate proof/term definition " ^ name_text)
                else ()
              (* Only outer definitions allocate global Named IDs. Local
                 @x names are ordinary lexical aliases, of either kind. *)
              val named = unique andalso String.isPrefix "@x" name_text
              fun name_proof wrap id = if named then
                  let val target = named_id name_text in
                    if Redblackmap.inDomain (!steps, target) then
                      error "duplicate named proof ID" else
                      (steps := Redblackmap.insert
                         (!steps, target, Alias id); wrap target)
                  end
                else wrap id
              val value = case value of
                  Term value => if named then
                    error "named proof definition is not a proof"
                    else Term value
                | ProofId id => name_proof ProofId id
                | ProofLambda id => if named then
                    error "named proof definition is not a proof"
                    else ProofLambda id
            in (Redblackmap.insert (aliases, name_text, value),
                HOLset.add (names, name_text)) end
          val (extended, _) = List.foldl install
            (aliases, HOLset.empty String.compare) values
          val parsed = parse_body child extended body
        in case parsed of
            Term value => Term
              {node = #node value, scope = #scope value,
               binder_blocks = #binder_blocks value, source_syntax = NONE,
               occurrence = P.ConstructionOccurrence
                 {value = #node value,
                  role = P.ConstructionLet (List.map (fn (name, _) =>
                    (key session name, P.proof_symbol_text name)) values),
                  token = "let", children = List.map
                    (#occurrence o #2) term_values @ [#occurrence value]}}
          | _ => parsed
        end
      and parse_lambda session aliases raw =
        let
          fun strip (List [Atom "lambda", binders, body]) entries sizes =
                let val entries_here = descriptors session binders
                    val _ = if null entries_here then
                      error "lambda requires at least one sorted variable"
                      else ()
                    val keys = List.map #1 entries_here
                    val _ = if HOLset.numItems
                        (HOLset.addList (HOLset.empty String.compare, keys))
                        = List.length keys then () else
                      error "duplicate lambda variable"
                in strip body (entries_here :: entries)
                  (List.length entries_here :: sizes) end
            | strip body entries sizes =
                (List.concat (List.rev entries), List.rev sizes, body)
          val (entries, sizes, raw_body) = strip raw [] []
          (* Flatten only the binder inventory, not its lexical shadowing.
             Hidden outer variables keep distinct Bound IDs, but cannot
             replace the rightmost spelling visible in the body. NUL keys
             cannot be supplied by the proof tokenizer. *)
          fun distinct ((key, name, ty), (seen, result, next)) =
            let val hidden = HOLset.member (seen, key)
                val actual = if hidden then
                    "\000z3-shadow-" ^ Int.toString next else key
            in (HOLset.add (seen, key),
                (actual, name, ty) :: result, next + 1) end
          val (_, lexical_entries, _) = List.foldr distinct
            (HOLset.empty String.compare, [], 0) entries
          val binding = scope session lexical_entries
          val child = binding_session binding
          val result = parse_value child
            (shadow_aliases aliases entries) raw_body
        in case result of
            ProofId id => ProofLambda (save
              (Bind {binding = binding, body = id, lambda_blocks = sizes}))
          | ProofLambda id => ProofLambda (save
              (Bind {binding = binding, body = id, lambda_blocks = sizes}))
          | Term _ => error "proof lambda body is not a proof"
        end
      and parse_bind session aliases body =
        case parse_value session aliases body of
          ProofLambda id => ProofId id
        | ProofId id => ProofId id
        | Term _ => error "proof-bind expects a proof lambda or proof"
      and parse_lemma session aliases indices operands =
        let
          val metadata = case List.map index_text indices of
              theory :: subkind :: rest =>
                mk_th_lemma_metadata (theory, SOME subkind, rest)
            | [theory] => mk_th_lemma_metadata (theory, NONE, [])
            | [] => error "th-lemma rule has no theory index"
          val name = "th-lemma[" ^ #theory metadata ^ "]"
          val rule = case lookup_rule version name of SOME rule => rule
            | NONE => error (registry_lookup_failure version name)
        in parse_rule session aliases rule (SOME metadata) [] operands end
      and parse_rule session aliases (rule : proof_rule) metadata indices
          operands =
        let
          val (premises, conclusion) = case List.rev operands of
              conclusion :: rest => (List.rev rest, conclusion)
            | [] => error ("proof rule " ^ #name rule ^ " has no conclusion")
          val (proofs, arguments) = case #premise_shape rule of
              ZeroPremises =>
                if null premises then ([], []) else
                  error "zero-premise proof rule has extra arguments"
            | OnePremise => if List.length premises = 1 then
                (List.map (proof o parse_value session aliases) premises, [])
              else error "proof rule expects one premise"
            | TwoPremises => if List.length premises = 2 then
                (List.map (proof o parse_value session aliases) premises, [])
              else error "proof rule expects two premises"
            | ListPremises =>
                (List.map (proof o parse_value session aliases) premises, [])
            | TermArguments =>
                if null premises then
                  ([], List.map (fn raw =>
                    case parse_value session aliases raw of
                    Term value => value | _ =>
                      error "proof ID used as a term argument") indices)
                else error "indexed term-argument rule expects one conclusion"
          val conclusion = boolean (parse_value session aliases conclusion)
          val accepts_bind = List.exists (Lib.equal (#replay_handler rule))
            ["nnf_neg", "nnf_pos", "quant_intro"]
        in ProofId (save (Rule {rule = rule, premises = proofs,
          conclusion = conclusion, arguments = arguments,
          metadata = metadata, accepts_bind = accepts_bind})) end
      val no_aliases : (string, 'a constructed_value) Redblackmap.dict =
        Redblackmap.mkDict String.compare
      fun declaration name domain range =
        let val ty = boolSyntax.list_mk_fun
              (List.map (sort terms) (list "function_domain" domain),
               sort terms range)
            val _ = (#declare terms) (name, ty)
            val value = term terms no_aliases (Atom name)
        in variables := #node value :: !variables end
      fun expression raw =
        let val value = parse_outer terms no_aliases raw
        in case value of ProofId id => id
          | ProofLambda _ => error "a proof lambda requires proof-bind"
          | Term _ =>
              let val head = case raw of List (head :: _) =>
                    atom "proof_rule" head | _ => "<term>"
              in error (registry_lookup_failure version head) end end
      fun commands () =
        let val _ = Library.expect_token "(" (tokenizer ())
            val head = tokenizer ()
        in case head of
            "set-logic" =>
              (tokenizer (); Library.expect_token ")" (tokenizer ());
               commands ())
          | "declare-fun" =>
              let val name = tokenizer ()
                  val domain = read tokenizer
                  val range = read tokenizer
                  val _ = Library.expect_token ")" (tokenizer ())
              in declaration name domain range; commands () end
          | "error" =>
              (tokenizer (); Library.expect_token ")" (tokenizer ());
               commands ())
          | "proof" =>
              let val root = expression (read tokenizer)
                  val _ = Library.expect_token ")" (tokenizer ())
              in root end
          | _ => expression (read
              (Library.undo_look_ahead ["(", head] tokenizer))
        end
      fun parse () =
        let val _ = Library.expect_token "(" (tokenizer ())
            val root = commands ()
            val _ = Library.expect_token ")" (tokenizer ())
            val _ = check_complete tokenizer
            val proof =
              {steps = !steps, root = root, vars = List.rev (!variables),
               z3_version = version, close = close}
        in publish
          {reader = #reader terms, proof = proof,
           requested_version = requested_version, close = close} end
    in parse () handle error =>
      ((close () handle _ => ()); raise error) end

  fun create_using make_session (options : F.options) requested_version input
      : proof SmtLib_GraphProof.packet =
    let
      val limit = #index_limit (#recipe_limits options)
      fun make_terms version tokenizer = configure_terms
        (make_session options (policy_description version) tokenizer)
        (Z3_ProofFpConstructors.bounded_entries limit)
        (Z3_ProofLiterals.bounded_word limit)
    in create_using_session (graph_observations (#graph options))
      SmtLib_GraphProof.new requested_version
      (fn () => P.make_proof_stream_tokenizer input) (fn _ => ())
      make_terms end

  fun create_packet options version input =
    create_using F.create_session options version input
  fun create_configured_packet
      (configured : F.configured_options) version input =
    create_using (fn _ => F.create_configured_session configured)
      (#base configured) version input
  fun create_translation_packet options translation version input =
    let
      val configured = SmtLib_GraphTranslation.configured_options
        options translation
    in create_using
      (fn _ => SmtLib_GraphTranslation.create_session options translation)
      (#base configured) version input end
  fun create options version input : proof =
    SmtLib_GraphProof.proof (create_packet options version input)

  fun create_using_with_policy_token_factory_for_backend
      (observations:'a policy_observations) publish make_session
      (options:'a F.constructed_policy_options)
      requested_version make_token check_complete =
    let
      val limit = #index_limit (#recipe_limits options)
      fun make_terms version tokenizer = configure_terms
        (make_session options (policy_description version) tokenizer)
        (Z3_ProofFpConstructors.entries_with_policy limit)
        (Z3_ProofLiterals.word_with_policy limit)
    in create_using_session observations publish requested_version
      make_token check_complete make_terms end

  fun create_using_with_policy_token_factory make_session
      (options:F.policy_options) requested_version make_token check_complete
      : proof SmtLib_GraphProof.packet =
    create_using_with_policy_token_factory_for_backend
      (graph_observations (#graph options)) SmtLib_GraphProof.new
      make_session options requested_version make_token check_complete

  fun create_using_with_policy make_session options version input =
    create_using_with_policy_token_factory make_session options version
      (fn () => P.make_proof_stream_tokenizer input) (fn _ => ())

  fun create_using_with_policy_from_input make_session options version input =
    let
      fun check_complete tokenizer =
        case (SOME (tokenizer ()) handle P.ProofEOF => NONE) of
          NONE => ()
        | SOME _ => raise ERR "parse" "trailing Z3 proof syntax"
    in create_using_with_policy_token_factory make_session options version
      (fn () => P.make_proof_input_tokenizer input) check_complete end

  fun create_packet_with_policy options version input =
    create_using_with_policy F.create_session_with_policy options version input
  fun create_packet_with_policy_from_input options version input =
    create_using_with_policy_from_input F.create_session_with_policy
      options version input
  fun create_configured_packet_with_policy
      (configured : F.policy_configured_options) version input =
    create_using_with_policy
      (fn _ => F.create_configured_session_with_policy configured)
      (#base configured) version input
  fun create_translation_packet_with_policy options translation version input =
    let
      val configured = SmtLib_GraphTranslation.configured_options_with_policy
        options translation
    in create_using_with_policy
      (fn _ => SmtLib_GraphTranslation.create_session_with_policy
        options translation)
      (#base configured) version input end
  fun create_translation_packet_with_policy_from_input options translation
      version input =
    let
      val configured = SmtLib_GraphTranslation.configured_options_with_policy
        options translation
    in create_using_with_policy_from_input
      (fn _ => SmtLib_GraphTranslation.create_session_with_policy
        options translation)
      (#base configured) version input end
  fun create_with_policy options version input : proof =
    SmtLib_GraphProof.proof (create_packet_with_policy options version input)

  local
    datatype recorded = Recorded of
      {packet : proof SmtLib_GraphProof.packet,
       definitions : SmtLib.emitted_definition list}
  in
    type recorded_translation = recorded
    fun create_recorded_translation_packet options translation version input =
      let
        val packet = create_translation_packet
          options translation version input
        val definitions = SmtLib.translation_definitions translation
          handle error => (SmtLib_GraphProof.close packet;raise error)
      in Recorded {packet = packet,definitions = definitions} end
    fun create_recorded_translation_packet_with_policy options translation
        version input =
      let
        val packet = create_translation_packet_with_policy
          options translation version input
        val definitions = SmtLib.translation_definitions translation
          handle error => (SmtLib_GraphProof.close packet;raise error)
      in Recorded {packet = packet,definitions = definitions} end
    fun recorded_packet (Recorded {packet,...}) = packet
    fun recorded_translation_definitions (Recorded {definitions,...}) =
      definitions
  end
end
